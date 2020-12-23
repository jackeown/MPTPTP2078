%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1975+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:58 EST 2020

% Result     : Theorem 3.77s
% Output     : CNFRefutation 3.77s
% Verified   : 
% Statistics : Number of formulae       :  308 (5951 expanded)
%              Number of clauses        :  207 (1070 expanded)
%              Number of leaves         :   24 (1566 expanded)
%              Depth                    :   27
%              Number of atoms          : 1865 (80513 expanded)
%              Number of equality atoms :  232 ( 593 expanded)
%              Maximal formula depth    :   20 (   7 average)
%              Maximal clause size      :   38 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ( v2_waybel_7(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ~ ( ~ r2_hidden(X3,X1)
                        & ~ r2_hidden(X2,X1)
                        & r2_hidden(k13_lattice3(X0,X2,X3),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_waybel_7(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | r2_hidden(X2,X1)
                    | ~ r2_hidden(k13_lattice3(X0,X2,X3),X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_waybel_7(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | r2_hidden(X2,X1)
                    | ~ r2_hidden(k13_lattice3(X0,X2,X3),X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f27])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_waybel_7(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & ~ r2_hidden(X2,X1)
                      & r2_hidden(k13_lattice3(X0,X2,X3),X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ! [X3] :
                      ( r2_hidden(X3,X1)
                      | r2_hidden(X2,X1)
                      | ~ r2_hidden(k13_lattice3(X0,X2,X3),X1)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v2_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_waybel_7(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & ~ r2_hidden(X2,X1)
                      & r2_hidden(k13_lattice3(X0,X2,X3),X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | r2_hidden(X4,X1)
                      | ~ r2_hidden(k13_lattice3(X0,X4,X5),X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v2_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(rectify,[],[f52])).

fof(f55,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & ~ r2_hidden(X2,X1)
          & r2_hidden(k13_lattice3(X0,X2,X3),X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & ~ r2_hidden(X2,X1)
        & r2_hidden(k13_lattice3(X0,X2,sK3(X0,X1)),X1)
        & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X2,X1)
              & r2_hidden(k13_lattice3(X0,X2,X3),X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r2_hidden(X3,X1)
            & ~ r2_hidden(sK2(X0,X1),X1)
            & r2_hidden(k13_lattice3(X0,sK2(X0,X1),X3),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_waybel_7(X1,X0)
              | ( ~ r2_hidden(sK3(X0,X1),X1)
                & ~ r2_hidden(sK2(X0,X1),X1)
                & r2_hidden(k13_lattice3(X0,sK2(X0,X1),sK3(X0,X1)),X1)
                & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | r2_hidden(X4,X1)
                      | ~ r2_hidden(k13_lattice3(X0,X4,X5),X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v2_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f53,f55,f54])).

fof(f87,plain,(
    ! [X0,X1] :
      ( v2_waybel_7(X1,X0)
      | m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v11_waybel_1(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ( v2_waybel_7(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_hidden(k7_waybel_1(X0,X2),X1)
                  | r2_hidden(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v11_waybel_1(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0)
              & v2_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v2_waybel_7(X1,X0)
            <=> ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ( r2_hidden(k7_waybel_1(X0,X2),X1)
                    | r2_hidden(X2,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f45,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_waybel_7(X1,X0)
          <~> ! [X2] :
                ( r2_hidden(k7_waybel_1(X0,X2),X1)
                | r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & v2_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v11_waybel_1(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_waybel_7(X1,X0)
          <~> ! [X2] :
                ( r2_hidden(k7_waybel_1(X0,X2),X1)
                | r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & v2_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v11_waybel_1(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f45])).

fof(f62,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ~ r2_hidden(k7_waybel_1(X0,X2),X1)
                & ~ r2_hidden(X2,X1)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ v2_waybel_7(X1,X0) )
          & ( ! [X2] :
                ( r2_hidden(k7_waybel_1(X0,X2),X1)
                | r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | v2_waybel_7(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & v2_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v11_waybel_1(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f46])).

fof(f63,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ~ r2_hidden(k7_waybel_1(X0,X2),X1)
                & ~ r2_hidden(X2,X1)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ v2_waybel_7(X1,X0) )
          & ( ! [X2] :
                ( r2_hidden(k7_waybel_1(X0,X2),X1)
                | r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | v2_waybel_7(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & v2_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v11_waybel_1(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f62])).

fof(f64,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ~ r2_hidden(k7_waybel_1(X0,X2),X1)
                & ~ r2_hidden(X2,X1)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ v2_waybel_7(X1,X0) )
          & ( ! [X3] :
                ( r2_hidden(k7_waybel_1(X0,X3),X1)
                | r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            | v2_waybel_7(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & v2_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v11_waybel_1(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(rectify,[],[f63])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(k7_waybel_1(X0,X2),X1)
          & ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ~ r2_hidden(k7_waybel_1(X0,sK8),X1)
        & ~ r2_hidden(sK8,X1)
        & m1_subset_1(sK8,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ~ r2_hidden(k7_waybel_1(X0,X2),X1)
                & ~ r2_hidden(X2,X1)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ v2_waybel_7(X1,X0) )
          & ( ! [X3] :
                ( r2_hidden(k7_waybel_1(X0,X3),X1)
                | r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            | v2_waybel_7(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & v2_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
     => ( ( ? [X2] :
              ( ~ r2_hidden(k7_waybel_1(X0,X2),sK7)
              & ~ r2_hidden(X2,sK7)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v2_waybel_7(sK7,X0) )
        & ( ! [X3] :
              ( r2_hidden(k7_waybel_1(X0,X3),sK7)
              | r2_hidden(X3,sK7)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | v2_waybel_7(sK7,X0) )
        & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0)))
        & v13_waybel_0(sK7,X0)
        & v2_waybel_0(sK7,X0)
        & ~ v1_xboole_0(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ? [X2] :
                  ( ~ r2_hidden(k7_waybel_1(X0,X2),X1)
                  & ~ r2_hidden(X2,X1)
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v2_waybel_7(X1,X0) )
            & ( ! [X3] :
                  ( r2_hidden(k7_waybel_1(X0,X3),X1)
                  | r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | v2_waybel_7(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v11_waybel_1(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ? [X1] :
          ( ( ? [X2] :
                ( ~ r2_hidden(k7_waybel_1(sK6,X2),X1)
                & ~ r2_hidden(X2,X1)
                & m1_subset_1(X2,u1_struct_0(sK6)) )
            | ~ v2_waybel_7(X1,sK6) )
          & ( ! [X3] :
                ( r2_hidden(k7_waybel_1(sK6,X3),X1)
                | r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(sK6)) )
            | v2_waybel_7(X1,sK6) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
          & v13_waybel_0(X1,sK6)
          & v2_waybel_0(X1,sK6)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(sK6)
      & v2_lattice3(sK6)
      & v1_lattice3(sK6)
      & v11_waybel_1(sK6)
      & v5_orders_2(sK6)
      & v4_orders_2(sK6)
      & v3_orders_2(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,
    ( ( ( ~ r2_hidden(k7_waybel_1(sK6,sK8),sK7)
        & ~ r2_hidden(sK8,sK7)
        & m1_subset_1(sK8,u1_struct_0(sK6)) )
      | ~ v2_waybel_7(sK7,sK6) )
    & ( ! [X3] :
          ( r2_hidden(k7_waybel_1(sK6,X3),sK7)
          | r2_hidden(X3,sK7)
          | ~ m1_subset_1(X3,u1_struct_0(sK6)) )
      | v2_waybel_7(sK7,sK6) )
    & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    & v13_waybel_0(sK7,sK6)
    & v2_waybel_0(sK7,sK6)
    & ~ v1_xboole_0(sK7)
    & l1_orders_2(sK6)
    & v2_lattice3(sK6)
    & v1_lattice3(sK6)
    & v11_waybel_1(sK6)
    & v5_orders_2(sK6)
    & v4_orders_2(sK6)
    & v3_orders_2(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f64,f67,f66,f65])).

fof(f111,plain,(
    v1_lattice3(sK6) ),
    inference(cnf_transformation,[],[f68])).

fof(f107,plain,(
    v3_orders_2(sK6) ),
    inference(cnf_transformation,[],[f68])).

fof(f108,plain,(
    v4_orders_2(sK6) ),
    inference(cnf_transformation,[],[f68])).

fof(f109,plain,(
    v5_orders_2(sK6) ),
    inference(cnf_transformation,[],[f68])).

fof(f113,plain,(
    l1_orders_2(sK6) ),
    inference(cnf_transformation,[],[f68])).

fof(f114,plain,(
    ~ v1_xboole_0(sK7) ),
    inference(cnf_transformation,[],[f68])).

fof(f115,plain,(
    v2_waybel_0(sK7,sK6) ),
    inference(cnf_transformation,[],[f68])).

fof(f116,plain,(
    v13_waybel_0(sK7,sK6) ),
    inference(cnf_transformation,[],[f68])).

fof(f117,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f68])).

fof(f119,plain,
    ( m1_subset_1(sK8,u1_struct_0(sK6))
    | ~ v2_waybel_7(sK7,sK6) ),
    inference(cnf_transformation,[],[f68])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v11_waybel_1(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( k13_lattice3(X0,k7_waybel_1(X0,X1),k7_waybel_1(X0,X2)) = k7_waybel_1(X0,k12_lattice3(X0,X1,X2))
                & k7_waybel_1(X0,k13_lattice3(X0,X1,X2)) = k12_lattice3(X0,k7_waybel_1(X0,X1),k7_waybel_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k13_lattice3(X0,k7_waybel_1(X0,X1),k7_waybel_1(X0,X2)) = k7_waybel_1(X0,k12_lattice3(X0,X1,X2))
                & k7_waybel_1(X0,k13_lattice3(X0,X1,X2)) = k12_lattice3(X0,k7_waybel_1(X0,X1),k7_waybel_1(X0,X2)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k13_lattice3(X0,k7_waybel_1(X0,X1),k7_waybel_1(X0,X2)) = k7_waybel_1(X0,k12_lattice3(X0,X1,X2))
                & k7_waybel_1(X0,k13_lattice3(X0,X1,X2)) = k12_lattice3(X0,k7_waybel_1(X0,X1),k7_waybel_1(X0,X2)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( k7_waybel_1(X0,k13_lattice3(X0,X1,X2)) = k12_lattice3(X0,k7_waybel_1(X0,X1),k7_waybel_1(X0,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f110,plain,(
    v11_waybel_1(sK6) ),
    inference(cnf_transformation,[],[f68])).

fof(f112,plain,(
    v2_lattice3(sK6) ),
    inference(cnf_transformation,[],[f68])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f19])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f120,plain,
    ( ~ r2_hidden(sK8,sK7)
    | ~ v2_waybel_7(sK7,sK6) ),
    inference(cnf_transformation,[],[f68])).

fof(f121,plain,
    ( ~ r2_hidden(k7_waybel_1(sK6,sK8),sK7)
    | ~ v2_waybel_7(sK7,sK6) ),
    inference(cnf_transformation,[],[f68])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( ( v11_waybel_1(X0)
          & ~ v2_struct_0(X0) )
       => ( v10_waybel_1(X0)
          & v2_waybel_1(X0)
          & v3_yellow_0(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( ( v11_waybel_1(X0)
          & ~ v2_struct_0(X0) )
       => ( v2_waybel_1(X0)
          & v3_yellow_0(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f18,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( ( v11_waybel_1(X0)
          & ~ v2_struct_0(X0) )
       => ( v3_yellow_0(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f23,plain,(
    ! [X0] :
      ( ( v3_yellow_0(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f24,plain,(
    ! [X0] :
      ( ( v3_yellow_0(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f23])).

fof(f78,plain,(
    ! [X0] :
      ( v3_yellow_0(X0)
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v3_yellow_0(X0)
       => ( v2_yellow_0(X0)
          & v1_yellow_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ( v2_yellow_0(X0)
        & v1_yellow_0(X0) )
      | ~ v3_yellow_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f22,plain,(
    ! [X0] :
      ( ( v2_yellow_0(X0)
        & v1_yellow_0(X0) )
      | ~ v3_yellow_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f21])).

fof(f71,plain,(
    ! [X0] :
      ( v2_yellow_0(X0)
      | ~ v3_yellow_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f9,axiom,(
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

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f94,plain,(
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
    inference(cnf_transformation,[],[f34])).

fof(f75,plain,(
    ! [X0] :
      ( v5_orders_2(X0)
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f74,plain,(
    ! [X0] :
      ( v4_orders_2(X0)
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f73,plain,(
    ! [X0] :
      ( v3_orders_2(X0)
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k7_waybel_1(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_waybel_1(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_waybel_1(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f93,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_waybel_1(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f85,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(k13_lattice3(X0,X4,X5),X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v2_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v11_waybel_1(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( k13_lattice3(X0,X1,k7_waybel_1(X0,X1)) = k4_yellow_0(X0)
            & k3_yellow_0(X0) = k12_lattice3(X0,X1,k7_waybel_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k13_lattice3(X0,X1,k7_waybel_1(X0,X1)) = k4_yellow_0(X0)
            & k3_yellow_0(X0) = k12_lattice3(X0,X1,k7_waybel_1(X0,X1)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k13_lattice3(X0,X1,k7_waybel_1(X0,X1)) = k4_yellow_0(X0)
            & k3_yellow_0(X0) = k12_lattice3(X0,X1,k7_waybel_1(X0,X1)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f96,plain,(
    ! [X0,X1] :
      ( k13_lattice3(X0,X1,k7_waybel_1(X0,X1)) = k4_yellow_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f86,plain,(
    ! [X0,X1] :
      ( v2_waybel_7(X1,X0)
      | m1_subset_1(sK2(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0) )
         => ( v2_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r2_hidden(X3,X1)
                        & r2_hidden(X2,X1) )
                     => r2_hidden(k12_lattice3(X0,X2,X3),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(k12_lattice3(X0,X2,X3),X1)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(k12_lattice3(X0,X2,X3),X1)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f39])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_waybel_0(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(k12_lattice3(X0,X2,X3),X1)
                      & r2_hidden(X3,X1)
                      & r2_hidden(X2,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ! [X3] :
                      ( r2_hidden(k12_lattice3(X0,X2,X3),X1)
                      | ~ r2_hidden(X3,X1)
                      | ~ r2_hidden(X2,X1)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v2_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_waybel_0(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(k12_lattice3(X0,X2,X3),X1)
                      & r2_hidden(X3,X1)
                      & r2_hidden(X2,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(k12_lattice3(X0,X4,X5),X1)
                      | ~ r2_hidden(X5,X1)
                      | ~ r2_hidden(X4,X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v2_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(rectify,[],[f57])).

fof(f60,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(k12_lattice3(X0,X2,X3),X1)
          & r2_hidden(X3,X1)
          & r2_hidden(X2,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(k12_lattice3(X0,X2,sK5(X0,X1)),X1)
        & r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(X2,X1)
        & m1_subset_1(sK5(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(k12_lattice3(X0,X2,X3),X1)
              & r2_hidden(X3,X1)
              & r2_hidden(X2,X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r2_hidden(k12_lattice3(X0,sK4(X0,X1),X3),X1)
            & r2_hidden(X3,X1)
            & r2_hidden(sK4(X0,X1),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_waybel_0(X1,X0)
              | ( ~ r2_hidden(k12_lattice3(X0,sK4(X0,X1),sK5(X0,X1)),X1)
                & r2_hidden(sK5(X0,X1),X1)
                & r2_hidden(sK4(X0,X1),X1)
                & m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(k12_lattice3(X0,X4,X5),X1)
                      | ~ r2_hidden(X5,X1)
                      | ~ r2_hidden(X4,X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v2_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f58,f60,f59])).

fof(f99,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k12_lattice3(X0,X4,X5),X1)
      | ~ r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v2_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f43])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f88,plain,(
    ! [X0,X1] :
      ( v2_waybel_7(X1,X0)
      | r2_hidden(k13_lattice3(X0,sK2(X0,X1),sK3(X0,X1)),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f95,plain,(
    ! [X0,X1] :
      ( k3_yellow_0(X0) = k12_lattice3(X0,X1,k7_waybel_1(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f48,plain,(
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
    inference(rectify,[],[f47])).

fof(f50,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & r1_orders_2(X0,X2,X3)
          & r2_hidden(X2,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r1_orders_2(X0,X2,sK1(X0,X1))
        & r2_hidden(X2,X1)
        & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
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
            & r1_orders_2(X0,sK0(X0,X1),X3)
            & r2_hidden(sK0(X0,X1),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v13_waybel_0(X1,X0)
              | ( ~ r2_hidden(sK1(X0,X1),X1)
                & r1_orders_2(X0,sK0(X0,X1),sK1(X0,X1))
                & r2_hidden(sK0(X0,X1),X1)
                & m1_subset_1(sK1(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f48,f50,f49])).

fof(f79,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r1_orders_2(X0,X4,X5)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f70,plain,(
    ! [X0] :
      ( v1_yellow_0(X0)
      | ~ v3_yellow_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,k3_yellow_0(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,k3_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,k3_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f105,plain,(
    ! [X0,X1] :
      ( r1_orders_2(X0,k3_yellow_0(X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f90,plain,(
    ! [X0,X1] :
      ( v2_waybel_7(X1,X0)
      | ~ r2_hidden(sK3(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f89,plain,(
    ! [X0,X1] :
      ( v2_waybel_7(X1,X0)
      | ~ r2_hidden(sK2(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f118,plain,(
    ! [X3] :
      ( r2_hidden(k7_waybel_1(sK6,X3),sK7)
      | r2_hidden(X3,sK7)
      | ~ m1_subset_1(X3,u1_struct_0(sK6))
      | v2_waybel_7(sK7,sK6) ) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_19,plain,
    ( ~ v2_waybel_0(X0,X1)
    | v2_waybel_7(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK3(X1,X0),u1_struct_0(X1))
    | ~ v13_waybel_0(X0,X1)
    | v1_xboole_0(X0)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_48,negated_conjecture,
    ( v1_lattice3(sK6) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_1267,plain,
    ( ~ v2_waybel_0(X0,X1)
    | v2_waybel_7(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK3(X1,X0),u1_struct_0(X1))
    | ~ v13_waybel_0(X0,X1)
    | v1_xboole_0(X0)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_48])).

cnf(c_1268,plain,
    ( ~ v2_waybel_0(X0,sK6)
    | v2_waybel_7(X0,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | m1_subset_1(sK3(sK6,X0),u1_struct_0(sK6))
    | ~ v13_waybel_0(X0,sK6)
    | v1_xboole_0(X0)
    | ~ v3_orders_2(sK6)
    | ~ v4_orders_2(sK6)
    | ~ v5_orders_2(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(unflattening,[status(thm)],[c_1267])).

cnf(c_52,negated_conjecture,
    ( v3_orders_2(sK6) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_51,negated_conjecture,
    ( v4_orders_2(sK6) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_50,negated_conjecture,
    ( v5_orders_2(sK6) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_46,negated_conjecture,
    ( l1_orders_2(sK6) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_1272,plain,
    ( ~ v2_waybel_0(X0,sK6)
    | v2_waybel_7(X0,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | m1_subset_1(sK3(sK6,X0),u1_struct_0(sK6))
    | ~ v13_waybel_0(X0,sK6)
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1268,c_52,c_51,c_50,c_46])).

cnf(c_45,negated_conjecture,
    ( ~ v1_xboole_0(sK7) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_1598,plain,
    ( ~ v2_waybel_0(X0,sK6)
    | v2_waybel_7(X0,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | m1_subset_1(sK3(sK6,X0),u1_struct_0(sK6))
    | ~ v13_waybel_0(X0,sK6)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1272,c_45])).

cnf(c_1599,plain,
    ( ~ v2_waybel_0(sK7,sK6)
    | v2_waybel_7(sK7,sK6)
    | m1_subset_1(sK3(sK6,sK7),u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ v13_waybel_0(sK7,sK6) ),
    inference(unflattening,[status(thm)],[c_1598])).

cnf(c_44,negated_conjecture,
    ( v2_waybel_0(sK7,sK6) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_43,negated_conjecture,
    ( v13_waybel_0(sK7,sK6) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_42,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_1601,plain,
    ( v2_waybel_7(sK7,sK6)
    | m1_subset_1(sK3(sK6,sK7),u1_struct_0(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1599,c_44,c_43,c_42])).

cnf(c_3056,plain,
    ( v2_waybel_7(sK7,sK6)
    | m1_subset_1(sK3(sK6,sK7),u1_struct_0(sK6)) ),
    inference(subtyping,[status(esa)],[c_1601])).

cnf(c_3719,plain,
    ( v2_waybel_7(sK7,sK6) = iProver_top
    | m1_subset_1(sK3(sK6,sK7),u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3056])).

cnf(c_1603,plain,
    ( v2_waybel_7(sK7,sK6) = iProver_top
    | m1_subset_1(sK3(sK6,sK7),u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1601])).

cnf(c_40,negated_conjecture,
    ( ~ v2_waybel_7(sK7,sK6)
    | m1_subset_1(sK8,u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_3083,negated_conjecture,
    ( ~ v2_waybel_7(sK7,sK6)
    | m1_subset_1(sK8,u1_struct_0(sK6)) ),
    inference(subtyping,[status(esa)],[c_40])).

cnf(c_3692,plain,
    ( v2_waybel_7(sK7,sK6) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3083])).

cnf(c_29,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v11_waybel_1(X1)
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1)
    | k12_lattice3(X1,k7_waybel_1(X1,X0),k7_waybel_1(X1,X2)) = k7_waybel_1(X1,k13_lattice3(X1,X0,X2)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_49,negated_conjecture,
    ( v11_waybel_1(sK6) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_858,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1)
    | k12_lattice3(X1,k7_waybel_1(X1,X2),k7_waybel_1(X1,X0)) = k7_waybel_1(X1,k13_lattice3(X1,X2,X0))
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_49])).

cnf(c_859,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ l1_orders_2(sK6)
    | v2_struct_0(sK6)
    | k12_lattice3(sK6,k7_waybel_1(sK6,X1),k7_waybel_1(sK6,X0)) = k7_waybel_1(sK6,k13_lattice3(sK6,X1,X0)) ),
    inference(unflattening,[status(thm)],[c_858])).

cnf(c_47,negated_conjecture,
    ( v2_lattice3(sK6) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_0,plain,
    ( ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_168,plain,
    ( ~ l1_orders_2(sK6)
    | ~ v2_lattice3(sK6)
    | ~ v2_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_863,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | k12_lattice3(sK6,k7_waybel_1(sK6,X1),k7_waybel_1(sK6,X0)) = k7_waybel_1(sK6,k13_lattice3(sK6,X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_859,c_47,c_46,c_168])).

cnf(c_3077,plain,
    ( ~ m1_subset_1(X0_62,u1_struct_0(sK6))
    | ~ m1_subset_1(X1_62,u1_struct_0(sK6))
    | k12_lattice3(sK6,k7_waybel_1(sK6,X1_62),k7_waybel_1(sK6,X0_62)) = k7_waybel_1(sK6,k13_lattice3(sK6,X1_62,X0_62)) ),
    inference(subtyping,[status(esa)],[c_863])).

cnf(c_3698,plain,
    ( k12_lattice3(sK6,k7_waybel_1(sK6,X0_62),k7_waybel_1(sK6,X1_62)) = k7_waybel_1(sK6,k13_lattice3(sK6,X0_62,X1_62))
    | m1_subset_1(X1_62,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X0_62,u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3077])).

cnf(c_4731,plain,
    ( k12_lattice3(sK6,k7_waybel_1(sK6,sK8),k7_waybel_1(sK6,X0_62)) = k7_waybel_1(sK6,k13_lattice3(sK6,sK8,X0_62))
    | v2_waybel_7(sK7,sK6) != iProver_top
    | m1_subset_1(X0_62,u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3692,c_3698])).

cnf(c_61,plain,
    ( v2_waybel_0(sK7,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_62,plain,
    ( v13_waybel_0(sK7,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_63,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_67,plain,
    ( v2_waybel_7(sK7,sK6) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_39,negated_conjecture,
    ( ~ v2_waybel_7(sK7,sK6)
    | ~ r2_hidden(sK8,sK7) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_68,plain,
    ( v2_waybel_7(sK7,sK6) != iProver_top
    | r2_hidden(sK8,sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_38,negated_conjecture,
    ( ~ v2_waybel_7(sK7,sK6)
    | ~ r2_hidden(k7_waybel_1(sK6,sK8),sK7) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_69,plain,
    ( v2_waybel_7(sK7,sK6) != iProver_top
    | r2_hidden(k7_waybel_1(sK6,sK8),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_3,plain,
    ( ~ v11_waybel_1(X0)
    | v3_yellow_0(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1,plain,
    ( ~ v3_yellow_0(X0)
    | v2_yellow_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_25,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(k4_yellow_0(X1),X0)
    | ~ v13_waybel_0(X0,X1)
    | v1_xboole_0(X0)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_yellow_0(X1)
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_593,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(k4_yellow_0(X1),X0)
    | ~ v13_waybel_0(X0,X1)
    | v1_xboole_0(X0)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v3_yellow_0(X2)
    | ~ l1_orders_2(X2)
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1)
    | X1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_25])).

cnf(c_594,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(k4_yellow_0(X1),X0)
    | ~ v13_waybel_0(X0,X1)
    | v1_xboole_0(X0)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v3_yellow_0(X1)
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1) ),
    inference(unflattening,[status(thm)],[c_593])).

cnf(c_659,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(k4_yellow_0(X1),X0)
    | ~ v13_waybel_0(X0,X1)
    | v1_xboole_0(X0)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v11_waybel_1(X2)
    | ~ l1_orders_2(X2)
    | ~ l1_orders_2(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | X1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_594])).

cnf(c_660,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(k4_yellow_0(X1),X0)
    | ~ v13_waybel_0(X0,X1)
    | v1_xboole_0(X0)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v11_waybel_1(X1)
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1) ),
    inference(unflattening,[status(thm)],[c_659])).

cnf(c_6,plain,
    ( v5_orders_2(X0)
    | ~ v11_waybel_1(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_7,plain,
    ( v4_orders_2(X0)
    | ~ v11_waybel_1(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_8,plain,
    ( v3_orders_2(X0)
    | ~ v11_waybel_1(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_686,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(k4_yellow_0(X1),X0)
    | ~ v13_waybel_0(X0,X1)
    | v1_xboole_0(X0)
    | ~ v11_waybel_1(X1)
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_660,c_6,c_7,c_8])).

cnf(c_831,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(k4_yellow_0(X1),X0)
    | ~ v13_waybel_0(X0,X1)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_686,c_49])).

cnf(c_832,plain,
    ( ~ v2_waybel_0(X0,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | r2_hidden(k4_yellow_0(sK6),X0)
    | ~ v13_waybel_0(X0,sK6)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(sK6)
    | v2_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_831])).

cnf(c_836,plain,
    ( ~ v2_waybel_0(X0,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | r2_hidden(k4_yellow_0(sK6),X0)
    | ~ v13_waybel_0(X0,sK6)
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_832,c_47,c_46,c_168])).

cnf(c_1656,plain,
    ( ~ v2_waybel_0(X0,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | r2_hidden(k4_yellow_0(sK6),X0)
    | ~ v13_waybel_0(X0,sK6)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_836,c_45])).

cnf(c_1657,plain,
    ( ~ v2_waybel_0(sK7,sK6)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | r2_hidden(k4_yellow_0(sK6),sK7)
    | ~ v13_waybel_0(sK7,sK6) ),
    inference(unflattening,[status(thm)],[c_1656])).

cnf(c_1658,plain,
    ( v2_waybel_0(sK7,sK6) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r2_hidden(k4_yellow_0(sK6),sK7) = iProver_top
    | v13_waybel_0(sK7,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1657])).

cnf(c_3088,plain,
    ( X0_62 = X0_62 ),
    theory(equality)).

cnf(c_3111,plain,
    ( sK7 = sK7 ),
    inference(instantiation,[status(thm)],[c_3088])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k7_waybel_1(X1,X0),u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_962,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k7_waybel_1(X1,X0),u1_struct_0(X1))
    | ~ l1_orders_2(X2)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X2)
    | X1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_24])).

cnf(c_963,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k7_waybel_1(X1,X0),u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1) ),
    inference(unflattening,[status(thm)],[c_962])).

cnf(c_985,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k7_waybel_1(X1,X0),u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_963,c_47])).

cnf(c_986,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | m1_subset_1(k7_waybel_1(sK6,X0),u1_struct_0(sK6))
    | ~ l1_orders_2(sK6) ),
    inference(unflattening,[status(thm)],[c_985])).

cnf(c_990,plain,
    ( m1_subset_1(k7_waybel_1(sK6,X0),u1_struct_0(sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_986,c_46])).

cnf(c_991,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | m1_subset_1(k7_waybel_1(sK6,X0),u1_struct_0(sK6)) ),
    inference(renaming,[status(thm)],[c_990])).

cnf(c_3073,plain,
    ( ~ m1_subset_1(X0_62,u1_struct_0(sK6))
    | m1_subset_1(k7_waybel_1(sK6,X0_62),u1_struct_0(sK6)) ),
    inference(subtyping,[status(esa)],[c_991])).

cnf(c_3802,plain,
    ( m1_subset_1(k7_waybel_1(sK6,sK8),u1_struct_0(sK6))
    | ~ m1_subset_1(sK8,u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_3073])).

cnf(c_3803,plain,
    ( m1_subset_1(k7_waybel_1(sK6,sK8),u1_struct_0(sK6)) = iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3802])).

cnf(c_21,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ v2_waybel_7(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | r2_hidden(X3,X0)
    | r2_hidden(X2,X0)
    | ~ r2_hidden(k13_lattice3(X1,X3,X2),X0)
    | ~ v13_waybel_0(X0,X1)
    | v1_xboole_0(X0)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1195,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ v2_waybel_7(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | r2_hidden(X3,X0)
    | r2_hidden(X2,X0)
    | ~ r2_hidden(k13_lattice3(X1,X3,X2),X0)
    | ~ v13_waybel_0(X0,X1)
    | v1_xboole_0(X0)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_48])).

cnf(c_1196,plain,
    ( ~ v2_waybel_0(X0,sK6)
    | ~ v2_waybel_7(X0,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X2,u1_struct_0(sK6))
    | r2_hidden(X2,X0)
    | r2_hidden(X1,X0)
    | ~ r2_hidden(k13_lattice3(sK6,X2,X1),X0)
    | ~ v13_waybel_0(X0,sK6)
    | v1_xboole_0(X0)
    | ~ v3_orders_2(sK6)
    | ~ v4_orders_2(sK6)
    | ~ v5_orders_2(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(unflattening,[status(thm)],[c_1195])).

cnf(c_1200,plain,
    ( ~ v2_waybel_0(X0,sK6)
    | ~ v2_waybel_7(X0,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X2,u1_struct_0(sK6))
    | r2_hidden(X2,X0)
    | r2_hidden(X1,X0)
    | ~ r2_hidden(k13_lattice3(sK6,X2,X1),X0)
    | ~ v13_waybel_0(X0,sK6)
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1196,c_52,c_51,c_50,c_46])).

cnf(c_1201,plain,
    ( ~ v2_waybel_0(X0,sK6)
    | ~ v2_waybel_7(X0,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X2,u1_struct_0(sK6))
    | r2_hidden(X1,X0)
    | r2_hidden(X2,X0)
    | ~ r2_hidden(k13_lattice3(sK6,X1,X2),X0)
    | ~ v13_waybel_0(X0,sK6)
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_1200])).

cnf(c_1626,plain,
    ( ~ v2_waybel_0(X0,sK6)
    | ~ v2_waybel_7(X0,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X2,u1_struct_0(sK6))
    | r2_hidden(X1,X0)
    | r2_hidden(X2,X0)
    | ~ r2_hidden(k13_lattice3(sK6,X2,X1),X0)
    | ~ v13_waybel_0(X0,sK6)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1201,c_45])).

cnf(c_1627,plain,
    ( ~ v2_waybel_0(sK7,sK6)
    | ~ v2_waybel_7(sK7,sK6)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | r2_hidden(X0,sK7)
    | r2_hidden(X1,sK7)
    | ~ r2_hidden(k13_lattice3(sK6,X0,X1),sK7)
    | ~ v13_waybel_0(sK7,sK6) ),
    inference(unflattening,[status(thm)],[c_1626])).

cnf(c_1631,plain,
    ( ~ r2_hidden(k13_lattice3(sK6,X0,X1),sK7)
    | r2_hidden(X1,sK7)
    | r2_hidden(X0,sK7)
    | ~ v2_waybel_7(sK7,sK6)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1627,c_44,c_43,c_42])).

cnf(c_1632,plain,
    ( ~ v2_waybel_7(sK7,sK6)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | r2_hidden(X0,sK7)
    | r2_hidden(X1,sK7)
    | ~ r2_hidden(k13_lattice3(sK6,X0,X1),sK7) ),
    inference(renaming,[status(thm)],[c_1631])).

cnf(c_3054,plain,
    ( ~ v2_waybel_7(sK7,sK6)
    | ~ m1_subset_1(X0_62,u1_struct_0(sK6))
    | ~ m1_subset_1(X1_62,u1_struct_0(sK6))
    | r2_hidden(X0_62,sK7)
    | r2_hidden(X1_62,sK7)
    | ~ r2_hidden(k13_lattice3(sK6,X0_62,X1_62),sK7) ),
    inference(subtyping,[status(esa)],[c_1632])).

cnf(c_3850,plain,
    ( ~ v2_waybel_7(sK7,sK6)
    | ~ m1_subset_1(X0_62,u1_struct_0(sK6))
    | ~ m1_subset_1(sK8,u1_struct_0(sK6))
    | r2_hidden(X0_62,sK7)
    | ~ r2_hidden(k13_lattice3(sK6,sK8,X0_62),sK7)
    | r2_hidden(sK8,sK7) ),
    inference(instantiation,[status(thm)],[c_3054])).

cnf(c_3946,plain,
    ( ~ v2_waybel_7(sK7,sK6)
    | ~ m1_subset_1(k7_waybel_1(sK6,sK8),u1_struct_0(sK6))
    | ~ m1_subset_1(sK8,u1_struct_0(sK6))
    | ~ r2_hidden(k13_lattice3(sK6,sK8,k7_waybel_1(sK6,sK8)),sK7)
    | r2_hidden(k7_waybel_1(sK6,sK8),sK7)
    | r2_hidden(sK8,sK7) ),
    inference(instantiation,[status(thm)],[c_3850])).

cnf(c_3947,plain,
    ( v2_waybel_7(sK7,sK6) != iProver_top
    | m1_subset_1(k7_waybel_1(sK6,sK8),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(k13_lattice3(sK6,sK8,k7_waybel_1(sK6,sK8)),sK7) != iProver_top
    | r2_hidden(k7_waybel_1(sK6,sK8),sK7) = iProver_top
    | r2_hidden(sK8,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3946])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v11_waybel_1(X1)
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1)
    | k13_lattice3(X1,X0,k7_waybel_1(X1,X0)) = k4_yellow_0(X1) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_918,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1)
    | k13_lattice3(X1,X0,k7_waybel_1(X1,X0)) = k4_yellow_0(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_49])).

cnf(c_919,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ l1_orders_2(sK6)
    | v2_struct_0(sK6)
    | k13_lattice3(sK6,X0,k7_waybel_1(sK6,X0)) = k4_yellow_0(sK6) ),
    inference(unflattening,[status(thm)],[c_918])).

cnf(c_923,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | k13_lattice3(sK6,X0,k7_waybel_1(sK6,X0)) = k4_yellow_0(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_919,c_47,c_46,c_168])).

cnf(c_3074,plain,
    ( ~ m1_subset_1(X0_62,u1_struct_0(sK6))
    | k13_lattice3(sK6,X0_62,k7_waybel_1(sK6,X0_62)) = k4_yellow_0(sK6) ),
    inference(subtyping,[status(esa)],[c_923])).

cnf(c_3701,plain,
    ( k13_lattice3(sK6,X0_62,k7_waybel_1(sK6,X0_62)) = k4_yellow_0(sK6)
    | m1_subset_1(X0_62,u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3074])).

cnf(c_4503,plain,
    ( k13_lattice3(sK6,sK8,k7_waybel_1(sK6,sK8)) = k4_yellow_0(sK6)
    | v2_waybel_7(sK7,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3692,c_3701])).

cnf(c_3091,plain,
    ( ~ r2_hidden(X0_62,X1_62)
    | r2_hidden(X2_62,X3_62)
    | X2_62 != X0_62
    | X3_62 != X1_62 ),
    theory(equality)).

cnf(c_4117,plain,
    ( r2_hidden(X0_62,X1_62)
    | ~ r2_hidden(k4_yellow_0(sK6),sK7)
    | X0_62 != k4_yellow_0(sK6)
    | X1_62 != sK7 ),
    inference(instantiation,[status(thm)],[c_3091])).

cnf(c_4841,plain,
    ( r2_hidden(k13_lattice3(sK6,sK8,k7_waybel_1(sK6,sK8)),X0_62)
    | ~ r2_hidden(k4_yellow_0(sK6),sK7)
    | X0_62 != sK7
    | k13_lattice3(sK6,sK8,k7_waybel_1(sK6,sK8)) != k4_yellow_0(sK6) ),
    inference(instantiation,[status(thm)],[c_4117])).

cnf(c_4842,plain,
    ( X0_62 != sK7
    | k13_lattice3(sK6,sK8,k7_waybel_1(sK6,sK8)) != k4_yellow_0(sK6)
    | r2_hidden(k13_lattice3(sK6,sK8,k7_waybel_1(sK6,sK8)),X0_62) = iProver_top
    | r2_hidden(k4_yellow_0(sK6),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4841])).

cnf(c_4844,plain,
    ( k13_lattice3(sK6,sK8,k7_waybel_1(sK6,sK8)) != k4_yellow_0(sK6)
    | sK7 != sK7
    | r2_hidden(k13_lattice3(sK6,sK8,k7_waybel_1(sK6,sK8)),sK7) = iProver_top
    | r2_hidden(k4_yellow_0(sK6),sK7) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4842])).

cnf(c_4885,plain,
    ( v2_waybel_7(sK7,sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4731,c_61,c_62,c_63,c_67,c_68,c_69,c_1658,c_3111,c_3803,c_3947,c_4503,c_4844])).

cnf(c_5231,plain,
    ( m1_subset_1(sK3(sK6,sK7),u1_struct_0(sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3719,c_61,c_62,c_63,c_67,c_68,c_69,c_1603,c_1658,c_3111,c_3803,c_3947,c_4503,c_4844])).

cnf(c_20,plain,
    ( ~ v2_waybel_0(X0,X1)
    | v2_waybel_7(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK2(X1,X0),u1_struct_0(X1))
    | ~ v13_waybel_0(X0,X1)
    | v1_xboole_0(X0)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1237,plain,
    ( ~ v2_waybel_0(X0,X1)
    | v2_waybel_7(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK2(X1,X0),u1_struct_0(X1))
    | ~ v13_waybel_0(X0,X1)
    | v1_xboole_0(X0)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_48])).

cnf(c_1238,plain,
    ( ~ v2_waybel_0(X0,sK6)
    | v2_waybel_7(X0,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | m1_subset_1(sK2(sK6,X0),u1_struct_0(sK6))
    | ~ v13_waybel_0(X0,sK6)
    | v1_xboole_0(X0)
    | ~ v3_orders_2(sK6)
    | ~ v4_orders_2(sK6)
    | ~ v5_orders_2(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(unflattening,[status(thm)],[c_1237])).

cnf(c_1242,plain,
    ( ~ v2_waybel_0(X0,sK6)
    | v2_waybel_7(X0,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | m1_subset_1(sK2(sK6,X0),u1_struct_0(sK6))
    | ~ v13_waybel_0(X0,sK6)
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1238,c_52,c_51,c_50,c_46])).

cnf(c_1612,plain,
    ( ~ v2_waybel_0(X0,sK6)
    | v2_waybel_7(X0,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | m1_subset_1(sK2(sK6,X0),u1_struct_0(sK6))
    | ~ v13_waybel_0(X0,sK6)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1242,c_45])).

cnf(c_1613,plain,
    ( ~ v2_waybel_0(sK7,sK6)
    | v2_waybel_7(sK7,sK6)
    | m1_subset_1(sK2(sK6,sK7),u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ v13_waybel_0(sK7,sK6) ),
    inference(unflattening,[status(thm)],[c_1612])).

cnf(c_1615,plain,
    ( v2_waybel_7(sK7,sK6)
    | m1_subset_1(sK2(sK6,sK7),u1_struct_0(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1613,c_44,c_43,c_42])).

cnf(c_3055,plain,
    ( v2_waybel_7(sK7,sK6)
    | m1_subset_1(sK2(sK6,sK7),u1_struct_0(sK6)) ),
    inference(subtyping,[status(esa)],[c_1615])).

cnf(c_3720,plain,
    ( v2_waybel_7(sK7,sK6) = iProver_top
    | m1_subset_1(sK2(sK6,sK7),u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3055])).

cnf(c_1617,plain,
    ( v2_waybel_7(sK7,sK6) = iProver_top
    | m1_subset_1(sK2(sK6,sK7),u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1615])).

cnf(c_5300,plain,
    ( m1_subset_1(sK2(sK6,sK7),u1_struct_0(sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3720,c_61,c_62,c_63,c_67,c_68,c_69,c_1617,c_1658,c_3111,c_3803,c_3947,c_4503,c_4844])).

cnf(c_5305,plain,
    ( k12_lattice3(sK6,k7_waybel_1(sK6,sK2(sK6,sK7)),k7_waybel_1(sK6,X0_62)) = k7_waybel_1(sK6,k13_lattice3(sK6,sK2(sK6,sK7),X0_62))
    | m1_subset_1(X0_62,u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5300,c_3698])).

cnf(c_13053,plain,
    ( k12_lattice3(sK6,k7_waybel_1(sK6,sK2(sK6,sK7)),k7_waybel_1(sK6,sK3(sK6,sK7))) = k7_waybel_1(sK6,k13_lattice3(sK6,sK2(sK6,sK7),sK3(sK6,sK7))) ),
    inference(superposition,[status(thm)],[c_5231,c_5305])).

cnf(c_35,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(X3,X0)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(k12_lattice3(X1,X3,X2),X0)
    | ~ v13_waybel_0(X0,X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1003,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(X3,X0)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(k12_lattice3(X1,X3,X2),X0)
    | ~ v13_waybel_0(X0,X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_35,c_47])).

cnf(c_1004,plain,
    ( ~ v2_waybel_0(X0,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X2,u1_struct_0(sK6))
    | ~ r2_hidden(X2,X0)
    | ~ r2_hidden(X1,X0)
    | r2_hidden(k12_lattice3(sK6,X2,X1),X0)
    | ~ v13_waybel_0(X0,sK6)
    | ~ v5_orders_2(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(unflattening,[status(thm)],[c_1003])).

cnf(c_1008,plain,
    ( ~ v2_waybel_0(X0,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X2,u1_struct_0(sK6))
    | ~ r2_hidden(X2,X0)
    | ~ r2_hidden(X1,X0)
    | r2_hidden(k12_lattice3(sK6,X2,X1),X0)
    | ~ v13_waybel_0(X0,sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1004,c_50,c_46])).

cnf(c_1009,plain,
    ( ~ v2_waybel_0(X0,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X2,u1_struct_0(sK6))
    | ~ r2_hidden(X1,X0)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(k12_lattice3(sK6,X1,X2),X0)
    | ~ v13_waybel_0(X0,sK6) ),
    inference(renaming,[status(thm)],[c_1008])).

cnf(c_37,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_1030,plain,
    ( ~ v2_waybel_0(X0,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(X1,X0)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(k12_lattice3(sK6,X2,X1),X0)
    | ~ v13_waybel_0(X0,sK6) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1009,c_37,c_37])).

cnf(c_3072,plain,
    ( ~ v2_waybel_0(X0_62,sK6)
    | ~ m1_subset_1(X0_62,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(X1_62,X0_62)
    | ~ r2_hidden(X2_62,X0_62)
    | r2_hidden(k12_lattice3(sK6,X2_62,X1_62),X0_62)
    | ~ v13_waybel_0(X0_62,sK6) ),
    inference(subtyping,[status(esa)],[c_1030])).

cnf(c_3703,plain,
    ( v2_waybel_0(X0_62,sK6) != iProver_top
    | m1_subset_1(X0_62,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r2_hidden(X1_62,X0_62) != iProver_top
    | r2_hidden(X2_62,X0_62) != iProver_top
    | r2_hidden(k12_lattice3(sK6,X1_62,X2_62),X0_62) = iProver_top
    | v13_waybel_0(X0_62,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3072])).

cnf(c_13400,plain,
    ( v2_waybel_0(X0_62,sK6) != iProver_top
    | m1_subset_1(X0_62,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r2_hidden(k7_waybel_1(sK6,k13_lattice3(sK6,sK2(sK6,sK7),sK3(sK6,sK7))),X0_62) = iProver_top
    | r2_hidden(k7_waybel_1(sK6,sK2(sK6,sK7)),X0_62) != iProver_top
    | r2_hidden(k7_waybel_1(sK6,sK3(sK6,sK7)),X0_62) != iProver_top
    | v13_waybel_0(X0_62,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_13053,c_3703])).

cnf(c_13402,plain,
    ( v2_waybel_0(sK7,sK6) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r2_hidden(k7_waybel_1(sK6,k13_lattice3(sK6,sK2(sK6,sK7),sK3(sK6,sK7))),sK7) = iProver_top
    | r2_hidden(k7_waybel_1(sK6,sK2(sK6,sK7)),sK7) != iProver_top
    | r2_hidden(k7_waybel_1(sK6,sK3(sK6,sK7)),sK7) != iProver_top
    | v13_waybel_0(sK7,sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_13400])).

cnf(c_18,plain,
    ( ~ v2_waybel_0(X0,X1)
    | v2_waybel_7(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(k13_lattice3(X1,sK2(X1,X0),sK3(X1,X0)),X0)
    | ~ v13_waybel_0(X0,X1)
    | v1_xboole_0(X0)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1297,plain,
    ( ~ v2_waybel_0(X0,X1)
    | v2_waybel_7(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(k13_lattice3(X1,sK2(X1,X0),sK3(X1,X0)),X0)
    | ~ v13_waybel_0(X0,X1)
    | v1_xboole_0(X0)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_48])).

cnf(c_1298,plain,
    ( ~ v2_waybel_0(X0,sK6)
    | v2_waybel_7(X0,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | r2_hidden(k13_lattice3(sK6,sK2(sK6,X0),sK3(sK6,X0)),X0)
    | ~ v13_waybel_0(X0,sK6)
    | v1_xboole_0(X0)
    | ~ v3_orders_2(sK6)
    | ~ v4_orders_2(sK6)
    | ~ v5_orders_2(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(unflattening,[status(thm)],[c_1297])).

cnf(c_1302,plain,
    ( ~ v2_waybel_0(X0,sK6)
    | v2_waybel_7(X0,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | r2_hidden(k13_lattice3(sK6,sK2(sK6,X0),sK3(sK6,X0)),X0)
    | ~ v13_waybel_0(X0,sK6)
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1298,c_52,c_51,c_50,c_46])).

cnf(c_1584,plain,
    ( ~ v2_waybel_0(X0,sK6)
    | v2_waybel_7(X0,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | r2_hidden(k13_lattice3(sK6,sK2(sK6,X0),sK3(sK6,X0)),X0)
    | ~ v13_waybel_0(X0,sK6)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1302,c_45])).

cnf(c_1585,plain,
    ( ~ v2_waybel_0(sK7,sK6)
    | v2_waybel_7(sK7,sK6)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | r2_hidden(k13_lattice3(sK6,sK2(sK6,sK7),sK3(sK6,sK7)),sK7)
    | ~ v13_waybel_0(sK7,sK6) ),
    inference(unflattening,[status(thm)],[c_1584])).

cnf(c_1587,plain,
    ( r2_hidden(k13_lattice3(sK6,sK2(sK6,sK7),sK3(sK6,sK7)),sK7)
    | v2_waybel_7(sK7,sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1585,c_44,c_43,c_42])).

cnf(c_1588,plain,
    ( v2_waybel_7(sK7,sK6)
    | r2_hidden(k13_lattice3(sK6,sK2(sK6,sK7),sK3(sK6,sK7)),sK7) ),
    inference(renaming,[status(thm)],[c_1587])).

cnf(c_3057,plain,
    ( v2_waybel_7(sK7,sK6)
    | r2_hidden(k13_lattice3(sK6,sK2(sK6,sK7),sK3(sK6,sK7)),sK7) ),
    inference(subtyping,[status(esa)],[c_1588])).

cnf(c_3718,plain,
    ( v2_waybel_7(sK7,sK6) = iProver_top
    | r2_hidden(k13_lattice3(sK6,sK2(sK6,sK7),sK3(sK6,sK7)),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3057])).

cnf(c_1589,plain,
    ( v2_waybel_7(sK7,sK6) = iProver_top
    | r2_hidden(k13_lattice3(sK6,sK2(sK6,sK7),sK3(sK6,sK7)),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1588])).

cnf(c_5315,plain,
    ( r2_hidden(k13_lattice3(sK6,sK2(sK6,sK7),sK3(sK6,sK7)),sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3718,c_61,c_62,c_63,c_67,c_68,c_69,c_1589,c_1658,c_3111,c_3803,c_3947,c_4503,c_4844])).

cnf(c_3081,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(subtyping,[status(esa)],[c_42])).

cnf(c_3694,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3081])).

cnf(c_3086,plain,
    ( m1_subset_1(X0_62,X0_64)
    | ~ m1_subset_1(X1_62,k1_zfmisc_1(X0_64))
    | ~ r2_hidden(X0_62,X1_62) ),
    inference(subtyping,[status(esa)],[c_37])).

cnf(c_3689,plain,
    ( m1_subset_1(X0_62,X0_64) = iProver_top
    | m1_subset_1(X1_62,k1_zfmisc_1(X0_64)) != iProver_top
    | r2_hidden(X0_62,X1_62) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3086])).

cnf(c_4061,plain,
    ( m1_subset_1(X0_62,u1_struct_0(sK6)) = iProver_top
    | r2_hidden(X0_62,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_3694,c_3689])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v11_waybel_1(X1)
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1)
    | k12_lattice3(X1,X0,k7_waybel_1(X1,X0)) = k3_yellow_0(X1) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_900,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1)
    | k12_lattice3(X1,X0,k7_waybel_1(X1,X0)) = k3_yellow_0(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_49])).

cnf(c_901,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ l1_orders_2(sK6)
    | v2_struct_0(sK6)
    | k12_lattice3(sK6,X0,k7_waybel_1(sK6,X0)) = k3_yellow_0(sK6) ),
    inference(unflattening,[status(thm)],[c_900])).

cnf(c_905,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | k12_lattice3(sK6,X0,k7_waybel_1(sK6,X0)) = k3_yellow_0(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_901,c_47,c_46,c_168])).

cnf(c_3075,plain,
    ( ~ m1_subset_1(X0_62,u1_struct_0(sK6))
    | k12_lattice3(sK6,X0_62,k7_waybel_1(sK6,X0_62)) = k3_yellow_0(sK6) ),
    inference(subtyping,[status(esa)],[c_905])).

cnf(c_3700,plain,
    ( k12_lattice3(sK6,X0_62,k7_waybel_1(sK6,X0_62)) = k3_yellow_0(sK6)
    | m1_subset_1(X0_62,u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3075])).

cnf(c_4476,plain,
    ( k12_lattice3(sK6,X0_62,k7_waybel_1(sK6,X0_62)) = k3_yellow_0(sK6)
    | r2_hidden(X0_62,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_4061,c_3700])).

cnf(c_5319,plain,
    ( k12_lattice3(sK6,k13_lattice3(sK6,sK2(sK6,sK7),sK3(sK6,sK7)),k7_waybel_1(sK6,k13_lattice3(sK6,sK2(sK6,sK7),sK3(sK6,sK7)))) = k3_yellow_0(sK6) ),
    inference(superposition,[status(thm)],[c_5315,c_4476])).

cnf(c_7445,plain,
    ( v2_waybel_0(X0_62,sK6) != iProver_top
    | m1_subset_1(X0_62,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r2_hidden(k13_lattice3(sK6,sK2(sK6,sK7),sK3(sK6,sK7)),X0_62) != iProver_top
    | r2_hidden(k7_waybel_1(sK6,k13_lattice3(sK6,sK2(sK6,sK7),sK3(sK6,sK7))),X0_62) != iProver_top
    | r2_hidden(k3_yellow_0(sK6),X0_62) = iProver_top
    | v13_waybel_0(X0_62,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_5319,c_3703])).

cnf(c_7447,plain,
    ( v2_waybel_0(sK7,sK6) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r2_hidden(k13_lattice3(sK6,sK2(sK6,sK7),sK3(sK6,sK7)),sK7) != iProver_top
    | r2_hidden(k7_waybel_1(sK6,k13_lattice3(sK6,sK2(sK6,sK7),sK3(sK6,sK7))),sK7) != iProver_top
    | r2_hidden(k3_yellow_0(sK6),sK7) = iProver_top
    | v13_waybel_0(sK7,sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7445])).

cnf(c_15,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(X1,X3)
    | r2_hidden(X2,X3)
    | ~ v13_waybel_0(X3,X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2,plain,
    ( v1_yellow_0(X0)
    | ~ v3_yellow_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_36,plain,
    ( r1_orders_2(X0,k3_yellow_0(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v1_yellow_0(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_563,plain,
    ( r1_orders_2(X0,k3_yellow_0(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v3_yellow_0(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_2,c_36])).

cnf(c_633,plain,
    ( r1_orders_2(X0,k3_yellow_0(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v11_waybel_1(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_3,c_563])).

cnf(c_637,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(X0))
    | r1_orders_2(X0,k3_yellow_0(X0),X1)
    | ~ v11_waybel_1(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_633,c_6,c_3,c_563])).

cnf(c_638,plain,
    ( r1_orders_2(X0,k3_yellow_0(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v11_waybel_1(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_637])).

cnf(c_742,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X5))
    | ~ r2_hidden(X3,X0)
    | r2_hidden(X2,X0)
    | ~ v13_waybel_0(X0,X1)
    | ~ v11_waybel_1(X5)
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X5)
    | v2_struct_0(X5)
    | X4 != X2
    | X5 != X1
    | k3_yellow_0(X5) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_638])).

cnf(c_743,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(k3_yellow_0(X1),u1_struct_0(X1))
    | r2_hidden(X2,X0)
    | ~ r2_hidden(k3_yellow_0(X1),X0)
    | ~ v13_waybel_0(X0,X1)
    | ~ v11_waybel_1(X1)
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1) ),
    inference(unflattening,[status(thm)],[c_742])).

cnf(c_765,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,X0)
    | ~ r2_hidden(k3_yellow_0(X1),X0)
    | ~ v13_waybel_0(X0,X1)
    | ~ v11_waybel_1(X1)
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_743,c_37])).

cnf(c_804,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,X0)
    | ~ r2_hidden(k3_yellow_0(X1),X0)
    | ~ v13_waybel_0(X0,X1)
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_765,c_49])).

cnf(c_805,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | r2_hidden(X1,X0)
    | ~ r2_hidden(k3_yellow_0(sK6),X0)
    | ~ v13_waybel_0(X0,sK6)
    | ~ l1_orders_2(sK6)
    | v2_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_804])).

cnf(c_809,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | r2_hidden(X1,X0)
    | ~ r2_hidden(k3_yellow_0(sK6),X0)
    | ~ v13_waybel_0(X0,sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_805,c_47,c_46,c_168])).

cnf(c_3078,plain,
    ( ~ m1_subset_1(X0_62,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1_62,u1_struct_0(sK6))
    | r2_hidden(X1_62,X0_62)
    | ~ r2_hidden(k3_yellow_0(sK6),X0_62)
    | ~ v13_waybel_0(X0_62,sK6) ),
    inference(subtyping,[status(esa)],[c_809])).

cnf(c_3697,plain,
    ( m1_subset_1(X0_62,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | m1_subset_1(X1_62,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X1_62,X0_62) = iProver_top
    | r2_hidden(k3_yellow_0(sK6),X0_62) != iProver_top
    | v13_waybel_0(X0_62,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3078])).

cnf(c_4630,plain,
    ( m1_subset_1(X0_62,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X0_62,sK7) = iProver_top
    | r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top
    | v13_waybel_0(sK7,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3694,c_3697])).

cnf(c_16,plain,
    ( ~ v2_waybel_0(X0,X1)
    | v2_waybel_7(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(sK3(X1,X0),X0)
    | ~ v13_waybel_0(X0,X1)
    | v1_xboole_0(X0)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1357,plain,
    ( ~ v2_waybel_0(X0,X1)
    | v2_waybel_7(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(sK3(X1,X0),X0)
    | ~ v13_waybel_0(X0,X1)
    | v1_xboole_0(X0)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_48])).

cnf(c_1358,plain,
    ( ~ v2_waybel_0(X0,sK6)
    | v2_waybel_7(X0,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(sK3(sK6,X0),X0)
    | ~ v13_waybel_0(X0,sK6)
    | v1_xboole_0(X0)
    | ~ v3_orders_2(sK6)
    | ~ v4_orders_2(sK6)
    | ~ v5_orders_2(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(unflattening,[status(thm)],[c_1357])).

cnf(c_1362,plain,
    ( ~ v2_waybel_0(X0,sK6)
    | v2_waybel_7(X0,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(sK3(sK6,X0),X0)
    | ~ v13_waybel_0(X0,sK6)
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1358,c_52,c_51,c_50,c_46])).

cnf(c_1556,plain,
    ( ~ v2_waybel_0(X0,sK6)
    | v2_waybel_7(X0,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(sK3(sK6,X0),X0)
    | ~ v13_waybel_0(X0,sK6)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1362,c_45])).

cnf(c_1557,plain,
    ( ~ v2_waybel_0(sK7,sK6)
    | v2_waybel_7(sK7,sK6)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(sK3(sK6,sK7),sK7)
    | ~ v13_waybel_0(sK7,sK6) ),
    inference(unflattening,[status(thm)],[c_1556])).

cnf(c_1559,plain,
    ( ~ r2_hidden(sK3(sK6,sK7),sK7)
    | v2_waybel_7(sK7,sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1557,c_44,c_43,c_42])).

cnf(c_1560,plain,
    ( v2_waybel_7(sK7,sK6)
    | ~ r2_hidden(sK3(sK6,sK7),sK7) ),
    inference(renaming,[status(thm)],[c_1559])).

cnf(c_1561,plain,
    ( v2_waybel_7(sK7,sK6) = iProver_top
    | r2_hidden(sK3(sK6,sK7),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1560])).

cnf(c_3899,plain,
    ( ~ m1_subset_1(X0_62,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK8,u1_struct_0(sK6))
    | ~ r2_hidden(k3_yellow_0(sK6),X0_62)
    | r2_hidden(sK8,X0_62)
    | ~ v13_waybel_0(X0_62,sK6) ),
    inference(instantiation,[status(thm)],[c_3078])).

cnf(c_3900,plain,
    ( m1_subset_1(X0_62,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(k3_yellow_0(sK6),X0_62) != iProver_top
    | r2_hidden(sK8,X0_62) = iProver_top
    | v13_waybel_0(X0_62,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3899])).

cnf(c_3902,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top
    | r2_hidden(sK8,sK7) = iProver_top
    | v13_waybel_0(sK7,sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3900])).

cnf(c_4040,plain,
    ( ~ m1_subset_1(X0_62,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK3(sK6,sK7),u1_struct_0(sK6))
    | r2_hidden(sK3(sK6,sK7),X0_62)
    | ~ r2_hidden(k3_yellow_0(sK6),X0_62)
    | ~ v13_waybel_0(X0_62,sK6) ),
    inference(instantiation,[status(thm)],[c_3078])).

cnf(c_4041,plain,
    ( m1_subset_1(X0_62,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | m1_subset_1(sK3(sK6,sK7),u1_struct_0(sK6)) != iProver_top
    | r2_hidden(sK3(sK6,sK7),X0_62) = iProver_top
    | r2_hidden(k3_yellow_0(sK6),X0_62) != iProver_top
    | v13_waybel_0(X0_62,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4040])).

cnf(c_4043,plain,
    ( m1_subset_1(sK3(sK6,sK7),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r2_hidden(sK3(sK6,sK7),sK7) = iProver_top
    | r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top
    | v13_waybel_0(sK7,sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4041])).

cnf(c_4635,plain,
    ( r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top
    | r2_hidden(X0_62,sK7) = iProver_top
    | m1_subset_1(X0_62,u1_struct_0(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4630,c_62,c_63,c_67,c_68,c_1561,c_1603,c_3902,c_4043])).

cnf(c_4636,plain,
    ( m1_subset_1(X0_62,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X0_62,sK7) = iProver_top
    | r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top ),
    inference(renaming,[status(thm)],[c_4635])).

cnf(c_4641,plain,
    ( v2_waybel_7(sK7,sK6) != iProver_top
    | r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top
    | r2_hidden(sK8,sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_3692,c_4636])).

cnf(c_4672,plain,
    ( r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top
    | r2_hidden(sK8,sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4641,c_62,c_63,c_67,c_68,c_1561,c_1603,c_3902,c_4043])).

cnf(c_1892,plain,
    ( m1_subset_1(sK2(sK6,sK7),u1_struct_0(sK6))
    | ~ r2_hidden(sK8,sK7) ),
    inference(resolution,[status(thm)],[c_1615,c_39])).

cnf(c_1893,plain,
    ( m1_subset_1(sK2(sK6,sK7),u1_struct_0(sK6)) = iProver_top
    | r2_hidden(sK8,sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1892])).

cnf(c_17,plain,
    ( ~ v2_waybel_0(X0,X1)
    | v2_waybel_7(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(sK2(X1,X0),X0)
    | ~ v13_waybel_0(X0,X1)
    | v1_xboole_0(X0)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1327,plain,
    ( ~ v2_waybel_0(X0,X1)
    | v2_waybel_7(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(sK2(X1,X0),X0)
    | ~ v13_waybel_0(X0,X1)
    | v1_xboole_0(X0)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_48])).

cnf(c_1328,plain,
    ( ~ v2_waybel_0(X0,sK6)
    | v2_waybel_7(X0,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(sK2(sK6,X0),X0)
    | ~ v13_waybel_0(X0,sK6)
    | v1_xboole_0(X0)
    | ~ v3_orders_2(sK6)
    | ~ v4_orders_2(sK6)
    | ~ v5_orders_2(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(unflattening,[status(thm)],[c_1327])).

cnf(c_1332,plain,
    ( ~ v2_waybel_0(X0,sK6)
    | v2_waybel_7(X0,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(sK2(sK6,X0),X0)
    | ~ v13_waybel_0(X0,sK6)
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1328,c_52,c_51,c_50,c_46])).

cnf(c_1570,plain,
    ( ~ v2_waybel_0(X0,sK6)
    | v2_waybel_7(X0,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(sK2(sK6,X0),X0)
    | ~ v13_waybel_0(X0,sK6)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1332,c_45])).

cnf(c_1571,plain,
    ( ~ v2_waybel_0(sK7,sK6)
    | v2_waybel_7(sK7,sK6)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(sK2(sK6,sK7),sK7)
    | ~ v13_waybel_0(sK7,sK6) ),
    inference(unflattening,[status(thm)],[c_1570])).

cnf(c_1573,plain,
    ( ~ r2_hidden(sK2(sK6,sK7),sK7)
    | v2_waybel_7(sK7,sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1571,c_44,c_43,c_42])).

cnf(c_1574,plain,
    ( v2_waybel_7(sK7,sK6)
    | ~ r2_hidden(sK2(sK6,sK7),sK7) ),
    inference(renaming,[status(thm)],[c_1573])).

cnf(c_2042,plain,
    ( ~ r2_hidden(sK2(sK6,sK7),sK7)
    | ~ r2_hidden(sK8,sK7) ),
    inference(resolution,[status(thm)],[c_1574,c_39])).

cnf(c_2043,plain,
    ( r2_hidden(sK2(sK6,sK7),sK7) != iProver_top
    | r2_hidden(sK8,sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2042])).

cnf(c_4005,plain,
    ( ~ m1_subset_1(X0_62,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK2(sK6,sK7),u1_struct_0(sK6))
    | r2_hidden(sK2(sK6,sK7),X0_62)
    | ~ r2_hidden(k3_yellow_0(sK6),X0_62)
    | ~ v13_waybel_0(X0_62,sK6) ),
    inference(instantiation,[status(thm)],[c_3078])).

cnf(c_4006,plain,
    ( m1_subset_1(X0_62,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | m1_subset_1(sK2(sK6,sK7),u1_struct_0(sK6)) != iProver_top
    | r2_hidden(sK2(sK6,sK7),X0_62) = iProver_top
    | r2_hidden(k3_yellow_0(sK6),X0_62) != iProver_top
    | v13_waybel_0(X0_62,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4005])).

cnf(c_4008,plain,
    ( m1_subset_1(sK2(sK6,sK7),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r2_hidden(sK2(sK6,sK7),sK7) = iProver_top
    | r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top
    | v13_waybel_0(sK7,sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4006])).

cnf(c_4676,plain,
    ( r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4672,c_62,c_63,c_67,c_68,c_1561,c_1603,c_3902,c_4043])).

cnf(c_41,negated_conjecture,
    ( v2_waybel_7(sK7,sK6)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | r2_hidden(X0,sK7)
    | r2_hidden(k7_waybel_1(sK6,X0),sK7) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_3082,negated_conjecture,
    ( v2_waybel_7(sK7,sK6)
    | ~ m1_subset_1(X0_62,u1_struct_0(sK6))
    | r2_hidden(X0_62,sK7)
    | r2_hidden(k7_waybel_1(sK6,X0_62),sK7) ),
    inference(subtyping,[status(esa)],[c_41])).

cnf(c_4010,plain,
    ( v2_waybel_7(sK7,sK6)
    | ~ m1_subset_1(sK3(sK6,sK7),u1_struct_0(sK6))
    | r2_hidden(k7_waybel_1(sK6,sK3(sK6,sK7)),sK7)
    | r2_hidden(sK3(sK6,sK7),sK7) ),
    inference(instantiation,[status(thm)],[c_3082])).

cnf(c_4038,plain,
    ( v2_waybel_7(sK7,sK6) = iProver_top
    | m1_subset_1(sK3(sK6,sK7),u1_struct_0(sK6)) != iProver_top
    | r2_hidden(k7_waybel_1(sK6,sK3(sK6,sK7)),sK7) = iProver_top
    | r2_hidden(sK3(sK6,sK7),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4010])).

cnf(c_3975,plain,
    ( v2_waybel_7(sK7,sK6)
    | ~ m1_subset_1(sK2(sK6,sK7),u1_struct_0(sK6))
    | r2_hidden(k7_waybel_1(sK6,sK2(sK6,sK7)),sK7)
    | r2_hidden(sK2(sK6,sK7),sK7) ),
    inference(instantiation,[status(thm)],[c_3082])).

cnf(c_4003,plain,
    ( v2_waybel_7(sK7,sK6) = iProver_top
    | m1_subset_1(sK2(sK6,sK7),u1_struct_0(sK6)) != iProver_top
    | r2_hidden(k7_waybel_1(sK6,sK2(sK6,sK7)),sK7) = iProver_top
    | r2_hidden(sK2(sK6,sK7),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3975])).

cnf(c_1575,plain,
    ( v2_waybel_7(sK7,sK6) = iProver_top
    | r2_hidden(sK2(sK6,sK7),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1574])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13402,c_7447,c_4885,c_4676,c_4038,c_4003,c_1617,c_1603,c_1589,c_1575,c_1561,c_63,c_62,c_61])).


%------------------------------------------------------------------------------
