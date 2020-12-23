%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1968+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:56 EST 2020

% Result     : Theorem 3.62s
% Output     : CNFRefutation 3.62s
% Verified   : 
% Statistics : Number of formulae       :  297 (18225 expanded)
%              Number of clauses        :  206 (4639 expanded)
%              Number of leaves         :   23 (5314 expanded)
%              Depth                    :   27
%              Number of atoms          : 1559 (278399 expanded)
%              Number of equality atoms :  382 (21734 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal clause size      :   42 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v12_waybel_0(X1,X0)
            & v1_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ( v1_waybel_7(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ~ ( ~ r2_hidden(X3,X1)
                        & ~ r2_hidden(X2,X1)
                        & r2_hidden(k12_lattice3(X0,X2,X3),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_waybel_7(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | r2_hidden(X2,X1)
                    | ~ r2_hidden(k12_lattice3(X0,X2,X3),X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_waybel_7(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | r2_hidden(X2,X1)
                    | ~ r2_hidden(k12_lattice3(X0,X2,X3),X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f19])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_waybel_7(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & ~ r2_hidden(X2,X1)
                      & r2_hidden(k12_lattice3(X0,X2,X3),X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ! [X3] :
                      ( r2_hidden(X3,X1)
                      | r2_hidden(X2,X1)
                      | ~ r2_hidden(k12_lattice3(X0,X2,X3),X1)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v1_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_waybel_7(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & ~ r2_hidden(X2,X1)
                      & r2_hidden(k12_lattice3(X0,X2,X3),X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | r2_hidden(X4,X1)
                      | ~ r2_hidden(k12_lattice3(X0,X4,X5),X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v1_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(rectify,[],[f40])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & ~ r2_hidden(X2,X1)
          & r2_hidden(k12_lattice3(X0,X2,X3),X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & ~ r2_hidden(X2,X1)
        & r2_hidden(k12_lattice3(X0,X2,sK1(X0,X1)),X1)
        & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X2,X1)
              & r2_hidden(k12_lattice3(X0,X2,X3),X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r2_hidden(X3,X1)
            & ~ r2_hidden(sK0(X0,X1),X1)
            & r2_hidden(k12_lattice3(X0,sK0(X0,X1),X3),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_waybel_7(X1,X0)
              | ( ~ r2_hidden(sK1(X0,X1),X1)
                & ~ r2_hidden(sK0(X0,X1),X1)
                & r2_hidden(k12_lattice3(X0,sK0(X0,X1),sK1(X0,X1)),X1)
                & m1_subset_1(sK1(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | r2_hidden(X4,X1)
                      | ~ r2_hidden(k12_lattice3(X0,X4,X5),X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v1_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f41,f43,f42])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v1_waybel_7(X1,X0)
      | m1_subset_1(sK0(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( ( l1_orders_2(X1)
            & v2_lattice3(X1)
            & v1_lattice3(X1)
            & v5_orders_2(X1)
            & v4_orders_2(X1)
            & v3_orders_2(X1) )
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  & v1_waybel_7(X2,X0)
                  & v12_waybel_0(X2,X0)
                  & v1_waybel_0(X2,X0)
                  & ~ v1_xboole_0(X2) )
               => ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                  & v1_waybel_7(X2,X1)
                  & v12_waybel_0(X2,X1)
                  & v1_waybel_0(X2,X1)
                  & ~ v1_xboole_0(X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( ( l1_orders_2(X1)
              & v2_lattice3(X1)
              & v1_lattice3(X1)
              & v5_orders_2(X1)
              & v4_orders_2(X1)
              & v3_orders_2(X1) )
           => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
             => ! [X2] :
                  ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                    & v1_waybel_7(X2,X0)
                    & v12_waybel_0(X2,X0)
                    & v1_waybel_0(X2,X0)
                    & ~ v1_xboole_0(X2) )
                 => ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                    & v1_waybel_7(X2,X1)
                    & v12_waybel_0(X2,X1)
                    & v1_waybel_0(X2,X1)
                    & ~ v1_xboole_0(X2) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f16,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v2_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( ( l1_orders_2(X1)
              & v2_lattice3(X1)
              & v5_orders_2(X1)
              & v4_orders_2(X1)
              & v3_orders_2(X1) )
           => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
             => ! [X2] :
                  ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                    & v1_waybel_7(X2,X0)
                    & v12_waybel_0(X2,X0)
                    & v1_waybel_0(X2,X0)
                    & ~ v1_xboole_0(X2) )
                 => ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                    & v1_waybel_7(X2,X1)
                    & v12_waybel_0(X2,X1)
                    & v1_waybel_0(X2,X1)
                    & ~ v1_xboole_0(X2) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                | ~ v1_waybel_7(X2,X1)
                | ~ v12_waybel_0(X2,X1)
                | ~ v1_waybel_0(X2,X1)
                | v1_xboole_0(X2) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_waybel_7(X2,X0)
              & v12_waybel_0(X2,X0)
              & v1_waybel_0(X2,X0)
              & ~ v1_xboole_0(X2) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1)
          & v2_lattice3(X1)
          & v5_orders_2(X1)
          & v4_orders_2(X1)
          & v3_orders_2(X1) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                | ~ v1_waybel_7(X2,X1)
                | ~ v12_waybel_0(X2,X1)
                | ~ v1_waybel_0(X2,X1)
                | v1_xboole_0(X2) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_waybel_7(X2,X0)
              & v12_waybel_0(X2,X0)
              & v1_waybel_0(X2,X0)
              & ~ v1_xboole_0(X2) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1)
          & v2_lattice3(X1)
          & v5_orders_2(X1)
          & v4_orders_2(X1)
          & v3_orders_2(X1) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f38])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
            | ~ v1_waybel_7(X2,X1)
            | ~ v12_waybel_0(X2,X1)
            | ~ v1_waybel_0(X2,X1)
            | v1_xboole_0(X2) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_waybel_7(X2,X0)
          & v12_waybel_0(X2,X0)
          & v1_waybel_0(X2,X0)
          & ~ v1_xboole_0(X2) )
     => ( ( ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X1)))
          | ~ v1_waybel_7(sK6,X1)
          | ~ v12_waybel_0(sK6,X1)
          | ~ v1_waybel_0(sK6,X1)
          | v1_xboole_0(sK6) )
        & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X0)))
        & v1_waybel_7(sK6,X0)
        & v12_waybel_0(sK6,X0)
        & v1_waybel_0(sK6,X0)
        & ~ v1_xboole_0(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                | ~ v1_waybel_7(X2,X1)
                | ~ v12_waybel_0(X2,X1)
                | ~ v1_waybel_0(X2,X1)
                | v1_xboole_0(X2) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_waybel_7(X2,X0)
              & v12_waybel_0(X2,X0)
              & v1_waybel_0(X2,X0)
              & ~ v1_xboole_0(X2) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1)
          & v2_lattice3(X1)
          & v5_orders_2(X1)
          & v4_orders_2(X1)
          & v3_orders_2(X1) )
     => ( ? [X2] :
            ( ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
              | ~ v1_waybel_7(X2,sK5)
              | ~ v12_waybel_0(X2,sK5)
              | ~ v1_waybel_0(X2,sK5)
              | v1_xboole_0(X2) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_waybel_7(X2,X0)
            & v12_waybel_0(X2,X0)
            & v1_waybel_0(X2,X0)
            & ~ v1_xboole_0(X2) )
        & g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) = g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        & l1_orders_2(sK5)
        & v2_lattice3(sK5)
        & v5_orders_2(sK5)
        & v4_orders_2(sK5)
        & v3_orders_2(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                  | ~ v1_waybel_7(X2,X1)
                  | ~ v12_waybel_0(X2,X1)
                  | ~ v1_waybel_0(X2,X1)
                  | v1_xboole_0(X2) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & v1_waybel_7(X2,X0)
                & v12_waybel_0(X2,X0)
                & v1_waybel_0(X2,X0)
                & ~ v1_xboole_0(X2) )
            & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
            & l1_orders_2(X1)
            & v2_lattice3(X1)
            & v5_orders_2(X1)
            & v4_orders_2(X1)
            & v3_orders_2(X1) )
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                | ~ v1_waybel_7(X2,X1)
                | ~ v12_waybel_0(X2,X1)
                | ~ v1_waybel_0(X2,X1)
                | v1_xboole_0(X2) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
              & v1_waybel_7(X2,sK4)
              & v12_waybel_0(X2,sK4)
              & v1_waybel_0(X2,sK4)
              & ~ v1_xboole_0(X2) )
          & g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1)
          & v2_lattice3(X1)
          & v5_orders_2(X1)
          & v4_orders_2(X1)
          & v3_orders_2(X1) )
      & l1_orders_2(sK4)
      & v2_lattice3(sK4)
      & v5_orders_2(sK4)
      & v4_orders_2(sK4)
      & v3_orders_2(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ( ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
      | ~ v1_waybel_7(sK6,sK5)
      | ~ v12_waybel_0(sK6,sK5)
      | ~ v1_waybel_0(sK6,sK5)
      | v1_xboole_0(sK6) )
    & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
    & v1_waybel_7(sK6,sK4)
    & v12_waybel_0(sK6,sK4)
    & v1_waybel_0(sK6,sK4)
    & ~ v1_xboole_0(sK6)
    & g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4)) = g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5))
    & l1_orders_2(sK5)
    & v2_lattice3(sK5)
    & v5_orders_2(sK5)
    & v4_orders_2(sK5)
    & v3_orders_2(sK5)
    & l1_orders_2(sK4)
    & v2_lattice3(sK4)
    & v5_orders_2(sK4)
    & v4_orders_2(sK4)
    & v3_orders_2(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f39,f52,f51,f50])).

fof(f83,plain,(
    v4_orders_2(sK5) ),
    inference(cnf_transformation,[],[f53])).

fof(f82,plain,(
    v3_orders_2(sK5) ),
    inference(cnf_transformation,[],[f53])).

fof(f84,plain,(
    v5_orders_2(sK5) ),
    inference(cnf_transformation,[],[f53])).

fof(f85,plain,(
    v2_lattice3(sK5) ),
    inference(cnf_transformation,[],[f53])).

fof(f86,plain,(
    l1_orders_2(sK5) ),
    inference(cnf_transformation,[],[f53])).

fof(f88,plain,(
    ~ v1_xboole_0(sK6) ),
    inference(cnf_transformation,[],[f53])).

fof(f93,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ v1_waybel_7(sK6,sK5)
    | ~ v12_waybel_0(sK6,sK5)
    | ~ v1_waybel_0(sK6,sK5)
    | v1_xboole_0(sK6) ),
    inference(cnf_transformation,[],[f53])).

fof(f81,plain,(
    l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f53])).

fof(f89,plain,(
    v1_waybel_0(sK6,sK4) ),
    inference(cnf_transformation,[],[f53])).

fof(f92,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f53])).

fof(f87,plain,(
    g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4)) = g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) ),
    inference(cnf_transformation,[],[f53])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f63,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( ( v1_waybel_0(X2,X0)
                        & X2 = X3 )
                     => v1_waybel_0(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v1_waybel_0(X3,X1)
                  | ~ v1_waybel_0(X2,X0)
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v1_waybel_0(X3,X1)
                  | ~ v1_waybel_0(X2,X0)
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f34])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_waybel_0(X3,X1)
      | ~ v1_waybel_0(X2,X0)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f96,plain,(
    ! [X0,X3,X1] :
      ( v1_waybel_0(X3,X1)
      | ~ v1_waybel_0(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f75])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v1_waybel_7(X1,X0)
      | m1_subset_1(sK1(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ( v2_lattice3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => r2_yellow_0(X0,k2_tarski(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ( v2_lattice3(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( r2_yellow_0(X0,k2_tarski(X1,X2))
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X0] :
      ( ( v2_lattice3(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( r2_yellow_0(X0,k2_tarski(X1,X2))
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f28])).

fof(f45,plain,(
    ! [X0] :
      ( ( ( v2_lattice3(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ~ r2_yellow_0(X0,k2_tarski(X1,X2))
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( r2_yellow_0(X0,k2_tarski(X1,X2))
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v2_lattice3(X0) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f46,plain,(
    ! [X0] :
      ( ( ( v2_lattice3(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ~ r2_yellow_0(X0,k2_tarski(X1,X2))
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( r2_yellow_0(X0,k2_tarski(X3,X4))
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v2_lattice3(X0) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(rectify,[],[f45])).

fof(f48,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_yellow_0(X0,k2_tarski(X1,X2))
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ~ r2_yellow_0(X0,k2_tarski(X1,sK3(X0)))
        & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_yellow_0(X0,k2_tarski(X1,X2))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ~ r2_yellow_0(X0,k2_tarski(sK2(X0),X2))
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK2(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0] :
      ( ( ( v2_lattice3(X0)
          | ( ~ r2_yellow_0(X0,k2_tarski(sK2(X0),sK3(X0)))
            & m1_subset_1(sK3(X0),u1_struct_0(X0))
            & m1_subset_1(sK2(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( r2_yellow_0(X0,k2_tarski(X3,X4))
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v2_lattice3(X0) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f46,f48,f47])).

fof(f68,plain,(
    ! [X4,X0,X3] :
      ( r2_yellow_0(X0,k2_tarski(X3,X4))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f79,plain,(
    v5_orders_2(sK4) ),
    inference(cnf_transformation,[],[f53])).

fof(f80,plain,(
    v2_lattice3(sK4) ),
    inference(cnf_transformation,[],[f53])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2] :
                ( r2_yellow_0(X0,X2)
               => k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2)
              | ~ r2_yellow_0(X0,X2) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2)
              | ~ r2_yellow_0(X0,X2) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f32])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2)
      | ~ r2_yellow_0(X0,X2)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f90,plain,(
    v12_waybel_0(sK6,sK4) ),
    inference(cnf_transformation,[],[f53])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( X2 = X3
                     => ( ( v13_waybel_0(X2,X0)
                         => v13_waybel_0(X3,X1) )
                        & ( v12_waybel_0(X2,X0)
                         => v12_waybel_0(X3,X1) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v13_waybel_0(X3,X1)
                      | ~ v13_waybel_0(X2,X0) )
                    & ( v12_waybel_0(X3,X1)
                      | ~ v12_waybel_0(X2,X0) ) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v13_waybel_0(X3,X1)
                      | ~ v13_waybel_0(X2,X0) )
                    & ( v12_waybel_0(X3,X1)
                      | ~ v12_waybel_0(X2,X0) ) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f30])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( v12_waybel_0(X3,X1)
      | ~ v12_waybel_0(X2,X0)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f95,plain,(
    ! [X0,X3,X1] :
      ( v12_waybel_0(X3,X1)
      | ~ v12_waybel_0(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f72])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,X0)
        & m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k2_tarski(X1,X2) = k7_domain_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X1,X2) = k7_domain_1(X0,X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X1,X2) = k7_domain_1(X0,X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = k7_domain_1(X0,X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f62,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f17])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k12_lattice3(X0,X1,X2) = k2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k12_lattice3(X0,X1,X2) = k2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k12_lattice3(X0,X1,X2) = k2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f36])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k12_lattice3(X0,X1,X2) = k2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f78,plain,(
    v4_orders_2(sK4) ),
    inference(cnf_transformation,[],[f53])).

fof(f77,plain,(
    v3_orders_2(sK4) ),
    inference(cnf_transformation,[],[f53])).

fof(f56,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(k12_lattice3(X0,X4,X5),X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v1_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f91,plain,(
    v1_waybel_7(sK6,sK4) ),
    inference(cnf_transformation,[],[f53])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v1_waybel_7(X1,X0)
      | r2_hidden(k12_lattice3(X0,sK0(X0,X1),sK1(X0,X1)),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v1_waybel_7(X1,X0)
      | ~ r2_hidden(sK0(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v1_waybel_7(X1,X0)
      | ~ r2_hidden(sK1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_6,plain,
    ( ~ v1_waybel_0(X0,X1)
    | ~ v12_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1,X0),u1_struct_0(X1))
    | v1_waybel_7(X0,X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_33,negated_conjecture,
    ( v4_orders_2(sK5) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_543,plain,
    ( ~ v1_waybel_0(X0,X1)
    | ~ v12_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1,X0),u1_struct_0(X1))
    | v1_waybel_7(X0,X1)
    | ~ v3_orders_2(X1)
    | ~ v5_orders_2(X1)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_33])).

cnf(c_544,plain,
    ( ~ v1_waybel_0(X0,sK5)
    | ~ v12_waybel_0(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | m1_subset_1(sK0(sK5,X0),u1_struct_0(sK5))
    | v1_waybel_7(X0,sK5)
    | ~ v3_orders_2(sK5)
    | ~ v5_orders_2(sK5)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(sK5)
    | ~ v2_lattice3(sK5) ),
    inference(unflattening,[status(thm)],[c_543])).

cnf(c_34,negated_conjecture,
    ( v3_orders_2(sK5) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_32,negated_conjecture,
    ( v5_orders_2(sK5) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_31,negated_conjecture,
    ( v2_lattice3(sK5) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_30,negated_conjecture,
    ( l1_orders_2(sK5) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_548,plain,
    ( ~ v1_waybel_0(X0,sK5)
    | ~ v12_waybel_0(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | m1_subset_1(sK0(sK5,X0),u1_struct_0(sK5))
    | v1_waybel_7(X0,sK5)
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_544,c_34,c_32,c_31,c_30])).

cnf(c_28,negated_conjecture,
    ( ~ v1_xboole_0(sK6) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1318,plain,
    ( ~ v1_waybel_0(X0,sK5)
    | ~ v12_waybel_0(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | m1_subset_1(sK0(sK5,X0),u1_struct_0(sK5))
    | v1_waybel_7(X0,sK5)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_548,c_28])).

cnf(c_1319,plain,
    ( ~ v1_waybel_0(sK6,sK5)
    | ~ v12_waybel_0(sK6,sK5)
    | m1_subset_1(sK0(sK5,sK6),u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | v1_waybel_7(sK6,sK5) ),
    inference(unflattening,[status(thm)],[c_1318])).

cnf(c_23,negated_conjecture,
    ( ~ v1_waybel_0(sK6,sK5)
    | ~ v12_waybel_0(sK6,sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ v1_waybel_7(sK6,sK5)
    | v1_xboole_0(sK6) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_201,plain,
    ( ~ v1_waybel_7(sK6,sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ v12_waybel_0(sK6,sK5)
    | ~ v1_waybel_0(sK6,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_23,c_28])).

cnf(c_202,negated_conjecture,
    ( ~ v1_waybel_0(sK6,sK5)
    | ~ v12_waybel_0(sK6,sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ v1_waybel_7(sK6,sK5) ),
    inference(renaming,[status(thm)],[c_201])).

cnf(c_1321,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | m1_subset_1(sK0(sK5,sK6),u1_struct_0(sK5))
    | ~ v12_waybel_0(sK6,sK5)
    | ~ v1_waybel_0(sK6,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1319,c_202])).

cnf(c_1322,plain,
    ( ~ v1_waybel_0(sK6,sK5)
    | ~ v12_waybel_0(sK6,sK5)
    | m1_subset_1(sK0(sK5,sK6),u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(renaming,[status(thm)],[c_1321])).

cnf(c_2992,plain,
    ( v1_waybel_0(sK6,sK5) != iProver_top
    | v12_waybel_0(sK6,sK5) != iProver_top
    | m1_subset_1(sK0(sK5,sK6),u1_struct_0(sK5)) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1322])).

cnf(c_35,negated_conjecture,
    ( l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_44,plain,
    ( l1_orders_2(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_49,plain,
    ( l1_orders_2(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_27,negated_conjecture,
    ( v1_waybel_0(sK6,sK4) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_51,plain,
    ( v1_waybel_0(sK6,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_54,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1323,plain,
    ( v1_waybel_0(sK6,sK5) != iProver_top
    | v12_waybel_0(sK6,sK5) != iProver_top
    | m1_subset_1(sK0(sK5,sK6),u1_struct_0(sK5)) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1322])).

cnf(c_29,negated_conjecture,
    ( g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4)) = g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | X2 = X1
    | g1_orders_2(X2,X3) != g1_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_3015,plain,
    ( X0 = X1
    | g1_orders_2(X0,X2) != g1_orders_2(X1,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3628,plain,
    ( g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) != g1_orders_2(X0,X1)
    | u1_struct_0(sK4) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_29,c_3015])).

cnf(c_9,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_82,plain,
    ( m1_subset_1(u1_orders_2(sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4))))
    | ~ l1_orders_2(sK4) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_3629,plain,
    ( g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) != g1_orders_2(X0,X1)
    | u1_struct_0(sK4) = X0
    | m1_subset_1(u1_orders_2(sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_29,c_3015])).

cnf(c_3646,plain,
    ( ~ m1_subset_1(u1_orders_2(sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4))))
    | g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) != g1_orders_2(X0,X1)
    | u1_struct_0(sK4) = X0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3629])).

cnf(c_3695,plain,
    ( u1_struct_0(sK4) = X0
    | g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) != g1_orders_2(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3628,c_35,c_82,c_3646])).

cnf(c_3696,plain,
    ( g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) != g1_orders_2(X0,X1)
    | u1_struct_0(sK4) = X0 ),
    inference(renaming,[status(thm)],[c_3695])).

cnf(c_3701,plain,
    ( u1_struct_0(sK4) = u1_struct_0(sK5) ),
    inference(equality_resolution,[status(thm)],[c_3696])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | X2 = X0
    | g1_orders_2(X3,X2) != g1_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_3016,plain,
    ( X0 = X1
    | g1_orders_2(X2,X0) != g1_orders_2(X3,X1)
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3673,plain,
    ( g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) != g1_orders_2(X0,X1)
    | u1_orders_2(sK4) = X1
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_29,c_3016])).

cnf(c_3674,plain,
    ( g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) != g1_orders_2(X0,X1)
    | u1_orders_2(sK4) = X1
    | m1_subset_1(u1_orders_2(sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_29,c_3016])).

cnf(c_3691,plain,
    ( ~ m1_subset_1(u1_orders_2(sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4))))
    | g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) != g1_orders_2(X0,X1)
    | u1_orders_2(sK4) = X1 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3674])).

cnf(c_3750,plain,
    ( u1_orders_2(sK4) = X1
    | g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) != g1_orders_2(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3673,c_35,c_82,c_3691])).

cnf(c_3751,plain,
    ( g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) != g1_orders_2(X0,X1)
    | u1_orders_2(sK4) = X1 ),
    inference(renaming,[status(thm)],[c_3750])).

cnf(c_3756,plain,
    ( u1_orders_2(sK5) = u1_orders_2(sK4) ),
    inference(equality_resolution,[status(thm)],[c_3751])).

cnf(c_3011,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3768,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3701,c_3011])).

cnf(c_21,plain,
    ( ~ v1_waybel_0(X0,X1)
    | v1_waybel_0(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X2)
    | g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_3715,plain,
    ( v1_waybel_0(sK6,X0)
    | ~ v1_waybel_0(sK6,sK4)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_orders_2(X0)
    | ~ l1_orders_2(sK4)
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4)) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_3812,plain,
    ( ~ v1_waybel_0(sK6,sK4)
    | v1_waybel_0(sK6,sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ l1_orders_2(sK4)
    | ~ l1_orders_2(sK5)
    | g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) != g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4)) ),
    inference(instantiation,[status(thm)],[c_3715])).

cnf(c_3813,plain,
    ( g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) != g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4))
    | v1_waybel_0(sK6,sK4) != iProver_top
    | v1_waybel_0(sK6,sK5) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | l1_orders_2(sK4) != iProver_top
    | l1_orders_2(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3812])).

cnf(c_2084,plain,
    ( X0 != X1
    | X2 != X3
    | g1_orders_2(X0,X2) = g1_orders_2(X1,X3) ),
    theory(equality)).

cnf(c_3954,plain,
    ( g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) = g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
    | u1_orders_2(sK5) != u1_orders_2(X0)
    | u1_struct_0(sK5) != u1_struct_0(X0) ),
    inference(instantiation,[status(thm)],[c_2084])).

cnf(c_3955,plain,
    ( g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) = g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4))
    | u1_orders_2(sK5) != u1_orders_2(sK4)
    | u1_struct_0(sK5) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_3954])).

cnf(c_3703,plain,
    ( g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) != g1_orders_2(X0,X1)
    | u1_struct_0(sK5) = X0 ),
    inference(demodulation,[status(thm)],[c_3701,c_3696])).

cnf(c_4272,plain,
    ( u1_struct_0(sK5) = u1_struct_0(sK5) ),
    inference(equality_resolution,[status(thm)],[c_3703])).

cnf(c_2070,plain,
    ( X0 != X1
    | X2 != X1
    | X0 = X2 ),
    theory(equality)).

cnf(c_4328,plain,
    ( u1_struct_0(X0) != X1
    | u1_struct_0(sK5) != X1
    | u1_struct_0(sK5) = u1_struct_0(X0) ),
    inference(instantiation,[status(thm)],[c_2070])).

cnf(c_4763,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK5)
    | u1_struct_0(sK5) = u1_struct_0(X0)
    | u1_struct_0(sK5) != u1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_4328])).

cnf(c_4764,plain,
    ( u1_struct_0(sK4) != u1_struct_0(sK5)
    | u1_struct_0(sK5) = u1_struct_0(sK4)
    | u1_struct_0(sK5) != u1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_4763])).

cnf(c_4802,plain,
    ( m1_subset_1(sK0(sK5,sK6),u1_struct_0(sK5)) = iProver_top
    | v12_waybel_0(sK6,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2992,c_44,c_49,c_51,c_54,c_1323,c_3701,c_3756,c_3768,c_3813,c_3955,c_4272,c_4764])).

cnf(c_4803,plain,
    ( v12_waybel_0(sK6,sK5) != iProver_top
    | m1_subset_1(sK0(sK5,sK6),u1_struct_0(sK5)) = iProver_top ),
    inference(renaming,[status(thm)],[c_4802])).

cnf(c_5,plain,
    ( ~ v1_waybel_0(X0,X1)
    | ~ v12_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK1(X1,X0),u1_struct_0(X1))
    | v1_waybel_7(X0,X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_573,plain,
    ( ~ v1_waybel_0(X0,X1)
    | ~ v12_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK1(X1,X0),u1_struct_0(X1))
    | v1_waybel_7(X0,X1)
    | ~ v3_orders_2(X1)
    | ~ v5_orders_2(X1)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_33])).

cnf(c_574,plain,
    ( ~ v1_waybel_0(X0,sK5)
    | ~ v12_waybel_0(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | m1_subset_1(sK1(sK5,X0),u1_struct_0(sK5))
    | v1_waybel_7(X0,sK5)
    | ~ v3_orders_2(sK5)
    | ~ v5_orders_2(sK5)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(sK5)
    | ~ v2_lattice3(sK5) ),
    inference(unflattening,[status(thm)],[c_573])).

cnf(c_578,plain,
    ( ~ v1_waybel_0(X0,sK5)
    | ~ v12_waybel_0(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | m1_subset_1(sK1(sK5,X0),u1_struct_0(sK5))
    | v1_waybel_7(X0,sK5)
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_574,c_34,c_32,c_31,c_30])).

cnf(c_1298,plain,
    ( ~ v1_waybel_0(X0,sK5)
    | ~ v12_waybel_0(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | m1_subset_1(sK1(sK5,X0),u1_struct_0(sK5))
    | v1_waybel_7(X0,sK5)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_578,c_28])).

cnf(c_1299,plain,
    ( ~ v1_waybel_0(sK6,sK5)
    | ~ v12_waybel_0(sK6,sK5)
    | m1_subset_1(sK1(sK5,sK6),u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | v1_waybel_7(sK6,sK5) ),
    inference(unflattening,[status(thm)],[c_1298])).

cnf(c_1301,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | m1_subset_1(sK1(sK5,sK6),u1_struct_0(sK5))
    | ~ v12_waybel_0(sK6,sK5)
    | ~ v1_waybel_0(sK6,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1299,c_28,c_23])).

cnf(c_1302,plain,
    ( ~ v1_waybel_0(sK6,sK5)
    | ~ v12_waybel_0(sK6,sK5)
    | m1_subset_1(sK1(sK5,sK6),u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(renaming,[status(thm)],[c_1301])).

cnf(c_2993,plain,
    ( v1_waybel_0(sK6,sK5) != iProver_top
    | v12_waybel_0(sK6,sK5) != iProver_top
    | m1_subset_1(sK1(sK5,sK6),u1_struct_0(sK5)) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1302])).

cnf(c_1303,plain,
    ( v1_waybel_0(sK6,sK5) != iProver_top
    | v12_waybel_0(sK6,sK5) != iProver_top
    | m1_subset_1(sK1(sK5,sK6),u1_struct_0(sK5)) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1302])).

cnf(c_4839,plain,
    ( m1_subset_1(sK1(sK5,sK6),u1_struct_0(sK5)) = iProver_top
    | v12_waybel_0(sK6,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2993,c_44,c_49,c_51,c_54,c_1303,c_3701,c_3756,c_3768,c_3813,c_3955,c_4272,c_4764])).

cnf(c_4840,plain,
    ( v12_waybel_0(sK6,sK5) != iProver_top
    | m1_subset_1(sK1(sK5,sK6),u1_struct_0(sK5)) = iProver_top ),
    inference(renaming,[status(thm)],[c_4839])).

cnf(c_17,plain,
    ( r2_yellow_0(X0,k2_tarski(X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_37,negated_conjecture,
    ( v5_orders_2(sK4) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1033,plain,
    ( r2_yellow_0(X0,k2_tarski(X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_37])).

cnf(c_1034,plain,
    ( r2_yellow_0(sK4,k2_tarski(X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ l1_orders_2(sK4)
    | ~ v2_lattice3(sK4) ),
    inference(unflattening,[status(thm)],[c_1033])).

cnf(c_36,negated_conjecture,
    ( v2_lattice3(sK4) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1038,plain,
    ( r2_yellow_0(sK4,k2_tarski(X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1034,c_36,c_35])).

cnf(c_1039,plain,
    ( r2_yellow_0(sK4,k2_tarski(X0,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_1038])).

cnf(c_3001,plain,
    ( r2_yellow_0(sK4,k2_tarski(X0,X1)) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1039])).

cnf(c_4448,plain,
    ( r2_yellow_0(sK4,k2_tarski(X0,X1)) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3001,c_3701])).

cnf(c_20,plain,
    ( ~ r2_yellow_0(X0,X1)
    | ~ l1_orders_2(X0)
    | ~ l1_orders_2(X2)
    | k2_yellow_0(X2,X1) = k2_yellow_0(X0,X1)
    | g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_3013,plain,
    ( k2_yellow_0(X0,X1) = k2_yellow_0(X2,X1)
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
    | r2_yellow_0(X2,X1) != iProver_top
    | l1_orders_2(X2) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4019,plain,
    ( k2_yellow_0(X0,X1) = k2_yellow_0(sK4,X1)
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK5))
    | r2_yellow_0(sK4,X1) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | l1_orders_2(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3756,c_3013])).

cnf(c_4026,plain,
    ( k2_yellow_0(X0,X1) = k2_yellow_0(sK4,X1)
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5))
    | r2_yellow_0(sK4,X1) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | l1_orders_2(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4019,c_3701])).

cnf(c_5199,plain,
    ( l1_orders_2(X0) != iProver_top
    | r2_yellow_0(sK4,X1) != iProver_top
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5))
    | k2_yellow_0(X0,X1) = k2_yellow_0(sK4,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4026,c_44])).

cnf(c_5200,plain,
    ( k2_yellow_0(X0,X1) = k2_yellow_0(sK4,X1)
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5))
    | r2_yellow_0(sK4,X1) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5199])).

cnf(c_5209,plain,
    ( k2_yellow_0(sK5,X0) = k2_yellow_0(sK4,X0)
    | r2_yellow_0(sK4,X0) != iProver_top
    | l1_orders_2(sK5) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_5200])).

cnf(c_7873,plain,
    ( r2_yellow_0(sK4,X0) != iProver_top
    | k2_yellow_0(sK5,X0) = k2_yellow_0(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5209,c_49])).

cnf(c_7874,plain,
    ( k2_yellow_0(sK5,X0) = k2_yellow_0(sK4,X0)
    | r2_yellow_0(sK4,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_7873])).

cnf(c_7881,plain,
    ( k2_yellow_0(sK4,k2_tarski(X0,X1)) = k2_yellow_0(sK5,k2_tarski(X0,X1))
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4448,c_7874])).

cnf(c_11226,plain,
    ( k2_yellow_0(sK5,k2_tarski(sK1(sK5,sK6),X0)) = k2_yellow_0(sK4,k2_tarski(sK1(sK5,sK6),X0))
    | v12_waybel_0(sK6,sK5) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4840,c_7881])).

cnf(c_26,negated_conjecture,
    ( v12_waybel_0(sK6,sK4) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_52,plain,
    ( v12_waybel_0(sK6,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_19,plain,
    ( ~ v12_waybel_0(X0,X1)
    | v12_waybel_0(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X2)
    | g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_3712,plain,
    ( v12_waybel_0(sK6,X0)
    | ~ v12_waybel_0(sK6,sK4)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_orders_2(X0)
    | ~ l1_orders_2(sK4)
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4)) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_5652,plain,
    ( ~ v12_waybel_0(sK6,sK4)
    | v12_waybel_0(sK6,sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ l1_orders_2(sK4)
    | ~ l1_orders_2(sK5)
    | g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) != g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4)) ),
    inference(instantiation,[status(thm)],[c_3712])).

cnf(c_5653,plain,
    ( g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) != g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4))
    | v12_waybel_0(sK6,sK4) != iProver_top
    | v12_waybel_0(sK6,sK5) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | l1_orders_2(sK4) != iProver_top
    | l1_orders_2(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5652])).

cnf(c_11311,plain,
    ( k2_yellow_0(sK5,k2_tarski(sK1(sK5,sK6),X0)) = k2_yellow_0(sK4,k2_tarski(sK1(sK5,sK6),X0))
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11226,c_44,c_49,c_52,c_54,c_3701,c_3756,c_3768,c_3955,c_4272,c_4764,c_5653])).

cnf(c_11320,plain,
    ( k2_yellow_0(sK5,k2_tarski(sK1(sK5,sK6),sK0(sK5,sK6))) = k2_yellow_0(sK4,k2_tarski(sK1(sK5,sK6),sK0(sK5,sK6)))
    | v12_waybel_0(sK6,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4803,c_11311])).

cnf(c_3014,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | v12_waybel_0(X2,X1) != iProver_top
    | v12_waybel_0(X2,X0) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | l1_orders_2(X1) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4220,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK5))
    | v12_waybel_0(X1,X0) = iProver_top
    | v12_waybel_0(X1,sK4) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | l1_orders_2(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3756,c_3014])).

cnf(c_4229,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5))
    | v12_waybel_0(X1,X0) = iProver_top
    | v12_waybel_0(X1,sK4) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | l1_orders_2(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4220,c_3701])).

cnf(c_5926,plain,
    ( l1_orders_2(X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v12_waybel_0(X1,sK4) != iProver_top
    | v12_waybel_0(X1,X0) = iProver_top
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4229,c_44])).

cnf(c_5927,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5))
    | v12_waybel_0(X1,X0) = iProver_top
    | v12_waybel_0(X1,sK4) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5926])).

cnf(c_5938,plain,
    ( v12_waybel_0(X0,sK4) != iProver_top
    | v12_waybel_0(X0,sK5) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | l1_orders_2(sK5) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_5927])).

cnf(c_10119,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | v12_waybel_0(X0,sK5) = iProver_top
    | v12_waybel_0(X0,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5938,c_49])).

cnf(c_10120,plain,
    ( v12_waybel_0(X0,sK4) != iProver_top
    | v12_waybel_0(X0,sK5) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
    inference(renaming,[status(thm)],[c_10119])).

cnf(c_10128,plain,
    ( v12_waybel_0(sK6,sK4) != iProver_top
    | v12_waybel_0(sK6,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3768,c_10120])).

cnf(c_10131,plain,
    ( v12_waybel_0(sK6,sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10128,c_44,c_49,c_52,c_54,c_3701,c_3756,c_3768,c_3955,c_4272,c_4764,c_5653])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,X1)
    | v1_xboole_0(X1)
    | k7_domain_1(X1,X2,X0) = k2_tarski(X2,X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_8,plain,
    ( l1_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_10,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_404,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_8,c_10])).

cnf(c_0,plain,
    ( ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_422,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0) ),
    inference(resolution,[status(thm)],[c_404,c_0])).

cnf(c_1068,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_422,c_31])).

cnf(c_1069,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK5))
    | ~ l1_orders_2(sK5) ),
    inference(unflattening,[status(thm)],[c_1068])).

cnf(c_1071,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1069,c_30])).

cnf(c_1186,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,X1)
    | k7_domain_1(X1,X2,X0) = k2_tarski(X2,X0)
    | u1_struct_0(sK5) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_1071])).

cnf(c_1187,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | k7_domain_1(u1_struct_0(sK5),X0,X1) = k2_tarski(X0,X1) ),
    inference(unflattening,[status(thm)],[c_1186])).

cnf(c_2998,plain,
    ( k7_domain_1(u1_struct_0(sK5),X0,X1) = k2_tarski(X0,X1)
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1187])).

cnf(c_4845,plain,
    ( k7_domain_1(u1_struct_0(sK5),sK1(sK5,sK6),X0) = k2_tarski(sK1(sK5,sK6),X0)
    | v12_waybel_0(sK6,sK5) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4840,c_2998])).

cnf(c_5529,plain,
    ( k7_domain_1(u1_struct_0(sK5),sK1(sK5,sK6),sK0(sK5,sK6)) = k2_tarski(sK1(sK5,sK6),sK0(sK5,sK6))
    | v12_waybel_0(sK6,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4803,c_4845])).

cnf(c_10136,plain,
    ( k7_domain_1(u1_struct_0(sK5),sK1(sK5,sK6),sK0(sK5,sK6)) = k2_tarski(sK1(sK5,sK6),sK0(sK5,sK6)) ),
    inference(superposition,[status(thm)],[c_10131,c_5529])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | k2_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X0,X2)) = k12_lattice3(X1,X0,X2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_38,negated_conjecture,
    ( v4_orders_2(sK4) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_693,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | k2_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X0)) = k12_lattice3(X1,X2,X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_38])).

cnf(c_694,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ v3_orders_2(sK4)
    | ~ v5_orders_2(sK4)
    | ~ l1_orders_2(sK4)
    | ~ v2_lattice3(sK4)
    | k2_yellow_0(sK4,k7_domain_1(u1_struct_0(sK4),X0,X1)) = k12_lattice3(sK4,X0,X1) ),
    inference(unflattening,[status(thm)],[c_693])).

cnf(c_39,negated_conjecture,
    ( v3_orders_2(sK4) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_698,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | k2_yellow_0(sK4,k7_domain_1(u1_struct_0(sK4),X0,X1)) = k12_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_694,c_39,c_37,c_36,c_35])).

cnf(c_3003,plain,
    ( k2_yellow_0(sK4,k7_domain_1(u1_struct_0(sK4),X0,X1)) = k12_lattice3(sK4,X0,X1)
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_698])).

cnf(c_4555,plain,
    ( k2_yellow_0(sK4,k7_domain_1(u1_struct_0(sK5),X0,X1)) = k12_lattice3(sK4,X0,X1)
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3003,c_3701])).

cnf(c_4847,plain,
    ( k2_yellow_0(sK4,k7_domain_1(u1_struct_0(sK5),sK1(sK5,sK6),X0)) = k12_lattice3(sK4,sK1(sK5,sK6),X0)
    | v12_waybel_0(sK6,sK5) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4840,c_4555])).

cnf(c_6551,plain,
    ( k2_yellow_0(sK4,k7_domain_1(u1_struct_0(sK5),sK1(sK5,sK6),X0)) = k12_lattice3(sK4,sK1(sK5,sK6),X0)
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4847,c_44,c_49,c_52,c_54,c_3701,c_3756,c_3768,c_3955,c_4272,c_4764,c_5653])).

cnf(c_6560,plain,
    ( k2_yellow_0(sK4,k7_domain_1(u1_struct_0(sK5),sK1(sK5,sK6),sK0(sK5,sK6))) = k12_lattice3(sK4,sK1(sK5,sK6),sK0(sK5,sK6))
    | v12_waybel_0(sK6,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4803,c_6551])).

cnf(c_6946,plain,
    ( k2_yellow_0(sK4,k7_domain_1(u1_struct_0(sK5),sK1(sK5,sK6),sK0(sK5,sK6))) = k12_lattice3(sK4,sK1(sK5,sK6),sK0(sK5,sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6560,c_44,c_49,c_52,c_54,c_3701,c_3756,c_3768,c_3955,c_4272,c_4764,c_5653])).

cnf(c_10182,plain,
    ( k2_yellow_0(sK4,k2_tarski(sK1(sK5,sK6),sK0(sK5,sK6))) = k12_lattice3(sK4,sK1(sK5,sK6),sK0(sK5,sK6)) ),
    inference(demodulation,[status(thm)],[c_10136,c_6946])).

cnf(c_480,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | k2_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X0)) = k12_lattice3(X1,X2,X0)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_33])).

cnf(c_481,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ v3_orders_2(sK5)
    | ~ v5_orders_2(sK5)
    | ~ l1_orders_2(sK5)
    | ~ v2_lattice3(sK5)
    | k2_yellow_0(sK5,k7_domain_1(u1_struct_0(sK5),X0,X1)) = k12_lattice3(sK5,X0,X1) ),
    inference(unflattening,[status(thm)],[c_480])).

cnf(c_485,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | k2_yellow_0(sK5,k7_domain_1(u1_struct_0(sK5),X0,X1)) = k12_lattice3(sK5,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_481,c_34,c_32,c_31,c_30])).

cnf(c_3004,plain,
    ( k2_yellow_0(sK5,k7_domain_1(u1_struct_0(sK5),X0,X1)) = k12_lattice3(sK5,X0,X1)
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_485])).

cnf(c_4846,plain,
    ( k2_yellow_0(sK5,k7_domain_1(u1_struct_0(sK5),sK1(sK5,sK6),X0)) = k12_lattice3(sK5,sK1(sK5,sK6),X0)
    | v12_waybel_0(sK6,sK5) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4840,c_3004])).

cnf(c_6287,plain,
    ( k2_yellow_0(sK5,k7_domain_1(u1_struct_0(sK5),sK1(sK5,sK6),X0)) = k12_lattice3(sK5,sK1(sK5,sK6),X0)
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4846,c_44,c_49,c_52,c_54,c_3701,c_3756,c_3768,c_3955,c_4272,c_4764,c_5653])).

cnf(c_6296,plain,
    ( k2_yellow_0(sK5,k7_domain_1(u1_struct_0(sK5),sK1(sK5,sK6),sK0(sK5,sK6))) = k12_lattice3(sK5,sK1(sK5,sK6),sK0(sK5,sK6))
    | v12_waybel_0(sK6,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4803,c_6287])).

cnf(c_6447,plain,
    ( k2_yellow_0(sK5,k7_domain_1(u1_struct_0(sK5),sK1(sK5,sK6),sK0(sK5,sK6))) = k12_lattice3(sK5,sK1(sK5,sK6),sK0(sK5,sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6296,c_44,c_49,c_52,c_54,c_3701,c_3756,c_3768,c_3955,c_4272,c_4764,c_5653])).

cnf(c_10183,plain,
    ( k2_yellow_0(sK5,k2_tarski(sK1(sK5,sK6),sK0(sK5,sK6))) = k12_lattice3(sK5,sK1(sK5,sK6),sK0(sK5,sK6)) ),
    inference(demodulation,[status(thm)],[c_10136,c_6447])).

cnf(c_11367,plain,
    ( k12_lattice3(sK4,sK1(sK5,sK6),sK0(sK5,sK6)) = k12_lattice3(sK5,sK1(sK5,sK6),sK0(sK5,sK6))
    | v12_waybel_0(sK6,sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11320,c_10182,c_10183])).

cnf(c_12247,plain,
    ( k12_lattice3(sK4,sK1(sK5,sK6),sK0(sK5,sK6)) = k12_lattice3(sK5,sK1(sK5,sK6),sK0(sK5,sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11367,c_44,c_49,c_52,c_54,c_3701,c_3756,c_3768,c_3955,c_4272,c_4764,c_5653])).

cnf(c_7,plain,
    ( ~ v1_waybel_0(X0,X1)
    | ~ v12_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | r2_hidden(X3,X0)
    | r2_hidden(X2,X0)
    | ~ r2_hidden(k12_lattice3(X1,X3,X2),X0)
    | ~ v1_waybel_7(X0,X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_714,plain,
    ( ~ v1_waybel_0(X0,X1)
    | ~ v12_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | r2_hidden(X3,X0)
    | r2_hidden(X2,X0)
    | ~ r2_hidden(k12_lattice3(X1,X3,X2),X0)
    | ~ v1_waybel_7(X0,X1)
    | ~ v3_orders_2(X1)
    | ~ v5_orders_2(X1)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_38])).

cnf(c_715,plain,
    ( ~ v1_waybel_0(X0,sK4)
    | ~ v12_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | r2_hidden(X2,X0)
    | r2_hidden(X1,X0)
    | ~ r2_hidden(k12_lattice3(sK4,X2,X1),X0)
    | ~ v1_waybel_7(X0,sK4)
    | ~ v3_orders_2(sK4)
    | ~ v5_orders_2(sK4)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(sK4)
    | ~ v2_lattice3(sK4) ),
    inference(unflattening,[status(thm)],[c_714])).

cnf(c_719,plain,
    ( ~ v1_waybel_0(X0,sK4)
    | ~ v12_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | r2_hidden(X2,X0)
    | r2_hidden(X1,X0)
    | ~ r2_hidden(k12_lattice3(sK4,X2,X1),X0)
    | ~ v1_waybel_7(X0,sK4)
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_715,c_39,c_37,c_36,c_35])).

cnf(c_720,plain,
    ( ~ v1_waybel_0(X0,sK4)
    | ~ v12_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | r2_hidden(X1,X0)
    | r2_hidden(X2,X0)
    | ~ r2_hidden(k12_lattice3(sK4,X1,X2),X0)
    | ~ v1_waybel_7(X0,sK4)
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_719])).

cnf(c_1211,plain,
    ( ~ v1_waybel_0(X0,sK4)
    | ~ v12_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | r2_hidden(X1,X0)
    | r2_hidden(X2,X0)
    | ~ r2_hidden(k12_lattice3(sK4,X2,X1),X0)
    | ~ v1_waybel_7(X0,sK4)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_720,c_28])).

cnf(c_1212,plain,
    ( ~ v1_waybel_0(sK6,sK4)
    | ~ v12_waybel_0(sK6,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(X0,sK6)
    | r2_hidden(X1,sK6)
    | ~ r2_hidden(k12_lattice3(sK4,X0,X1),sK6)
    | ~ v1_waybel_7(sK6,sK4) ),
    inference(unflattening,[status(thm)],[c_1211])).

cnf(c_25,negated_conjecture,
    ( v1_waybel_7(sK6,sK4) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1216,plain,
    ( ~ r2_hidden(k12_lattice3(sK4,X0,X1),sK6)
    | r2_hidden(X1,sK6)
    | r2_hidden(X0,sK6)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1212,c_27,c_26,c_25,c_24])).

cnf(c_1217,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | r2_hidden(X1,sK6)
    | r2_hidden(X0,sK6)
    | ~ r2_hidden(k12_lattice3(sK4,X0,X1),sK6) ),
    inference(renaming,[status(thm)],[c_1216])).

cnf(c_2997,plain,
    ( m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0,sK6) = iProver_top
    | r2_hidden(X1,sK6) = iProver_top
    | r2_hidden(k12_lattice3(sK4,X0,X1),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1217])).

cnf(c_5040,plain,
    ( m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X0,sK6) = iProver_top
    | r2_hidden(X1,sK6) = iProver_top
    | r2_hidden(k12_lattice3(sK4,X0,X1),sK6) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2997,c_3701])).

cnf(c_12261,plain,
    ( m1_subset_1(sK0(sK5,sK6),u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK1(sK5,sK6),u1_struct_0(sK5)) != iProver_top
    | r2_hidden(k12_lattice3(sK5,sK1(sK5,sK6),sK0(sK5,sK6)),sK6) != iProver_top
    | r2_hidden(sK0(sK5,sK6),sK6) = iProver_top
    | r2_hidden(sK1(sK5,sK6),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_12247,c_5040])).

cnf(c_1,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_4808,plain,
    ( k7_domain_1(u1_struct_0(sK5),sK0(sK5,sK6),X0) = k2_tarski(sK0(sK5,sK6),X0)
    | v12_waybel_0(sK6,sK5) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4803,c_2998])).

cnf(c_5410,plain,
    ( k7_domain_1(u1_struct_0(sK5),sK0(sK5,sK6),sK1(sK5,sK6)) = k2_tarski(sK0(sK5,sK6),sK1(sK5,sK6))
    | v12_waybel_0(sK6,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4840,c_4808])).

cnf(c_10139,plain,
    ( k7_domain_1(u1_struct_0(sK5),sK0(sK5,sK6),sK1(sK5,sK6)) = k2_tarski(sK0(sK5,sK6),sK1(sK5,sK6)) ),
    inference(superposition,[status(thm)],[c_10131,c_5410])).

cnf(c_4809,plain,
    ( k2_yellow_0(sK5,k7_domain_1(u1_struct_0(sK5),sK0(sK5,sK6),X0)) = k12_lattice3(sK5,sK0(sK5,sK6),X0)
    | v12_waybel_0(sK6,sK5) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4803,c_3004])).

cnf(c_5680,plain,
    ( k2_yellow_0(sK5,k7_domain_1(u1_struct_0(sK5),sK0(sK5,sK6),X0)) = k12_lattice3(sK5,sK0(sK5,sK6),X0)
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4809,c_44,c_49,c_52,c_54,c_3701,c_3756,c_3768,c_3955,c_4272,c_4764,c_5653])).

cnf(c_5688,plain,
    ( k2_yellow_0(sK5,k7_domain_1(u1_struct_0(sK5),sK0(sK5,sK6),sK1(sK5,sK6))) = k12_lattice3(sK5,sK0(sK5,sK6),sK1(sK5,sK6))
    | v12_waybel_0(sK6,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4840,c_5680])).

cnf(c_5725,plain,
    ( k2_yellow_0(sK5,k7_domain_1(u1_struct_0(sK5),sK0(sK5,sK6),sK1(sK5,sK6))) = k12_lattice3(sK5,sK0(sK5,sK6),sK1(sK5,sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5688,c_44,c_49,c_52,c_54,c_3701,c_3756,c_3768,c_3955,c_4272,c_4764,c_5653])).

cnf(c_10551,plain,
    ( k2_yellow_0(sK5,k2_tarski(sK0(sK5,sK6),sK1(sK5,sK6))) = k12_lattice3(sK5,sK0(sK5,sK6),sK1(sK5,sK6)) ),
    inference(demodulation,[status(thm)],[c_10139,c_5725])).

cnf(c_11099,plain,
    ( k2_yellow_0(sK5,k2_tarski(sK1(sK5,sK6),sK0(sK5,sK6))) = k12_lattice3(sK5,sK0(sK5,sK6),sK1(sK5,sK6)) ),
    inference(superposition,[status(thm)],[c_1,c_10551])).

cnf(c_11101,plain,
    ( k12_lattice3(sK5,sK1(sK5,sK6),sK0(sK5,sK6)) = k12_lattice3(sK5,sK0(sK5,sK6),sK1(sK5,sK6)) ),
    inference(light_normalisation,[status(thm)],[c_11099,c_10183])).

cnf(c_4,plain,
    ( ~ v1_waybel_0(X0,X1)
    | ~ v12_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(k12_lattice3(X1,sK0(X1,X0),sK1(X1,X0)),X0)
    | v1_waybel_7(X0,X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_603,plain,
    ( ~ v1_waybel_0(X0,X1)
    | ~ v12_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(k12_lattice3(X1,sK0(X1,X0),sK1(X1,X0)),X0)
    | v1_waybel_7(X0,X1)
    | ~ v3_orders_2(X1)
    | ~ v5_orders_2(X1)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_33])).

cnf(c_604,plain,
    ( ~ v1_waybel_0(X0,sK5)
    | ~ v12_waybel_0(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | r2_hidden(k12_lattice3(sK5,sK0(sK5,X0),sK1(sK5,X0)),X0)
    | v1_waybel_7(X0,sK5)
    | ~ v3_orders_2(sK5)
    | ~ v5_orders_2(sK5)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(sK5)
    | ~ v2_lattice3(sK5) ),
    inference(unflattening,[status(thm)],[c_603])).

cnf(c_608,plain,
    ( ~ v1_waybel_0(X0,sK5)
    | ~ v12_waybel_0(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | r2_hidden(k12_lattice3(sK5,sK0(sK5,X0),sK1(sK5,X0)),X0)
    | v1_waybel_7(X0,sK5)
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_604,c_34,c_32,c_31,c_30])).

cnf(c_1278,plain,
    ( ~ v1_waybel_0(X0,sK5)
    | ~ v12_waybel_0(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | r2_hidden(k12_lattice3(sK5,sK0(sK5,X0),sK1(sK5,X0)),X0)
    | v1_waybel_7(X0,sK5)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_608,c_28])).

cnf(c_1279,plain,
    ( ~ v1_waybel_0(sK6,sK5)
    | ~ v12_waybel_0(sK6,sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | r2_hidden(k12_lattice3(sK5,sK0(sK5,sK6),sK1(sK5,sK6)),sK6)
    | v1_waybel_7(sK6,sK5) ),
    inference(unflattening,[status(thm)],[c_1278])).

cnf(c_1281,plain,
    ( r2_hidden(k12_lattice3(sK5,sK0(sK5,sK6),sK1(sK5,sK6)),sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ v12_waybel_0(sK6,sK5)
    | ~ v1_waybel_0(sK6,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1279,c_28,c_23])).

cnf(c_1282,plain,
    ( ~ v1_waybel_0(sK6,sK5)
    | ~ v12_waybel_0(sK6,sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | r2_hidden(k12_lattice3(sK5,sK0(sK5,sK6),sK1(sK5,sK6)),sK6) ),
    inference(renaming,[status(thm)],[c_1281])).

cnf(c_2994,plain,
    ( v1_waybel_0(sK6,sK5) != iProver_top
    | v12_waybel_0(sK6,sK5) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r2_hidden(k12_lattice3(sK5,sK0(sK5,sK6),sK1(sK5,sK6)),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1282])).

cnf(c_1283,plain,
    ( v1_waybel_0(sK6,sK5) != iProver_top
    | v12_waybel_0(sK6,sK5) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r2_hidden(k12_lattice3(sK5,sK0(sK5,sK6),sK1(sK5,sK6)),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1282])).

cnf(c_5033,plain,
    ( v12_waybel_0(sK6,sK5) != iProver_top
    | r2_hidden(k12_lattice3(sK5,sK0(sK5,sK6),sK1(sK5,sK6)),sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2994,c_44,c_49,c_51,c_54,c_1283,c_3701,c_3756,c_3768,c_3813,c_3955,c_4272,c_4764])).

cnf(c_11727,plain,
    ( v12_waybel_0(sK6,sK5) != iProver_top
    | r2_hidden(k12_lattice3(sK5,sK1(sK5,sK6),sK0(sK5,sK6)),sK6) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11101,c_5033])).

cnf(c_3,plain,
    ( ~ v1_waybel_0(X0,X1)
    | ~ v12_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(sK0(X1,X0),X0)
    | v1_waybel_7(X0,X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_633,plain,
    ( ~ v1_waybel_0(X0,X1)
    | ~ v12_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(sK0(X1,X0),X0)
    | v1_waybel_7(X0,X1)
    | ~ v3_orders_2(X1)
    | ~ v5_orders_2(X1)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_33])).

cnf(c_634,plain,
    ( ~ v1_waybel_0(X0,sK5)
    | ~ v12_waybel_0(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(sK0(sK5,X0),X0)
    | v1_waybel_7(X0,sK5)
    | ~ v3_orders_2(sK5)
    | ~ v5_orders_2(sK5)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(sK5)
    | ~ v2_lattice3(sK5) ),
    inference(unflattening,[status(thm)],[c_633])).

cnf(c_638,plain,
    ( ~ v1_waybel_0(X0,sK5)
    | ~ v12_waybel_0(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(sK0(sK5,X0),X0)
    | v1_waybel_7(X0,sK5)
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_634,c_34,c_32,c_31,c_30])).

cnf(c_1258,plain,
    ( ~ v1_waybel_0(X0,sK5)
    | ~ v12_waybel_0(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(sK0(sK5,X0),X0)
    | v1_waybel_7(X0,sK5)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_638,c_28])).

cnf(c_1259,plain,
    ( ~ v1_waybel_0(sK6,sK5)
    | ~ v12_waybel_0(sK6,sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(sK0(sK5,sK6),sK6)
    | v1_waybel_7(sK6,sK5) ),
    inference(unflattening,[status(thm)],[c_1258])).

cnf(c_1261,plain,
    ( ~ r2_hidden(sK0(sK5,sK6),sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ v12_waybel_0(sK6,sK5)
    | ~ v1_waybel_0(sK6,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1259,c_28,c_23])).

cnf(c_1262,plain,
    ( ~ v1_waybel_0(sK6,sK5)
    | ~ v12_waybel_0(sK6,sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(sK0(sK5,sK6),sK6) ),
    inference(renaming,[status(thm)],[c_1261])).

cnf(c_1263,plain,
    ( v1_waybel_0(sK6,sK5) != iProver_top
    | v12_waybel_0(sK6,sK5) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r2_hidden(sK0(sK5,sK6),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1262])).

cnf(c_2,plain,
    ( ~ v1_waybel_0(X0,X1)
    | ~ v12_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(sK1(X1,X0),X0)
    | v1_waybel_7(X0,X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_663,plain,
    ( ~ v1_waybel_0(X0,X1)
    | ~ v12_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(sK1(X1,X0),X0)
    | v1_waybel_7(X0,X1)
    | ~ v3_orders_2(X1)
    | ~ v5_orders_2(X1)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_33])).

cnf(c_664,plain,
    ( ~ v1_waybel_0(X0,sK5)
    | ~ v12_waybel_0(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(sK1(sK5,X0),X0)
    | v1_waybel_7(X0,sK5)
    | ~ v3_orders_2(sK5)
    | ~ v5_orders_2(sK5)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(sK5)
    | ~ v2_lattice3(sK5) ),
    inference(unflattening,[status(thm)],[c_663])).

cnf(c_668,plain,
    ( ~ v1_waybel_0(X0,sK5)
    | ~ v12_waybel_0(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(sK1(sK5,X0),X0)
    | v1_waybel_7(X0,sK5)
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_664,c_34,c_32,c_31,c_30])).

cnf(c_1238,plain,
    ( ~ v1_waybel_0(X0,sK5)
    | ~ v12_waybel_0(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(sK1(sK5,X0),X0)
    | v1_waybel_7(X0,sK5)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_668,c_28])).

cnf(c_1239,plain,
    ( ~ v1_waybel_0(sK6,sK5)
    | ~ v12_waybel_0(sK6,sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(sK1(sK5,sK6),sK6)
    | v1_waybel_7(sK6,sK5) ),
    inference(unflattening,[status(thm)],[c_1238])).

cnf(c_1241,plain,
    ( ~ r2_hidden(sK1(sK5,sK6),sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ v12_waybel_0(sK6,sK5)
    | ~ v1_waybel_0(sK6,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1239,c_28,c_23])).

cnf(c_1242,plain,
    ( ~ v1_waybel_0(sK6,sK5)
    | ~ v12_waybel_0(sK6,sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(sK1(sK5,sK6),sK6) ),
    inference(renaming,[status(thm)],[c_1241])).

cnf(c_1243,plain,
    ( v1_waybel_0(sK6,sK5) != iProver_top
    | v12_waybel_0(sK6,sK5) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r2_hidden(sK1(sK5,sK6),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1242])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12261,c_11727,c_5653,c_4764,c_4272,c_3955,c_3813,c_3768,c_3756,c_3701,c_1323,c_1303,c_1263,c_1243,c_54,c_52,c_51,c_49,c_44])).


%------------------------------------------------------------------------------
