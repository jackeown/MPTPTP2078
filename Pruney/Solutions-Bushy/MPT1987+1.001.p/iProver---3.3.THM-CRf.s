%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1987+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:59 EST 2020

% Result     : Theorem 1.37s
% Output     : CNFRefutation 1.37s
% Verified   : 
% Statistics : Number of formulae       :  240 (3738 expanded)
%              Number of clauses        :  158 ( 499 expanded)
%              Number of leaves         :   16 (1198 expanded)
%              Depth                    :   20
%              Number of atoms          : 1853 (73763 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   21 (   8 average)
%              Maximal clause size      :   52 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_waybel_3(X0,X1,X2)
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                      & v12_waybel_0(X3,X0)
                      & v1_waybel_0(X3,X0)
                      & ~ v1_xboole_0(X3) )
                   => ( r3_orders_2(X0,X2,k1_yellow_0(X0,X3))
                     => r2_hidden(X1,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_hidden(X1,X3)
                  | ~ r3_orders_2(X0,X2,k1_yellow_0(X0,X3))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  | ~ v12_waybel_0(X3,X0)
                  | ~ v1_waybel_0(X3,X0)
                  | v1_xboole_0(X3) )
              | ~ r1_waybel_3(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_hidden(X1,X3)
                  | ~ r3_orders_2(X0,X2,k1_yellow_0(X0,X3))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  | ~ v12_waybel_0(X3,X0)
                  | ~ v1_waybel_0(X3,X0)
                  | v1_xboole_0(X3) )
              | ~ r1_waybel_3(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r3_orders_2(X0,X2,k1_yellow_0(X0,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X3,X0)
      | ~ v1_waybel_0(X3,X0)
      | v1_xboole_0(X3)
      | ~ r1_waybel_3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f16,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f15])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_lattice3(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v2_waybel_1(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_waybel_3(X0,X1,X2)
              <=> ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                      & v1_waybel_7(X3,X0)
                      & v12_waybel_0(X3,X0)
                      & v1_waybel_0(X3,X0)
                      & ~ v1_xboole_0(X3) )
                   => ( r3_orders_2(X0,X2,k1_yellow_0(X0,X3))
                     => r2_hidden(X1,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v3_lattice3(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v2_waybel_1(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r1_waybel_3(X0,X1,X2)
                <=> ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                        & v1_waybel_7(X3,X0)
                        & v12_waybel_0(X3,X0)
                        & v1_waybel_0(X3,X0)
                        & ~ v1_xboole_0(X3) )
                     => ( r3_orders_2(X0,X2,k1_yellow_0(X0,X3))
                       => r2_hidden(X1,X3) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r1_waybel_3(X0,X1,X2)
              <~> ! [X3] :
                    ( r2_hidden(X1,X3)
                    | ~ r3_orders_2(X0,X2,k1_yellow_0(X0,X3))
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                    | ~ v1_waybel_7(X3,X0)
                    | ~ v12_waybel_0(X3,X0)
                    | ~ v1_waybel_0(X3,X0)
                    | v1_xboole_0(X3) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_lattice3(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v2_waybel_1(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r1_waybel_3(X0,X1,X2)
              <~> ! [X3] :
                    ( r2_hidden(X1,X3)
                    | ~ r3_orders_2(X0,X2,k1_yellow_0(X0,X3))
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                    | ~ v1_waybel_7(X3,X0)
                    | ~ v12_waybel_0(X3,X0)
                    | ~ v1_waybel_0(X3,X0)
                    | v1_xboole_0(X3) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_lattice3(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v2_waybel_1(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f30])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ r2_hidden(X1,X3)
                    & r3_orders_2(X0,X2,k1_yellow_0(X0,X3))
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                    & v1_waybel_7(X3,X0)
                    & v12_waybel_0(X3,X0)
                    & v1_waybel_0(X3,X0)
                    & ~ v1_xboole_0(X3) )
                | ~ r1_waybel_3(X0,X1,X2) )
              & ( ! [X3] :
                    ( r2_hidden(X1,X3)
                    | ~ r3_orders_2(X0,X2,k1_yellow_0(X0,X3))
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                    | ~ v1_waybel_7(X3,X0)
                    | ~ v12_waybel_0(X3,X0)
                    | ~ v1_waybel_0(X3,X0)
                    | v1_xboole_0(X3) )
                | r1_waybel_3(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_lattice3(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v2_waybel_1(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ r2_hidden(X1,X3)
                    & r3_orders_2(X0,X2,k1_yellow_0(X0,X3))
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                    & v1_waybel_7(X3,X0)
                    & v12_waybel_0(X3,X0)
                    & v1_waybel_0(X3,X0)
                    & ~ v1_xboole_0(X3) )
                | ~ r1_waybel_3(X0,X1,X2) )
              & ( ! [X3] :
                    ( r2_hidden(X1,X3)
                    | ~ r3_orders_2(X0,X2,k1_yellow_0(X0,X3))
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                    | ~ v1_waybel_7(X3,X0)
                    | ~ v12_waybel_0(X3,X0)
                    | ~ v1_waybel_0(X3,X0)
                    | v1_xboole_0(X3) )
                | r1_waybel_3(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_lattice3(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v2_waybel_1(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f37])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ r2_hidden(X1,X3)
                    & r3_orders_2(X0,X2,k1_yellow_0(X0,X3))
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                    & v1_waybel_7(X3,X0)
                    & v12_waybel_0(X3,X0)
                    & v1_waybel_0(X3,X0)
                    & ~ v1_xboole_0(X3) )
                | ~ r1_waybel_3(X0,X1,X2) )
              & ( ! [X4] :
                    ( r2_hidden(X1,X4)
                    | ~ r3_orders_2(X0,X2,k1_yellow_0(X0,X4))
                    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                    | ~ v1_waybel_7(X4,X0)
                    | ~ v12_waybel_0(X4,X0)
                    | ~ v1_waybel_0(X4,X0)
                    | v1_xboole_0(X4) )
                | r1_waybel_3(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_lattice3(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v2_waybel_1(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(rectify,[],[f38])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_hidden(X1,X3)
          & r3_orders_2(X0,X2,k1_yellow_0(X0,X3))
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_waybel_7(X3,X0)
          & v12_waybel_0(X3,X0)
          & v1_waybel_0(X3,X0)
          & ~ v1_xboole_0(X3) )
     => ( ~ r2_hidden(X1,sK5)
        & r3_orders_2(X0,X2,k1_yellow_0(X0,sK5))
        & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
        & v1_waybel_7(sK5,X0)
        & v12_waybel_0(sK5,X0)
        & v1_waybel_0(sK5,X0)
        & ~ v1_xboole_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( ~ r2_hidden(X1,X3)
                & r3_orders_2(X0,X2,k1_yellow_0(X0,X3))
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                & v1_waybel_7(X3,X0)
                & v12_waybel_0(X3,X0)
                & v1_waybel_0(X3,X0)
                & ~ v1_xboole_0(X3) )
            | ~ r1_waybel_3(X0,X1,X2) )
          & ( ! [X4] :
                ( r2_hidden(X1,X4)
                | ~ r3_orders_2(X0,X2,k1_yellow_0(X0,X4))
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                | ~ v1_waybel_7(X4,X0)
                | ~ v12_waybel_0(X4,X0)
                | ~ v1_waybel_0(X4,X0)
                | v1_xboole_0(X4) )
            | r1_waybel_3(X0,X1,X2) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( ? [X3] :
              ( ~ r2_hidden(X1,X3)
              & r3_orders_2(X0,sK4,k1_yellow_0(X0,X3))
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_waybel_7(X3,X0)
              & v12_waybel_0(X3,X0)
              & v1_waybel_0(X3,X0)
              & ~ v1_xboole_0(X3) )
          | ~ r1_waybel_3(X0,X1,sK4) )
        & ( ! [X4] :
              ( r2_hidden(X1,X4)
              | ~ r3_orders_2(X0,sK4,k1_yellow_0(X0,X4))
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v1_waybel_7(X4,X0)
              | ~ v12_waybel_0(X4,X0)
              | ~ v1_waybel_0(X4,X0)
              | v1_xboole_0(X4) )
          | r1_waybel_3(X0,X1,sK4) )
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ r2_hidden(X1,X3)
                    & r3_orders_2(X0,X2,k1_yellow_0(X0,X3))
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                    & v1_waybel_7(X3,X0)
                    & v12_waybel_0(X3,X0)
                    & v1_waybel_0(X3,X0)
                    & ~ v1_xboole_0(X3) )
                | ~ r1_waybel_3(X0,X1,X2) )
              & ( ! [X4] :
                    ( r2_hidden(X1,X4)
                    | ~ r3_orders_2(X0,X2,k1_yellow_0(X0,X4))
                    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                    | ~ v1_waybel_7(X4,X0)
                    | ~ v12_waybel_0(X4,X0)
                    | ~ v1_waybel_0(X4,X0)
                    | v1_xboole_0(X4) )
                | r1_waybel_3(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ( ? [X3] :
                  ( ~ r2_hidden(sK3,X3)
                  & r3_orders_2(X0,X2,k1_yellow_0(X0,X3))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  & v1_waybel_7(X3,X0)
                  & v12_waybel_0(X3,X0)
                  & v1_waybel_0(X3,X0)
                  & ~ v1_xboole_0(X3) )
              | ~ r1_waybel_3(X0,sK3,X2) )
            & ( ! [X4] :
                  ( r2_hidden(sK3,X4)
                  | ~ r3_orders_2(X0,X2,k1_yellow_0(X0,X4))
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                  | ~ v1_waybel_7(X4,X0)
                  | ~ v12_waybel_0(X4,X0)
                  | ~ v1_waybel_0(X4,X0)
                  | v1_xboole_0(X4) )
              | r1_waybel_3(X0,sK3,X2) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ? [X3] :
                      ( ~ r2_hidden(X1,X3)
                      & r3_orders_2(X0,X2,k1_yellow_0(X0,X3))
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                      & v1_waybel_7(X3,X0)
                      & v12_waybel_0(X3,X0)
                      & v1_waybel_0(X3,X0)
                      & ~ v1_xboole_0(X3) )
                  | ~ r1_waybel_3(X0,X1,X2) )
                & ( ! [X4] :
                      ( r2_hidden(X1,X4)
                      | ~ r3_orders_2(X0,X2,k1_yellow_0(X0,X4))
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                      | ~ v1_waybel_7(X4,X0)
                      | ~ v12_waybel_0(X4,X0)
                      | ~ v1_waybel_0(X4,X0)
                      | v1_xboole_0(X4) )
                  | r1_waybel_3(X0,X1,X2) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v3_lattice3(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v2_waybel_1(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ r2_hidden(X1,X3)
                    & r3_orders_2(sK2,X2,k1_yellow_0(sK2,X3))
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
                    & v1_waybel_7(X3,sK2)
                    & v12_waybel_0(X3,sK2)
                    & v1_waybel_0(X3,sK2)
                    & ~ v1_xboole_0(X3) )
                | ~ r1_waybel_3(sK2,X1,X2) )
              & ( ! [X4] :
                    ( r2_hidden(X1,X4)
                    | ~ r3_orders_2(sK2,X2,k1_yellow_0(sK2,X4))
                    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK2)))
                    | ~ v1_waybel_7(X4,sK2)
                    | ~ v12_waybel_0(X4,sK2)
                    | ~ v1_waybel_0(X4,sK2)
                    | v1_xboole_0(X4) )
                | r1_waybel_3(sK2,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(sK2)) )
          & m1_subset_1(X1,u1_struct_0(sK2)) )
      & l1_orders_2(sK2)
      & v3_lattice3(sK2)
      & v2_lattice3(sK2)
      & v1_lattice3(sK2)
      & v2_waybel_1(sK2)
      & v5_orders_2(sK2)
      & v4_orders_2(sK2)
      & v3_orders_2(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ( ( ~ r2_hidden(sK3,sK5)
        & r3_orders_2(sK2,sK4,k1_yellow_0(sK2,sK5))
        & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
        & v1_waybel_7(sK5,sK2)
        & v12_waybel_0(sK5,sK2)
        & v1_waybel_0(sK5,sK2)
        & ~ v1_xboole_0(sK5) )
      | ~ r1_waybel_3(sK2,sK3,sK4) )
    & ( ! [X4] :
          ( r2_hidden(sK3,X4)
          | ~ r3_orders_2(sK2,sK4,k1_yellow_0(sK2,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK2)))
          | ~ v1_waybel_7(X4,sK2)
          | ~ v12_waybel_0(X4,sK2)
          | ~ v1_waybel_0(X4,sK2)
          | v1_xboole_0(X4) )
      | r1_waybel_3(sK2,sK3,sK4) )
    & m1_subset_1(sK4,u1_struct_0(sK2))
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l1_orders_2(sK2)
    & v3_lattice3(sK2)
    & v2_lattice3(sK2)
    & v1_lattice3(sK2)
    & v2_waybel_1(sK2)
    & v5_orders_2(sK2)
    & v4_orders_2(sK2)
    & v3_orders_2(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f39,f43,f42,f41,f40])).

fof(f70,plain,(
    v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f69,plain,(
    v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f74,plain,(
    v2_lattice3(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f76,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,X1,X2)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X2) )
                   => r1_orders_2(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X1,X3)
                  | ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X1,X3)
                  | ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(flattening,[],[f24])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_lattice3(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => ( r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
            & r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
            & r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) )
          | ~ r1_tarski(X1,X2) )
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
            & r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) )
          | ~ r1_tarski(X1,X2) )
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f28])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f75,plain,(
    v3_lattice3(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f71,plain,(
    v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f73,plain,(
    v1_lattice3(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v2_waybel_1(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v12_waybel_0(X1,X0)
            & v1_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ~ ( ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                        & v12_waybel_0(X3,X0)
                        & v1_waybel_0(X3,X0)
                        & ~ v1_xboole_0(X3) )
                     => ~ ( ~ r2_hidden(X2,X3)
                          & r1_tarski(X1,X3)
                          & v1_waybel_7(X3,X0) ) )
                  & ~ r2_hidden(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(X2,X3)
                  & r1_tarski(X1,X3)
                  & v1_waybel_7(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  & v12_waybel_0(X3,X0)
                  & v1_waybel_0(X3,X0)
                  & ~ v1_xboole_0(X3) )
              | r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(X2,X3)
                  & r1_tarski(X1,X3)
                  & v1_waybel_7(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  & v12_waybel_0(X3,X0)
                  & v1_waybel_0(X3,X0)
                  & ~ v1_xboole_0(X3) )
              | r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f26])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X2,X3)
          & r1_tarski(X1,X3)
          & v1_waybel_7(X3,X0)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
          & v12_waybel_0(X3,X0)
          & v1_waybel_0(X3,X0)
          & ~ v1_xboole_0(X3) )
     => ( ~ r2_hidden(X2,sK1(X0,X1,X2))
        & r1_tarski(X1,sK1(X0,X1,X2))
        & v1_waybel_7(sK1(X0,X1,X2),X0)
        & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
        & v12_waybel_0(sK1(X0,X1,X2),X0)
        & v1_waybel_0(sK1(X0,X1,X2),X0)
        & ~ v1_xboole_0(sK1(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ~ r2_hidden(X2,sK1(X0,X1,X2))
                & r1_tarski(X1,sK1(X0,X1,X2))
                & v1_waybel_7(sK1(X0,X1,X2),X0)
                & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                & v12_waybel_0(sK1(X0,X1,X2),X0)
                & v1_waybel_0(sK1(X0,X1,X2),X0)
                & ~ v1_xboole_0(sK1(X0,X1,X2)) )
              | r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f35])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f72,plain,(
    v2_waybel_1(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v12_waybel_0(sK1(X0,X1,X2),X0)
      | r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v1_waybel_0(sK1(X0,X1,X2),X0)
      | r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(sK1(X0,X1,X2))
      | r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v1_waybel_7(sK1(X0,X1,X2),X0)
      | r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f79,plain,(
    ! [X4] :
      ( r2_hidden(sK3,X4)
      | ~ r3_orders_2(sK2,sK4,k1_yellow_0(sK2,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v1_waybel_7(X4,sK2)
      | ~ v12_waybel_0(X4,sK2)
      | ~ v1_waybel_0(X4,sK2)
      | v1_xboole_0(X4)
      | r1_waybel_3(sK2,sK3,sK4) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,sK1(X0,X1,X2))
      | r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,sK1(X0,X1,X2))
      | r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v24_waybel_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                      & v12_waybel_0(X3,X0)
                      & v1_waybel_0(X3,X0)
                      & ~ v1_xboole_0(X3) )
                   => ( r3_orders_2(X0,X2,k1_yellow_0(X0,X3))
                     => r2_hidden(X1,X3) ) )
               => r1_waybel_3(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r2_hidden(X1,X3)
                  & r3_orders_2(X0,X2,k1_yellow_0(X0,X3))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  & v12_waybel_0(X3,X0)
                  & v1_waybel_0(X3,X0)
                  & ~ v1_xboole_0(X3) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v24_waybel_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r2_hidden(X1,X3)
                  & r3_orders_2(X0,X2,k1_yellow_0(X0,X3))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  & v12_waybel_0(X3,X0)
                  & v1_waybel_0(X3,X0)
                  & ~ v1_xboole_0(X3) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v24_waybel_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X1,X3)
          & r3_orders_2(X0,X2,k1_yellow_0(X0,X3))
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
          & v12_waybel_0(X3,X0)
          & v1_waybel_0(X3,X0)
          & ~ v1_xboole_0(X3) )
     => ( ~ r2_hidden(X1,sK0(X0,X1,X2))
        & r3_orders_2(X0,X2,k1_yellow_0(X0,sK0(X0,X1,X2)))
        & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
        & v12_waybel_0(sK0(X0,X1,X2),X0)
        & v1_waybel_0(sK0(X0,X1,X2),X0)
        & ~ v1_xboole_0(sK0(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_3(X0,X1,X2)
              | ( ~ r2_hidden(X1,sK0(X0,X1,X2))
                & r3_orders_2(X0,X2,k1_yellow_0(X0,sK0(X0,X1,X2)))
                & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                & v12_waybel_0(sK0(X0,X1,X2),X0)
                & v1_waybel_0(sK0(X0,X1,X2),X0)
                & ~ v1_xboole_0(sK0(X0,X1,X2)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v24_waybel_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f33])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r1_waybel_3(X0,X1,X2)
      | r3_orders_2(X0,X2,k1_yellow_0(X0,sK0(X0,X1,X2)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v24_waybel_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( ( v3_lattice3(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ( v25_waybel_0(X0)
          & v24_waybel_0(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( ( v3_lattice3(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ( v24_waybel_0(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f1])).

fof(f13,plain,(
    ! [X0] :
      ( ( v24_waybel_0(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
      | ~ v3_lattice3(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f14,plain,(
    ! [X0] :
      ( ( v24_waybel_0(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
      | ~ v3_lattice3(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f13])).

fof(f47,plain,(
    ! [X0] :
      ( v24_waybel_0(X0)
      | ~ v3_lattice3(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r1_waybel_3(X0,X1,X2)
      | ~ r2_hidden(X1,sK0(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v24_waybel_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_waybel_3(X0,X1,X2)
      | ~ v1_xboole_0(sK0(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v24_waybel_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_waybel_3(X0,X1,X2)
      | v1_waybel_0(sK0(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v24_waybel_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r1_waybel_3(X0,X1,X2)
      | v12_waybel_0(sK0(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v24_waybel_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r1_waybel_3(X0,X1,X2)
      | m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v24_waybel_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f86,plain,
    ( ~ r2_hidden(sK3,sK5)
    | ~ r1_waybel_3(sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f44])).

fof(f77,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f44])).

fof(f78,plain,(
    m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f44])).

fof(f85,plain,
    ( r3_orders_2(sK2,sK4,k1_yellow_0(sK2,sK5))
    | ~ r1_waybel_3(sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f44])).

fof(f84,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_waybel_3(sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f44])).

fof(f82,plain,
    ( v12_waybel_0(sK5,sK2)
    | ~ r1_waybel_3(sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f44])).

fof(f81,plain,
    ( v1_waybel_0(sK5,sK2)
    | ~ r1_waybel_3(sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f44])).

fof(f80,plain,
    ( ~ v1_xboole_0(sK5)
    | ~ r1_waybel_3(sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_7,plain,
    ( ~ r1_waybel_3(X0,X1,X2)
    | ~ r3_orders_2(X0,X2,k1_yellow_0(X0,X3))
    | ~ v1_waybel_0(X3,X0)
    | ~ v12_waybel_0(X3,X0)
    | r2_hidden(X1,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_orders_2(X0)
    | v1_xboole_0(X3)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_3,plain,
    ( ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_786,plain,
    ( ~ r1_waybel_3(X0,X1,X2)
    | ~ r3_orders_2(X0,X2,k1_yellow_0(X0,X3))
    | ~ v1_waybel_0(X3,X0)
    | ~ v12_waybel_0(X3,X0)
    | r2_hidden(X1,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_orders_2(X0)
    | v1_xboole_0(X3)
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v3_orders_2(X0) ),
    inference(resolution,[status(thm)],[c_7,c_3])).

cnf(c_40,negated_conjecture,
    ( v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1221,plain,
    ( ~ r1_waybel_3(sK2,X0,X1)
    | ~ r3_orders_2(sK2,X1,k1_yellow_0(sK2,X2))
    | ~ v1_waybel_0(X2,sK2)
    | ~ v12_waybel_0(X2,sK2)
    | r2_hidden(X0,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | v1_xboole_0(X2)
    | ~ v2_lattice3(sK2)
    | ~ l1_orders_2(sK2)
    | ~ v3_orders_2(sK2) ),
    inference(resolution,[status(thm)],[c_786,c_40])).

cnf(c_41,negated_conjecture,
    ( v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_36,negated_conjecture,
    ( v2_lattice3(sK2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_34,negated_conjecture,
    ( l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1225,plain,
    ( v1_xboole_0(X2)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(X0,X2)
    | ~ v12_waybel_0(X2,sK2)
    | ~ v1_waybel_0(X2,sK2)
    | ~ r3_orders_2(sK2,X1,k1_yellow_0(sK2,X2))
    | ~ r1_waybel_3(sK2,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1221,c_41,c_36,c_34])).

cnf(c_1226,plain,
    ( ~ r1_waybel_3(sK2,X0,X1)
    | ~ r3_orders_2(sK2,X1,k1_yellow_0(sK2,X2))
    | ~ v1_waybel_0(X2,sK2)
    | ~ v12_waybel_0(X2,sK2)
    | r2_hidden(X0,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | v1_xboole_0(X2) ),
    inference(renaming,[status(thm)],[c_1225])).

cnf(c_4254,plain,
    ( ~ r1_waybel_3(sK2,X0_58,X1_58)
    | ~ r3_orders_2(sK2,X1_58,k1_yellow_0(sK2,X2_58))
    | ~ v1_waybel_0(X2_58,sK2)
    | ~ v12_waybel_0(X2_58,sK2)
    | r2_hidden(X0_58,X2_58)
    | ~ m1_subset_1(X2_58,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1_58,u1_struct_0(sK2))
    | ~ m1_subset_1(X0_58,u1_struct_0(sK2))
    | v1_xboole_0(X2_58) ),
    inference(subtyping,[status(esa)],[c_1226])).

cnf(c_4461,plain,
    ( ~ r1_waybel_3(sK2,X0_58,X1_58)
    | ~ r3_orders_2(sK2,X1_58,k1_yellow_0(sK2,sK5))
    | ~ v1_waybel_0(sK5,sK2)
    | ~ v12_waybel_0(sK5,sK2)
    | r2_hidden(X0_58,sK5)
    | ~ m1_subset_1(X1_58,u1_struct_0(sK2))
    | ~ m1_subset_1(X0_58,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(sK5) ),
    inference(instantiation,[status(thm)],[c_4254])).

cnf(c_5457,plain,
    ( ~ r1_waybel_3(sK2,X0_58,sK4)
    | ~ r3_orders_2(sK2,sK4,k1_yellow_0(sK2,sK5))
    | ~ v1_waybel_0(sK5,sK2)
    | ~ v12_waybel_0(sK5,sK2)
    | r2_hidden(X0_58,sK5)
    | ~ m1_subset_1(X0_58,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(sK5) ),
    inference(instantiation,[status(thm)],[c_4461])).

cnf(c_5459,plain,
    ( ~ r1_waybel_3(sK2,sK3,sK4)
    | ~ r3_orders_2(sK2,sK4,k1_yellow_0(sK2,sK5))
    | ~ v1_waybel_0(sK5,sK2)
    | ~ v12_waybel_0(sK5,sK2)
    | r2_hidden(sK3,sK5)
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | v1_xboole_0(sK5) ),
    inference(instantiation,[status(thm)],[c_5457])).

cnf(c_5,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_856,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v3_orders_2(X0) ),
    inference(resolution,[status(thm)],[c_5,c_3])).

cnf(c_1301,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | r3_orders_2(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ v2_lattice3(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(resolution,[status(thm)],[c_856,c_41])).

cnf(c_1305,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | r3_orders_2(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1301,c_36,c_34])).

cnf(c_4252,plain,
    ( ~ r1_orders_2(sK2,X0_58,X1_58)
    | r3_orders_2(sK2,X0_58,X1_58)
    | ~ m1_subset_1(X1_58,u1_struct_0(sK2))
    | ~ m1_subset_1(X0_58,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_1305])).

cnf(c_5263,plain,
    ( ~ r1_orders_2(sK2,sK4,k1_yellow_0(sK2,sK1(sK2,sK0(sK2,sK3,sK4),X0_58)))
    | r3_orders_2(sK2,sK4,k1_yellow_0(sK2,sK1(sK2,sK0(sK2,sK3,sK4),X0_58)))
    | ~ m1_subset_1(k1_yellow_0(sK2,sK1(sK2,sK0(sK2,sK3,sK4),X0_58)),u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_4252])).

cnf(c_5265,plain,
    ( ~ r1_orders_2(sK2,sK4,k1_yellow_0(sK2,sK1(sK2,sK0(sK2,sK3,sK4),sK3)))
    | r3_orders_2(sK2,sK4,k1_yellow_0(sK2,sK1(sK2,sK0(sK2,sK3,sK4),sK3)))
    | ~ m1_subset_1(k1_yellow_0(sK2,sK1(sK2,sK0(sK2,sK3,sK4),sK3)),u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_5263])).

cnf(c_14,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,X3)
    | r1_orders_2(X0,X1,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v4_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1259,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X1,X2)
    | r1_orders_2(sK2,X0,X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ l1_orders_2(sK2) ),
    inference(resolution,[status(thm)],[c_14,c_40])).

cnf(c_1261,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r1_orders_2(sK2,X0,X2)
    | ~ r1_orders_2(sK2,X1,X2)
    | ~ r1_orders_2(sK2,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1259,c_34])).

cnf(c_1262,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X1,X2)
    | r1_orders_2(sK2,X0,X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_1261])).

cnf(c_4253,plain,
    ( ~ r1_orders_2(sK2,X0_58,X1_58)
    | ~ r1_orders_2(sK2,X1_58,X2_58)
    | r1_orders_2(sK2,X0_58,X2_58)
    | ~ m1_subset_1(X1_58,u1_struct_0(sK2))
    | ~ m1_subset_1(X0_58,u1_struct_0(sK2))
    | ~ m1_subset_1(X2_58,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_1262])).

cnf(c_4651,plain,
    ( ~ r1_orders_2(sK2,k1_yellow_0(sK2,sK0(sK2,sK3,sK4)),X0_58)
    | r1_orders_2(sK2,sK4,X0_58)
    | ~ r1_orders_2(sK2,sK4,k1_yellow_0(sK2,sK0(sK2,sK3,sK4)))
    | ~ m1_subset_1(X0_58,u1_struct_0(sK2))
    | ~ m1_subset_1(k1_yellow_0(sK2,sK0(sK2,sK3,sK4)),u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_4253])).

cnf(c_4922,plain,
    ( ~ r1_orders_2(sK2,k1_yellow_0(sK2,sK0(sK2,sK3,sK4)),k1_yellow_0(sK2,sK1(sK2,sK0(sK2,sK3,sK4),X0_58)))
    | r1_orders_2(sK2,sK4,k1_yellow_0(sK2,sK1(sK2,sK0(sK2,sK3,sK4),X0_58)))
    | ~ r1_orders_2(sK2,sK4,k1_yellow_0(sK2,sK0(sK2,sK3,sK4)))
    | ~ m1_subset_1(k1_yellow_0(sK2,sK1(sK2,sK0(sK2,sK3,sK4),X0_58)),u1_struct_0(sK2))
    | ~ m1_subset_1(k1_yellow_0(sK2,sK0(sK2,sK3,sK4)),u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_4651])).

cnf(c_4924,plain,
    ( ~ r1_orders_2(sK2,k1_yellow_0(sK2,sK0(sK2,sK3,sK4)),k1_yellow_0(sK2,sK1(sK2,sK0(sK2,sK3,sK4),sK3)))
    | r1_orders_2(sK2,sK4,k1_yellow_0(sK2,sK1(sK2,sK0(sK2,sK3,sK4),sK3)))
    | ~ r1_orders_2(sK2,sK4,k1_yellow_0(sK2,sK0(sK2,sK3,sK4)))
    | ~ m1_subset_1(k1_yellow_0(sK2,sK1(sK2,sK0(sK2,sK3,sK4),sK3)),u1_struct_0(sK2))
    | ~ m1_subset_1(k1_yellow_0(sK2,sK0(sK2,sK3,sK4)),u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_4922])).

cnf(c_4,plain,
    ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1357,plain,
    ( m1_subset_1(k1_yellow_0(sK2,X0),u1_struct_0(sK2)) ),
    inference(resolution,[status(thm)],[c_4,c_34])).

cnf(c_4250,plain,
    ( m1_subset_1(k1_yellow_0(sK2,X0_58),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_1357])).

cnf(c_4749,plain,
    ( m1_subset_1(k1_yellow_0(sK2,sK1(sK2,sK0(sK2,sK3,sK4),X0_58)),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_4250])).

cnf(c_4751,plain,
    ( m1_subset_1(k1_yellow_0(sK2,sK1(sK2,sK0(sK2,sK3,sK4),sK3)),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_4749])).

cnf(c_6,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_830,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v3_orders_2(X0) ),
    inference(resolution,[status(thm)],[c_6,c_3])).

cnf(c_1324,plain,
    ( r1_orders_2(sK2,X0,X1)
    | ~ r3_orders_2(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ v2_lattice3(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(resolution,[status(thm)],[c_830,c_41])).

cnf(c_1328,plain,
    ( r1_orders_2(sK2,X0,X1)
    | ~ r3_orders_2(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1324,c_36,c_34])).

cnf(c_4251,plain,
    ( r1_orders_2(sK2,X0_58,X1_58)
    | ~ r3_orders_2(sK2,X0_58,X1_58)
    | ~ m1_subset_1(X1_58,u1_struct_0(sK2))
    | ~ m1_subset_1(X0_58,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_1328])).

cnf(c_4669,plain,
    ( r1_orders_2(sK2,k1_yellow_0(sK2,sK0(sK2,sK3,sK4)),k1_yellow_0(sK2,sK1(sK2,sK0(sK2,sK3,sK4),X0_58)))
    | ~ r3_orders_2(sK2,k1_yellow_0(sK2,sK0(sK2,sK3,sK4)),k1_yellow_0(sK2,sK1(sK2,sK0(sK2,sK3,sK4),X0_58)))
    | ~ m1_subset_1(k1_yellow_0(sK2,sK1(sK2,sK0(sK2,sK3,sK4),X0_58)),u1_struct_0(sK2))
    | ~ m1_subset_1(k1_yellow_0(sK2,sK0(sK2,sK3,sK4)),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_4251])).

cnf(c_4671,plain,
    ( r1_orders_2(sK2,k1_yellow_0(sK2,sK0(sK2,sK3,sK4)),k1_yellow_0(sK2,sK1(sK2,sK0(sK2,sK3,sK4),sK3)))
    | ~ r3_orders_2(sK2,k1_yellow_0(sK2,sK0(sK2,sK3,sK4)),k1_yellow_0(sK2,sK1(sK2,sK0(sK2,sK3,sK4),sK3)))
    | ~ m1_subset_1(k1_yellow_0(sK2,sK1(sK2,sK0(sK2,sK3,sK4),sK3)),u1_struct_0(sK2))
    | ~ m1_subset_1(k1_yellow_0(sK2,sK0(sK2,sK3,sK4)),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_4669])).

cnf(c_23,plain,
    ( r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_lattice3(X0)
    | ~ v5_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v3_orders_2(X0)
    | ~ v3_lattice3(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_35,negated_conjecture,
    ( v3_lattice3(sK2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_420,plain,
    ( r3_orders_2(sK2,k1_yellow_0(sK2,X0),k1_yellow_0(sK2,X1))
    | ~ r1_tarski(X0,X1)
    | ~ v1_lattice3(sK2)
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v2_lattice3(sK2)
    | ~ l1_orders_2(sK2)
    | ~ v3_orders_2(sK2) ),
    inference(resolution,[status(thm)],[c_23,c_35])).

cnf(c_39,negated_conjecture,
    ( v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_37,negated_conjecture,
    ( v1_lattice3(sK2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_424,plain,
    ( r3_orders_2(sK2,k1_yellow_0(sK2,X0),k1_yellow_0(sK2,X1))
    | ~ r1_tarski(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_420,c_41,c_40,c_39,c_37,c_36,c_34])).

cnf(c_4269,plain,
    ( r3_orders_2(sK2,k1_yellow_0(sK2,X0_58),k1_yellow_0(sK2,X1_58))
    | ~ r1_tarski(X0_58,X1_58) ),
    inference(subtyping,[status(esa)],[c_424])).

cnf(c_4600,plain,
    ( r3_orders_2(sK2,k1_yellow_0(sK2,sK0(sK2,sK3,sK4)),k1_yellow_0(sK2,sK1(sK2,sK0(sK2,sK3,sK4),X0_58)))
    | ~ r1_tarski(sK0(sK2,sK3,sK4),sK1(sK2,sK0(sK2,sK3,sK4),X0_58)) ),
    inference(instantiation,[status(thm)],[c_4269])).

cnf(c_4602,plain,
    ( r3_orders_2(sK2,k1_yellow_0(sK2,sK0(sK2,sK3,sK4)),k1_yellow_0(sK2,sK1(sK2,sK0(sK2,sK3,sK4),sK3)))
    | ~ r1_tarski(sK0(sK2,sK3,sK4),sK1(sK2,sK0(sK2,sK3,sK4),sK3)) ),
    inference(instantiation,[status(thm)],[c_4600])).

cnf(c_4592,plain,
    ( m1_subset_1(k1_yellow_0(sK2,sK0(sK2,sK3,sK4)),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_4250])).

cnf(c_18,plain,
    ( ~ v1_waybel_0(X0,X1)
    | ~ v12_waybel_0(X0,X1)
    | r2_hidden(X2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(sK1(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_1(X1)
    | ~ v1_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | v1_xboole_0(X0)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_995,plain,
    ( ~ v1_waybel_0(X0,sK2)
    | ~ v12_waybel_0(X0,sK2)
    | r2_hidden(X1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(sK1(sK2,X0,X1),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_waybel_1(sK2)
    | ~ v1_lattice3(sK2)
    | ~ v4_orders_2(sK2)
    | v1_xboole_0(X0)
    | ~ v2_lattice3(sK2)
    | ~ l1_orders_2(sK2)
    | ~ v3_orders_2(sK2) ),
    inference(resolution,[status(thm)],[c_18,c_39])).

cnf(c_38,negated_conjecture,
    ( v2_waybel_1(sK2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_999,plain,
    ( v1_xboole_0(X0)
    | ~ v1_waybel_0(X0,sK2)
    | ~ v12_waybel_0(X0,sK2)
    | r2_hidden(X1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(sK1(sK2,X0,X1),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_995,c_41,c_40,c_38,c_37,c_36,c_34])).

cnf(c_1000,plain,
    ( ~ v1_waybel_0(X0,sK2)
    | ~ v12_waybel_0(X0,sK2)
    | r2_hidden(X1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(sK1(sK2,X0,X1),k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_999])).

cnf(c_19,plain,
    ( ~ v1_waybel_0(X0,X1)
    | ~ v12_waybel_0(X0,X1)
    | v12_waybel_0(sK1(X1,X0,X2),X1)
    | r2_hidden(X2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_waybel_1(X1)
    | ~ v1_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | v1_xboole_0(X0)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_963,plain,
    ( ~ v1_waybel_0(X0,sK2)
    | ~ v12_waybel_0(X0,sK2)
    | v12_waybel_0(sK1(sK2,X0,X1),sK2)
    | r2_hidden(X1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ v2_waybel_1(sK2)
    | ~ v1_lattice3(sK2)
    | ~ v4_orders_2(sK2)
    | v1_xboole_0(X0)
    | ~ v2_lattice3(sK2)
    | ~ l1_orders_2(sK2)
    | ~ v3_orders_2(sK2) ),
    inference(resolution,[status(thm)],[c_19,c_39])).

cnf(c_967,plain,
    ( v1_xboole_0(X0)
    | ~ v1_waybel_0(X0,sK2)
    | ~ v12_waybel_0(X0,sK2)
    | v12_waybel_0(sK1(sK2,X0,X1),sK2)
    | r2_hidden(X1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_963,c_41,c_40,c_38,c_37,c_36,c_34])).

cnf(c_968,plain,
    ( ~ v1_waybel_0(X0,sK2)
    | ~ v12_waybel_0(X0,sK2)
    | v12_waybel_0(sK1(sK2,X0,X1),sK2)
    | r2_hidden(X1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_967])).

cnf(c_20,plain,
    ( ~ v1_waybel_0(X0,X1)
    | v1_waybel_0(sK1(X1,X0,X2),X1)
    | ~ v12_waybel_0(X0,X1)
    | r2_hidden(X2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_waybel_1(X1)
    | ~ v1_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | v1_xboole_0(X0)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_931,plain,
    ( ~ v1_waybel_0(X0,sK2)
    | v1_waybel_0(sK1(sK2,X0,X1),sK2)
    | ~ v12_waybel_0(X0,sK2)
    | r2_hidden(X1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ v2_waybel_1(sK2)
    | ~ v1_lattice3(sK2)
    | ~ v4_orders_2(sK2)
    | v1_xboole_0(X0)
    | ~ v2_lattice3(sK2)
    | ~ l1_orders_2(sK2)
    | ~ v3_orders_2(sK2) ),
    inference(resolution,[status(thm)],[c_20,c_39])).

cnf(c_935,plain,
    ( v1_xboole_0(X0)
    | ~ v1_waybel_0(X0,sK2)
    | v1_waybel_0(sK1(sK2,X0,X1),sK2)
    | ~ v12_waybel_0(X0,sK2)
    | r2_hidden(X1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_931,c_41,c_40,c_38,c_37,c_36,c_34])).

cnf(c_936,plain,
    ( ~ v1_waybel_0(X0,sK2)
    | v1_waybel_0(sK1(sK2,X0,X1),sK2)
    | ~ v12_waybel_0(X0,sK2)
    | r2_hidden(X1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_935])).

cnf(c_21,plain,
    ( ~ v1_waybel_0(X0,X1)
    | ~ v12_waybel_0(X0,X1)
    | r2_hidden(X2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_waybel_1(X1)
    | ~ v1_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(sK1(X1,X0,X2))
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_899,plain,
    ( ~ v1_waybel_0(X0,sK2)
    | ~ v12_waybel_0(X0,sK2)
    | r2_hidden(X1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ v2_waybel_1(sK2)
    | ~ v1_lattice3(sK2)
    | ~ v4_orders_2(sK2)
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(sK1(sK2,X0,X1))
    | ~ v2_lattice3(sK2)
    | ~ l1_orders_2(sK2)
    | ~ v3_orders_2(sK2) ),
    inference(resolution,[status(thm)],[c_21,c_39])).

cnf(c_903,plain,
    ( ~ v1_xboole_0(sK1(sK2,X0,X1))
    | v1_xboole_0(X0)
    | ~ v1_waybel_0(X0,sK2)
    | ~ v12_waybel_0(X0,sK2)
    | r2_hidden(X1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_899,c_41,c_40,c_38,c_37,c_36,c_34])).

cnf(c_904,plain,
    ( ~ v1_waybel_0(X0,sK2)
    | ~ v12_waybel_0(X0,sK2)
    | r2_hidden(X1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(sK1(sK2,X0,X1)) ),
    inference(renaming,[status(thm)],[c_903])).

cnf(c_17,plain,
    ( v1_waybel_7(sK1(X0,X1,X2),X0)
    | ~ v1_waybel_0(X1,X0)
    | ~ v12_waybel_0(X1,X0)
    | r2_hidden(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_waybel_1(X0)
    | ~ v1_lattice3(X0)
    | ~ v5_orders_2(X0)
    | ~ v4_orders_2(X0)
    | v1_xboole_0(X1)
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v3_orders_2(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_31,negated_conjecture,
    ( r1_waybel_3(sK2,sK3,sK4)
    | ~ r3_orders_2(sK2,sK4,k1_yellow_0(sK2,X0))
    | ~ v1_waybel_7(X0,sK2)
    | ~ v1_waybel_0(X0,sK2)
    | ~ v12_waybel_0(X0,sK2)
    | r2_hidden(sK3,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_566,plain,
    ( r1_waybel_3(sK2,sK3,sK4)
    | ~ r3_orders_2(sK2,sK4,k1_yellow_0(sK2,sK1(sK2,X0,X1)))
    | ~ v1_waybel_0(X0,sK2)
    | ~ v1_waybel_0(sK1(sK2,X0,X1),sK2)
    | ~ v12_waybel_0(X0,sK2)
    | ~ v12_waybel_0(sK1(sK2,X0,X1),sK2)
    | r2_hidden(X1,X0)
    | r2_hidden(sK3,sK1(sK2,X0,X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(sK1(sK2,X0,X1),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_waybel_1(sK2)
    | ~ v1_lattice3(sK2)
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | v1_xboole_0(X0)
    | v1_xboole_0(sK1(sK2,X0,X1))
    | ~ v2_lattice3(sK2)
    | ~ l1_orders_2(sK2)
    | ~ v3_orders_2(sK2) ),
    inference(resolution,[status(thm)],[c_17,c_31])).

cnf(c_570,plain,
    ( v1_xboole_0(sK1(sK2,X0,X1))
    | v1_xboole_0(X0)
    | ~ m1_subset_1(sK1(sK2,X0,X1),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(sK3,sK1(sK2,X0,X1))
    | r2_hidden(X1,X0)
    | ~ v12_waybel_0(sK1(sK2,X0,X1),sK2)
    | ~ v12_waybel_0(X0,sK2)
    | ~ v1_waybel_0(sK1(sK2,X0,X1),sK2)
    | ~ v1_waybel_0(X0,sK2)
    | ~ r3_orders_2(sK2,sK4,k1_yellow_0(sK2,sK1(sK2,X0,X1)))
    | r1_waybel_3(sK2,sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_566,c_41,c_40,c_39,c_38,c_37,c_36,c_34])).

cnf(c_571,plain,
    ( r1_waybel_3(sK2,sK3,sK4)
    | ~ r3_orders_2(sK2,sK4,k1_yellow_0(sK2,sK1(sK2,X0,X1)))
    | ~ v1_waybel_0(X0,sK2)
    | ~ v1_waybel_0(sK1(sK2,X0,X1),sK2)
    | ~ v12_waybel_0(X0,sK2)
    | ~ v12_waybel_0(sK1(sK2,X0,X1),sK2)
    | r2_hidden(X1,X0)
    | r2_hidden(sK3,sK1(sK2,X0,X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(sK1(sK2,X0,X1),k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(X0)
    | v1_xboole_0(sK1(sK2,X0,X1)) ),
    inference(renaming,[status(thm)],[c_570])).

cnf(c_1098,plain,
    ( r1_waybel_3(sK2,sK3,sK4)
    | ~ r3_orders_2(sK2,sK4,k1_yellow_0(sK2,sK1(sK2,X0,X1)))
    | ~ v1_waybel_0(X0,sK2)
    | ~ v1_waybel_0(sK1(sK2,X0,X1),sK2)
    | ~ v12_waybel_0(X0,sK2)
    | ~ v12_waybel_0(sK1(sK2,X0,X1),sK2)
    | r2_hidden(X1,X0)
    | r2_hidden(sK3,sK1(sK2,X0,X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(sK1(sK2,X0,X1),k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_904,c_571])).

cnf(c_1105,plain,
    ( r1_waybel_3(sK2,sK3,sK4)
    | ~ r3_orders_2(sK2,sK4,k1_yellow_0(sK2,sK1(sK2,X0,X1)))
    | ~ v1_waybel_0(X0,sK2)
    | ~ v12_waybel_0(X0,sK2)
    | ~ v12_waybel_0(sK1(sK2,X0,X1),sK2)
    | r2_hidden(X1,X0)
    | r2_hidden(sK3,sK1(sK2,X0,X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(sK1(sK2,X0,X1),k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_936,c_1098])).

cnf(c_1118,plain,
    ( r1_waybel_3(sK2,sK3,sK4)
    | ~ r3_orders_2(sK2,sK4,k1_yellow_0(sK2,sK1(sK2,X0,X1)))
    | ~ v1_waybel_0(X0,sK2)
    | ~ v12_waybel_0(X0,sK2)
    | r2_hidden(X1,X0)
    | r2_hidden(sK3,sK1(sK2,X0,X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(sK1(sK2,X0,X1),k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_968,c_1105])).

cnf(c_1133,plain,
    ( r1_waybel_3(sK2,sK3,sK4)
    | ~ r3_orders_2(sK2,sK4,k1_yellow_0(sK2,sK1(sK2,X0,X1)))
    | ~ v1_waybel_0(X0,sK2)
    | ~ v12_waybel_0(X0,sK2)
    | r2_hidden(X1,X0)
    | r2_hidden(sK3,sK1(sK2,X0,X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | v1_xboole_0(X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1000,c_1118])).

cnf(c_4255,plain,
    ( r1_waybel_3(sK2,sK3,sK4)
    | ~ r3_orders_2(sK2,sK4,k1_yellow_0(sK2,sK1(sK2,X0_58,X1_58)))
    | ~ v1_waybel_0(X0_58,sK2)
    | ~ v12_waybel_0(X0_58,sK2)
    | r2_hidden(X1_58,X0_58)
    | r2_hidden(sK3,sK1(sK2,X0_58,X1_58))
    | ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1_58,u1_struct_0(sK2))
    | v1_xboole_0(X0_58) ),
    inference(subtyping,[status(esa)],[c_1133])).

cnf(c_4540,plain,
    ( r1_waybel_3(sK2,sK3,sK4)
    | ~ r3_orders_2(sK2,sK4,k1_yellow_0(sK2,sK1(sK2,sK0(sK2,sK3,sK4),X0_58)))
    | ~ v1_waybel_0(sK0(sK2,sK3,sK4),sK2)
    | ~ v12_waybel_0(sK0(sK2,sK3,sK4),sK2)
    | r2_hidden(X0_58,sK0(sK2,sK3,sK4))
    | r2_hidden(sK3,sK1(sK2,sK0(sK2,sK3,sK4),X0_58))
    | ~ m1_subset_1(X0_58,u1_struct_0(sK2))
    | ~ m1_subset_1(sK0(sK2,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(sK0(sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_4255])).

cnf(c_4572,plain,
    ( r1_waybel_3(sK2,sK3,sK4)
    | ~ r3_orders_2(sK2,sK4,k1_yellow_0(sK2,sK1(sK2,sK0(sK2,sK3,sK4),sK3)))
    | ~ v1_waybel_0(sK0(sK2,sK3,sK4),sK2)
    | ~ v12_waybel_0(sK0(sK2,sK3,sK4),sK2)
    | r2_hidden(sK3,sK1(sK2,sK0(sK2,sK3,sK4),sK3))
    | r2_hidden(sK3,sK0(sK2,sK3,sK4))
    | ~ m1_subset_1(sK0(sK2,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | v1_xboole_0(sK0(sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_4540])).

cnf(c_16,plain,
    ( r1_tarski(X0,sK1(X1,X0,X2))
    | ~ v1_waybel_0(X0,X1)
    | ~ v12_waybel_0(X0,X1)
    | r2_hidden(X2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_waybel_1(X1)
    | ~ v1_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | v1_xboole_0(X0)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1027,plain,
    ( r1_tarski(X0,sK1(sK2,X0,X1))
    | ~ v1_waybel_0(X0,sK2)
    | ~ v12_waybel_0(X0,sK2)
    | r2_hidden(X1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ v2_waybel_1(sK2)
    | ~ v1_lattice3(sK2)
    | ~ v4_orders_2(sK2)
    | v1_xboole_0(X0)
    | ~ v2_lattice3(sK2)
    | ~ l1_orders_2(sK2)
    | ~ v3_orders_2(sK2) ),
    inference(resolution,[status(thm)],[c_16,c_39])).

cnf(c_1031,plain,
    ( v1_xboole_0(X0)
    | r1_tarski(X0,sK1(sK2,X0,X1))
    | ~ v1_waybel_0(X0,sK2)
    | ~ v12_waybel_0(X0,sK2)
    | r2_hidden(X1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1027,c_41,c_40,c_38,c_37,c_36,c_34])).

cnf(c_1032,plain,
    ( r1_tarski(X0,sK1(sK2,X0,X1))
    | ~ v1_waybel_0(X0,sK2)
    | ~ v12_waybel_0(X0,sK2)
    | r2_hidden(X1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_1031])).

cnf(c_4257,plain,
    ( r1_tarski(X0_58,sK1(sK2,X0_58,X1_58))
    | ~ v1_waybel_0(X0_58,sK2)
    | ~ v12_waybel_0(X0_58,sK2)
    | r2_hidden(X1_58,X0_58)
    | ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1_58,u1_struct_0(sK2))
    | v1_xboole_0(X0_58) ),
    inference(subtyping,[status(esa)],[c_1032])).

cnf(c_4541,plain,
    ( r1_tarski(sK0(sK2,sK3,sK4),sK1(sK2,sK0(sK2,sK3,sK4),X0_58))
    | ~ v1_waybel_0(sK0(sK2,sK3,sK4),sK2)
    | ~ v12_waybel_0(sK0(sK2,sK3,sK4),sK2)
    | r2_hidden(X0_58,sK0(sK2,sK3,sK4))
    | ~ m1_subset_1(X0_58,u1_struct_0(sK2))
    | ~ m1_subset_1(sK0(sK2,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(sK0(sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_4257])).

cnf(c_4568,plain,
    ( r1_tarski(sK0(sK2,sK3,sK4),sK1(sK2,sK0(sK2,sK3,sK4),sK3))
    | ~ v1_waybel_0(sK0(sK2,sK3,sK4),sK2)
    | ~ v12_waybel_0(sK0(sK2,sK3,sK4),sK2)
    | r2_hidden(sK3,sK0(sK2,sK3,sK4))
    | ~ m1_subset_1(sK0(sK2,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | v1_xboole_0(sK0(sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_4541])).

cnf(c_15,plain,
    ( ~ v1_waybel_0(X0,X1)
    | ~ v12_waybel_0(X0,X1)
    | r2_hidden(X2,X0)
    | ~ r2_hidden(X2,sK1(X1,X0,X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_waybel_1(X1)
    | ~ v1_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | v1_xboole_0(X0)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1059,plain,
    ( ~ v1_waybel_0(X0,sK2)
    | ~ v12_waybel_0(X0,sK2)
    | r2_hidden(X1,X0)
    | ~ r2_hidden(X1,sK1(sK2,X0,X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ v2_waybel_1(sK2)
    | ~ v1_lattice3(sK2)
    | ~ v4_orders_2(sK2)
    | v1_xboole_0(X0)
    | ~ v2_lattice3(sK2)
    | ~ l1_orders_2(sK2)
    | ~ v3_orders_2(sK2) ),
    inference(resolution,[status(thm)],[c_15,c_39])).

cnf(c_1063,plain,
    ( v1_xboole_0(X0)
    | ~ v1_waybel_0(X0,sK2)
    | ~ v12_waybel_0(X0,sK2)
    | r2_hidden(X1,X0)
    | ~ r2_hidden(X1,sK1(sK2,X0,X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1059,c_41,c_40,c_38,c_37,c_36,c_34])).

cnf(c_1064,plain,
    ( ~ v1_waybel_0(X0,sK2)
    | ~ v12_waybel_0(X0,sK2)
    | r2_hidden(X1,X0)
    | ~ r2_hidden(X1,sK1(sK2,X0,X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_1063])).

cnf(c_4256,plain,
    ( ~ v1_waybel_0(X0_58,sK2)
    | ~ v12_waybel_0(X0_58,sK2)
    | r2_hidden(X1_58,X0_58)
    | ~ r2_hidden(X1_58,sK1(sK2,X0_58,X1_58))
    | ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1_58,u1_struct_0(sK2))
    | v1_xboole_0(X0_58) ),
    inference(subtyping,[status(esa)],[c_1064])).

cnf(c_4542,plain,
    ( ~ v1_waybel_0(sK0(sK2,sK3,sK4),sK2)
    | ~ v12_waybel_0(sK0(sK2,sK3,sK4),sK2)
    | ~ r2_hidden(X0_58,sK1(sK2,sK0(sK2,sK3,sK4),X0_58))
    | r2_hidden(X0_58,sK0(sK2,sK3,sK4))
    | ~ m1_subset_1(X0_58,u1_struct_0(sK2))
    | ~ m1_subset_1(sK0(sK2,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(sK0(sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_4256])).

cnf(c_4564,plain,
    ( ~ v1_waybel_0(sK0(sK2,sK3,sK4),sK2)
    | ~ v12_waybel_0(sK0(sK2,sK3,sK4),sK2)
    | ~ r2_hidden(sK3,sK1(sK2,sK0(sK2,sK3,sK4),sK3))
    | r2_hidden(sK3,sK0(sK2,sK3,sK4))
    | ~ m1_subset_1(sK0(sK2,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | v1_xboole_0(sK0(sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_4542])).

cnf(c_4532,plain,
    ( r1_orders_2(sK2,sK4,k1_yellow_0(sK2,sK0(sK2,sK3,sK4)))
    | ~ r3_orders_2(sK2,sK4,k1_yellow_0(sK2,sK0(sK2,sK3,sK4)))
    | ~ m1_subset_1(k1_yellow_0(sK2,sK0(sK2,sK3,sK4)),u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_4251])).

cnf(c_9,plain,
    ( r1_waybel_3(X0,X1,X2)
    | r3_orders_2(X0,X2,k1_yellow_0(X0,sK0(X0,X1,X2)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v24_waybel_0(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_0,plain,
    ( ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v3_lattice3(X0)
    | v24_waybel_0(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_454,plain,
    ( ~ l1_orders_2(sK2)
    | v2_struct_0(sK2)
    | ~ v3_orders_2(sK2)
    | v24_waybel_0(sK2) ),
    inference(resolution,[status(thm)],[c_0,c_35])).

cnf(c_121,plain,
    ( ~ v2_lattice3(sK2)
    | ~ l1_orders_2(sK2)
    | ~ v2_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_126,plain,
    ( ~ l1_orders_2(sK2)
    | v2_struct_0(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v3_lattice3(sK2)
    | v24_waybel_0(sK2) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_456,plain,
    ( v24_waybel_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_454,c_41,c_36,c_35,c_34,c_121,c_126])).

cnf(c_710,plain,
    ( r1_waybel_3(sK2,X0,X1)
    | r3_orders_2(sK2,X1,k1_yellow_0(sK2,sK0(sK2,X0,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2)
    | ~ v3_orders_2(sK2) ),
    inference(resolution,[status(thm)],[c_9,c_456])).

cnf(c_714,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r3_orders_2(sK2,X1,k1_yellow_0(sK2,sK0(sK2,X0,X1)))
    | r1_waybel_3(sK2,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_710,c_41,c_40,c_39,c_36,c_34,c_121])).

cnf(c_715,plain,
    ( r1_waybel_3(sK2,X0,X1)
    | r3_orders_2(sK2,X1,k1_yellow_0(sK2,sK0(sK2,X0,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_714])).

cnf(c_4263,plain,
    ( r1_waybel_3(sK2,X0_58,X1_58)
    | r3_orders_2(sK2,X1_58,k1_yellow_0(sK2,sK0(sK2,X0_58,X1_58)))
    | ~ m1_subset_1(X1_58,u1_struct_0(sK2))
    | ~ m1_subset_1(X0_58,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_715])).

cnf(c_4514,plain,
    ( r1_waybel_3(sK2,sK3,sK4)
    | r3_orders_2(sK2,sK4,k1_yellow_0(sK2,sK0(sK2,sK3,sK4)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_4263])).

cnf(c_8,plain,
    ( r1_waybel_3(X0,X1,X2)
    | ~ r2_hidden(X1,sK0(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v24_waybel_0(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_733,plain,
    ( r1_waybel_3(sK2,X0,X1)
    | ~ r2_hidden(X0,sK0(sK2,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2)
    | ~ v3_orders_2(sK2) ),
    inference(resolution,[status(thm)],[c_8,c_456])).

cnf(c_737,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ r2_hidden(X0,sK0(sK2,X0,X1))
    | r1_waybel_3(sK2,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_733,c_41,c_40,c_39,c_36,c_34,c_121])).

cnf(c_738,plain,
    ( r1_waybel_3(sK2,X0,X1)
    | ~ r2_hidden(X0,sK0(sK2,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_737])).

cnf(c_4262,plain,
    ( r1_waybel_3(sK2,X0_58,X1_58)
    | ~ r2_hidden(X0_58,sK0(sK2,X0_58,X1_58))
    | ~ m1_subset_1(X1_58,u1_struct_0(sK2))
    | ~ m1_subset_1(X0_58,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_738])).

cnf(c_4515,plain,
    ( r1_waybel_3(sK2,sK3,sK4)
    | ~ r2_hidden(sK3,sK0(sK2,sK3,sK4))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_4262])).

cnf(c_13,plain,
    ( r1_waybel_3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v1_xboole_0(sK0(X0,X1,X2))
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v24_waybel_0(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_618,plain,
    ( r1_waybel_3(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v1_xboole_0(sK0(sK2,X0,X1))
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2)
    | ~ v3_orders_2(sK2) ),
    inference(resolution,[status(thm)],[c_13,c_456])).

cnf(c_622,plain,
    ( ~ v1_xboole_0(sK0(sK2,X0,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r1_waybel_3(sK2,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_618,c_41,c_40,c_39,c_36,c_34,c_121])).

cnf(c_623,plain,
    ( r1_waybel_3(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ v1_xboole_0(sK0(sK2,X0,X1)) ),
    inference(renaming,[status(thm)],[c_622])).

cnf(c_4267,plain,
    ( r1_waybel_3(sK2,X0_58,X1_58)
    | ~ m1_subset_1(X1_58,u1_struct_0(sK2))
    | ~ m1_subset_1(X0_58,u1_struct_0(sK2))
    | ~ v1_xboole_0(sK0(sK2,X0_58,X1_58)) ),
    inference(subtyping,[status(esa)],[c_623])).

cnf(c_4516,plain,
    ( r1_waybel_3(sK2,sK3,sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ v1_xboole_0(sK0(sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_4267])).

cnf(c_12,plain,
    ( r1_waybel_3(X0,X1,X2)
    | v1_waybel_0(sK0(X0,X1,X2),X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v24_waybel_0(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_641,plain,
    ( r1_waybel_3(sK2,X0,X1)
    | v1_waybel_0(sK0(sK2,X0,X1),sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2)
    | ~ v3_orders_2(sK2) ),
    inference(resolution,[status(thm)],[c_12,c_456])).

cnf(c_645,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | v1_waybel_0(sK0(sK2,X0,X1),sK2)
    | r1_waybel_3(sK2,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_641,c_41,c_40,c_39,c_36,c_34,c_121])).

cnf(c_646,plain,
    ( r1_waybel_3(sK2,X0,X1)
    | v1_waybel_0(sK0(sK2,X0,X1),sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_645])).

cnf(c_4266,plain,
    ( r1_waybel_3(sK2,X0_58,X1_58)
    | v1_waybel_0(sK0(sK2,X0_58,X1_58),sK2)
    | ~ m1_subset_1(X1_58,u1_struct_0(sK2))
    | ~ m1_subset_1(X0_58,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_646])).

cnf(c_4517,plain,
    ( r1_waybel_3(sK2,sK3,sK4)
    | v1_waybel_0(sK0(sK2,sK3,sK4),sK2)
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_4266])).

cnf(c_11,plain,
    ( r1_waybel_3(X0,X1,X2)
    | v12_waybel_0(sK0(X0,X1,X2),X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v24_waybel_0(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_664,plain,
    ( r1_waybel_3(sK2,X0,X1)
    | v12_waybel_0(sK0(sK2,X0,X1),sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2)
    | ~ v3_orders_2(sK2) ),
    inference(resolution,[status(thm)],[c_11,c_456])).

cnf(c_668,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | v12_waybel_0(sK0(sK2,X0,X1),sK2)
    | r1_waybel_3(sK2,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_664,c_41,c_40,c_39,c_36,c_34,c_121])).

cnf(c_669,plain,
    ( r1_waybel_3(sK2,X0,X1)
    | v12_waybel_0(sK0(sK2,X0,X1),sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_668])).

cnf(c_4265,plain,
    ( r1_waybel_3(sK2,X0_58,X1_58)
    | v12_waybel_0(sK0(sK2,X0_58,X1_58),sK2)
    | ~ m1_subset_1(X1_58,u1_struct_0(sK2))
    | ~ m1_subset_1(X0_58,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_669])).

cnf(c_4518,plain,
    ( r1_waybel_3(sK2,sK3,sK4)
    | v12_waybel_0(sK0(sK2,sK3,sK4),sK2)
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_4265])).

cnf(c_10,plain,
    ( r1_waybel_3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v5_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v24_waybel_0(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_687,plain,
    ( r1_waybel_3(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | m1_subset_1(sK0(sK2,X0,X1),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2)
    | ~ v3_orders_2(sK2) ),
    inference(resolution,[status(thm)],[c_10,c_456])).

cnf(c_691,plain,
    ( m1_subset_1(sK0(sK2,X0,X1),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r1_waybel_3(sK2,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_687,c_41,c_40,c_39,c_36,c_34,c_121])).

cnf(c_692,plain,
    ( r1_waybel_3(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | m1_subset_1(sK0(sK2,X0,X1),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(renaming,[status(thm)],[c_691])).

cnf(c_4264,plain,
    ( r1_waybel_3(sK2,X0_58,X1_58)
    | ~ m1_subset_1(X1_58,u1_struct_0(sK2))
    | ~ m1_subset_1(X0_58,u1_struct_0(sK2))
    | m1_subset_1(sK0(sK2,X0_58,X1_58),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subtyping,[status(esa)],[c_692])).

cnf(c_4519,plain,
    ( r1_waybel_3(sK2,sK3,sK4)
    | m1_subset_1(sK0(sK2,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_4264])).

cnf(c_24,negated_conjecture,
    ( ~ r1_waybel_3(sK2,sK3,sK4)
    | ~ r2_hidden(sK3,sK5) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_2477,plain,
    ( r3_orders_2(sK2,sK4,k1_yellow_0(sK2,sK0(sK2,sK3,sK4)))
    | ~ r2_hidden(sK3,sK5)
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(resolution,[status(thm)],[c_24,c_715])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2479,plain,
    ( r3_orders_2(sK2,sK4,k1_yellow_0(sK2,sK0(sK2,sK3,sK4)))
    | ~ r2_hidden(sK3,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2477,c_33,c_32])).

cnf(c_25,negated_conjecture,
    ( ~ r1_waybel_3(sK2,sK3,sK4)
    | r3_orders_2(sK2,sK4,k1_yellow_0(sK2,sK5)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_2399,plain,
    ( r3_orders_2(sK2,sK4,k1_yellow_0(sK2,sK0(sK2,sK3,sK4)))
    | r3_orders_2(sK2,sK4,k1_yellow_0(sK2,sK5))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(resolution,[status(thm)],[c_25,c_715])).

cnf(c_2401,plain,
    ( r3_orders_2(sK2,sK4,k1_yellow_0(sK2,sK0(sK2,sK3,sK4)))
    | r3_orders_2(sK2,sK4,k1_yellow_0(sK2,sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2399,c_33,c_32])).

cnf(c_26,negated_conjecture,
    ( ~ r1_waybel_3(sK2,sK3,sK4)
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2321,plain,
    ( r3_orders_2(sK2,sK4,k1_yellow_0(sK2,sK0(sK2,sK3,sK4)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(resolution,[status(thm)],[c_26,c_715])).

cnf(c_2323,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | r3_orders_2(sK2,sK4,k1_yellow_0(sK2,sK0(sK2,sK3,sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2321,c_33,c_32])).

cnf(c_2324,plain,
    ( r3_orders_2(sK2,sK4,k1_yellow_0(sK2,sK0(sK2,sK3,sK4)))
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(renaming,[status(thm)],[c_2323])).

cnf(c_28,negated_conjecture,
    ( ~ r1_waybel_3(sK2,sK3,sK4)
    | v12_waybel_0(sK5,sK2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2243,plain,
    ( r3_orders_2(sK2,sK4,k1_yellow_0(sK2,sK0(sK2,sK3,sK4)))
    | v12_waybel_0(sK5,sK2)
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(resolution,[status(thm)],[c_28,c_715])).

cnf(c_2245,plain,
    ( r3_orders_2(sK2,sK4,k1_yellow_0(sK2,sK0(sK2,sK3,sK4)))
    | v12_waybel_0(sK5,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2243,c_33,c_32])).

cnf(c_29,negated_conjecture,
    ( ~ r1_waybel_3(sK2,sK3,sK4)
    | v1_waybel_0(sK5,sK2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2165,plain,
    ( r3_orders_2(sK2,sK4,k1_yellow_0(sK2,sK0(sK2,sK3,sK4)))
    | v1_waybel_0(sK5,sK2)
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(resolution,[status(thm)],[c_29,c_715])).

cnf(c_2167,plain,
    ( r3_orders_2(sK2,sK4,k1_yellow_0(sK2,sK0(sK2,sK3,sK4)))
    | v1_waybel_0(sK5,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2165,c_33,c_32])).

cnf(c_30,negated_conjecture,
    ( ~ r1_waybel_3(sK2,sK3,sK4)
    | ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2087,plain,
    ( r3_orders_2(sK2,sK4,k1_yellow_0(sK2,sK0(sK2,sK3,sK4)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ v1_xboole_0(sK5) ),
    inference(resolution,[status(thm)],[c_30,c_715])).

cnf(c_2089,plain,
    ( r3_orders_2(sK2,sK4,k1_yellow_0(sK2,sK0(sK2,sK3,sK4)))
    | ~ v1_xboole_0(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2087,c_33,c_32])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5459,c_5265,c_4924,c_4751,c_4671,c_4602,c_4592,c_4572,c_4568,c_4564,c_4532,c_4514,c_4515,c_4516,c_4517,c_4518,c_4519,c_2479,c_2401,c_2324,c_2245,c_2167,c_2089,c_24,c_25,c_26,c_28,c_29,c_30,c_32,c_33])).


%------------------------------------------------------------------------------
