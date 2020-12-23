%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1970+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:57 EST 2020

% Result     : Theorem 3.87s
% Output     : CNFRefutation 3.87s
% Verified   : 
% Statistics : Number of formulae       :  278 (8895 expanded)
%              Number of clauses        :  189 (2380 expanded)
%              Number of leaves         :   22 (2776 expanded)
%              Depth                    :   28
%              Number of atoms          : 1518 (141447 expanded)
%              Number of equality atoms :  317 (10449 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal clause size      :   46 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f39,plain,(
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
    inference(rectify,[],[f38])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & ~ r2_hidden(X2,X1)
          & r2_hidden(k13_lattice3(X0,X2,X3),X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & ~ r2_hidden(X2,X1)
        & r2_hidden(k13_lattice3(X0,X2,sK1(X0,X1)),X1)
        & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
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
            & ~ r2_hidden(sK0(X0,X1),X1)
            & r2_hidden(k13_lattice3(X0,sK0(X0,X1),X3),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_waybel_7(X1,X0)
              | ( ~ r2_hidden(sK1(X0,X1),X1)
                & ~ r2_hidden(sK0(X0,X1),X1)
                & r2_hidden(k13_lattice3(X0,sK0(X0,X1),sK1(X0,X1)),X1)
                & m1_subset_1(sK1(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f39,f41,f40])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v2_waybel_7(X1,X0)
      | m1_subset_1(sK1(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f13,conjecture,(
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
                  & v2_waybel_7(X2,X0)
                  & v13_waybel_0(X2,X0)
                  & v2_waybel_0(X2,X0)
                  & ~ v1_xboole_0(X2) )
               => ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                  & v2_waybel_7(X2,X1)
                  & v13_waybel_0(X2,X1)
                  & v2_waybel_0(X2,X1)
                  & ~ v1_xboole_0(X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
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
                    & v2_waybel_7(X2,X0)
                    & v13_waybel_0(X2,X0)
                    & v2_waybel_0(X2,X0)
                    & ~ v1_xboole_0(X2) )
                 => ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                    & v2_waybel_7(X2,X1)
                    & v13_waybel_0(X2,X1)
                    & v2_waybel_0(X2,X1)
                    & ~ v1_xboole_0(X2) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                | ~ v2_waybel_7(X2,X1)
                | ~ v13_waybel_0(X2,X1)
                | ~ v2_waybel_0(X2,X1)
                | v1_xboole_0(X2) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              & v2_waybel_7(X2,X0)
              & v13_waybel_0(X2,X0)
              & v2_waybel_0(X2,X0)
              & ~ v1_xboole_0(X2) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1)
          & v2_lattice3(X1)
          & v1_lattice3(X1)
          & v5_orders_2(X1)
          & v4_orders_2(X1)
          & v3_orders_2(X1) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                | ~ v2_waybel_7(X2,X1)
                | ~ v13_waybel_0(X2,X1)
                | ~ v2_waybel_0(X2,X1)
                | v1_xboole_0(X2) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              & v2_waybel_7(X2,X0)
              & v13_waybel_0(X2,X0)
              & v2_waybel_0(X2,X0)
              & ~ v1_xboole_0(X2) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1)
          & v2_lattice3(X1)
          & v1_lattice3(X1)
          & v5_orders_2(X1)
          & v4_orders_2(X1)
          & v3_orders_2(X1) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f36])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
            | ~ v2_waybel_7(X2,X1)
            | ~ v13_waybel_0(X2,X1)
            | ~ v2_waybel_0(X2,X1)
            | v1_xboole_0(X2) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          & v2_waybel_7(X2,X0)
          & v13_waybel_0(X2,X0)
          & v2_waybel_0(X2,X0)
          & ~ v1_xboole_0(X2) )
     => ( ( ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X1)))
          | ~ v2_waybel_7(sK6,X1)
          | ~ v13_waybel_0(sK6,X1)
          | ~ v2_waybel_0(sK6,X1)
          | v1_xboole_0(sK6) )
        & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X0)))
        & v2_waybel_7(sK6,X0)
        & v13_waybel_0(sK6,X0)
        & v2_waybel_0(sK6,X0)
        & ~ v1_xboole_0(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                | ~ v2_waybel_7(X2,X1)
                | ~ v13_waybel_0(X2,X1)
                | ~ v2_waybel_0(X2,X1)
                | v1_xboole_0(X2) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              & v2_waybel_7(X2,X0)
              & v13_waybel_0(X2,X0)
              & v2_waybel_0(X2,X0)
              & ~ v1_xboole_0(X2) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1)
          & v2_lattice3(X1)
          & v1_lattice3(X1)
          & v5_orders_2(X1)
          & v4_orders_2(X1)
          & v3_orders_2(X1) )
     => ( ? [X2] :
            ( ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
              | ~ v2_waybel_7(X2,sK5)
              | ~ v13_waybel_0(X2,sK5)
              | ~ v2_waybel_0(X2,sK5)
              | v1_xboole_0(X2) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
            & v2_waybel_7(X2,X0)
            & v13_waybel_0(X2,X0)
            & v2_waybel_0(X2,X0)
            & ~ v1_xboole_0(X2) )
        & g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) = g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        & l1_orders_2(sK5)
        & v2_lattice3(sK5)
        & v1_lattice3(sK5)
        & v5_orders_2(sK5)
        & v4_orders_2(sK5)
        & v3_orders_2(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                  | ~ v2_waybel_7(X2,X1)
                  | ~ v13_waybel_0(X2,X1)
                  | ~ v2_waybel_0(X2,X1)
                  | v1_xboole_0(X2) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & v2_waybel_7(X2,X0)
                & v13_waybel_0(X2,X0)
                & v2_waybel_0(X2,X0)
                & ~ v1_xboole_0(X2) )
            & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
            & l1_orders_2(X1)
            & v2_lattice3(X1)
            & v1_lattice3(X1)
            & v5_orders_2(X1)
            & v4_orders_2(X1)
            & v3_orders_2(X1) )
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                | ~ v2_waybel_7(X2,X1)
                | ~ v13_waybel_0(X2,X1)
                | ~ v2_waybel_0(X2,X1)
                | v1_xboole_0(X2) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
              & v2_waybel_7(X2,sK4)
              & v13_waybel_0(X2,sK4)
              & v2_waybel_0(X2,sK4)
              & ~ v1_xboole_0(X2) )
          & g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1)
          & v2_lattice3(X1)
          & v1_lattice3(X1)
          & v5_orders_2(X1)
          & v4_orders_2(X1)
          & v3_orders_2(X1) )
      & l1_orders_2(sK4)
      & v2_lattice3(sK4)
      & v1_lattice3(sK4)
      & v5_orders_2(sK4)
      & v4_orders_2(sK4)
      & v3_orders_2(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ( ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
      | ~ v2_waybel_7(sK6,sK5)
      | ~ v13_waybel_0(sK6,sK5)
      | ~ v2_waybel_0(sK6,sK5)
      | v1_xboole_0(sK6) )
    & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
    & v2_waybel_7(sK6,sK4)
    & v13_waybel_0(sK6,sK4)
    & v2_waybel_0(sK6,sK4)
    & ~ v1_xboole_0(sK6)
    & g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4)) = g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5))
    & l1_orders_2(sK5)
    & v2_lattice3(sK5)
    & v1_lattice3(sK5)
    & v5_orders_2(sK5)
    & v4_orders_2(sK5)
    & v3_orders_2(sK5)
    & l1_orders_2(sK4)
    & v2_lattice3(sK4)
    & v1_lattice3(sK4)
    & v5_orders_2(sK4)
    & v4_orders_2(sK4)
    & v3_orders_2(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f37,f50,f49,f48])).

fof(f81,plain,(
    v4_orders_2(sK5) ),
    inference(cnf_transformation,[],[f51])).

fof(f80,plain,(
    v3_orders_2(sK5) ),
    inference(cnf_transformation,[],[f51])).

fof(f82,plain,(
    v5_orders_2(sK5) ),
    inference(cnf_transformation,[],[f51])).

fof(f83,plain,(
    v1_lattice3(sK5) ),
    inference(cnf_transformation,[],[f51])).

fof(f85,plain,(
    l1_orders_2(sK5) ),
    inference(cnf_transformation,[],[f51])).

fof(f87,plain,(
    ~ v1_xboole_0(sK6) ),
    inference(cnf_transformation,[],[f51])).

fof(f92,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ v2_waybel_7(sK6,sK5)
    | ~ v13_waybel_0(sK6,sK5)
    | ~ v2_waybel_0(sK6,sK5)
    | v1_xboole_0(sK6) ),
    inference(cnf_transformation,[],[f51])).

fof(f79,plain,(
    l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f88,plain,(
    v2_waybel_0(sK6,sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f91,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f51])).

fof(f86,plain,(
    g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4)) = g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) ),
    inference(cnf_transformation,[],[f51])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f60,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f23])).

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
                   => ( ( v2_waybel_0(X2,X0)
                        & X2 = X3 )
                     => v2_waybel_0(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v2_waybel_0(X3,X1)
                  | ~ v2_waybel_0(X2,X0)
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
                  ( v2_waybel_0(X3,X1)
                  | ~ v2_waybel_0(X2,X0)
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f34])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_waybel_0(X3,X1)
      | ~ v2_waybel_0(X2,X0)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f95,plain,(
    ! [X0,X3,X1] :
      ( v2_waybel_0(X3,X1)
      | ~ v2_waybel_0(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f73])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v2_waybel_7(X1,X0)
      | m1_subset_1(sK0(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ( v1_lattice3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => r1_yellow_0(X0,k2_tarski(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_lattice3(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( r1_yellow_0(X0,k2_tarski(X1,X2))
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_lattice3(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( r1_yellow_0(X0,k2_tarski(X1,X2))
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f26])).

fof(f43,plain,(
    ! [X0] :
      ( ( ( v1_lattice3(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ~ r1_yellow_0(X0,k2_tarski(X1,X2))
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( r1_yellow_0(X0,k2_tarski(X1,X2))
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v1_lattice3(X0) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f44,plain,(
    ! [X0] :
      ( ( ( v1_lattice3(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ~ r1_yellow_0(X0,k2_tarski(X1,X2))
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( r1_yellow_0(X0,k2_tarski(X3,X4))
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v1_lattice3(X0) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(rectify,[],[f43])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_yellow_0(X0,k2_tarski(X1,X2))
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ~ r1_yellow_0(X0,k2_tarski(X1,sK3(X0)))
        & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_yellow_0(X0,k2_tarski(X1,X2))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ~ r1_yellow_0(X0,k2_tarski(sK2(X0),X2))
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK2(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ( ( v1_lattice3(X0)
          | ( ~ r1_yellow_0(X0,k2_tarski(sK2(X0),sK3(X0)))
            & m1_subset_1(sK3(X0),u1_struct_0(X0))
            & m1_subset_1(sK2(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( r1_yellow_0(X0,k2_tarski(X3,X4))
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v1_lattice3(X0) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f44,f46,f45])).

fof(f65,plain,(
    ! [X4,X0,X3] :
      ( r1_yellow_0(X0,k2_tarski(X3,X4))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f76,plain,(
    v5_orders_2(sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f77,plain,(
    v1_lattice3(sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2] :
                ( r1_yellow_0(X0,X2)
               => k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2)
              | ~ r1_yellow_0(X0,X2) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2)
              | ~ r1_yellow_0(X0,X2) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f30])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2)
      | ~ r1_yellow_0(X0,X2)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f89,plain,(
    v13_waybel_0(sK6,sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f9,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( v13_waybel_0(X3,X1)
      | ~ v13_waybel_0(X2,X0)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f93,plain,(
    ! [X0,X3,X1] :
      ( v13_waybel_0(X3,X1)
      | ~ v13_waybel_0(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f70])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k13_lattice3(X0,X1,X2) = k1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k13_lattice3(X0,X1,X2) = k1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k13_lattice3(X0,X1,X2) = k1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f32])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k13_lattice3(X0,X1,X2) = k1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,X0)
        & m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f59,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1,axiom,(
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
    inference(ennf_transformation,[],[f1])).

fof(f16,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f15])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f84,plain,(
    v2_lattice3(sK5) ),
    inference(cnf_transformation,[],[f51])).

fof(f75,plain,(
    v4_orders_2(sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f74,plain,(
    v3_orders_2(sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f53,plain,(
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
    inference(cnf_transformation,[],[f42])).

fof(f90,plain,(
    v2_waybel_7(sK6,sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v2_waybel_7(X1,X0)
      | r2_hidden(k13_lattice3(X0,sK0(X0,X1),sK1(X0,X1)),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v2_waybel_7(X1,X0)
      | ~ r2_hidden(sK0(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v2_waybel_7(X1,X0)
      | ~ r2_hidden(sK1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_4,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK1(X1,X0),u1_struct_0(X1))
    | v2_waybel_7(X0,X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_33,negated_conjecture,
    ( v4_orders_2(sK5) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_616,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK1(X1,X0),u1_struct_0(X1))
    | v2_waybel_7(X0,X1)
    | ~ v3_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_33])).

cnf(c_617,plain,
    ( ~ v2_waybel_0(X0,sK5)
    | ~ v13_waybel_0(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | m1_subset_1(sK1(sK5,X0),u1_struct_0(sK5))
    | v2_waybel_7(X0,sK5)
    | ~ v3_orders_2(sK5)
    | ~ v5_orders_2(sK5)
    | ~ v1_lattice3(sK5)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(sK5) ),
    inference(unflattening,[status(thm)],[c_616])).

cnf(c_34,negated_conjecture,
    ( v3_orders_2(sK5) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_32,negated_conjecture,
    ( v5_orders_2(sK5) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_31,negated_conjecture,
    ( v1_lattice3(sK5) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_29,negated_conjecture,
    ( l1_orders_2(sK5) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_621,plain,
    ( v1_xboole_0(X0)
    | ~ v2_waybel_0(X0,sK5)
    | ~ v13_waybel_0(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | m1_subset_1(sK1(sK5,X0),u1_struct_0(sK5))
    | v2_waybel_7(X0,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_617,c_34,c_32,c_31,c_29])).

cnf(c_622,plain,
    ( ~ v2_waybel_0(X0,sK5)
    | ~ v13_waybel_0(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | m1_subset_1(sK1(sK5,X0),u1_struct_0(sK5))
    | v2_waybel_7(X0,sK5)
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_621])).

cnf(c_27,negated_conjecture,
    ( ~ v1_xboole_0(sK6) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1315,plain,
    ( ~ v2_waybel_0(X0,sK5)
    | ~ v13_waybel_0(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | m1_subset_1(sK1(sK5,X0),u1_struct_0(sK5))
    | v2_waybel_7(X0,sK5)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_622,c_27])).

cnf(c_1316,plain,
    ( ~ v2_waybel_0(sK6,sK5)
    | ~ v13_waybel_0(sK6,sK5)
    | m1_subset_1(sK1(sK5,sK6),u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | v2_waybel_7(sK6,sK5) ),
    inference(unflattening,[status(thm)],[c_1315])).

cnf(c_22,negated_conjecture,
    ( ~ v2_waybel_0(sK6,sK5)
    | ~ v13_waybel_0(sK6,sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ v2_waybel_7(sK6,sK5)
    | v1_xboole_0(sK6) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_209,plain,
    ( ~ v2_waybel_7(sK6,sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ v13_waybel_0(sK6,sK5)
    | ~ v2_waybel_0(sK6,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_22,c_27])).

cnf(c_210,negated_conjecture,
    ( ~ v2_waybel_0(sK6,sK5)
    | ~ v13_waybel_0(sK6,sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ v2_waybel_7(sK6,sK5) ),
    inference(renaming,[status(thm)],[c_209])).

cnf(c_1318,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | m1_subset_1(sK1(sK5,sK6),u1_struct_0(sK5))
    | ~ v13_waybel_0(sK6,sK5)
    | ~ v2_waybel_0(sK6,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1316,c_210])).

cnf(c_1319,plain,
    ( ~ v2_waybel_0(sK6,sK5)
    | ~ v13_waybel_0(sK6,sK5)
    | m1_subset_1(sK1(sK5,sK6),u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(renaming,[status(thm)],[c_1318])).

cnf(c_3010,plain,
    ( v2_waybel_0(sK6,sK5) != iProver_top
    | v13_waybel_0(sK6,sK5) != iProver_top
    | m1_subset_1(sK1(sK5,sK6),u1_struct_0(sK5)) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1319])).

cnf(c_35,negated_conjecture,
    ( l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_46,plain,
    ( l1_orders_2(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_52,plain,
    ( l1_orders_2(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_26,negated_conjecture,
    ( v2_waybel_0(sK6,sK4) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_54,plain,
    ( v2_waybel_0(sK6,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_57,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1320,plain,
    ( v2_waybel_0(sK6,sK5) != iProver_top
    | v13_waybel_0(sK6,sK5) != iProver_top
    | m1_subset_1(sK1(sK5,sK6),u1_struct_0(sK5)) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1319])).

cnf(c_28,negated_conjecture,
    ( g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4)) = g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | X2 = X1
    | g1_orders_2(X2,X3) != g1_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_3032,plain,
    ( X0 = X1
    | g1_orders_2(X0,X2) != g1_orders_2(X1,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3652,plain,
    ( g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) != g1_orders_2(X0,X1)
    | u1_struct_0(sK4) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_28,c_3032])).

cnf(c_8,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_85,plain,
    ( m1_subset_1(u1_orders_2(sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4))))
    | ~ l1_orders_2(sK4) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_3653,plain,
    ( g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) != g1_orders_2(X0,X1)
    | u1_struct_0(sK4) = X0
    | m1_subset_1(u1_orders_2(sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_28,c_3032])).

cnf(c_3670,plain,
    ( ~ m1_subset_1(u1_orders_2(sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4))))
    | g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) != g1_orders_2(X0,X1)
    | u1_struct_0(sK4) = X0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3653])).

cnf(c_3709,plain,
    ( u1_struct_0(sK4) = X0
    | g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) != g1_orders_2(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3652,c_35,c_85,c_3670])).

cnf(c_3710,plain,
    ( g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) != g1_orders_2(X0,X1)
    | u1_struct_0(sK4) = X0 ),
    inference(renaming,[status(thm)],[c_3709])).

cnf(c_3715,plain,
    ( u1_struct_0(sK4) = u1_struct_0(sK5) ),
    inference(equality_resolution,[status(thm)],[c_3710])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | X2 = X0
    | g1_orders_2(X3,X2) != g1_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_3033,plain,
    ( X0 = X1
    | g1_orders_2(X2,X0) != g1_orders_2(X3,X1)
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3677,plain,
    ( g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) != g1_orders_2(X0,X1)
    | u1_orders_2(sK4) = X1
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_28,c_3033])).

cnf(c_3678,plain,
    ( g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) != g1_orders_2(X0,X1)
    | u1_orders_2(sK4) = X1
    | m1_subset_1(u1_orders_2(sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_28,c_3033])).

cnf(c_3695,plain,
    ( ~ m1_subset_1(u1_orders_2(sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4))))
    | g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) != g1_orders_2(X0,X1)
    | u1_orders_2(sK4) = X1 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3678])).

cnf(c_3727,plain,
    ( u1_orders_2(sK4) = X1
    | g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) != g1_orders_2(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3677,c_35,c_85,c_3695])).

cnf(c_3728,plain,
    ( g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) != g1_orders_2(X0,X1)
    | u1_orders_2(sK4) = X1 ),
    inference(renaming,[status(thm)],[c_3727])).

cnf(c_3733,plain,
    ( u1_orders_2(sK5) = u1_orders_2(sK4) ),
    inference(equality_resolution,[status(thm)],[c_3728])).

cnf(c_3028,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3788,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3715,c_3028])).

cnf(c_21,plain,
    ( ~ v2_waybel_0(X0,X1)
    | v2_waybel_0(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X2)
    | g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_3747,plain,
    ( v2_waybel_0(sK6,X0)
    | ~ v2_waybel_0(sK6,sK4)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_orders_2(X0)
    | ~ l1_orders_2(sK4)
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4)) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_3838,plain,
    ( ~ v2_waybel_0(sK6,sK4)
    | v2_waybel_0(sK6,sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ l1_orders_2(sK4)
    | ~ l1_orders_2(sK5)
    | g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) != g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4)) ),
    inference(instantiation,[status(thm)],[c_3747])).

cnf(c_3839,plain,
    ( g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) != g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4))
    | v2_waybel_0(sK6,sK4) != iProver_top
    | v2_waybel_0(sK6,sK5) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | l1_orders_2(sK4) != iProver_top
    | l1_orders_2(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3838])).

cnf(c_2101,plain,
    ( X0 != X1
    | X2 != X3
    | g1_orders_2(X0,X2) = g1_orders_2(X1,X3) ),
    theory(equality)).

cnf(c_4017,plain,
    ( g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) = g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
    | u1_orders_2(sK5) != u1_orders_2(X0)
    | u1_struct_0(sK5) != u1_struct_0(X0) ),
    inference(instantiation,[status(thm)],[c_2101])).

cnf(c_4018,plain,
    ( g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) = g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4))
    | u1_orders_2(sK5) != u1_orders_2(sK4)
    | u1_struct_0(sK5) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_4017])).

cnf(c_3717,plain,
    ( g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) != g1_orders_2(X0,X1)
    | u1_struct_0(sK5) = X0 ),
    inference(demodulation,[status(thm)],[c_3715,c_3710])).

cnf(c_4325,plain,
    ( u1_struct_0(sK5) = u1_struct_0(sK5) ),
    inference(equality_resolution,[status(thm)],[c_3717])).

cnf(c_2087,plain,
    ( X0 != X1
    | X2 != X1
    | X0 = X2 ),
    theory(equality)).

cnf(c_4350,plain,
    ( u1_struct_0(X0) != X1
    | u1_struct_0(sK5) != X1
    | u1_struct_0(sK5) = u1_struct_0(X0) ),
    inference(instantiation,[status(thm)],[c_2087])).

cnf(c_4819,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK5)
    | u1_struct_0(sK5) = u1_struct_0(X0)
    | u1_struct_0(sK5) != u1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_4350])).

cnf(c_4820,plain,
    ( u1_struct_0(sK4) != u1_struct_0(sK5)
    | u1_struct_0(sK5) = u1_struct_0(sK4)
    | u1_struct_0(sK5) != u1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_4819])).

cnf(c_4866,plain,
    ( m1_subset_1(sK1(sK5,sK6),u1_struct_0(sK5)) = iProver_top
    | v13_waybel_0(sK6,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3010,c_46,c_52,c_54,c_57,c_1320,c_3715,c_3733,c_3788,c_3839,c_4018,c_4325,c_4820])).

cnf(c_4867,plain,
    ( v13_waybel_0(sK6,sK5) != iProver_top
    | m1_subset_1(sK1(sK5,sK6),u1_struct_0(sK5)) = iProver_top ),
    inference(renaming,[status(thm)],[c_4866])).

cnf(c_5,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1,X0),u1_struct_0(X1))
    | v2_waybel_7(X0,X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_586,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1,X0),u1_struct_0(X1))
    | v2_waybel_7(X0,X1)
    | ~ v3_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_33])).

cnf(c_587,plain,
    ( ~ v2_waybel_0(X0,sK5)
    | ~ v13_waybel_0(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | m1_subset_1(sK0(sK5,X0),u1_struct_0(sK5))
    | v2_waybel_7(X0,sK5)
    | ~ v3_orders_2(sK5)
    | ~ v5_orders_2(sK5)
    | ~ v1_lattice3(sK5)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(sK5) ),
    inference(unflattening,[status(thm)],[c_586])).

cnf(c_591,plain,
    ( v1_xboole_0(X0)
    | ~ v2_waybel_0(X0,sK5)
    | ~ v13_waybel_0(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | m1_subset_1(sK0(sK5,X0),u1_struct_0(sK5))
    | v2_waybel_7(X0,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_587,c_34,c_32,c_31,c_29])).

cnf(c_592,plain,
    ( ~ v2_waybel_0(X0,sK5)
    | ~ v13_waybel_0(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | m1_subset_1(sK0(sK5,X0),u1_struct_0(sK5))
    | v2_waybel_7(X0,sK5)
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_591])).

cnf(c_1335,plain,
    ( ~ v2_waybel_0(X0,sK5)
    | ~ v13_waybel_0(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | m1_subset_1(sK0(sK5,X0),u1_struct_0(sK5))
    | v2_waybel_7(X0,sK5)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_592,c_27])).

cnf(c_1336,plain,
    ( ~ v2_waybel_0(sK6,sK5)
    | ~ v13_waybel_0(sK6,sK5)
    | m1_subset_1(sK0(sK5,sK6),u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | v2_waybel_7(sK6,sK5) ),
    inference(unflattening,[status(thm)],[c_1335])).

cnf(c_1338,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | m1_subset_1(sK0(sK5,sK6),u1_struct_0(sK5))
    | ~ v13_waybel_0(sK6,sK5)
    | ~ v2_waybel_0(sK6,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1336,c_27,c_22])).

cnf(c_1339,plain,
    ( ~ v2_waybel_0(sK6,sK5)
    | ~ v13_waybel_0(sK6,sK5)
    | m1_subset_1(sK0(sK5,sK6),u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(renaming,[status(thm)],[c_1338])).

cnf(c_3009,plain,
    ( v2_waybel_0(sK6,sK5) != iProver_top
    | v13_waybel_0(sK6,sK5) != iProver_top
    | m1_subset_1(sK0(sK5,sK6),u1_struct_0(sK5)) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1339])).

cnf(c_1340,plain,
    ( v2_waybel_0(sK6,sK5) != iProver_top
    | v13_waybel_0(sK6,sK5) != iProver_top
    | m1_subset_1(sK0(sK5,sK6),u1_struct_0(sK5)) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1339])).

cnf(c_4751,plain,
    ( m1_subset_1(sK0(sK5,sK6),u1_struct_0(sK5)) = iProver_top
    | v13_waybel_0(sK6,sK5) != iProver_top
    | v2_waybel_0(sK6,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3009,c_1340,c_3788])).

cnf(c_4752,plain,
    ( v2_waybel_0(sK6,sK5) != iProver_top
    | v13_waybel_0(sK6,sK5) != iProver_top
    | m1_subset_1(sK0(sK5,sK6),u1_struct_0(sK5)) = iProver_top ),
    inference(renaming,[status(thm)],[c_4751])).

cnf(c_16,plain,
    ( r1_yellow_0(X0,k2_tarski(X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_38,negated_conjecture,
    ( v5_orders_2(sK4) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1076,plain,
    ( r1_yellow_0(X0,k2_tarski(X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_38])).

cnf(c_1077,plain,
    ( r1_yellow_0(sK4,k2_tarski(X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ v1_lattice3(sK4)
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_1076])).

cnf(c_37,negated_conjecture,
    ( v1_lattice3(sK4) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1081,plain,
    ( r1_yellow_0(sK4,k2_tarski(X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1077,c_37,c_35])).

cnf(c_1082,plain,
    ( r1_yellow_0(sK4,k2_tarski(X0,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_1081])).

cnf(c_3018,plain,
    ( r1_yellow_0(sK4,k2_tarski(X0,X1)) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1082])).

cnf(c_4486,plain,
    ( r1_yellow_0(sK4,k2_tarski(X0,X1)) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3018,c_3715])).

cnf(c_19,plain,
    ( ~ r1_yellow_0(X0,X1)
    | ~ l1_orders_2(X0)
    | ~ l1_orders_2(X2)
    | k1_yellow_0(X2,X1) = k1_yellow_0(X0,X1)
    | g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_3030,plain,
    ( k1_yellow_0(X0,X1) = k1_yellow_0(X2,X1)
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
    | r1_yellow_0(X2,X1) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | l1_orders_2(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3967,plain,
    ( k1_yellow_0(X0,X1) = k1_yellow_0(sK4,X1)
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK5))
    | r1_yellow_0(sK4,X1) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | l1_orders_2(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3733,c_3030])).

cnf(c_3974,plain,
    ( k1_yellow_0(X0,X1) = k1_yellow_0(sK4,X1)
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5))
    | r1_yellow_0(sK4,X1) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | l1_orders_2(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3967,c_3715])).

cnf(c_5223,plain,
    ( l1_orders_2(X0) != iProver_top
    | r1_yellow_0(sK4,X1) != iProver_top
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5))
    | k1_yellow_0(X0,X1) = k1_yellow_0(sK4,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3974,c_46])).

cnf(c_5224,plain,
    ( k1_yellow_0(X0,X1) = k1_yellow_0(sK4,X1)
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5))
    | r1_yellow_0(sK4,X1) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5223])).

cnf(c_5233,plain,
    ( k1_yellow_0(sK5,X0) = k1_yellow_0(sK4,X0)
    | r1_yellow_0(sK4,X0) != iProver_top
    | l1_orders_2(sK5) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_5224])).

cnf(c_8581,plain,
    ( r1_yellow_0(sK4,X0) != iProver_top
    | k1_yellow_0(sK5,X0) = k1_yellow_0(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5233,c_52])).

cnf(c_8582,plain,
    ( k1_yellow_0(sK5,X0) = k1_yellow_0(sK4,X0)
    | r1_yellow_0(sK4,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_8581])).

cnf(c_8589,plain,
    ( k1_yellow_0(sK4,k2_tarski(X0,X1)) = k1_yellow_0(sK5,k2_tarski(X0,X1))
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4486,c_8582])).

cnf(c_10053,plain,
    ( k1_yellow_0(sK5,k2_tarski(sK0(sK5,sK6),X0)) = k1_yellow_0(sK4,k2_tarski(sK0(sK5,sK6),X0))
    | v2_waybel_0(sK6,sK5) != iProver_top
    | v13_waybel_0(sK6,sK5) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4752,c_8589])).

cnf(c_25,negated_conjecture,
    ( v13_waybel_0(sK6,sK4) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_55,plain,
    ( v13_waybel_0(sK6,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_17,plain,
    ( ~ v13_waybel_0(X0,X1)
    | v13_waybel_0(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X2)
    | g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_3744,plain,
    ( v13_waybel_0(sK6,X0)
    | ~ v13_waybel_0(sK6,sK4)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_orders_2(X0)
    | ~ l1_orders_2(sK4)
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_5741,plain,
    ( ~ v13_waybel_0(sK6,sK4)
    | v13_waybel_0(sK6,sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ l1_orders_2(sK4)
    | ~ l1_orders_2(sK5)
    | g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) != g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4)) ),
    inference(instantiation,[status(thm)],[c_3744])).

cnf(c_5742,plain,
    ( g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) != g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4))
    | v13_waybel_0(sK6,sK4) != iProver_top
    | v13_waybel_0(sK6,sK5) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | l1_orders_2(sK4) != iProver_top
    | l1_orders_2(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5741])).

cnf(c_10353,plain,
    ( k1_yellow_0(sK5,k2_tarski(sK0(sK5,sK6),X0)) = k1_yellow_0(sK4,k2_tarski(sK0(sK5,sK6),X0))
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10053,c_46,c_52,c_54,c_55,c_57,c_3715,c_3733,c_3788,c_3839,c_4018,c_4325,c_4820,c_5742])).

cnf(c_10361,plain,
    ( k1_yellow_0(sK4,k2_tarski(sK0(sK5,sK6),sK1(sK5,sK6))) = k1_yellow_0(sK5,k2_tarski(sK0(sK5,sK6),sK1(sK5,sK6)))
    | v13_waybel_0(sK6,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4867,c_10353])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1)
    | k1_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X0,X2)) = k13_lattice3(X1,X0,X2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_523,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1)
    | k1_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X0)) = k13_lattice3(X1,X2,X0)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_33])).

cnf(c_524,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ v3_orders_2(sK5)
    | ~ v5_orders_2(sK5)
    | ~ v1_lattice3(sK5)
    | ~ l1_orders_2(sK5)
    | k1_yellow_0(sK5,k7_domain_1(u1_struct_0(sK5),X0,X1)) = k13_lattice3(sK5,X0,X1) ),
    inference(unflattening,[status(thm)],[c_523])).

cnf(c_528,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | k1_yellow_0(sK5,k7_domain_1(u1_struct_0(sK5),X0,X1)) = k13_lattice3(sK5,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_524,c_34,c_32,c_31,c_29])).

cnf(c_3021,plain,
    ( k1_yellow_0(sK5,k7_domain_1(u1_struct_0(sK5),X0,X1)) = k13_lattice3(sK5,X0,X1)
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_528])).

cnf(c_4759,plain,
    ( k1_yellow_0(sK5,k7_domain_1(u1_struct_0(sK5),sK0(sK5,sK6),X0)) = k13_lattice3(sK5,sK0(sK5,sK6),X0)
    | v2_waybel_0(sK6,sK5) != iProver_top
    | v13_waybel_0(sK6,sK5) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4752,c_3021])).

cnf(c_6469,plain,
    ( k1_yellow_0(sK5,k7_domain_1(u1_struct_0(sK5),sK0(sK5,sK6),X0)) = k13_lattice3(sK5,sK0(sK5,sK6),X0)
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4759,c_46,c_52,c_54,c_55,c_57,c_3715,c_3733,c_3788,c_3839,c_4018,c_4325,c_4820,c_5742])).

cnf(c_6477,plain,
    ( k1_yellow_0(sK5,k7_domain_1(u1_struct_0(sK5),sK0(sK5,sK6),sK1(sK5,sK6))) = k13_lattice3(sK5,sK0(sK5,sK6),sK1(sK5,sK6))
    | v13_waybel_0(sK6,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4867,c_6469])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,X1)
    | v1_xboole_0(X1)
    | k7_domain_1(X1,X2,X0) = k2_tarski(X2,X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_7,plain,
    ( l1_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_9,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_421,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_7,c_9])).

cnf(c_0,plain,
    ( ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_439,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0) ),
    inference(resolution,[status(thm)],[c_421,c_0])).

cnf(c_30,negated_conjecture,
    ( v2_lattice3(sK5) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_457,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_439,c_30])).

cnf(c_458,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK5))
    | ~ l1_orders_2(sK5) ),
    inference(unflattening,[status(thm)],[c_457])).

cnf(c_460,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_458,c_29])).

cnf(c_1203,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,X1)
    | k7_domain_1(X1,X2,X0) = k2_tarski(X2,X0)
    | u1_struct_0(sK5) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_460])).

cnf(c_1204,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | k7_domain_1(u1_struct_0(sK5),X0,X1) = k2_tarski(X0,X1) ),
    inference(unflattening,[status(thm)],[c_1203])).

cnf(c_3015,plain,
    ( k7_domain_1(u1_struct_0(sK5),X0,X1) = k2_tarski(X0,X1)
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1204])).

cnf(c_4758,plain,
    ( k7_domain_1(u1_struct_0(sK5),sK0(sK5,sK6),X0) = k2_tarski(sK0(sK5,sK6),X0)
    | v2_waybel_0(sK6,sK5) != iProver_top
    | v13_waybel_0(sK6,sK5) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4752,c_3015])).

cnf(c_6008,plain,
    ( k7_domain_1(u1_struct_0(sK5),sK0(sK5,sK6),X0) = k2_tarski(sK0(sK5,sK6),X0)
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4758,c_46,c_52,c_54,c_55,c_57,c_3715,c_3733,c_3788,c_3839,c_4018,c_4325,c_4820,c_5742])).

cnf(c_6016,plain,
    ( k7_domain_1(u1_struct_0(sK5),sK0(sK5,sK6),sK1(sK5,sK6)) = k2_tarski(sK0(sK5,sK6),sK1(sK5,sK6))
    | v13_waybel_0(sK6,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4867,c_6008])).

cnf(c_6110,plain,
    ( k7_domain_1(u1_struct_0(sK5),sK0(sK5,sK6),sK1(sK5,sK6)) = k2_tarski(sK0(sK5,sK6),sK1(sK5,sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6016,c_46,c_52,c_55,c_57,c_3715,c_3733,c_3788,c_4018,c_4325,c_4820,c_5742])).

cnf(c_6510,plain,
    ( k1_yellow_0(sK5,k2_tarski(sK0(sK5,sK6),sK1(sK5,sK6))) = k13_lattice3(sK5,sK0(sK5,sK6),sK1(sK5,sK6))
    | v13_waybel_0(sK6,sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6477,c_6110])).

cnf(c_8749,plain,
    ( k1_yellow_0(sK5,k2_tarski(sK0(sK5,sK6),sK1(sK5,sK6))) = k13_lattice3(sK5,sK0(sK5,sK6),sK1(sK5,sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6510,c_46,c_52,c_55,c_57,c_3715,c_3733,c_3788,c_4018,c_4325,c_4820,c_5742])).

cnf(c_39,negated_conjecture,
    ( v4_orders_2(sK4) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_736,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1)
    | k1_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X0)) = k13_lattice3(X1,X2,X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_39])).

cnf(c_737,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ v3_orders_2(sK4)
    | ~ v5_orders_2(sK4)
    | ~ v1_lattice3(sK4)
    | ~ l1_orders_2(sK4)
    | k1_yellow_0(sK4,k7_domain_1(u1_struct_0(sK4),X0,X1)) = k13_lattice3(sK4,X0,X1) ),
    inference(unflattening,[status(thm)],[c_736])).

cnf(c_40,negated_conjecture,
    ( v3_orders_2(sK4) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_741,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | k1_yellow_0(sK4,k7_domain_1(u1_struct_0(sK4),X0,X1)) = k13_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_737,c_40,c_38,c_37,c_35])).

cnf(c_3020,plain,
    ( k1_yellow_0(sK4,k7_domain_1(u1_struct_0(sK4),X0,X1)) = k13_lattice3(sK4,X0,X1)
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_741])).

cnf(c_4589,plain,
    ( k1_yellow_0(sK4,k7_domain_1(u1_struct_0(sK5),X0,X1)) = k13_lattice3(sK4,X0,X1)
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3020,c_3715])).

cnf(c_4760,plain,
    ( k1_yellow_0(sK4,k7_domain_1(u1_struct_0(sK5),sK0(sK5,sK6),X0)) = k13_lattice3(sK4,sK0(sK5,sK6),X0)
    | v2_waybel_0(sK6,sK5) != iProver_top
    | v13_waybel_0(sK6,sK5) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4752,c_4589])).

cnf(c_6602,plain,
    ( k1_yellow_0(sK4,k7_domain_1(u1_struct_0(sK5),sK0(sK5,sK6),X0)) = k13_lattice3(sK4,sK0(sK5,sK6),X0)
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4760,c_46,c_52,c_54,c_55,c_57,c_3715,c_3733,c_3788,c_3839,c_4018,c_4325,c_4820,c_5742])).

cnf(c_6610,plain,
    ( k1_yellow_0(sK4,k7_domain_1(u1_struct_0(sK5),sK0(sK5,sK6),sK1(sK5,sK6))) = k13_lattice3(sK4,sK0(sK5,sK6),sK1(sK5,sK6))
    | v13_waybel_0(sK6,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4867,c_6602])).

cnf(c_6643,plain,
    ( k1_yellow_0(sK4,k2_tarski(sK0(sK5,sK6),sK1(sK5,sK6))) = k13_lattice3(sK4,sK0(sK5,sK6),sK1(sK5,sK6))
    | v13_waybel_0(sK6,sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6610,c_6110])).

cnf(c_8753,plain,
    ( k1_yellow_0(sK4,k2_tarski(sK0(sK5,sK6),sK1(sK5,sK6))) = k13_lattice3(sK4,sK0(sK5,sK6),sK1(sK5,sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6643,c_46,c_52,c_55,c_57,c_3715,c_3733,c_3788,c_4018,c_4325,c_4820,c_5742])).

cnf(c_10415,plain,
    ( k13_lattice3(sK4,sK0(sK5,sK6),sK1(sK5,sK6)) = k13_lattice3(sK5,sK0(sK5,sK6),sK1(sK5,sK6))
    | v13_waybel_0(sK6,sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10361,c_8749,c_8753])).

cnf(c_10485,plain,
    ( k13_lattice3(sK4,sK0(sK5,sK6),sK1(sK5,sK6)) = k13_lattice3(sK5,sK0(sK5,sK6),sK1(sK5,sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10415,c_46,c_52,c_55,c_57,c_3715,c_3733,c_3788,c_4018,c_4325,c_4820,c_5742])).

cnf(c_6,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | r2_hidden(X3,X0)
    | r2_hidden(X2,X0)
    | ~ r2_hidden(k13_lattice3(X1,X3,X2),X0)
    | ~ v2_waybel_7(X0,X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_757,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | r2_hidden(X3,X0)
    | r2_hidden(X2,X0)
    | ~ r2_hidden(k13_lattice3(X1,X3,X2),X0)
    | ~ v2_waybel_7(X0,X1)
    | ~ v3_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_39])).

cnf(c_758,plain,
    ( ~ v2_waybel_0(X0,sK4)
    | ~ v13_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | r2_hidden(X2,X0)
    | r2_hidden(X1,X0)
    | ~ r2_hidden(k13_lattice3(sK4,X2,X1),X0)
    | ~ v2_waybel_7(X0,sK4)
    | ~ v3_orders_2(sK4)
    | ~ v5_orders_2(sK4)
    | ~ v1_lattice3(sK4)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_757])).

cnf(c_762,plain,
    ( v1_xboole_0(X0)
    | ~ v2_waybel_0(X0,sK4)
    | ~ v13_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | r2_hidden(X2,X0)
    | r2_hidden(X1,X0)
    | ~ r2_hidden(k13_lattice3(sK4,X2,X1),X0)
    | ~ v2_waybel_7(X0,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_758,c_40,c_38,c_37,c_35])).

cnf(c_763,plain,
    ( ~ v2_waybel_0(X0,sK4)
    | ~ v13_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | r2_hidden(X1,X0)
    | r2_hidden(X2,X0)
    | ~ r2_hidden(k13_lattice3(sK4,X1,X2),X0)
    | ~ v2_waybel_7(X0,sK4)
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_762])).

cnf(c_1228,plain,
    ( ~ v2_waybel_0(X0,sK4)
    | ~ v13_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | r2_hidden(X1,X0)
    | r2_hidden(X2,X0)
    | ~ r2_hidden(k13_lattice3(sK4,X2,X1),X0)
    | ~ v2_waybel_7(X0,sK4)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_763,c_27])).

cnf(c_1229,plain,
    ( ~ v2_waybel_0(sK6,sK4)
    | ~ v13_waybel_0(sK6,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(X0,sK6)
    | r2_hidden(X1,sK6)
    | ~ r2_hidden(k13_lattice3(sK4,X0,X1),sK6)
    | ~ v2_waybel_7(sK6,sK4) ),
    inference(unflattening,[status(thm)],[c_1228])).

cnf(c_24,negated_conjecture,
    ( v2_waybel_7(sK6,sK4) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1233,plain,
    ( ~ r2_hidden(k13_lattice3(sK4,X0,X1),sK6)
    | r2_hidden(X1,sK6)
    | r2_hidden(X0,sK6)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1229,c_26,c_25,c_24,c_23])).

cnf(c_1234,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | r2_hidden(X1,sK6)
    | r2_hidden(X0,sK6)
    | ~ r2_hidden(k13_lattice3(sK4,X0,X1),sK6) ),
    inference(renaming,[status(thm)],[c_1233])).

cnf(c_3014,plain,
    ( m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0,sK6) = iProver_top
    | r2_hidden(X1,sK6) = iProver_top
    | r2_hidden(k13_lattice3(sK4,X0,X1),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1234])).

cnf(c_5074,plain,
    ( m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X0,sK6) = iProver_top
    | r2_hidden(X1,sK6) = iProver_top
    | r2_hidden(k13_lattice3(sK4,X0,X1),sK6) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3014,c_3715])).

cnf(c_10491,plain,
    ( m1_subset_1(sK0(sK5,sK6),u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK1(sK5,sK6),u1_struct_0(sK5)) != iProver_top
    | r2_hidden(k13_lattice3(sK5,sK0(sK5,sK6),sK1(sK5,sK6)),sK6) != iProver_top
    | r2_hidden(sK0(sK5,sK6),sK6) = iProver_top
    | r2_hidden(sK1(sK5,sK6),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_10485,c_5074])).

cnf(c_3,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(k13_lattice3(X1,sK0(X1,X0),sK1(X1,X0)),X0)
    | v2_waybel_7(X0,X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_646,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(k13_lattice3(X1,sK0(X1,X0),sK1(X1,X0)),X0)
    | v2_waybel_7(X0,X1)
    | ~ v3_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_33])).

cnf(c_647,plain,
    ( ~ v2_waybel_0(X0,sK5)
    | ~ v13_waybel_0(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | r2_hidden(k13_lattice3(sK5,sK0(sK5,X0),sK1(sK5,X0)),X0)
    | v2_waybel_7(X0,sK5)
    | ~ v3_orders_2(sK5)
    | ~ v5_orders_2(sK5)
    | ~ v1_lattice3(sK5)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(sK5) ),
    inference(unflattening,[status(thm)],[c_646])).

cnf(c_651,plain,
    ( v1_xboole_0(X0)
    | ~ v2_waybel_0(X0,sK5)
    | ~ v13_waybel_0(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | r2_hidden(k13_lattice3(sK5,sK0(sK5,X0),sK1(sK5,X0)),X0)
    | v2_waybel_7(X0,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_647,c_34,c_32,c_31,c_29])).

cnf(c_652,plain,
    ( ~ v2_waybel_0(X0,sK5)
    | ~ v13_waybel_0(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | r2_hidden(k13_lattice3(sK5,sK0(sK5,X0),sK1(sK5,X0)),X0)
    | v2_waybel_7(X0,sK5)
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_651])).

cnf(c_1295,plain,
    ( ~ v2_waybel_0(X0,sK5)
    | ~ v13_waybel_0(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | r2_hidden(k13_lattice3(sK5,sK0(sK5,X0),sK1(sK5,X0)),X0)
    | v2_waybel_7(X0,sK5)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_652,c_27])).

cnf(c_1296,plain,
    ( ~ v2_waybel_0(sK6,sK5)
    | ~ v13_waybel_0(sK6,sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | r2_hidden(k13_lattice3(sK5,sK0(sK5,sK6),sK1(sK5,sK6)),sK6)
    | v2_waybel_7(sK6,sK5) ),
    inference(unflattening,[status(thm)],[c_1295])).

cnf(c_1298,plain,
    ( r2_hidden(k13_lattice3(sK5,sK0(sK5,sK6),sK1(sK5,sK6)),sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ v13_waybel_0(sK6,sK5)
    | ~ v2_waybel_0(sK6,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1296,c_27,c_22])).

cnf(c_1299,plain,
    ( ~ v2_waybel_0(sK6,sK5)
    | ~ v13_waybel_0(sK6,sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | r2_hidden(k13_lattice3(sK5,sK0(sK5,sK6),sK1(sK5,sK6)),sK6) ),
    inference(renaming,[status(thm)],[c_1298])).

cnf(c_1300,plain,
    ( v2_waybel_0(sK6,sK5) != iProver_top
    | v13_waybel_0(sK6,sK5) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r2_hidden(k13_lattice3(sK5,sK0(sK5,sK6),sK1(sK5,sK6)),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1299])).

cnf(c_2,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(sK0(X1,X0),X0)
    | v2_waybel_7(X0,X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_676,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(sK0(X1,X0),X0)
    | v2_waybel_7(X0,X1)
    | ~ v3_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_33])).

cnf(c_677,plain,
    ( ~ v2_waybel_0(X0,sK5)
    | ~ v13_waybel_0(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(sK0(sK5,X0),X0)
    | v2_waybel_7(X0,sK5)
    | ~ v3_orders_2(sK5)
    | ~ v5_orders_2(sK5)
    | ~ v1_lattice3(sK5)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(sK5) ),
    inference(unflattening,[status(thm)],[c_676])).

cnf(c_681,plain,
    ( v1_xboole_0(X0)
    | ~ v2_waybel_0(X0,sK5)
    | ~ v13_waybel_0(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(sK0(sK5,X0),X0)
    | v2_waybel_7(X0,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_677,c_34,c_32,c_31,c_29])).

cnf(c_682,plain,
    ( ~ v2_waybel_0(X0,sK5)
    | ~ v13_waybel_0(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(sK0(sK5,X0),X0)
    | v2_waybel_7(X0,sK5)
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_681])).

cnf(c_1275,plain,
    ( ~ v2_waybel_0(X0,sK5)
    | ~ v13_waybel_0(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(sK0(sK5,X0),X0)
    | v2_waybel_7(X0,sK5)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_682,c_27])).

cnf(c_1276,plain,
    ( ~ v2_waybel_0(sK6,sK5)
    | ~ v13_waybel_0(sK6,sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(sK0(sK5,sK6),sK6)
    | v2_waybel_7(sK6,sK5) ),
    inference(unflattening,[status(thm)],[c_1275])).

cnf(c_1278,plain,
    ( ~ r2_hidden(sK0(sK5,sK6),sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ v13_waybel_0(sK6,sK5)
    | ~ v2_waybel_0(sK6,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1276,c_27,c_22])).

cnf(c_1279,plain,
    ( ~ v2_waybel_0(sK6,sK5)
    | ~ v13_waybel_0(sK6,sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(sK0(sK5,sK6),sK6) ),
    inference(renaming,[status(thm)],[c_1278])).

cnf(c_1280,plain,
    ( v2_waybel_0(sK6,sK5) != iProver_top
    | v13_waybel_0(sK6,sK5) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r2_hidden(sK0(sK5,sK6),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1279])).

cnf(c_1,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(sK1(X1,X0),X0)
    | v2_waybel_7(X0,X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_706,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(sK1(X1,X0),X0)
    | v2_waybel_7(X0,X1)
    | ~ v3_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_33])).

cnf(c_707,plain,
    ( ~ v2_waybel_0(X0,sK5)
    | ~ v13_waybel_0(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(sK1(sK5,X0),X0)
    | v2_waybel_7(X0,sK5)
    | ~ v3_orders_2(sK5)
    | ~ v5_orders_2(sK5)
    | ~ v1_lattice3(sK5)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(sK5) ),
    inference(unflattening,[status(thm)],[c_706])).

cnf(c_711,plain,
    ( v1_xboole_0(X0)
    | ~ v2_waybel_0(X0,sK5)
    | ~ v13_waybel_0(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(sK1(sK5,X0),X0)
    | v2_waybel_7(X0,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_707,c_34,c_32,c_31,c_29])).

cnf(c_712,plain,
    ( ~ v2_waybel_0(X0,sK5)
    | ~ v13_waybel_0(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(sK1(sK5,X0),X0)
    | v2_waybel_7(X0,sK5)
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_711])).

cnf(c_1255,plain,
    ( ~ v2_waybel_0(X0,sK5)
    | ~ v13_waybel_0(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(sK1(sK5,X0),X0)
    | v2_waybel_7(X0,sK5)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_712,c_27])).

cnf(c_1256,plain,
    ( ~ v2_waybel_0(sK6,sK5)
    | ~ v13_waybel_0(sK6,sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(sK1(sK5,sK6),sK6)
    | v2_waybel_7(sK6,sK5) ),
    inference(unflattening,[status(thm)],[c_1255])).

cnf(c_1258,plain,
    ( ~ r2_hidden(sK1(sK5,sK6),sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ v13_waybel_0(sK6,sK5)
    | ~ v2_waybel_0(sK6,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1256,c_27,c_22])).

cnf(c_1259,plain,
    ( ~ v2_waybel_0(sK6,sK5)
    | ~ v13_waybel_0(sK6,sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(sK1(sK5,sK6),sK6) ),
    inference(renaming,[status(thm)],[c_1258])).

cnf(c_1260,plain,
    ( v2_waybel_0(sK6,sK5) != iProver_top
    | v13_waybel_0(sK6,sK5) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r2_hidden(sK1(sK5,sK6),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1259])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10491,c_5742,c_4820,c_4325,c_4018,c_3839,c_3788,c_3733,c_3715,c_1340,c_1320,c_1300,c_1280,c_1260,c_57,c_55,c_54,c_52,c_46])).


%------------------------------------------------------------------------------
