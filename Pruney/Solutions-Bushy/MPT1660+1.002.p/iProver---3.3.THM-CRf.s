%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1660+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:07 EST 2020

% Result     : Theorem 26.74s
% Output     : CNFRefutation 26.74s
% Verified   : 
% Statistics : Number of formulae       :  227 (1739 expanded)
%              Number of clauses        :  144 ( 435 expanded)
%              Number of leaves         :   19 ( 497 expanded)
%              Depth                    :   25
%              Number of atoms          : 1305 (19377 expanded)
%              Number of equality atoms :  146 ( 507 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal clause size      :   34 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( k13_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( ( r1_orders_2(X0,X2,X4)
                              & r1_orders_2(X0,X1,X4) )
                           => r1_orders_2(X0,X3,X4) ) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k13_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r1_orders_2(X0,X3,X4)
                          | ~ r1_orders_2(X0,X2,X4)
                          | ~ r1_orders_2(X0,X1,X4)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k13_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r1_orders_2(X0,X3,X4)
                          | ~ r1_orders_2(X0,X2,X4)
                          | ~ r1_orders_2(X0,X1,X4)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f20])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k13_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X3,X4)
                          & r1_orders_2(X0,X2,X4)
                          & r1_orders_2(X0,X1,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3) )
                    & ( ( ! [X4] :
                            ( r1_orders_2(X0,X3,X4)
                            | ~ r1_orders_2(X0,X2,X4)
                            | ~ r1_orders_2(X0,X1,X4)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | k13_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k13_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X3,X4)
                          & r1_orders_2(X0,X2,X4)
                          & r1_orders_2(X0,X1,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3) )
                    & ( ( ! [X4] :
                            ( r1_orders_2(X0,X3,X4)
                            | ~ r1_orders_2(X0,X2,X4)
                            | ~ r1_orders_2(X0,X1,X4)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | k13_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f42])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k13_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X3,X4)
                          & r1_orders_2(X0,X2,X4)
                          & r1_orders_2(X0,X1,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X3,X5)
                            | ~ r1_orders_2(X0,X2,X5)
                            | ~ r1_orders_2(X0,X1,X5)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | k13_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(rectify,[],[f43])).

fof(f45,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X3,X4)
          & r1_orders_2(X0,X2,X4)
          & r1_orders_2(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X3,sK7(X0,X1,X2,X3))
        & r1_orders_2(X0,X2,sK7(X0,X1,X2,X3))
        & r1_orders_2(X0,X1,sK7(X0,X1,X2,X3))
        & m1_subset_1(sK7(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k13_lattice3(X0,X1,X2) = X3
                      | ( ~ r1_orders_2(X0,X3,sK7(X0,X1,X2,X3))
                        & r1_orders_2(X0,X2,sK7(X0,X1,X2,X3))
                        & r1_orders_2(X0,X1,sK7(X0,X1,X2,X3))
                        & m1_subset_1(sK7(X0,X1,X2,X3),u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X3,X5)
                            | ~ r1_orders_2(X0,X2,X5)
                            | ~ r1_orders_2(X0,X1,X5)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | k13_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f44,f45])).

fof(f78,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_orders_2(X0,X3,X5)
      | ~ r1_orders_2(X0,X2,X5)
      | ~ r1_orders_2(X0,X1,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | k13_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f95,plain,(
    ! [X2,X0,X5,X1] :
      ( r1_orders_2(X0,k13_lattice3(X0,X1,X2),X5)
      | ~ r1_orders_2(X0,X2,X5)
      | ~ r1_orders_2(X0,X1,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f78])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v12_waybel_0(X1,X0) )
         => ( v1_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r2_hidden(X3,X1)
                        & r2_hidden(X2,X1) )
                     => r2_hidden(k13_lattice3(X0,X2,X3),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v12_waybel_0(X1,X0) )
           => ( v1_waybel_0(X1,X0)
            <=> ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( ( r2_hidden(X3,X1)
                          & r2_hidden(X2,X1) )
                       => r2_hidden(k13_lattice3(X0,X2,X3),X1) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_waybel_0(X1,X0)
          <~> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(k13_lattice3(X0,X2,X3),X1)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v12_waybel_0(X1,X0) )
      & l1_orders_2(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_waybel_0(X1,X0)
          <~> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(k13_lattice3(X0,X2,X3),X1)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v12_waybel_0(X1,X0) )
      & l1_orders_2(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0) ) ),
    inference(flattening,[],[f24])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(k13_lattice3(X0,X2,X3),X1)
                    & r2_hidden(X3,X1)
                    & r2_hidden(X2,X1)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ v1_waybel_0(X1,X0) )
          & ( ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(k13_lattice3(X0,X2,X3),X1)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | v1_waybel_0(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v12_waybel_0(X1,X0) )
      & l1_orders_2(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f48,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(k13_lattice3(X0,X2,X3),X1)
                    & r2_hidden(X3,X1)
                    & r2_hidden(X2,X1)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ v1_waybel_0(X1,X0) )
          & ( ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(k13_lattice3(X0,X2,X3),X1)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | v1_waybel_0(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v12_waybel_0(X1,X0) )
      & l1_orders_2(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0) ) ),
    inference(flattening,[],[f47])).

fof(f49,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(k13_lattice3(X0,X2,X3),X1)
                    & r2_hidden(X3,X1)
                    & r2_hidden(X2,X1)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ v1_waybel_0(X1,X0) )
          & ( ! [X4] :
                ( ! [X5] :
                    ( r2_hidden(k13_lattice3(X0,X4,X5),X1)
                    | ~ r2_hidden(X5,X1)
                    | ~ r2_hidden(X4,X1)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            | v1_waybel_0(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v12_waybel_0(X1,X0) )
      & l1_orders_2(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0) ) ),
    inference(rectify,[],[f48])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_hidden(k13_lattice3(X0,X2,X3),X1)
          & r2_hidden(X3,X1)
          & r2_hidden(X2,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(k13_lattice3(X0,X2,sK11),X1)
        & r2_hidden(sK11,X1)
        & r2_hidden(X2,X1)
        & m1_subset_1(sK11,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(k13_lattice3(X0,X2,X3),X1)
              & r2_hidden(X3,X1)
              & r2_hidden(X2,X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r2_hidden(k13_lattice3(X0,sK10,X3),X1)
            & r2_hidden(X3,X1)
            & r2_hidden(sK10,X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK10,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(k13_lattice3(X0,X2,X3),X1)
                    & r2_hidden(X3,X1)
                    & r2_hidden(X2,X1)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ v1_waybel_0(X1,X0) )
          & ( ! [X4] :
                ( ! [X5] :
                    ( r2_hidden(k13_lattice3(X0,X4,X5),X1)
                    | ~ r2_hidden(X5,X1)
                    | ~ r2_hidden(X4,X1)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            | v1_waybel_0(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v12_waybel_0(X1,X0) )
     => ( ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k13_lattice3(X0,X2,X3),sK9)
                  & r2_hidden(X3,sK9)
                  & r2_hidden(X2,sK9)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v1_waybel_0(sK9,X0) )
        & ( ! [X4] :
              ( ! [X5] :
                  ( r2_hidden(k13_lattice3(X0,X4,X5),sK9)
                  | ~ r2_hidden(X5,sK9)
                  | ~ r2_hidden(X4,sK9)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | v1_waybel_0(sK9,X0) )
        & m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(X0)))
        & v12_waybel_0(sK9,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(k13_lattice3(X0,X2,X3),X1)
                      & r2_hidden(X3,X1)
                      & r2_hidden(X2,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v1_waybel_0(X1,X0) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(k13_lattice3(X0,X4,X5),X1)
                      | ~ r2_hidden(X5,X1)
                      | ~ r2_hidden(X4,X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | v1_waybel_0(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v12_waybel_0(X1,X0) )
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
   => ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(k13_lattice3(sK8,X2,X3),X1)
                    & r2_hidden(X3,X1)
                    & r2_hidden(X2,X1)
                    & m1_subset_1(X3,u1_struct_0(sK8)) )
                & m1_subset_1(X2,u1_struct_0(sK8)) )
            | ~ v1_waybel_0(X1,sK8) )
          & ( ! [X4] :
                ( ! [X5] :
                    ( r2_hidden(k13_lattice3(sK8,X4,X5),X1)
                    | ~ r2_hidden(X5,X1)
                    | ~ r2_hidden(X4,X1)
                    | ~ m1_subset_1(X5,u1_struct_0(sK8)) )
                | ~ m1_subset_1(X4,u1_struct_0(sK8)) )
            | v1_waybel_0(X1,sK8) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8)))
          & v12_waybel_0(X1,sK8) )
      & l1_orders_2(sK8)
      & v1_lattice3(sK8)
      & v5_orders_2(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
    ( ( ( ~ r2_hidden(k13_lattice3(sK8,sK10,sK11),sK9)
        & r2_hidden(sK11,sK9)
        & r2_hidden(sK10,sK9)
        & m1_subset_1(sK11,u1_struct_0(sK8))
        & m1_subset_1(sK10,u1_struct_0(sK8)) )
      | ~ v1_waybel_0(sK9,sK8) )
    & ( ! [X4] :
          ( ! [X5] :
              ( r2_hidden(k13_lattice3(sK8,X4,X5),sK9)
              | ~ r2_hidden(X5,sK9)
              | ~ r2_hidden(X4,sK9)
              | ~ m1_subset_1(X5,u1_struct_0(sK8)) )
          | ~ m1_subset_1(X4,u1_struct_0(sK8)) )
      | v1_waybel_0(sK9,sK8) )
    & m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))
    & v12_waybel_0(sK9,sK8)
    & l1_orders_2(sK8)
    & v1_lattice3(sK8)
    & v5_orders_2(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10,sK11])],[f49,f53,f52,f51,f50])).

fof(f85,plain,(
    v1_lattice3(sK8) ),
    inference(cnf_transformation,[],[f54])).

fof(f84,plain,(
    v5_orders_2(sK8) ),
    inference(cnf_transformation,[],[f54])).

fof(f86,plain,(
    l1_orders_2(sK8) ),
    inference(cnf_transformation,[],[f54])).

fof(f26,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ! [X2] :
          ( ! [X3] :
              ( ? [X4] :
                  ( r1_orders_2(X0,X3,X4)
                  & r1_orders_2(X0,X2,X4)
                  & r2_hidden(X4,X1)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ? [X3] :
                ( ! [X4] :
                    ( ~ r1_orders_2(X0,X3,X4)
                    | ~ r1_orders_2(X0,X2,X4)
                    | ~ r2_hidden(X4,X1)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) ) )
      & ( ! [X2] :
            ( ! [X3] :
                ( ? [X4] :
                    ( r1_orders_2(X0,X3,X4)
                    & r1_orders_2(X0,X2,X4)
                    & r2_hidden(X4,X1)
                    & m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r2_hidden(X3,X1)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ? [X3] :
                ( ! [X4] :
                    ( ~ r1_orders_2(X0,X3,X4)
                    | ~ r1_orders_2(X0,X2,X4)
                    | ~ r2_hidden(X4,X1)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) ) )
      & ( ! [X5] :
            ( ! [X6] :
                ( ? [X7] :
                    ( r1_orders_2(X0,X6,X7)
                    & r1_orders_2(X0,X5,X7)
                    & r2_hidden(X7,X1)
                    & m1_subset_1(X7,u1_struct_0(X0)) )
                | ~ r2_hidden(X6,X1)
                | ~ r2_hidden(X5,X1)
                | ~ m1_subset_1(X6,u1_struct_0(X0)) )
            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f36])).

fof(f40,plain,(
    ! [X6,X5,X1,X0] :
      ( ? [X7] :
          ( r1_orders_2(X0,X6,X7)
          & r1_orders_2(X0,X5,X7)
          & r2_hidden(X7,X1)
          & m1_subset_1(X7,u1_struct_0(X0)) )
     => ( r1_orders_2(X0,X6,sK6(X0,X1,X5,X6))
        & r1_orders_2(X0,X5,sK6(X0,X1,X5,X6))
        & r2_hidden(sK6(X0,X1,X5,X6),X1)
        & m1_subset_1(sK6(X0,X1,X5,X6),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ! [X4] :
              ( ~ r1_orders_2(X0,X3,X4)
              | ~ r1_orders_2(X0,X2,X4)
              | ~ r2_hidden(X4,X1)
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          & r2_hidden(X3,X1)
          & r2_hidden(X2,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ! [X4] :
            ( ~ r1_orders_2(X0,sK5(X0,X1),X4)
            | ~ r1_orders_2(X0,X2,X4)
            | ~ r2_hidden(X4,X1)
            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
        & r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(X2,X1)
        & m1_subset_1(sK5(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ! [X4] :
                  ( ~ r1_orders_2(X0,X3,X4)
                  | ~ r1_orders_2(X0,X2,X4)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & r2_hidden(X3,X1)
              & r2_hidden(X2,X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ! [X4] :
                ( ~ r1_orders_2(X0,X3,X4)
                | ~ r1_orders_2(X0,sK4(X0,X1),X4)
                | ~ r2_hidden(X4,X1)
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            & r2_hidden(X3,X1)
            & r2_hidden(sK4(X0,X1),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ! [X4] :
              ( ~ r1_orders_2(X0,sK5(X0,X1),X4)
              | ~ r1_orders_2(X0,sK4(X0,X1),X4)
              | ~ r2_hidden(X4,X1)
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          & r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X1)
          & m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
          & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) ) )
      & ( ! [X5] :
            ( ! [X6] :
                ( ( r1_orders_2(X0,X6,sK6(X0,X1,X5,X6))
                  & r1_orders_2(X0,X5,sK6(X0,X1,X5,X6))
                  & r2_hidden(sK6(X0,X1,X5,X6),X1)
                  & m1_subset_1(sK6(X0,X1,X5,X6),u1_struct_0(X0)) )
                | ~ r2_hidden(X6,X1)
                | ~ r2_hidden(X5,X1)
                | ~ m1_subset_1(X6,u1_struct_0(X0)) )
            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f37,f40,f39,f38])).

fof(f67,plain,(
    ! [X6,X0,X5,X1] :
      ( r1_orders_2(X0,X6,sK6(X0,X1,X5,X6))
      | ~ r2_hidden(X6,X1)
      | ~ r2_hidden(X5,X1)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f66,plain,(
    ! [X6,X0,X5,X1] :
      ( r1_orders_2(X0,X5,sK6(X0,X1,X5,X6))
      | ~ r2_hidden(X6,X1)
      | ~ r2_hidden(X5,X1)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

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

fof(f12,plain,(
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

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f32,plain,(
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

fof(f31,plain,(
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

fof(f33,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f30,f32,f31])).

fof(f56,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r1_orders_2(X0,X5,X4)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v12_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f65,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(sK6(X0,X1,X5,X6),X1)
      | ~ r2_hidden(X6,X1)
      | ~ r2_hidden(X5,X1)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f89,plain,(
    ! [X4,X5] :
      ( r2_hidden(k13_lattice3(sK8,X4,X5),sK9)
      | ~ r2_hidden(X5,sK9)
      | ~ r2_hidden(X4,sK9)
      | ~ m1_subset_1(X5,u1_struct_0(sK8))
      | ~ m1_subset_1(X4,u1_struct_0(sK8))
      | v1_waybel_0(sK9,sK8) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f90,plain,
    ( m1_subset_1(sK10,u1_struct_0(sK8))
    | ~ v1_waybel_0(sK9,sK8) ),
    inference(cnf_transformation,[],[f54])).

fof(f91,plain,
    ( m1_subset_1(sK11,u1_struct_0(sK8))
    | ~ v1_waybel_0(sK9,sK8) ),
    inference(cnf_transformation,[],[f54])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f16])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f88,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(cnf_transformation,[],[f54])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f18])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f71,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f70,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | r2_hidden(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f69,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | m1_subset_1(sK5(X0,X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f68,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ( v1_waybel_0(X1,X0)
      <=> sP0(X0,X1) )
      | ~ sP1(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ( ( v1_waybel_0(X1,X0)
          | ~ sP0(X0,X1) )
        & ( sP0(X0,X1)
          | ~ v1_waybel_0(X1,X0) ) )
      | ~ sP1(X1,X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ( v1_waybel_0(X0,X1)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ v1_waybel_0(X0,X1) ) )
      | ~ sP1(X0,X1) ) ),
    inference(rectify,[],[f34])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_waybel_0(X0,X1)
      | ~ sP0(X1,X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ~ ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X0))
                           => ~ ( r1_orders_2(X0,X3,X4)
                                & r1_orders_2(X0,X2,X4)
                                & r2_hidden(X4,X1) ) )
                        & r2_hidden(X3,X1)
                        & r2_hidden(X2,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( ? [X4] :
                        ( r1_orders_2(X0,X3,X4)
                        & r1_orders_2(X0,X2,X4)
                        & r2_hidden(X4,X1)
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( ? [X4] :
                        ( r1_orders_2(X0,X3,X4)
                        & r1_orders_2(X0,X2,X4)
                        & r2_hidden(X4,X1)
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f14])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f15,f27,f26])).

fof(f73,plain,(
    ! [X0,X1] :
      ( sP1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X2,X3)
      | k13_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X2,k13_lattice3(X0,X1,X2))
      | ~ m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f77])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X1,X3)
      | k13_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,k13_lattice3(X0,X1,X2))
      | ~ m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f76])).

fof(f72,plain,(
    ! [X4,X0,X1] :
      ( sP0(X0,X1)
      | ~ r1_orders_2(X0,sK5(X0,X1),X4)
      | ~ r1_orders_2(X0,sK4(X0,X1),X4)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f62,plain,(
    ! [X0,X1] :
      ( sP0(X1,X0)
      | ~ v1_waybel_0(X0,X1)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f94,plain,
    ( ~ r2_hidden(k13_lattice3(sK8,sK10,sK11),sK9)
    | ~ v1_waybel_0(sK9,sK8) ),
    inference(cnf_transformation,[],[f54])).

fof(f93,plain,
    ( r2_hidden(sK11,sK9)
    | ~ v1_waybel_0(sK9,sK8) ),
    inference(cnf_transformation,[],[f54])).

fof(f92,plain,
    ( r2_hidden(sK10,sK9)
    | ~ v1_waybel_0(sK9,sK8) ),
    inference(cnf_transformation,[],[f54])).

fof(f87,plain,(
    v12_waybel_0(sK9,sK8) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_25,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,k13_lattice3(X0,X3,X1),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k13_lattice3(X0,X3,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_38,negated_conjecture,
    ( v1_lattice3(sK8) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_984,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,k13_lattice3(X0,X3,X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(k13_lattice3(X0,X3,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_38])).

cnf(c_985,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X2,X1)
    | r1_orders_2(sK8,k13_lattice3(sK8,X2,X0),X1)
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(k13_lattice3(sK8,X2,X0),u1_struct_0(sK8))
    | ~ v5_orders_2(sK8)
    | ~ l1_orders_2(sK8) ),
    inference(unflattening,[status(thm)],[c_984])).

cnf(c_39,negated_conjecture,
    ( v5_orders_2(sK8) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_37,negated_conjecture,
    ( l1_orders_2(sK8) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_989,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X2,X1)
    | r1_orders_2(sK8,k13_lattice3(sK8,X2,X0),X1)
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(k13_lattice3(sK8,X2,X0),u1_struct_0(sK8)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_985,c_39,c_37])).

cnf(c_990,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X2,X1)
    | r1_orders_2(sK8,k13_lattice3(sK8,X2,X0),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(k13_lattice3(sK8,X2,X0),u1_struct_0(sK8)) ),
    inference(renaming,[status(thm)],[c_989])).

cnf(c_4193,plain,
    ( ~ r1_orders_2(sK8,X0_53,X1_53)
    | ~ r1_orders_2(sK8,X2_53,X1_53)
    | r1_orders_2(sK8,k13_lattice3(sK8,X2_53,X0_53),X1_53)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK8))
    | ~ m1_subset_1(X2_53,u1_struct_0(sK8))
    | ~ m1_subset_1(k13_lattice3(sK8,X2_53,X0_53),u1_struct_0(sK8)) ),
    inference(subtyping,[status(esa)],[c_990])).

cnf(c_58744,plain,
    ( ~ r1_orders_2(sK8,X0_53,sK6(sK8,X1_53,X0_53,X2_53))
    | ~ r1_orders_2(sK8,X3_53,sK6(sK8,X1_53,X0_53,X2_53))
    | r1_orders_2(sK8,k13_lattice3(sK8,X3_53,X0_53),sK6(sK8,X1_53,X0_53,X2_53))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
    | ~ m1_subset_1(X3_53,u1_struct_0(sK8))
    | ~ m1_subset_1(sK6(sK8,X1_53,X0_53,X2_53),u1_struct_0(sK8))
    | ~ m1_subset_1(k13_lattice3(sK8,X3_53,X0_53),u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_4193])).

cnf(c_61329,plain,
    ( ~ r1_orders_2(sK8,X0_53,sK6(sK8,sK9,sK11,sK10))
    | r1_orders_2(sK8,k13_lattice3(sK8,X0_53,sK11),sK6(sK8,sK9,sK11,sK10))
    | ~ r1_orders_2(sK8,sK11,sK6(sK8,sK9,sK11,sK10))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
    | ~ m1_subset_1(sK6(sK8,sK9,sK11,sK10),u1_struct_0(sK8))
    | ~ m1_subset_1(k13_lattice3(sK8,X0_53,sK11),u1_struct_0(sK8))
    | ~ m1_subset_1(sK11,u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_58744])).

cnf(c_63682,plain,
    ( r1_orders_2(sK8,k13_lattice3(sK8,sK10,sK11),sK6(sK8,sK9,sK11,sK10))
    | ~ r1_orders_2(sK8,sK11,sK6(sK8,sK9,sK11,sK10))
    | ~ r1_orders_2(sK8,sK10,sK6(sK8,sK9,sK11,sK10))
    | ~ m1_subset_1(sK6(sK8,sK9,sK11,sK10),u1_struct_0(sK8))
    | ~ m1_subset_1(k13_lattice3(sK8,sK10,sK11),u1_struct_0(sK8))
    | ~ m1_subset_1(sK11,u1_struct_0(sK8))
    | ~ m1_subset_1(sK10,u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_61329])).

cnf(c_14,plain,
    ( r1_orders_2(X0,X1,sK6(X0,X2,X3,X1))
    | ~ sP0(X0,X2)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_4208,plain,
    ( r1_orders_2(X0_52,X0_53,sK6(X0_52,X1_53,X2_53,X0_53))
    | ~ sP0(X0_52,X1_53)
    | ~ r2_hidden(X0_53,X1_53)
    | ~ r2_hidden(X2_53,X1_53)
    | ~ m1_subset_1(X2_53,u1_struct_0(X0_52))
    | ~ m1_subset_1(X0_53,u1_struct_0(X0_52)) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_59200,plain,
    ( r1_orders_2(sK8,X0_53,sK6(sK8,X1_53,X2_53,X0_53))
    | ~ sP0(sK8,X1_53)
    | ~ r2_hidden(X0_53,X1_53)
    | ~ r2_hidden(X2_53,X1_53)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
    | ~ m1_subset_1(X2_53,u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_4208])).

cnf(c_60347,plain,
    ( r1_orders_2(sK8,sK10,sK6(sK8,sK9,X0_53,sK10))
    | ~ sP0(sK8,sK9)
    | ~ r2_hidden(X0_53,sK9)
    | ~ r2_hidden(sK10,sK9)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
    | ~ m1_subset_1(sK10,u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_59200])).

cnf(c_61218,plain,
    ( r1_orders_2(sK8,sK10,sK6(sK8,sK9,sK11,sK10))
    | ~ sP0(sK8,sK9)
    | ~ r2_hidden(sK11,sK9)
    | ~ r2_hidden(sK10,sK9)
    | ~ m1_subset_1(sK11,u1_struct_0(sK8))
    | ~ m1_subset_1(sK10,u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_60347])).

cnf(c_15,plain,
    ( r1_orders_2(X0,X1,sK6(X0,X2,X1,X3))
    | ~ sP0(X0,X2)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_4207,plain,
    ( r1_orders_2(X0_52,X0_53,sK6(X0_52,X1_53,X0_53,X2_53))
    | ~ sP0(X0_52,X1_53)
    | ~ r2_hidden(X0_53,X1_53)
    | ~ r2_hidden(X2_53,X1_53)
    | ~ m1_subset_1(X2_53,u1_struct_0(X0_52))
    | ~ m1_subset_1(X0_53,u1_struct_0(X0_52)) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_59188,plain,
    ( r1_orders_2(sK8,X0_53,sK6(sK8,X1_53,X0_53,X2_53))
    | ~ sP0(sK8,X1_53)
    | ~ r2_hidden(X0_53,X1_53)
    | ~ r2_hidden(X2_53,X1_53)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
    | ~ m1_subset_1(X2_53,u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_4207])).

cnf(c_60319,plain,
    ( r1_orders_2(sK8,sK11,sK6(sK8,sK9,sK11,X0_53))
    | ~ sP0(sK8,sK9)
    | ~ r2_hidden(X0_53,sK9)
    | ~ r2_hidden(sK11,sK9)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
    | ~ m1_subset_1(sK11,u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_59188])).

cnf(c_61156,plain,
    ( r1_orders_2(sK8,sK11,sK6(sK8,sK9,sK11,sK10))
    | ~ sP0(sK8,sK9)
    | ~ r2_hidden(sK11,sK9)
    | ~ r2_hidden(sK10,sK9)
    | ~ m1_subset_1(sK11,u1_struct_0(sK8))
    | ~ m1_subset_1(sK10,u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_60319])).

cnf(c_28,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_4204,plain,
    ( ~ r2_hidden(X0_53,X1_53)
    | m1_subset_1(X0_53,X0_54)
    | ~ m1_subset_1(X1_53,k1_zfmisc_1(X0_54)) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_4958,plain,
    ( ~ r2_hidden(X0_53,X1_53)
    | ~ m1_subset_1(X1_53,k1_zfmisc_1(u1_struct_0(sK8)))
    | m1_subset_1(X0_53,u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_4204])).

cnf(c_5403,plain,
    ( ~ r2_hidden(sK6(X0_52,X0_53,X1_53,X2_53),X0_53)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK8)))
    | m1_subset_1(sK6(X0_52,X0_53,X1_53,X2_53),u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_4958])).

cnf(c_25631,plain,
    ( ~ r2_hidden(sK6(X0_52,sK9,sK11,sK10),sK9)
    | m1_subset_1(sK6(X0_52,sK9,sK11,sK10),u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(instantiation,[status(thm)],[c_5403])).

cnf(c_25633,plain,
    ( ~ r2_hidden(sK6(sK8,sK9,sK11,sK10),sK9)
    | m1_subset_1(sK6(sK8,sK9,sK11,sK10),u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(instantiation,[status(thm)],[c_25631])).

cnf(c_6,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(X1,X3)
    | ~ v12_waybel_0(X3,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1245,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(X1,X3)
    | ~ v12_waybel_0(X3,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_37])).

cnf(c_1246,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r2_hidden(X1,X2)
    | r2_hidden(X0,X2)
    | ~ v12_waybel_0(X2,sK8)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8)) ),
    inference(unflattening,[status(thm)],[c_1245])).

cnf(c_1262,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r2_hidden(X1,X2)
    | r2_hidden(X0,X2)
    | ~ v12_waybel_0(X2,sK8)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ m1_subset_1(X0,u1_struct_0(sK8)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1246,c_28])).

cnf(c_4186,plain,
    ( ~ r1_orders_2(sK8,X0_53,X1_53)
    | ~ r2_hidden(X1_53,X2_53)
    | r2_hidden(X0_53,X2_53)
    | ~ v12_waybel_0(X2_53,sK8)
    | ~ m1_subset_1(X2_53,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK8)) ),
    inference(subtyping,[status(esa)],[c_1262])).

cnf(c_15453,plain,
    ( ~ r1_orders_2(sK8,k13_lattice3(sK8,sK10,sK11),X0_53)
    | ~ r2_hidden(X0_53,sK9)
    | r2_hidden(k13_lattice3(sK8,sK10,sK11),sK9)
    | ~ v12_waybel_0(sK9,sK8)
    | ~ m1_subset_1(k13_lattice3(sK8,sK10,sK11),u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(instantiation,[status(thm)],[c_4186])).

cnf(c_25612,plain,
    ( ~ r1_orders_2(sK8,k13_lattice3(sK8,sK10,sK11),sK6(X0_52,sK9,sK11,sK10))
    | ~ r2_hidden(sK6(X0_52,sK9,sK11,sK10),sK9)
    | r2_hidden(k13_lattice3(sK8,sK10,sK11),sK9)
    | ~ v12_waybel_0(sK9,sK8)
    | ~ m1_subset_1(k13_lattice3(sK8,sK10,sK11),u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(instantiation,[status(thm)],[c_15453])).

cnf(c_25614,plain,
    ( ~ r1_orders_2(sK8,k13_lattice3(sK8,sK10,sK11),sK6(sK8,sK9,sK11,sK10))
    | ~ r2_hidden(sK6(sK8,sK9,sK11,sK10),sK9)
    | r2_hidden(k13_lattice3(sK8,sK10,sK11),sK9)
    | ~ v12_waybel_0(sK9,sK8)
    | ~ m1_subset_1(k13_lattice3(sK8,sK10,sK11),u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(instantiation,[status(thm)],[c_25612])).

cnf(c_16,plain,
    ( ~ sP0(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X3,X1)
    | r2_hidden(sK6(X0,X1,X3,X2),X1)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_4206,plain,
    ( ~ sP0(X0_52,X0_53)
    | ~ r2_hidden(X1_53,X0_53)
    | ~ r2_hidden(X2_53,X0_53)
    | r2_hidden(sK6(X0_52,X0_53,X2_53,X1_53),X0_53)
    | ~ m1_subset_1(X2_53,u1_struct_0(X0_52))
    | ~ m1_subset_1(X1_53,u1_struct_0(X0_52)) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_10094,plain,
    ( ~ sP0(X0_52,sK9)
    | ~ r2_hidden(X0_53,sK9)
    | r2_hidden(sK6(X0_52,sK9,X0_53,sK10),sK9)
    | ~ r2_hidden(sK10,sK9)
    | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
    | ~ m1_subset_1(sK10,u1_struct_0(X0_52)) ),
    inference(instantiation,[status(thm)],[c_4206])).

cnf(c_23284,plain,
    ( ~ sP0(X0_52,sK9)
    | r2_hidden(sK6(X0_52,sK9,sK11,sK10),sK9)
    | ~ r2_hidden(sK11,sK9)
    | ~ r2_hidden(sK10,sK9)
    | ~ m1_subset_1(sK11,u1_struct_0(X0_52))
    | ~ m1_subset_1(sK10,u1_struct_0(X0_52)) ),
    inference(instantiation,[status(thm)],[c_10094])).

cnf(c_23286,plain,
    ( ~ sP0(sK8,sK9)
    | r2_hidden(sK6(sK8,sK9,sK11,sK10),sK9)
    | ~ r2_hidden(sK11,sK9)
    | ~ r2_hidden(sK10,sK9)
    | ~ m1_subset_1(sK11,u1_struct_0(sK8))
    | ~ m1_subset_1(sK10,u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_23284])).

cnf(c_34,negated_conjecture,
    ( v1_waybel_0(sK9,sK8)
    | ~ r2_hidden(X0,sK9)
    | ~ r2_hidden(X1,sK9)
    | r2_hidden(k13_lattice3(sK8,X1,X0),sK9)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_4198,negated_conjecture,
    ( v1_waybel_0(sK9,sK8)
    | ~ r2_hidden(X0_53,sK9)
    | ~ r2_hidden(X1_53,sK9)
    | r2_hidden(k13_lattice3(sK8,X1_53,X0_53),sK9)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK8)) ),
    inference(subtyping,[status(esa)],[c_34])).

cnf(c_4858,plain,
    ( v1_waybel_0(sK9,sK8) = iProver_top
    | r2_hidden(X0_53,sK9) != iProver_top
    | r2_hidden(X1_53,sK9) != iProver_top
    | r2_hidden(k13_lattice3(sK8,X1_53,X0_53),sK9) = iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4198])).

cnf(c_33,negated_conjecture,
    ( ~ v1_waybel_0(sK9,sK8)
    | m1_subset_1(sK10,u1_struct_0(sK8)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_4199,negated_conjecture,
    ( ~ v1_waybel_0(sK9,sK8)
    | m1_subset_1(sK10,u1_struct_0(sK8)) ),
    inference(subtyping,[status(esa)],[c_33])).

cnf(c_4857,plain,
    ( v1_waybel_0(sK9,sK8) != iProver_top
    | m1_subset_1(sK10,u1_struct_0(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4199])).

cnf(c_32,negated_conjecture,
    ( ~ v1_waybel_0(sK9,sK8)
    | m1_subset_1(sK11,u1_struct_0(sK8)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_4200,negated_conjecture,
    ( ~ v1_waybel_0(sK9,sK8)
    | m1_subset_1(sK11,u1_struct_0(sK8)) ),
    inference(subtyping,[status(esa)],[c_32])).

cnf(c_4856,plain,
    ( v1_waybel_0(sK9,sK8) != iProver_top
    | m1_subset_1(sK11,u1_struct_0(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4200])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k10_lattice3(X1,X2,X0),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1315,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k10_lattice3(X1,X2,X0),u1_struct_0(X1))
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_37])).

cnf(c_1316,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | m1_subset_1(k10_lattice3(sK8,X1,X0),u1_struct_0(sK8)) ),
    inference(unflattening,[status(thm)],[c_1315])).

cnf(c_4182,plain,
    ( ~ m1_subset_1(X0_53,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK8))
    | m1_subset_1(k10_lattice3(sK8,X1_53,X0_53),u1_struct_0(sK8)) ),
    inference(subtyping,[status(esa)],[c_1316])).

cnf(c_4874,plain,
    ( m1_subset_1(X0_53,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(k10_lattice3(sK8,X1_53,X0_53),u1_struct_0(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4182])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_4197,negated_conjecture,
    ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(subtyping,[status(esa)],[c_35])).

cnf(c_4859,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4197])).

cnf(c_4852,plain,
    ( r2_hidden(X0_53,X1_53) != iProver_top
    | m1_subset_1(X0_53,X0_54) = iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(X0_54)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4204])).

cnf(c_5754,plain,
    ( r2_hidden(X0_53,sK9) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4859,c_4852])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1)
    | k10_lattice3(X1,X2,X0) = k13_lattice3(X1,X2,X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1145,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k10_lattice3(X1,X2,X0) = k13_lattice3(X1,X2,X0)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_38])).

cnf(c_1146,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ v5_orders_2(sK8)
    | ~ l1_orders_2(sK8)
    | k10_lattice3(sK8,X1,X0) = k13_lattice3(sK8,X1,X0) ),
    inference(unflattening,[status(thm)],[c_1145])).

cnf(c_1150,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | k10_lattice3(sK8,X1,X0) = k13_lattice3(sK8,X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1146,c_39,c_37])).

cnf(c_4188,plain,
    ( ~ m1_subset_1(X0_53,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK8))
    | k10_lattice3(sK8,X1_53,X0_53) = k13_lattice3(sK8,X1_53,X0_53) ),
    inference(subtyping,[status(esa)],[c_1150])).

cnf(c_4868,plain,
    ( k10_lattice3(sK8,X0_53,X1_53) = k13_lattice3(sK8,X0_53,X1_53)
    | m1_subset_1(X1_53,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4188])).

cnf(c_6158,plain,
    ( k10_lattice3(sK8,X0_53,X1_53) = k13_lattice3(sK8,X0_53,X1_53)
    | r2_hidden(X0_53,sK9) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5754,c_4868])).

cnf(c_9984,plain,
    ( k10_lattice3(sK8,X0_53,k10_lattice3(sK8,X1_53,X2_53)) = k13_lattice3(sK8,X0_53,k10_lattice3(sK8,X1_53,X2_53))
    | r2_hidden(X0_53,sK9) != iProver_top
    | m1_subset_1(X2_53,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4874,c_6158])).

cnf(c_20896,plain,
    ( k10_lattice3(sK8,X0_53,k10_lattice3(sK8,sK11,X1_53)) = k13_lattice3(sK8,X0_53,k10_lattice3(sK8,sK11,X1_53))
    | v1_waybel_0(sK9,sK8) != iProver_top
    | r2_hidden(X0_53,sK9) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4856,c_9984])).

cnf(c_21112,plain,
    ( k10_lattice3(sK8,X0_53,k10_lattice3(sK8,sK11,sK10)) = k13_lattice3(sK8,X0_53,k10_lattice3(sK8,sK11,sK10))
    | v1_waybel_0(sK9,sK8) != iProver_top
    | r2_hidden(X0_53,sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_4857,c_20896])).

cnf(c_44,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_10,plain,
    ( sP0(X0,X1)
    | r2_hidden(sK5(X0,X1),X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_4212,plain,
    ( sP0(X0_52,X0_53)
    | r2_hidden(sK5(X0_52,X0_53),X0_53) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_4234,plain,
    ( sP0(X0_52,X0_53) = iProver_top
    | r2_hidden(sK5(X0_52,X0_53),X0_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4212])).

cnf(c_4236,plain,
    ( sP0(sK8,sK9) = iProver_top
    | r2_hidden(sK5(sK8,sK9),sK9) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4234])).

cnf(c_11,plain,
    ( sP0(X0,X1)
    | r2_hidden(sK4(X0,X1),X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_4211,plain,
    ( sP0(X0_52,X0_53)
    | r2_hidden(sK4(X0_52,X0_53),X0_53) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_4237,plain,
    ( sP0(X0_52,X0_53) = iProver_top
    | r2_hidden(sK4(X0_52,X0_53),X0_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4211])).

cnf(c_4239,plain,
    ( sP0(sK8,sK9) = iProver_top
    | r2_hidden(sK4(sK8,sK9),sK9) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4237])).

cnf(c_12,plain,
    ( sP0(X0,X1)
    | m1_subset_1(sK5(X0,X1),u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_4210,plain,
    ( sP0(X0_52,X0_53)
    | m1_subset_1(sK5(X0_52,X0_53),u1_struct_0(X0_52)) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_4240,plain,
    ( sP0(X0_52,X0_53) = iProver_top
    | m1_subset_1(sK5(X0_52,X0_53),u1_struct_0(X0_52)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4210])).

cnf(c_4242,plain,
    ( sP0(sK8,sK9) = iProver_top
    | m1_subset_1(sK5(sK8,sK9),u1_struct_0(sK8)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4240])).

cnf(c_13,plain,
    ( sP0(X0,X1)
    | m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_4209,plain,
    ( sP0(X0_52,X0_53)
    | m1_subset_1(sK4(X0_52,X0_53),u1_struct_0(X0_52)) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_4243,plain,
    ( sP0(X0_52,X0_53) = iProver_top
    | m1_subset_1(sK4(X0_52,X0_53),u1_struct_0(X0_52)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4209])).

cnf(c_4245,plain,
    ( sP0(sK8,sK9) = iProver_top
    | m1_subset_1(sK4(sK8,sK9),u1_struct_0(sK8)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4243])).

cnf(c_7,plain,
    ( ~ sP1(X0,X1)
    | ~ sP0(X1,X0)
    | v1_waybel_0(X0,X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_18,plain,
    ( sP1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1330,plain,
    ( sP1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_37])).

cnf(c_1331,plain,
    ( sP1(X0,sK8)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(unflattening,[status(thm)],[c_1330])).

cnf(c_1421,plain,
    ( ~ sP0(X0,X1)
    | v1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK8)))
    | X2 != X1
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_1331])).

cnf(c_1422,plain,
    ( ~ sP0(sK8,X0)
    | v1_waybel_0(X0,sK8)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(unflattening,[status(thm)],[c_1421])).

cnf(c_4178,plain,
    ( ~ sP0(sK8,X0_53)
    | v1_waybel_0(X0_53,sK8)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(subtyping,[status(esa)],[c_1422])).

cnf(c_4304,plain,
    ( sP0(sK8,X0_53) != iProver_top
    | v1_waybel_0(X0_53,sK8) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4178])).

cnf(c_4306,plain,
    ( sP0(sK8,sK9) != iProver_top
    | v1_waybel_0(sK9,sK8) = iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4304])).

cnf(c_6100,plain,
    ( v1_waybel_0(sK9,sK8)
    | ~ r2_hidden(X0_53,sK9)
    | r2_hidden(k13_lattice3(sK8,X0_53,sK4(sK8,sK9)),sK9)
    | ~ r2_hidden(sK4(sK8,sK9),sK9)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
    | ~ m1_subset_1(sK4(sK8,sK9),u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_4198])).

cnf(c_6407,plain,
    ( v1_waybel_0(sK9,sK8)
    | r2_hidden(k13_lattice3(sK8,sK5(sK8,sK9),sK4(sK8,sK9)),sK9)
    | ~ r2_hidden(sK4(sK8,sK9),sK9)
    | ~ r2_hidden(sK5(sK8,sK9),sK9)
    | ~ m1_subset_1(sK4(sK8,sK9),u1_struct_0(sK8))
    | ~ m1_subset_1(sK5(sK8,sK9),u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_6100])).

cnf(c_6408,plain,
    ( v1_waybel_0(sK9,sK8) = iProver_top
    | r2_hidden(k13_lattice3(sK8,sK5(sK8,sK9),sK4(sK8,sK9)),sK9) = iProver_top
    | r2_hidden(sK4(sK8,sK9),sK9) != iProver_top
    | r2_hidden(sK5(sK8,sK9),sK9) != iProver_top
    | m1_subset_1(sK4(sK8,sK9),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK5(sK8,sK9),u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6407])).

cnf(c_26,plain,
    ( r1_orders_2(X0,X1,k13_lattice3(X0,X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k13_lattice3(X0,X2,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_964,plain,
    ( r1_orders_2(X0,X1,k13_lattice3(X0,X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k13_lattice3(X0,X2,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_38])).

cnf(c_965,plain,
    ( r1_orders_2(sK8,X0,k13_lattice3(sK8,X1,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(k13_lattice3(sK8,X1,X0),u1_struct_0(sK8))
    | ~ v5_orders_2(sK8)
    | ~ l1_orders_2(sK8) ),
    inference(unflattening,[status(thm)],[c_964])).

cnf(c_967,plain,
    ( r1_orders_2(sK8,X0,k13_lattice3(sK8,X1,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(k13_lattice3(sK8,X1,X0),u1_struct_0(sK8)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_965,c_39,c_37])).

cnf(c_4194,plain,
    ( r1_orders_2(sK8,X0_53,k13_lattice3(sK8,X1_53,X0_53))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK8))
    | ~ m1_subset_1(k13_lattice3(sK8,X1_53,X0_53),u1_struct_0(sK8)) ),
    inference(subtyping,[status(esa)],[c_967])).

cnf(c_5811,plain,
    ( r1_orders_2(sK8,sK4(sK8,X0_53),k13_lattice3(sK8,X1_53,sK4(sK8,X0_53)))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK8))
    | ~ m1_subset_1(k13_lattice3(sK8,X1_53,sK4(sK8,X0_53)),u1_struct_0(sK8))
    | ~ m1_subset_1(sK4(sK8,X0_53),u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_4194])).

cnf(c_6620,plain,
    ( r1_orders_2(sK8,sK4(sK8,X0_53),k13_lattice3(sK8,sK5(sK8,X1_53),sK4(sK8,X0_53)))
    | ~ m1_subset_1(k13_lattice3(sK8,sK5(sK8,X1_53),sK4(sK8,X0_53)),u1_struct_0(sK8))
    | ~ m1_subset_1(sK4(sK8,X0_53),u1_struct_0(sK8))
    | ~ m1_subset_1(sK5(sK8,X1_53),u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_5811])).

cnf(c_6621,plain,
    ( r1_orders_2(sK8,sK4(sK8,X0_53),k13_lattice3(sK8,sK5(sK8,X1_53),sK4(sK8,X0_53))) = iProver_top
    | m1_subset_1(k13_lattice3(sK8,sK5(sK8,X1_53),sK4(sK8,X0_53)),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK4(sK8,X0_53),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK5(sK8,X1_53),u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6620])).

cnf(c_6623,plain,
    ( r1_orders_2(sK8,sK4(sK8,sK9),k13_lattice3(sK8,sK5(sK8,sK9),sK4(sK8,sK9))) = iProver_top
    | m1_subset_1(k13_lattice3(sK8,sK5(sK8,sK9),sK4(sK8,sK9)),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK4(sK8,sK9),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK5(sK8,sK9),u1_struct_0(sK8)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6621])).

cnf(c_27,plain,
    ( r1_orders_2(X0,X1,k13_lattice3(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_940,plain,
    ( r1_orders_2(X0,X1,k13_lattice3(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_38])).

cnf(c_941,plain,
    ( r1_orders_2(sK8,X0,k13_lattice3(sK8,X0,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(k13_lattice3(sK8,X0,X1),u1_struct_0(sK8))
    | ~ v5_orders_2(sK8)
    | ~ l1_orders_2(sK8) ),
    inference(unflattening,[status(thm)],[c_940])).

cnf(c_945,plain,
    ( r1_orders_2(sK8,X0,k13_lattice3(sK8,X0,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(k13_lattice3(sK8,X0,X1),u1_struct_0(sK8)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_941,c_39,c_37])).

cnf(c_4195,plain,
    ( r1_orders_2(sK8,X0_53,k13_lattice3(sK8,X0_53,X1_53))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK8))
    | ~ m1_subset_1(k13_lattice3(sK8,X0_53,X1_53),u1_struct_0(sK8)) ),
    inference(subtyping,[status(esa)],[c_945])).

cnf(c_5950,plain,
    ( r1_orders_2(sK8,sK5(sK8,X0_53),k13_lattice3(sK8,sK5(sK8,X0_53),X1_53))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK8))
    | ~ m1_subset_1(k13_lattice3(sK8,sK5(sK8,X0_53),X1_53),u1_struct_0(sK8))
    | ~ m1_subset_1(sK5(sK8,X0_53),u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_4195])).

cnf(c_6638,plain,
    ( r1_orders_2(sK8,sK5(sK8,X0_53),k13_lattice3(sK8,sK5(sK8,X0_53),sK4(sK8,X1_53)))
    | ~ m1_subset_1(k13_lattice3(sK8,sK5(sK8,X0_53),sK4(sK8,X1_53)),u1_struct_0(sK8))
    | ~ m1_subset_1(sK4(sK8,X1_53),u1_struct_0(sK8))
    | ~ m1_subset_1(sK5(sK8,X0_53),u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_5950])).

cnf(c_6639,plain,
    ( r1_orders_2(sK8,sK5(sK8,X0_53),k13_lattice3(sK8,sK5(sK8,X0_53),sK4(sK8,X1_53))) = iProver_top
    | m1_subset_1(k13_lattice3(sK8,sK5(sK8,X0_53),sK4(sK8,X1_53)),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK4(sK8,X1_53),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK5(sK8,X0_53),u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6638])).

cnf(c_6641,plain,
    ( r1_orders_2(sK8,sK5(sK8,sK9),k13_lattice3(sK8,sK5(sK8,sK9),sK4(sK8,sK9))) = iProver_top
    | m1_subset_1(k13_lattice3(sK8,sK5(sK8,sK9),sK4(sK8,sK9)),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK4(sK8,sK9),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK5(sK8,sK9),u1_struct_0(sK8)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6639])).

cnf(c_7492,plain,
    ( ~ r2_hidden(k13_lattice3(sK8,sK5(sK8,sK9),sK4(sK8,sK9)),sK9)
    | m1_subset_1(k13_lattice3(sK8,sK5(sK8,sK9),sK4(sK8,sK9)),u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(instantiation,[status(thm)],[c_4958])).

cnf(c_7493,plain,
    ( r2_hidden(k13_lattice3(sK8,sK5(sK8,sK9),sK4(sK8,sK9)),sK9) != iProver_top
    | m1_subset_1(k13_lattice3(sK8,sK5(sK8,sK9),sK4(sK8,sK9)),u1_struct_0(sK8)) = iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7492])).

cnf(c_9,plain,
    ( ~ r1_orders_2(X0,sK4(X0,X1),X2)
    | ~ r1_orders_2(X0,sK5(X0,X1),X2)
    | sP0(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_4213,plain,
    ( ~ r1_orders_2(X0_52,sK4(X0_52,X0_53),X1_53)
    | ~ r1_orders_2(X0_52,sK5(X0_52,X0_53),X1_53)
    | sP0(X0_52,X0_53)
    | ~ r2_hidden(X1_53,X0_53)
    | ~ m1_subset_1(X1_53,u1_struct_0(X0_52)) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_5552,plain,
    ( ~ r1_orders_2(sK8,sK4(sK8,X0_53),X1_53)
    | ~ r1_orders_2(sK8,sK5(sK8,X0_53),X1_53)
    | sP0(sK8,X0_53)
    | ~ r2_hidden(X1_53,X0_53)
    | ~ m1_subset_1(X1_53,u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_4213])).

cnf(c_21159,plain,
    ( ~ r1_orders_2(sK8,sK4(sK8,X0_53),k13_lattice3(sK8,sK5(sK8,X1_53),sK4(sK8,X0_53)))
    | ~ r1_orders_2(sK8,sK5(sK8,X0_53),k13_lattice3(sK8,sK5(sK8,X1_53),sK4(sK8,X0_53)))
    | sP0(sK8,X0_53)
    | ~ r2_hidden(k13_lattice3(sK8,sK5(sK8,X1_53),sK4(sK8,X0_53)),X0_53)
    | ~ m1_subset_1(k13_lattice3(sK8,sK5(sK8,X1_53),sK4(sK8,X0_53)),u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_5552])).

cnf(c_21160,plain,
    ( r1_orders_2(sK8,sK4(sK8,X0_53),k13_lattice3(sK8,sK5(sK8,X1_53),sK4(sK8,X0_53))) != iProver_top
    | r1_orders_2(sK8,sK5(sK8,X0_53),k13_lattice3(sK8,sK5(sK8,X1_53),sK4(sK8,X0_53))) != iProver_top
    | sP0(sK8,X0_53) = iProver_top
    | r2_hidden(k13_lattice3(sK8,sK5(sK8,X1_53),sK4(sK8,X0_53)),X0_53) != iProver_top
    | m1_subset_1(k13_lattice3(sK8,sK5(sK8,X1_53),sK4(sK8,X0_53)),u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21159])).

cnf(c_21162,plain,
    ( r1_orders_2(sK8,sK4(sK8,sK9),k13_lattice3(sK8,sK5(sK8,sK9),sK4(sK8,sK9))) != iProver_top
    | r1_orders_2(sK8,sK5(sK8,sK9),k13_lattice3(sK8,sK5(sK8,sK9),sK4(sK8,sK9))) != iProver_top
    | sP0(sK8,sK9) = iProver_top
    | r2_hidden(k13_lattice3(sK8,sK5(sK8,sK9),sK4(sK8,sK9)),sK9) != iProver_top
    | m1_subset_1(k13_lattice3(sK8,sK5(sK8,sK9),sK4(sK8,sK9)),u1_struct_0(sK8)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_21160])).

cnf(c_21317,plain,
    ( k10_lattice3(sK8,X0_53,k10_lattice3(sK8,sK11,sK10)) = k13_lattice3(sK8,X0_53,k10_lattice3(sK8,sK11,sK10))
    | r2_hidden(X0_53,sK9) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_21112,c_44,c_4236,c_4239,c_4242,c_4245,c_4306,c_6408,c_6623,c_6641,c_7493,c_21162])).

cnf(c_21323,plain,
    ( k10_lattice3(sK8,k13_lattice3(sK8,X0_53,X1_53),k10_lattice3(sK8,sK11,sK10)) = k13_lattice3(sK8,k13_lattice3(sK8,X0_53,X1_53),k10_lattice3(sK8,sK11,sK10))
    | v1_waybel_0(sK9,sK8) = iProver_top
    | r2_hidden(X1_53,sK9) != iProver_top
    | r2_hidden(X0_53,sK9) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4858,c_21317])).

cnf(c_21698,plain,
    ( v1_waybel_0(sK9,sK8) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_21323,c_44,c_4236,c_4239,c_4242,c_4245,c_4306,c_6408,c_6623,c_6641,c_7493,c_21162])).

cnf(c_5584,plain,
    ( k10_lattice3(sK8,sK10,X0_53) = k13_lattice3(sK8,sK10,X0_53)
    | v1_waybel_0(sK9,sK8) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4857,c_4868])).

cnf(c_5669,plain,
    ( k10_lattice3(sK8,sK10,sK11) = k13_lattice3(sK8,sK10,sK11)
    | v1_waybel_0(sK9,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_4856,c_5584])).

cnf(c_21796,plain,
    ( k10_lattice3(sK8,sK10,sK11) = k13_lattice3(sK8,sK10,sK11) ),
    inference(superposition,[status(thm)],[c_21698,c_5669])).

cnf(c_22639,plain,
    ( m1_subset_1(k13_lattice3(sK8,sK10,sK11),u1_struct_0(sK8)) = iProver_top
    | m1_subset_1(sK11,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK10,u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_21796,c_4874])).

cnf(c_22640,plain,
    ( m1_subset_1(k13_lattice3(sK8,sK10,sK11),u1_struct_0(sK8))
    | ~ m1_subset_1(sK11,u1_struct_0(sK8))
    | ~ m1_subset_1(sK10,u1_struct_0(sK8)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_22639])).

cnf(c_21700,plain,
    ( v1_waybel_0(sK9,sK8) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_21698])).

cnf(c_8,plain,
    ( ~ sP1(X0,X1)
    | sP0(X1,X0)
    | ~ v1_waybel_0(X0,X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1406,plain,
    ( sP0(X0,X1)
    | ~ v1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK8)))
    | X2 != X1
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_1331])).

cnf(c_1407,plain,
    ( sP0(sK8,X0)
    | ~ v1_waybel_0(X0,sK8)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(unflattening,[status(thm)],[c_1406])).

cnf(c_4179,plain,
    ( sP0(sK8,X0_53)
    | ~ v1_waybel_0(X0_53,sK8)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(subtyping,[status(esa)],[c_1407])).

cnf(c_4302,plain,
    ( sP0(sK8,sK9)
    | ~ v1_waybel_0(sK9,sK8)
    | ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(instantiation,[status(thm)],[c_4179])).

cnf(c_29,negated_conjecture,
    ( ~ v1_waybel_0(sK9,sK8)
    | ~ r2_hidden(k13_lattice3(sK8,sK10,sK11),sK9) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_30,negated_conjecture,
    ( ~ v1_waybel_0(sK9,sK8)
    | r2_hidden(sK11,sK9) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_31,negated_conjecture,
    ( ~ v1_waybel_0(sK9,sK8)
    | r2_hidden(sK10,sK9) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_36,negated_conjecture,
    ( v12_waybel_0(sK9,sK8) ),
    inference(cnf_transformation,[],[f87])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_63682,c_61218,c_61156,c_25633,c_25614,c_23286,c_22640,c_21700,c_4302,c_29,c_30,c_31,c_32,c_33,c_35,c_36])).


%------------------------------------------------------------------------------
