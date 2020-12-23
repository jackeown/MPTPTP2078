%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1979+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:58 EST 2020

% Result     : Theorem 1.59s
% Output     : CNFRefutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :  226 (2004 expanded)
%              Number of clauses        :  133 ( 395 expanded)
%              Number of leaves         :   20 ( 649 expanded)
%              Depth                    :   18
%              Number of atoms          : 1631 (29544 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   23 (   8 average)
%              Maximal clause size      :   40 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f11])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f51,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f51])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k6_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k6_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k6_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k6_waybel_0(X0,X1))
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( r1_orders_2(X0,X1,X2)
                  | ~ r2_hidden(X2,k6_waybel_0(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r2_hidden(X2,k6_waybel_0(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f16])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f17])).

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

fof(f18,plain,(
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

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f19])).

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
    inference(rectify,[],[f41])).

fof(f44,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & r1_orders_2(X0,X3,X2)
          & r2_hidden(X2,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r1_orders_2(X0,sK1(X0,X1),X2)
        & r2_hidden(X2,X1)
        & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
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
            & r1_orders_2(X0,X3,sK0(X0,X1))
            & r2_hidden(sK0(X0,X1),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v12_waybel_0(X1,X0)
              | ( ~ r2_hidden(sK1(X0,X1),X1)
                & r1_orders_2(X0,sK1(X0,X1),sK0(X0,X1))
                & r2_hidden(sK0(X0,X1),X1)
                & m1_subset_1(sK1(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f42,f44,f43])).

fof(f58,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r1_orders_2(X0,X5,X4)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v12_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f37])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f13,conjecture,(
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

fof(f14,negated_conjecture,(
    ~ ! [X0] :
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
    inference(negated_conjecture,[],[f13])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( r2_hidden(X2,X3)
                  | ~ r1_tarski(X1,X3)
                  | ~ v1_waybel_7(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  | ~ v12_waybel_0(X3,X0)
                  | ~ v1_waybel_0(X3,X0)
                  | v1_xboole_0(X3) )
              & ~ r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v12_waybel_0(X1,X0)
          & v1_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v2_waybel_1(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( r2_hidden(X2,X3)
                  | ~ r1_tarski(X1,X3)
                  | ~ v1_waybel_7(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  | ~ v12_waybel_0(X3,X0)
                  | ~ v1_waybel_0(X3,X0)
                  | v1_xboole_0(X3) )
              & ~ r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v12_waybel_0(X1,X0)
          & v1_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v2_waybel_1(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f39])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( r2_hidden(X2,X3)
              | ~ r1_tarski(X1,X3)
              | ~ v1_waybel_7(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v12_waybel_0(X3,X0)
              | ~ v1_waybel_0(X3,X0)
              | v1_xboole_0(X3) )
          & ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ! [X3] :
            ( r2_hidden(sK6,X3)
            | ~ r1_tarski(X1,X3)
            | ~ v1_waybel_7(X3,X0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v12_waybel_0(X3,X0)
            | ~ v1_waybel_0(X3,X0)
            | v1_xboole_0(X3) )
        & ~ r2_hidden(sK6,X1)
        & m1_subset_1(sK6,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( r2_hidden(X2,X3)
                  | ~ r1_tarski(X1,X3)
                  | ~ v1_waybel_7(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  | ~ v12_waybel_0(X3,X0)
                  | ~ v1_waybel_0(X3,X0)
                  | v1_xboole_0(X3) )
              & ~ r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v12_waybel_0(X1,X0)
          & v1_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
     => ( ? [X2] :
            ( ! [X3] :
                ( r2_hidden(X2,X3)
                | ~ r1_tarski(sK5,X3)
                | ~ v1_waybel_7(X3,X0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                | ~ v12_waybel_0(X3,X0)
                | ~ v1_waybel_0(X3,X0)
                | v1_xboole_0(X3) )
            & ~ r2_hidden(X2,sK5)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
        & v12_waybel_0(sK5,X0)
        & v1_waybel_0(sK5,X0)
        & ~ v1_xboole_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ! [X3] :
                    ( r2_hidden(X2,X3)
                    | ~ r1_tarski(X1,X3)
                    | ~ v1_waybel_7(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                    | ~ v12_waybel_0(X3,X0)
                    | ~ v1_waybel_0(X3,X0)
                    | v1_xboole_0(X3) )
                & ~ r2_hidden(X2,X1)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v12_waybel_0(X1,X0)
            & v1_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v2_waybel_1(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( r2_hidden(X2,X3)
                  | ~ r1_tarski(X1,X3)
                  | ~ v1_waybel_7(X3,sK4)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))
                  | ~ v12_waybel_0(X3,sK4)
                  | ~ v1_waybel_0(X3,sK4)
                  | v1_xboole_0(X3) )
              & ~ r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(sK4)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
          & v12_waybel_0(X1,sK4)
          & v1_waybel_0(X1,sK4)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(sK4)
      & v2_lattice3(sK4)
      & v1_lattice3(sK4)
      & v2_waybel_1(sK4)
      & v5_orders_2(sK4)
      & v4_orders_2(sK4)
      & v3_orders_2(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
    ( ! [X3] :
        ( r2_hidden(sK6,X3)
        | ~ r1_tarski(sK5,X3)
        | ~ v1_waybel_7(X3,sK4)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))
        | ~ v12_waybel_0(X3,sK4)
        | ~ v1_waybel_0(X3,sK4)
        | v1_xboole_0(X3) )
    & ~ r2_hidden(sK6,sK5)
    & m1_subset_1(sK6,u1_struct_0(sK4))
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    & v12_waybel_0(sK5,sK4)
    & v1_waybel_0(sK5,sK4)
    & ~ v1_xboole_0(sK5)
    & l1_orders_2(sK4)
    & v2_lattice3(sK4)
    & v1_lattice3(sK4)
    & v2_waybel_1(sK4)
    & v5_orders_2(sK4)
    & v4_orders_2(sK4)
    & v3_orders_2(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f40,f55,f54,f53])).

fof(f91,plain,(
    v2_lattice3(sK4) ),
    inference(cnf_transformation,[],[f56])).

fof(f92,plain,(
    l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f56])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k6_waybel_0(X0,X1))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r3_orders_2(X0,X1,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f86,plain,(
    v3_orders_2(sK4) ),
    inference(cnf_transformation,[],[f56])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_subset_1(X0,X1)
      | ~ r1_xboole_0(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f10,axiom,(
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
              ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & v13_waybel_0(X2,X0)
                & v2_waybel_0(X2,X0)
                & ~ v1_xboole_0(X2) )
             => ~ ( ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                        & v12_waybel_0(X3,X0)
                        & v1_waybel_0(X3,X0)
                        & ~ v1_xboole_0(X3) )
                     => ~ ( r1_subset_1(X3,X2)
                          & r1_tarski(X1,X3)
                          & v1_waybel_7(X3,X0) ) )
                  & r1_subset_1(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( r1_subset_1(X3,X2)
                  & r1_tarski(X1,X3)
                  & v1_waybel_7(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  & v12_waybel_0(X3,X0)
                  & v1_waybel_0(X3,X0)
                  & ~ v1_xboole_0(X3) )
              | ~ r1_subset_1(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v13_waybel_0(X2,X0)
              | ~ v2_waybel_0(X2,X0)
              | v1_xboole_0(X2) )
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
    inference(ennf_transformation,[],[f10])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( r1_subset_1(X3,X2)
                  & r1_tarski(X1,X3)
                  & v1_waybel_7(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  & v12_waybel_0(X3,X0)
                  & v1_waybel_0(X3,X0)
                  & ~ v1_xboole_0(X3) )
              | ~ r1_subset_1(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v13_waybel_0(X2,X0)
              | ~ v2_waybel_0(X2,X0)
              | v1_xboole_0(X2) )
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
    inference(flattening,[],[f34])).

fof(f49,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r1_subset_1(X3,X2)
          & r1_tarski(X1,X3)
          & v1_waybel_7(X3,X0)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
          & v12_waybel_0(X3,X0)
          & v1_waybel_0(X3,X0)
          & ~ v1_xboole_0(X3) )
     => ( r1_subset_1(sK2(X0,X1,X2),X2)
        & r1_tarski(X1,sK2(X0,X1,X2))
        & v1_waybel_7(sK2(X0,X1,X2),X0)
        & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
        & v12_waybel_0(sK2(X0,X1,X2),X0)
        & v1_waybel_0(sK2(X0,X1,X2),X0)
        & ~ v1_xboole_0(sK2(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_subset_1(sK2(X0,X1,X2),X2)
                & r1_tarski(X1,sK2(X0,X1,X2))
                & v1_waybel_7(sK2(X0,X1,X2),X0)
                & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                & v12_waybel_0(sK2(X0,X1,X2),X0)
                & v1_waybel_0(sK2(X0,X1,X2),X0)
                & ~ v1_xboole_0(sK2(X0,X1,X2)) )
              | ~ r1_subset_1(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v13_waybel_0(X2,X0)
              | ~ v2_waybel_0(X2,X0)
              | v1_xboole_0(X2) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f35,f49])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( r1_subset_1(sK2(X0,X1,X2),X2)
      | ~ r1_subset_1(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X2,X0)
      | ~ v2_waybel_0(X2,X0)
      | v1_xboole_0(X2)
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
    inference(cnf_transformation,[],[f50])).

fof(f90,plain,(
    v1_lattice3(sK4) ),
    inference(cnf_transformation,[],[f56])).

fof(f87,plain,(
    v4_orders_2(sK4) ),
    inference(cnf_transformation,[],[f56])).

fof(f88,plain,(
    v5_orders_2(sK4) ),
    inference(cnf_transformation,[],[f56])).

fof(f89,plain,(
    v2_waybel_1(sK4) ),
    inference(cnf_transformation,[],[f56])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v4_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => v13_waybel_0(k6_waybel_0(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( v13_waybel_0(k6_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v13_waybel_0(k6_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v13_waybel_0(k6_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_waybel_0(k6_waybel_0(X0,X1),X0)
        & ~ v1_xboole_0(k6_waybel_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v2_waybel_0(k6_waybel_0(X0,X1),X0)
        & ~ v1_xboole_0(k6_waybel_0(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v2_waybel_0(k6_waybel_0(X0,X1),X0)
        & ~ v1_xboole_0(k6_waybel_0(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k6_waybel_0(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k6_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v2_waybel_0(k6_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_subset_1(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X2,X0)
      | ~ v2_waybel_0(X2,X0)
      | v1_xboole_0(X2)
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
    inference(cnf_transformation,[],[f50])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v12_waybel_0(sK2(X0,X1,X2),X0)
      | ~ r1_subset_1(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X2,X0)
      | ~ v2_waybel_0(X2,X0)
      | v1_xboole_0(X2)
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
    inference(cnf_transformation,[],[f50])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( v1_waybel_0(sK2(X0,X1,X2),X0)
      | ~ r1_subset_1(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X2,X0)
      | ~ v2_waybel_0(X2,X0)
      | v1_xboole_0(X2)
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
    inference(cnf_transformation,[],[f50])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(sK2(X0,X1,X2))
      | ~ r1_subset_1(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X2,X0)
      | ~ v2_waybel_0(X2,X0)
      | v1_xboole_0(X2)
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
    inference(cnf_transformation,[],[f50])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,sK2(X0,X1,X2))
      | ~ r1_subset_1(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X2,X0)
      | ~ v2_waybel_0(X2,X0)
      | v1_xboole_0(X2)
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
    inference(cnf_transformation,[],[f50])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( v1_waybel_7(sK2(X0,X1,X2),X0)
      | ~ r1_subset_1(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X2,X0)
      | ~ v2_waybel_0(X2,X0)
      | v1_xboole_0(X2)
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
    inference(cnf_transformation,[],[f50])).

fof(f99,plain,(
    ! [X3] :
      ( r2_hidden(sK6,X3)
      | ~ r1_tarski(sK5,X3)
      | ~ v1_waybel_7(X3,sK4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))
      | ~ v12_waybel_0(X3,sK4)
      | ~ v1_waybel_0(X3,sK4)
      | v1_xboole_0(X3) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f93,plain,(
    ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f56])).

fof(f94,plain,(
    v1_waybel_0(sK5,sK4) ),
    inference(cnf_transformation,[],[f56])).

fof(f95,plain,(
    v12_waybel_0(sK5,sK4) ),
    inference(cnf_transformation,[],[f56])).

fof(f96,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f56])).

fof(f98,plain,(
    ~ r2_hidden(sK6,sK5) ),
    inference(cnf_transformation,[],[f56])).

fof(f97,plain,(
    m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_12,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_subset_1(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2130,plain,
    ( r1_xboole_0(X0_59,X1_59)
    | ~ r1_subset_1(X0_59,X1_59)
    | v1_xboole_0(X0_59)
    | v1_xboole_0(X1_59) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_2358,plain,
    ( r1_xboole_0(X0_59,k6_waybel_0(sK4,sK6))
    | ~ r1_subset_1(X0_59,k6_waybel_0(sK4,sK6))
    | v1_xboole_0(X0_59)
    | v1_xboole_0(k6_waybel_0(sK4,sK6)) ),
    inference(instantiation,[status(thm)],[c_2130])).

cnf(c_2692,plain,
    ( r1_xboole_0(sK2(sK4,sK5,k6_waybel_0(sK4,sK6)),k6_waybel_0(sK4,sK6))
    | ~ r1_subset_1(sK2(sK4,sK5,k6_waybel_0(sK4,sK6)),k6_waybel_0(sK4,sK6))
    | v1_xboole_0(sK2(sK4,sK5,k6_waybel_0(sK4,sK6)))
    | v1_xboole_0(k6_waybel_0(sK4,sK6)) ),
    inference(instantiation,[status(thm)],[c_2358])).

cnf(c_25,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2129,plain,
    ( ~ r1_xboole_0(X0_59,X1_59)
    | ~ r2_hidden(X2_59,X0_59)
    | ~ r2_hidden(X2_59,X1_59) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_2444,plain,
    ( ~ r1_xboole_0(sK2(sK4,sK5,k6_waybel_0(sK4,sK6)),X0_59)
    | ~ r2_hidden(sK6,X0_59)
    | ~ r2_hidden(sK6,sK2(sK4,sK5,k6_waybel_0(sK4,sK6))) ),
    inference(instantiation,[status(thm)],[c_2129])).

cnf(c_2594,plain,
    ( ~ r1_xboole_0(sK2(sK4,sK5,k6_waybel_0(sK4,sK6)),k6_waybel_0(sK4,sK6))
    | ~ r2_hidden(sK6,sK2(sK4,sK5,k6_waybel_0(sK4,sK6)))
    | ~ r2_hidden(sK6,k6_waybel_0(sK4,sK6)) ),
    inference(instantiation,[status(thm)],[c_2444])).

cnf(c_17,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X2,k6_waybel_0(X0,X1))
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_0,plain,
    ( ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_759,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(X2,k6_waybel_0(X0,X1))
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0) ),
    inference(resolution,[status(thm)],[c_17,c_0])).

cnf(c_6,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X2,X3)
    | r2_hidden(X1,X3)
    | ~ v12_waybel_0(X3,X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_927,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X3,X0)
    | ~ r2_hidden(X2,k6_waybel_0(X1,X3))
    | ~ v12_waybel_0(X0,X1)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1) ),
    inference(resolution,[status(thm)],[c_759,c_6])).

cnf(c_28,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_947,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X3,X0)
    | r2_hidden(X2,X0)
    | ~ r2_hidden(X3,k6_waybel_0(X1,X2))
    | ~ v12_waybel_0(X0,X1)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_927,c_28])).

cnf(c_37,negated_conjecture,
    ( v2_lattice3(sK4) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1429,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X1,X0)
    | ~ r2_hidden(X2,k6_waybel_0(sK4,X1))
    | ~ v12_waybel_0(X0,sK4)
    | ~ l1_orders_2(sK4) ),
    inference(resolution,[status(thm)],[c_947,c_37])).

cnf(c_36,negated_conjecture,
    ( l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1431,plain,
    ( ~ v12_waybel_0(X0,sK4)
    | ~ r2_hidden(X2,k6_waybel_0(sK4,X1))
    | r2_hidden(X1,X0)
    | ~ r2_hidden(X2,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1429,c_36])).

cnf(c_1432,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X1,X0)
    | ~ r2_hidden(X2,k6_waybel_0(sK4,X1))
    | ~ v12_waybel_0(X0,sK4) ),
    inference(renaming,[status(thm)],[c_1431])).

cnf(c_2116,plain,
    ( ~ m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1_59,u1_struct_0(sK4))
    | ~ r2_hidden(X2_59,X0_59)
    | r2_hidden(X1_59,X0_59)
    | ~ r2_hidden(X2_59,k6_waybel_0(sK4,X1_59))
    | ~ v12_waybel_0(X0_59,sK4) ),
    inference(subtyping,[status(esa)],[c_1432])).

cnf(c_2294,plain,
    ( ~ m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ r2_hidden(X1_59,X0_59)
    | ~ r2_hidden(X1_59,k6_waybel_0(sK4,sK6))
    | r2_hidden(sK6,X0_59)
    | ~ v12_waybel_0(X0_59,sK4) ),
    inference(instantiation,[status(thm)],[c_2116])).

cnf(c_2383,plain,
    ( ~ m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ r2_hidden(sK3(sK5,k6_waybel_0(sK4,sK6)),X0_59)
    | ~ r2_hidden(sK3(sK5,k6_waybel_0(sK4,sK6)),k6_waybel_0(sK4,sK6))
    | r2_hidden(sK6,X0_59)
    | ~ v12_waybel_0(X0_59,sK4) ),
    inference(instantiation,[status(thm)],[c_2294])).

cnf(c_2385,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ r2_hidden(sK3(sK5,k6_waybel_0(sK4,sK6)),k6_waybel_0(sK4,sK6))
    | ~ r2_hidden(sK3(sK5,k6_waybel_0(sK4,sK6)),sK5)
    | r2_hidden(sK6,sK5)
    | ~ v12_waybel_0(sK5,sK4) ),
    inference(instantiation,[status(thm)],[c_2383])).

cnf(c_26,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK3(X0,X1),X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2128,plain,
    ( r1_xboole_0(X0_59,X1_59)
    | r2_hidden(sK3(X0_59,X1_59),X1_59) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_2350,plain,
    ( r1_xboole_0(sK5,k6_waybel_0(sK4,sK6))
    | r2_hidden(sK3(sK5,k6_waybel_0(sK4,sK6)),k6_waybel_0(sK4,sK6)) ),
    inference(instantiation,[status(thm)],[c_2128])).

cnf(c_27,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK3(X0,X1),X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2127,plain,
    ( r1_xboole_0(X0_59,X1_59)
    | r2_hidden(sK3(X0_59,X1_59),X0_59) ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_2351,plain,
    ( r1_xboole_0(sK5,k6_waybel_0(sK4,sK6))
    | r2_hidden(sK3(sK5,k6_waybel_0(sK4,sK6)),sK5) ),
    inference(instantiation,[status(thm)],[c_2127])).

cnf(c_16,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(X2,k6_waybel_0(X0,X1))
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_782,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r2_hidden(X2,k6_waybel_0(X0,X1))
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0) ),
    inference(resolution,[status(thm)],[c_16,c_0])).

cnf(c_14,plain,
    ( ~ r3_orders_2(X0,X1,X2)
    | r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_15,plain,
    ( r3_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_556,plain,
    ( r1_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_14,c_15])).

cnf(c_736,plain,
    ( r1_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0) ),
    inference(resolution,[status(thm)],[c_556,c_0])).

cnf(c_1011,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X0,k6_waybel_0(X1,X0))
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1) ),
    inference(resolution,[status(thm)],[c_782,c_736])).

cnf(c_42,negated_conjecture,
    ( v3_orders_2(sK4) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1362,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | r2_hidden(X0,k6_waybel_0(sK4,X0))
    | ~ l1_orders_2(sK4)
    | ~ v2_lattice3(sK4) ),
    inference(resolution,[status(thm)],[c_1011,c_42])).

cnf(c_1366,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | r2_hidden(X0,k6_waybel_0(sK4,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1362,c_37,c_36])).

cnf(c_2119,plain,
    ( ~ m1_subset_1(X0_59,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_59,u1_struct_0(sK4))
    | r2_hidden(X0_59,k6_waybel_0(sK4,X0_59)) ),
    inference(subtyping,[status(esa)],[c_1366])).

cnf(c_2132,plain,
    ( ~ m1_subset_1(X0_59,u1_struct_0(sK4))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_2119])).

cnf(c_2337,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ sP0_iProver_split ),
    inference(instantiation,[status(thm)],[c_2132])).

cnf(c_11,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_subset_1(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2131,plain,
    ( ~ r1_xboole_0(X0_59,X1_59)
    | r1_subset_1(X0_59,X1_59)
    | v1_xboole_0(X0_59)
    | v1_xboole_0(X1_59) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_2327,plain,
    ( ~ r1_xboole_0(sK5,k6_waybel_0(sK4,sK6))
    | r1_subset_1(sK5,k6_waybel_0(sK4,sK6))
    | v1_xboole_0(k6_waybel_0(sK4,sK6))
    | v1_xboole_0(sK5) ),
    inference(instantiation,[status(thm)],[c_2131])).

cnf(c_18,plain,
    ( ~ v1_waybel_0(X0,X1)
    | ~ r1_subset_1(X0,X2)
    | r1_subset_1(sK2(X1,X0,X2),X2)
    | ~ v2_waybel_0(X2,X1)
    | ~ v13_waybel_0(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v12_waybel_0(X0,X1)
    | ~ v5_orders_2(X1)
    | ~ v2_waybel_1(X1)
    | ~ v1_lattice3(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X2)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_38,negated_conjecture,
    ( v1_lattice3(sK4) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1229,plain,
    ( ~ v1_waybel_0(X0,sK4)
    | ~ r1_subset_1(X0,X1)
    | r1_subset_1(sK2(sK4,X0,X1),X1)
    | ~ v2_waybel_0(X1,sK4)
    | ~ v13_waybel_0(X1,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v12_waybel_0(X0,sK4)
    | ~ v5_orders_2(sK4)
    | ~ v2_waybel_1(sK4)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ l1_orders_2(sK4)
    | ~ v2_lattice3(sK4) ),
    inference(resolution,[status(thm)],[c_18,c_38])).

cnf(c_41,negated_conjecture,
    ( v4_orders_2(sK4) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_40,negated_conjecture,
    ( v5_orders_2(sK4) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_39,negated_conjecture,
    ( v2_waybel_1(sK4) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1233,plain,
    ( ~ v1_waybel_0(X0,sK4)
    | ~ r1_subset_1(X0,X1)
    | r1_subset_1(sK2(sK4,X0,X1),X1)
    | ~ v2_waybel_0(X1,sK4)
    | ~ v13_waybel_0(X1,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v12_waybel_0(X0,sK4)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1229,c_42,c_41,c_40,c_39,c_37,c_36])).

cnf(c_8,plain,
    ( v13_waybel_0(k6_waybel_0(X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_orders_2(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_825,plain,
    ( v13_waybel_0(k6_waybel_0(X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0) ),
    inference(resolution,[status(thm)],[c_8,c_0])).

cnf(c_1325,plain,
    ( v13_waybel_0(k6_waybel_0(sK4,X0),sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ l1_orders_2(sK4)
    | ~ v2_lattice3(sK4) ),
    inference(resolution,[status(thm)],[c_825,c_41])).

cnf(c_1329,plain,
    ( v13_waybel_0(k6_waybel_0(sK4,X0),sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1325,c_37,c_36])).

cnf(c_1585,plain,
    ( ~ v1_waybel_0(X0,sK4)
    | ~ r1_subset_1(X0,k6_waybel_0(sK4,X1))
    | r1_subset_1(sK2(sK4,X0,k6_waybel_0(sK4,X1)),k6_waybel_0(sK4,X1))
    | ~ v2_waybel_0(k6_waybel_0(sK4,X1),sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(k6_waybel_0(sK4,X1),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v12_waybel_0(X0,sK4)
    | v1_xboole_0(X0)
    | v1_xboole_0(k6_waybel_0(sK4,X1)) ),
    inference(resolution,[status(thm)],[c_1233,c_1329])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v1_xboole_0(k6_waybel_0(X1,X0))
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_845,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v1_xboole_0(k6_waybel_0(X1,X0))
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1) ),
    inference(resolution,[status(thm)],[c_0,c_10])).

cnf(c_1382,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ v1_xboole_0(k6_waybel_0(sK4,X0))
    | ~ l1_orders_2(sK4)
    | ~ v2_lattice3(sK4) ),
    inference(resolution,[status(thm)],[c_845,c_42])).

cnf(c_1386,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ v1_xboole_0(k6_waybel_0(sK4,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1382,c_37,c_36])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k6_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_865,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k6_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1) ),
    inference(resolution,[status(thm)],[c_0,c_7])).

cnf(c_1454,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(k6_waybel_0(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_orders_2(sK4) ),
    inference(resolution,[status(thm)],[c_865,c_37])).

cnf(c_1458,plain,
    ( m1_subset_1(k6_waybel_0(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1454,c_36])).

cnf(c_1459,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(k6_waybel_0(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(renaming,[status(thm)],[c_1458])).

cnf(c_9,plain,
    ( v2_waybel_0(k6_waybel_0(X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_805,plain,
    ( v2_waybel_0(k6_waybel_0(X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0) ),
    inference(resolution,[status(thm)],[c_9,c_0])).

cnf(c_1345,plain,
    ( v2_waybel_0(k6_waybel_0(sK4,X0),sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ l1_orders_2(sK4)
    | ~ v2_lattice3(sK4) ),
    inference(resolution,[status(thm)],[c_805,c_42])).

cnf(c_1349,plain,
    ( v2_waybel_0(k6_waybel_0(sK4,X0),sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1345,c_37,c_36])).

cnf(c_1609,plain,
    ( ~ v1_waybel_0(X0,sK4)
    | ~ r1_subset_1(X0,k6_waybel_0(sK4,X1))
    | r1_subset_1(sK2(sK4,X0,k6_waybel_0(sK4,X1)),k6_waybel_0(sK4,X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ v12_waybel_0(X0,sK4)
    | v1_xboole_0(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1585,c_1386,c_1459,c_1349])).

cnf(c_2109,plain,
    ( ~ v1_waybel_0(X0_59,sK4)
    | ~ r1_subset_1(X0_59,k6_waybel_0(sK4,X1_59))
    | r1_subset_1(sK2(sK4,X0_59,k6_waybel_0(sK4,X1_59)),k6_waybel_0(sK4,X1_59))
    | ~ m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1_59,u1_struct_0(sK4))
    | ~ v12_waybel_0(X0_59,sK4)
    | v1_xboole_0(X0_59) ),
    inference(subtyping,[status(esa)],[c_1609])).

cnf(c_2322,plain,
    ( ~ v1_waybel_0(X0_59,sK4)
    | ~ r1_subset_1(X0_59,k6_waybel_0(sK4,sK6))
    | r1_subset_1(sK2(sK4,X0_59,k6_waybel_0(sK4,sK6)),k6_waybel_0(sK4,sK6))
    | ~ m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ v12_waybel_0(X0_59,sK4)
    | v1_xboole_0(X0_59) ),
    inference(instantiation,[status(thm)],[c_2109])).

cnf(c_2324,plain,
    ( ~ v1_waybel_0(sK5,sK4)
    | r1_subset_1(sK2(sK4,sK5,k6_waybel_0(sK4,sK6)),k6_waybel_0(sK4,sK6))
    | ~ r1_subset_1(sK5,k6_waybel_0(sK4,sK6))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ v12_waybel_0(sK5,sK4)
    | v1_xboole_0(sK5) ),
    inference(instantiation,[status(thm)],[c_2322])).

cnf(c_21,plain,
    ( ~ v1_waybel_0(X0,X1)
    | ~ r1_subset_1(X0,X2)
    | ~ v2_waybel_0(X2,X1)
    | ~ v13_waybel_0(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK2(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v12_waybel_0(X0,X1)
    | ~ v5_orders_2(X1)
    | ~ v2_waybel_1(X1)
    | ~ v1_lattice3(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X2)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1188,plain,
    ( ~ v1_waybel_0(X0,sK4)
    | ~ r1_subset_1(X0,X1)
    | ~ v2_waybel_0(X1,sK4)
    | ~ v13_waybel_0(X1,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK2(sK4,X0,X1),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v12_waybel_0(X0,sK4)
    | ~ v5_orders_2(sK4)
    | ~ v2_waybel_1(sK4)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ l1_orders_2(sK4)
    | ~ v2_lattice3(sK4) ),
    inference(resolution,[status(thm)],[c_21,c_38])).

cnf(c_1192,plain,
    ( ~ v1_waybel_0(X0,sK4)
    | ~ r1_subset_1(X0,X1)
    | ~ v2_waybel_0(X1,sK4)
    | ~ v13_waybel_0(X1,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK2(sK4,X0,X1),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v12_waybel_0(X0,sK4)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1188,c_42,c_41,c_40,c_39,c_37,c_36])).

cnf(c_1620,plain,
    ( ~ v1_waybel_0(X0,sK4)
    | ~ r1_subset_1(X0,k6_waybel_0(sK4,X1))
    | ~ v2_waybel_0(k6_waybel_0(sK4,X1),sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | m1_subset_1(sK2(sK4,X0,k6_waybel_0(sK4,X1)),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(k6_waybel_0(sK4,X1),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v12_waybel_0(X0,sK4)
    | v1_xboole_0(X0)
    | v1_xboole_0(k6_waybel_0(sK4,X1)) ),
    inference(resolution,[status(thm)],[c_1192,c_1329])).

cnf(c_1644,plain,
    ( ~ v1_waybel_0(X0,sK4)
    | ~ r1_subset_1(X0,k6_waybel_0(sK4,X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | m1_subset_1(sK2(sK4,X0,k6_waybel_0(sK4,X1)),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v12_waybel_0(X0,sK4)
    | v1_xboole_0(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1620,c_1386,c_1459,c_1349])).

cnf(c_2108,plain,
    ( ~ v1_waybel_0(X0_59,sK4)
    | ~ r1_subset_1(X0_59,k6_waybel_0(sK4,X1_59))
    | ~ m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1_59,u1_struct_0(sK4))
    | m1_subset_1(sK2(sK4,X0_59,k6_waybel_0(sK4,X1_59)),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v12_waybel_0(X0_59,sK4)
    | v1_xboole_0(X0_59) ),
    inference(subtyping,[status(esa)],[c_1644])).

cnf(c_2317,plain,
    ( ~ v1_waybel_0(X0_59,sK4)
    | ~ r1_subset_1(X0_59,k6_waybel_0(sK4,sK6))
    | ~ m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK2(sK4,X0_59,k6_waybel_0(sK4,sK6)),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ v12_waybel_0(X0_59,sK4)
    | v1_xboole_0(X0_59) ),
    inference(instantiation,[status(thm)],[c_2108])).

cnf(c_2319,plain,
    ( ~ v1_waybel_0(sK5,sK4)
    | ~ r1_subset_1(sK5,k6_waybel_0(sK4,sK6))
    | m1_subset_1(sK2(sK4,sK5,k6_waybel_0(sK4,sK6)),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ v12_waybel_0(sK5,sK4)
    | v1_xboole_0(sK5) ),
    inference(instantiation,[status(thm)],[c_2317])).

cnf(c_22,plain,
    ( ~ v1_waybel_0(X0,X1)
    | ~ r1_subset_1(X0,X2)
    | ~ v2_waybel_0(X2,X1)
    | ~ v13_waybel_0(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v12_waybel_0(X0,X1)
    | v12_waybel_0(sK2(X1,X0,X2),X1)
    | ~ v5_orders_2(X1)
    | ~ v2_waybel_1(X1)
    | ~ v1_lattice3(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X2)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1147,plain,
    ( ~ v1_waybel_0(X0,sK4)
    | ~ r1_subset_1(X0,X1)
    | ~ v2_waybel_0(X1,sK4)
    | ~ v13_waybel_0(X1,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v12_waybel_0(X0,sK4)
    | v12_waybel_0(sK2(sK4,X0,X1),sK4)
    | ~ v5_orders_2(sK4)
    | ~ v2_waybel_1(sK4)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ l1_orders_2(sK4)
    | ~ v2_lattice3(sK4) ),
    inference(resolution,[status(thm)],[c_22,c_38])).

cnf(c_1151,plain,
    ( ~ v1_waybel_0(X0,sK4)
    | ~ r1_subset_1(X0,X1)
    | ~ v2_waybel_0(X1,sK4)
    | ~ v13_waybel_0(X1,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v12_waybel_0(X0,sK4)
    | v12_waybel_0(sK2(sK4,X0,X1),sK4)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1147,c_42,c_41,c_40,c_39,c_37,c_36])).

cnf(c_1655,plain,
    ( ~ v1_waybel_0(X0,sK4)
    | ~ r1_subset_1(X0,k6_waybel_0(sK4,X1))
    | ~ v2_waybel_0(k6_waybel_0(sK4,X1),sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(k6_waybel_0(sK4,X1),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v12_waybel_0(X0,sK4)
    | v12_waybel_0(sK2(sK4,X0,k6_waybel_0(sK4,X1)),sK4)
    | v1_xboole_0(X0)
    | v1_xboole_0(k6_waybel_0(sK4,X1)) ),
    inference(resolution,[status(thm)],[c_1151,c_1329])).

cnf(c_1679,plain,
    ( ~ v1_waybel_0(X0,sK4)
    | ~ r1_subset_1(X0,k6_waybel_0(sK4,X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ v12_waybel_0(X0,sK4)
    | v12_waybel_0(sK2(sK4,X0,k6_waybel_0(sK4,X1)),sK4)
    | v1_xboole_0(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1655,c_1386,c_1459,c_1349])).

cnf(c_2107,plain,
    ( ~ v1_waybel_0(X0_59,sK4)
    | ~ r1_subset_1(X0_59,k6_waybel_0(sK4,X1_59))
    | ~ m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1_59,u1_struct_0(sK4))
    | ~ v12_waybel_0(X0_59,sK4)
    | v12_waybel_0(sK2(sK4,X0_59,k6_waybel_0(sK4,X1_59)),sK4)
    | v1_xboole_0(X0_59) ),
    inference(subtyping,[status(esa)],[c_1679])).

cnf(c_2312,plain,
    ( ~ v1_waybel_0(X0_59,sK4)
    | ~ r1_subset_1(X0_59,k6_waybel_0(sK4,sK6))
    | ~ m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ v12_waybel_0(X0_59,sK4)
    | v12_waybel_0(sK2(sK4,X0_59,k6_waybel_0(sK4,sK6)),sK4)
    | v1_xboole_0(X0_59) ),
    inference(instantiation,[status(thm)],[c_2107])).

cnf(c_2314,plain,
    ( ~ v1_waybel_0(sK5,sK4)
    | ~ r1_subset_1(sK5,k6_waybel_0(sK4,sK6))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | v12_waybel_0(sK2(sK4,sK5,k6_waybel_0(sK4,sK6)),sK4)
    | ~ v12_waybel_0(sK5,sK4)
    | v1_xboole_0(sK5) ),
    inference(instantiation,[status(thm)],[c_2312])).

cnf(c_23,plain,
    ( ~ v1_waybel_0(X0,X1)
    | v1_waybel_0(sK2(X1,X0,X2),X1)
    | ~ r1_subset_1(X0,X2)
    | ~ v2_waybel_0(X2,X1)
    | ~ v13_waybel_0(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v12_waybel_0(X0,X1)
    | ~ v5_orders_2(X1)
    | ~ v2_waybel_1(X1)
    | ~ v1_lattice3(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X2)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1106,plain,
    ( ~ v1_waybel_0(X0,sK4)
    | v1_waybel_0(sK2(sK4,X0,X1),sK4)
    | ~ r1_subset_1(X0,X1)
    | ~ v2_waybel_0(X1,sK4)
    | ~ v13_waybel_0(X1,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v12_waybel_0(X0,sK4)
    | ~ v5_orders_2(sK4)
    | ~ v2_waybel_1(sK4)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ l1_orders_2(sK4)
    | ~ v2_lattice3(sK4) ),
    inference(resolution,[status(thm)],[c_23,c_38])).

cnf(c_1110,plain,
    ( ~ v1_waybel_0(X0,sK4)
    | v1_waybel_0(sK2(sK4,X0,X1),sK4)
    | ~ r1_subset_1(X0,X1)
    | ~ v2_waybel_0(X1,sK4)
    | ~ v13_waybel_0(X1,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v12_waybel_0(X0,sK4)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1106,c_42,c_41,c_40,c_39,c_37,c_36])).

cnf(c_1690,plain,
    ( ~ v1_waybel_0(X0,sK4)
    | v1_waybel_0(sK2(sK4,X0,k6_waybel_0(sK4,X1)),sK4)
    | ~ r1_subset_1(X0,k6_waybel_0(sK4,X1))
    | ~ v2_waybel_0(k6_waybel_0(sK4,X1),sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(k6_waybel_0(sK4,X1),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v12_waybel_0(X0,sK4)
    | v1_xboole_0(X0)
    | v1_xboole_0(k6_waybel_0(sK4,X1)) ),
    inference(resolution,[status(thm)],[c_1110,c_1329])).

cnf(c_1714,plain,
    ( ~ v1_waybel_0(X0,sK4)
    | v1_waybel_0(sK2(sK4,X0,k6_waybel_0(sK4,X1)),sK4)
    | ~ r1_subset_1(X0,k6_waybel_0(sK4,X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ v12_waybel_0(X0,sK4)
    | v1_xboole_0(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1690,c_1386,c_1459,c_1349])).

cnf(c_2106,plain,
    ( ~ v1_waybel_0(X0_59,sK4)
    | v1_waybel_0(sK2(sK4,X0_59,k6_waybel_0(sK4,X1_59)),sK4)
    | ~ r1_subset_1(X0_59,k6_waybel_0(sK4,X1_59))
    | ~ m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1_59,u1_struct_0(sK4))
    | ~ v12_waybel_0(X0_59,sK4)
    | v1_xboole_0(X0_59) ),
    inference(subtyping,[status(esa)],[c_1714])).

cnf(c_2307,plain,
    ( ~ v1_waybel_0(X0_59,sK4)
    | v1_waybel_0(sK2(sK4,X0_59,k6_waybel_0(sK4,sK6)),sK4)
    | ~ r1_subset_1(X0_59,k6_waybel_0(sK4,sK6))
    | ~ m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ v12_waybel_0(X0_59,sK4)
    | v1_xboole_0(X0_59) ),
    inference(instantiation,[status(thm)],[c_2106])).

cnf(c_2309,plain,
    ( v1_waybel_0(sK2(sK4,sK5,k6_waybel_0(sK4,sK6)),sK4)
    | ~ v1_waybel_0(sK5,sK4)
    | ~ r1_subset_1(sK5,k6_waybel_0(sK4,sK6))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ v12_waybel_0(sK5,sK4)
    | v1_xboole_0(sK5) ),
    inference(instantiation,[status(thm)],[c_2307])).

cnf(c_24,plain,
    ( ~ v1_waybel_0(X0,X1)
    | ~ r1_subset_1(X0,X2)
    | ~ v2_waybel_0(X2,X1)
    | ~ v13_waybel_0(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v12_waybel_0(X0,X1)
    | ~ v5_orders_2(X1)
    | ~ v2_waybel_1(X1)
    | ~ v1_lattice3(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X2)
    | ~ v1_xboole_0(sK2(X1,X0,X2))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1065,plain,
    ( ~ v1_waybel_0(X0,sK4)
    | ~ r1_subset_1(X0,X1)
    | ~ v2_waybel_0(X1,sK4)
    | ~ v13_waybel_0(X1,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v12_waybel_0(X0,sK4)
    | ~ v5_orders_2(sK4)
    | ~ v2_waybel_1(sK4)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | ~ v1_xboole_0(sK2(sK4,X0,X1))
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ l1_orders_2(sK4)
    | ~ v2_lattice3(sK4) ),
    inference(resolution,[status(thm)],[c_24,c_38])).

cnf(c_1069,plain,
    ( ~ v1_waybel_0(X0,sK4)
    | ~ r1_subset_1(X0,X1)
    | ~ v2_waybel_0(X1,sK4)
    | ~ v13_waybel_0(X1,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v12_waybel_0(X0,sK4)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | ~ v1_xboole_0(sK2(sK4,X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1065,c_42,c_41,c_40,c_39,c_37,c_36])).

cnf(c_1725,plain,
    ( ~ v1_waybel_0(X0,sK4)
    | ~ r1_subset_1(X0,k6_waybel_0(sK4,X1))
    | ~ v2_waybel_0(k6_waybel_0(sK4,X1),sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(k6_waybel_0(sK4,X1),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v12_waybel_0(X0,sK4)
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(sK2(sK4,X0,k6_waybel_0(sK4,X1)))
    | v1_xboole_0(k6_waybel_0(sK4,X1)) ),
    inference(resolution,[status(thm)],[c_1069,c_1329])).

cnf(c_1749,plain,
    ( ~ v1_waybel_0(X0,sK4)
    | ~ r1_subset_1(X0,k6_waybel_0(sK4,X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ v12_waybel_0(X0,sK4)
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(sK2(sK4,X0,k6_waybel_0(sK4,X1))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1725,c_1386,c_1459,c_1349])).

cnf(c_2105,plain,
    ( ~ v1_waybel_0(X0_59,sK4)
    | ~ r1_subset_1(X0_59,k6_waybel_0(sK4,X1_59))
    | ~ m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1_59,u1_struct_0(sK4))
    | ~ v12_waybel_0(X0_59,sK4)
    | v1_xboole_0(X0_59)
    | ~ v1_xboole_0(sK2(sK4,X0_59,k6_waybel_0(sK4,X1_59))) ),
    inference(subtyping,[status(esa)],[c_1749])).

cnf(c_2302,plain,
    ( ~ v1_waybel_0(X0_59,sK4)
    | ~ r1_subset_1(X0_59,k6_waybel_0(sK4,sK6))
    | ~ m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ v12_waybel_0(X0_59,sK4)
    | v1_xboole_0(X0_59)
    | ~ v1_xboole_0(sK2(sK4,X0_59,k6_waybel_0(sK4,sK6))) ),
    inference(instantiation,[status(thm)],[c_2105])).

cnf(c_2304,plain,
    ( ~ v1_waybel_0(sK5,sK4)
    | ~ r1_subset_1(sK5,k6_waybel_0(sK4,sK6))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ v12_waybel_0(sK5,sK4)
    | ~ v1_xboole_0(sK2(sK4,sK5,k6_waybel_0(sK4,sK6)))
    | v1_xboole_0(sK5) ),
    inference(instantiation,[status(thm)],[c_2302])).

cnf(c_19,plain,
    ( r1_tarski(X0,sK2(X1,X0,X2))
    | ~ v1_waybel_0(X0,X1)
    | ~ r1_subset_1(X0,X2)
    | ~ v2_waybel_0(X2,X1)
    | ~ v13_waybel_0(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v12_waybel_0(X0,X1)
    | ~ v5_orders_2(X1)
    | ~ v2_waybel_1(X1)
    | ~ v1_lattice3(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X2)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_20,plain,
    ( v1_waybel_7(sK2(X0,X1,X2),X0)
    | ~ v1_waybel_0(X1,X0)
    | ~ r1_subset_1(X1,X2)
    | ~ v2_waybel_0(X2,X0)
    | ~ v13_waybel_0(X2,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v12_waybel_0(X1,X0)
    | ~ v5_orders_2(X0)
    | ~ v2_waybel_1(X0)
    | ~ v1_lattice3(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_29,negated_conjecture,
    ( ~ v1_waybel_7(X0,sK4)
    | ~ r1_tarski(sK5,X0)
    | ~ v1_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(sK6,X0)
    | ~ v12_waybel_0(X0,sK4)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_498,plain,
    ( ~ r1_tarski(sK5,sK2(sK4,X0,X1))
    | ~ v1_waybel_0(X0,sK4)
    | ~ v1_waybel_0(sK2(sK4,X0,X1),sK4)
    | ~ r1_subset_1(X0,X1)
    | ~ v2_waybel_0(X1,sK4)
    | ~ v13_waybel_0(X1,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK2(sK4,X0,X1),k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(sK6,sK2(sK4,X0,X1))
    | ~ v12_waybel_0(X0,sK4)
    | ~ v12_waybel_0(sK2(sK4,X0,X1),sK4)
    | ~ v5_orders_2(sK4)
    | ~ v2_waybel_1(sK4)
    | ~ v1_lattice3(sK4)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(sK2(sK4,X0,X1))
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ l1_orders_2(sK4)
    | ~ v2_lattice3(sK4) ),
    inference(resolution,[status(thm)],[c_20,c_29])).

cnf(c_502,plain,
    ( ~ v12_waybel_0(sK2(sK4,X0,X1),sK4)
    | ~ v12_waybel_0(X0,sK4)
    | r2_hidden(sK6,sK2(sK4,X0,X1))
    | ~ m1_subset_1(sK2(sK4,X0,X1),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v13_waybel_0(X1,sK4)
    | ~ v2_waybel_0(X1,sK4)
    | ~ r1_subset_1(X0,X1)
    | ~ v1_waybel_0(sK2(sK4,X0,X1),sK4)
    | ~ v1_waybel_0(X0,sK4)
    | ~ r1_tarski(sK5,sK2(sK4,X0,X1))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(sK2(sK4,X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_498,c_42,c_41,c_40,c_39,c_38,c_37,c_36])).

cnf(c_503,plain,
    ( ~ r1_tarski(sK5,sK2(sK4,X0,X1))
    | ~ v1_waybel_0(X0,sK4)
    | ~ v1_waybel_0(sK2(sK4,X0,X1),sK4)
    | ~ r1_subset_1(X0,X1)
    | ~ v2_waybel_0(X1,sK4)
    | ~ v13_waybel_0(X1,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK2(sK4,X0,X1),k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(sK6,sK2(sK4,X0,X1))
    | ~ v12_waybel_0(X0,sK4)
    | ~ v12_waybel_0(sK2(sK4,X0,X1),sK4)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(sK2(sK4,X0,X1)) ),
    inference(renaming,[status(thm)],[c_502])).

cnf(c_684,plain,
    ( ~ v1_waybel_0(sK2(sK4,sK5,X0),sK4)
    | ~ v1_waybel_0(sK5,sK4)
    | ~ r1_subset_1(sK5,X0)
    | ~ v2_waybel_0(X0,sK4)
    | ~ v13_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK2(sK4,sK5,X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(sK6,sK2(sK4,sK5,X0))
    | ~ v12_waybel_0(sK2(sK4,sK5,X0),sK4)
    | ~ v12_waybel_0(sK5,sK4)
    | ~ v5_orders_2(sK4)
    | ~ v2_waybel_1(sK4)
    | ~ v1_lattice3(sK4)
    | v1_xboole_0(X0)
    | v1_xboole_0(sK2(sK4,sK5,X0))
    | v1_xboole_0(sK5)
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ l1_orders_2(sK4)
    | ~ v2_lattice3(sK4) ),
    inference(resolution,[status(thm)],[c_19,c_503])).

cnf(c_35,negated_conjecture,
    ( ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_34,negated_conjecture,
    ( v1_waybel_0(sK5,sK4) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_33,negated_conjecture,
    ( v12_waybel_0(sK5,sK4) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_688,plain,
    ( v1_xboole_0(sK2(sK4,sK5,X0))
    | v1_xboole_0(X0)
    | ~ v12_waybel_0(sK2(sK4,sK5,X0),sK4)
    | r2_hidden(sK6,sK2(sK4,sK5,X0))
    | ~ v1_waybel_0(sK2(sK4,sK5,X0),sK4)
    | ~ r1_subset_1(sK5,X0)
    | ~ v2_waybel_0(X0,sK4)
    | ~ v13_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK2(sK4,sK5,X0),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_684,c_42,c_41,c_40,c_39,c_38,c_37,c_36,c_35,c_34,c_33,c_32])).

cnf(c_689,plain,
    ( ~ v1_waybel_0(sK2(sK4,sK5,X0),sK4)
    | ~ r1_subset_1(sK5,X0)
    | ~ v2_waybel_0(X0,sK4)
    | ~ v13_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK2(sK4,sK5,X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(sK6,sK2(sK4,sK5,X0))
    | ~ v12_waybel_0(sK2(sK4,sK5,X0),sK4)
    | v1_xboole_0(X0)
    | v1_xboole_0(sK2(sK4,sK5,X0)) ),
    inference(renaming,[status(thm)],[c_688])).

cnf(c_1760,plain,
    ( ~ v1_waybel_0(sK2(sK4,sK5,k6_waybel_0(sK4,X0)),sK4)
    | ~ r1_subset_1(sK5,k6_waybel_0(sK4,X0))
    | ~ v2_waybel_0(k6_waybel_0(sK4,X0),sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(sK2(sK4,sK5,k6_waybel_0(sK4,X0)),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(k6_waybel_0(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(sK6,sK2(sK4,sK5,k6_waybel_0(sK4,X0)))
    | ~ v12_waybel_0(sK2(sK4,sK5,k6_waybel_0(sK4,X0)),sK4)
    | v1_xboole_0(sK2(sK4,sK5,k6_waybel_0(sK4,X0)))
    | v1_xboole_0(k6_waybel_0(sK4,X0)) ),
    inference(resolution,[status(thm)],[c_689,c_1329])).

cnf(c_1764,plain,
    ( v1_xboole_0(sK2(sK4,sK5,k6_waybel_0(sK4,X0)))
    | ~ v12_waybel_0(sK2(sK4,sK5,k6_waybel_0(sK4,X0)),sK4)
    | r2_hidden(sK6,sK2(sK4,sK5,k6_waybel_0(sK4,X0)))
    | ~ r1_subset_1(sK5,k6_waybel_0(sK4,X0))
    | ~ v1_waybel_0(sK2(sK4,sK5,k6_waybel_0(sK4,X0)),sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(sK2(sK4,sK5,k6_waybel_0(sK4,X0)),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1760,c_37,c_36,c_1349,c_1382,c_1454])).

cnf(c_1765,plain,
    ( ~ v1_waybel_0(sK2(sK4,sK5,k6_waybel_0(sK4,X0)),sK4)
    | ~ r1_subset_1(sK5,k6_waybel_0(sK4,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(sK2(sK4,sK5,k6_waybel_0(sK4,X0)),k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(sK6,sK2(sK4,sK5,k6_waybel_0(sK4,X0)))
    | ~ v12_waybel_0(sK2(sK4,sK5,k6_waybel_0(sK4,X0)),sK4)
    | v1_xboole_0(sK2(sK4,sK5,k6_waybel_0(sK4,X0))) ),
    inference(renaming,[status(thm)],[c_1764])).

cnf(c_2104,plain,
    ( ~ v1_waybel_0(sK2(sK4,sK5,k6_waybel_0(sK4,X0_59)),sK4)
    | ~ r1_subset_1(sK5,k6_waybel_0(sK4,X0_59))
    | ~ m1_subset_1(X0_59,u1_struct_0(sK4))
    | ~ m1_subset_1(sK2(sK4,sK5,k6_waybel_0(sK4,X0_59)),k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(sK6,sK2(sK4,sK5,k6_waybel_0(sK4,X0_59)))
    | ~ v12_waybel_0(sK2(sK4,sK5,k6_waybel_0(sK4,X0_59)),sK4)
    | v1_xboole_0(sK2(sK4,sK5,k6_waybel_0(sK4,X0_59))) ),
    inference(subtyping,[status(esa)],[c_1765])).

cnf(c_2299,plain,
    ( ~ v1_waybel_0(sK2(sK4,sK5,k6_waybel_0(sK4,sK6)),sK4)
    | ~ r1_subset_1(sK5,k6_waybel_0(sK4,sK6))
    | ~ m1_subset_1(sK2(sK4,sK5,k6_waybel_0(sK4,sK6)),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | r2_hidden(sK6,sK2(sK4,sK5,k6_waybel_0(sK4,sK6)))
    | ~ v12_waybel_0(sK2(sK4,sK5,k6_waybel_0(sK4,sK6)),sK4)
    | v1_xboole_0(sK2(sK4,sK5,k6_waybel_0(sK4,sK6))) ),
    inference(instantiation,[status(thm)],[c_2104])).

cnf(c_2133,plain,
    ( ~ m1_subset_1(X0_59,u1_struct_0(sK4))
    | r2_hidden(X0_59,k6_waybel_0(sK4,X0_59))
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_2119])).

cnf(c_2291,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | r2_hidden(sK6,k6_waybel_0(sK4,sK6))
    | ~ sP1_iProver_split ),
    inference(instantiation,[status(thm)],[c_2133])).

cnf(c_2118,plain,
    ( ~ m1_subset_1(X0_59,u1_struct_0(sK4))
    | ~ v1_xboole_0(k6_waybel_0(sK4,X0_59)) ),
    inference(subtyping,[status(esa)],[c_1386])).

cnf(c_2288,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ v1_xboole_0(k6_waybel_0(sK4,sK6)) ),
    inference(instantiation,[status(thm)],[c_2118])).

cnf(c_2134,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_2119])).

cnf(c_30,negated_conjecture,
    ( ~ r2_hidden(sK6,sK5) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f97])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2692,c_2594,c_2385,c_2350,c_2351,c_2337,c_2327,c_2324,c_2319,c_2314,c_2309,c_2304,c_2299,c_2291,c_2288,c_2134,c_30,c_31,c_32,c_33,c_34,c_35])).


%------------------------------------------------------------------------------
