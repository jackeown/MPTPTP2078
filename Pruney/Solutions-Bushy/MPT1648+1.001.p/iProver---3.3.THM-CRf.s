%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1648+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:05 EST 2020

% Result     : Theorem 3.76s
% Output     : CNFRefutation 3.76s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 397 expanded)
%              Number of clauses        :   69 ( 124 expanded)
%              Number of leaves         :   15 ( 105 expanded)
%              Depth                    :   21
%              Number of atoms          :  508 (2350 expanded)
%              Number of equality atoms :  117 ( 213 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) ) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] :
                  ( r2_hidden(X4,X0)
                  & r2_hidden(X2,X4) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ? [X7] :
                  ( r2_hidden(X7,X0)
                  & r2_hidden(X5,X7) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f21])).

fof(f25,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK4(X0,X5),X0)
        & r2_hidden(X5,sK4(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(X2,X4) )
     => ( r2_hidden(sK3(X0,X1),X0)
        & r2_hidden(X2,sK3(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X3) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( r2_hidden(X4,X0)
                & r2_hidden(X2,X4) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( ~ r2_hidden(X3,X0)
              | ~ r2_hidden(sK2(X0,X1),X3) )
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( ? [X4] :
              ( r2_hidden(X4,X0)
              & r2_hidden(sK2(X0,X1),X4) )
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(sK2(X0,X1),X3) )
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( ( r2_hidden(sK3(X0,X1),X0)
              & r2_hidden(sK2(X0,X1),sK3(X0,X1)) )
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ( r2_hidden(sK4(X0,X5),X0)
                & r2_hidden(X5,sK4(X0,X5)) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f22,f25,f24,f23])).

fof(f37,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK4(X0,X5),X0)
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f50,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK4(X0,X5),X0)
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f37])).

fof(f6,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v13_waybel_0(X2,X0) ) )
           => ( m1_subset_1(k5_setfam_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(k5_setfam_1(u1_struct_0(X0),X1),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( r2_hidden(X2,X1)
                   => v13_waybel_0(X2,X0) ) )
             => ( m1_subset_1(k5_setfam_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
                & v13_waybel_0(k5_setfam_1(u1_struct_0(X0),X1),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(k5_setfam_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v13_waybel_0(k5_setfam_1(u1_struct_0(X0),X1),X0) )
          & ! [X2] :
              ( v13_waybel_0(X2,X0)
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(k5_setfam_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v13_waybel_0(k5_setfam_1(u1_struct_0(X0),X1),X0) )
          & ! [X2] :
              ( v13_waybel_0(X2,X0)
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f14])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(k5_setfam_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v13_waybel_0(k5_setfam_1(u1_struct_0(X0),X1),X0) )
          & ! [X2] :
              ( v13_waybel_0(X2,X0)
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ( ~ m1_subset_1(k5_setfam_1(u1_struct_0(X0),sK6),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(k5_setfam_1(u1_struct_0(X0),sK6),X0) )
        & ! [X2] :
            ( v13_waybel_0(X2,X0)
            | ~ r2_hidden(X2,sK6)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ m1_subset_1(k5_setfam_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v13_waybel_0(k5_setfam_1(u1_struct_0(X0),X1),X0) )
            & ! [X2] :
                ( v13_waybel_0(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ( ~ m1_subset_1(k5_setfam_1(u1_struct_0(sK5),X1),k1_zfmisc_1(u1_struct_0(sK5)))
            | ~ v13_waybel_0(k5_setfam_1(u1_struct_0(sK5),X1),sK5) )
          & ! [X2] :
              ( v13_waybel_0(X2,sK5)
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) )
      & l1_orders_2(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ( ~ m1_subset_1(k5_setfam_1(u1_struct_0(sK5),sK6),k1_zfmisc_1(u1_struct_0(sK5)))
      | ~ v13_waybel_0(k5_setfam_1(u1_struct_0(sK5),sK6),sK5) )
    & ! [X2] :
        ( v13_waybel_0(X2,sK5)
        | ~ r2_hidden(X2,sK6)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5))) )
    & m1_subset_1(sK6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    & l1_orders_2(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f15,f28,f27])).

fof(f46,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) ),
    inference(cnf_transformation,[],[f29])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f47,plain,(
    ! [X2] :
      ( v13_waybel_0(X2,sK5)
      | ~ r2_hidden(X2,sK6)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f36,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,sK4(X0,X5))
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f51,plain,(
    ! [X0,X5] :
      ( r2_hidden(X5,sK4(X0,X5))
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f36])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k3_tarski(X1) = k5_setfam_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( k3_tarski(X1) = k5_setfam_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k3_tarski(X1) = k5_setfam_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f1,axiom,(
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

fof(f8,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f9,plain,(
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
    inference(flattening,[],[f8])).

fof(f16,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f17,plain,(
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
    inference(rectify,[],[f16])).

fof(f19,plain,(
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

fof(f18,plain,(
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

fof(f20,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f19,f18])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v13_waybel_0(X1,X0)
      | r1_orders_2(X0,sK0(X0,X1),sK1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f30,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r1_orders_2(X0,X4,X5)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v13_waybel_0(X1,X0)
      | m1_subset_1(sK0(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v13_waybel_0(X1,X0)
      | m1_subset_1(sK1(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f45,plain,(
    l1_orders_2(sK5) ),
    inference(cnf_transformation,[],[f29])).

fof(f48,plain,
    ( ~ m1_subset_1(k5_setfam_1(u1_struct_0(sK5),sK6),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ v13_waybel_0(k5_setfam_1(u1_struct_0(sK5),sK6),sK5) ),
    inference(cnf_transformation,[],[f29])).

fof(f38,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f49,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k3_tarski(X0))
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6) ) ),
    inference(equality_resolution,[],[f38])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v13_waybel_0(X1,X0)
      | ~ r2_hidden(sK1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v13_waybel_0(X1,X0)
      | r2_hidden(sK0(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k3_tarski(X1))
    | r2_hidden(sK4(X1,X0),X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_785,plain,
    ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
    | r2_hidden(sK4(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_778,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_14,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_781,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1148,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_778,c_781])).

cnf(c_16,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(X0,sK6)
    | v13_waybel_0(X0,sK5) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_779,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r2_hidden(X0,sK6) != iProver_top
    | v13_waybel_0(X0,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1412,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | v13_waybel_0(X0,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1148,c_779])).

cnf(c_1420,plain,
    ( r2_hidden(X0,k3_tarski(sK6)) != iProver_top
    | v13_waybel_0(sK4(sK6,X0),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_785,c_1412])).

cnf(c_11,plain,
    ( r2_hidden(X0,sK4(X1,X0))
    | ~ r2_hidden(X0,k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_784,plain,
    ( r2_hidden(X0,sK4(X1,X0)) = iProver_top
    | r2_hidden(X0,k3_tarski(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k5_setfam_1(X1,X0) = k3_tarski(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_782,plain,
    ( k5_setfam_1(X0,X1) = k3_tarski(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1153,plain,
    ( k5_setfam_1(u1_struct_0(sK5),sK6) = k3_tarski(sK6) ),
    inference(superposition,[status(thm)],[c_778,c_782])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | m1_subset_1(k5_setfam_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_783,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | m1_subset_1(k5_setfam_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1294,plain,
    ( m1_subset_1(k3_tarski(sK6),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1153,c_783])).

cnf(c_20,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1685,plain,
    ( m1_subset_1(k3_tarski(sK6),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1294,c_20])).

cnf(c_1,plain,
    ( r1_orders_2(X0,sK0(X0,X1),sK1(X0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | v13_waybel_0(X1,X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_5,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(X1,X3)
    | r2_hidden(X2,X3)
    | ~ v13_waybel_0(X3,X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_217,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X5,u1_struct_0(X3))
    | ~ r2_hidden(X5,X2)
    | r2_hidden(X4,X2)
    | ~ v13_waybel_0(X2,X3)
    | v13_waybel_0(X0,X1)
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X3)
    | X3 != X1
    | sK0(X1,X0) != X5
    | sK1(X1,X0) != X4 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_5])).

cnf(c_218,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK0(X1,X0),u1_struct_0(X1))
    | ~ m1_subset_1(sK1(X1,X0),u1_struct_0(X1))
    | ~ r2_hidden(sK0(X1,X0),X2)
    | r2_hidden(sK1(X1,X0),X2)
    | ~ v13_waybel_0(X2,X1)
    | v13_waybel_0(X0,X1)
    | ~ l1_orders_2(X1) ),
    inference(unflattening,[status(thm)],[c_217])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1,X0),u1_struct_0(X1))
    | v13_waybel_0(X0,X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK1(X1,X0),u1_struct_0(X1))
    | v13_waybel_0(X0,X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_220,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(sK0(X1,X0),X2)
    | r2_hidden(sK1(X1,X0),X2)
    | ~ v13_waybel_0(X2,X1)
    | v13_waybel_0(X0,X1)
    | ~ l1_orders_2(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_218,c_4,c_3])).

cnf(c_18,negated_conjecture,
    ( l1_orders_2(sK5) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_254,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(sK0(X1,X0),X2)
    | r2_hidden(sK1(X1,X0),X2)
    | ~ v13_waybel_0(X2,X1)
    | v13_waybel_0(X0,X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_220,c_18])).

cnf(c_255,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(sK0(sK5,X0),X1)
    | r2_hidden(sK1(sK5,X0),X1)
    | ~ v13_waybel_0(X1,sK5)
    | v13_waybel_0(X0,sK5) ),
    inference(unflattening,[status(thm)],[c_254])).

cnf(c_777,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r2_hidden(sK0(sK5,X0),X1) != iProver_top
    | r2_hidden(sK1(sK5,X0),X1) = iProver_top
    | v13_waybel_0(X1,sK5) != iProver_top
    | v13_waybel_0(X0,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_255])).

cnf(c_1690,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r2_hidden(sK0(sK5,k3_tarski(sK6)),X0) != iProver_top
    | r2_hidden(sK1(sK5,k3_tarski(sK6)),X0) = iProver_top
    | v13_waybel_0(X0,sK5) != iProver_top
    | v13_waybel_0(k3_tarski(sK6),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1685,c_777])).

cnf(c_15,negated_conjecture,
    ( ~ m1_subset_1(k5_setfam_1(u1_struct_0(sK5),sK6),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ v13_waybel_0(k5_setfam_1(u1_struct_0(sK5),sK6),sK5) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_24,plain,
    ( m1_subset_1(k5_setfam_1(u1_struct_0(sK5),sK6),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | v13_waybel_0(k5_setfam_1(u1_struct_0(sK5),sK6),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_478,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_497,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_478])).

cnf(c_480,plain,
    ( ~ v13_waybel_0(X0,X1)
    | v13_waybel_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_815,plain,
    ( ~ v13_waybel_0(X0,X1)
    | v13_waybel_0(k5_setfam_1(u1_struct_0(sK5),sK6),sK5)
    | k5_setfam_1(u1_struct_0(sK5),sK6) != X0
    | sK5 != X1 ),
    inference(instantiation,[status(thm)],[c_480])).

cnf(c_885,plain,
    ( v13_waybel_0(k5_setfam_1(u1_struct_0(sK5),sK6),sK5)
    | ~ v13_waybel_0(k3_tarski(sK6),X0)
    | k5_setfam_1(u1_struct_0(sK5),sK6) != k3_tarski(sK6)
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_815])).

cnf(c_886,plain,
    ( k5_setfam_1(u1_struct_0(sK5),sK6) != k3_tarski(sK6)
    | sK5 != X0
    | v13_waybel_0(k5_setfam_1(u1_struct_0(sK5),sK6),sK5) = iProver_top
    | v13_waybel_0(k3_tarski(sK6),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_885])).

cnf(c_888,plain,
    ( k5_setfam_1(u1_struct_0(sK5),sK6) != k3_tarski(sK6)
    | sK5 != sK5
    | v13_waybel_0(k5_setfam_1(u1_struct_0(sK5),sK6),sK5) = iProver_top
    | v13_waybel_0(k3_tarski(sK6),sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_886])).

cnf(c_979,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | k5_setfam_1(u1_struct_0(sK5),sK6) = k3_tarski(sK6) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_905,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | m1_subset_1(k5_setfam_1(u1_struct_0(sK5),X0),k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1013,plain,
    ( m1_subset_1(k5_setfam_1(u1_struct_0(sK5),sK6),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) ),
    inference(instantiation,[status(thm)],[c_905])).

cnf(c_1014,plain,
    ( m1_subset_1(k5_setfam_1(u1_struct_0(sK5),sK6),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1013])).

cnf(c_2653,plain,
    ( v13_waybel_0(X0,sK5) != iProver_top
    | r2_hidden(sK1(sK5,k3_tarski(sK6)),X0) = iProver_top
    | r2_hidden(sK0(sK5,k3_tarski(sK6)),X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1690,c_17,c_20,c_24,c_497,c_888,c_979,c_1014])).

cnf(c_2654,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r2_hidden(sK0(sK5,k3_tarski(sK6)),X0) != iProver_top
    | r2_hidden(sK1(sK5,k3_tarski(sK6)),X0) = iProver_top
    | v13_waybel_0(X0,sK5) != iProver_top ),
    inference(renaming,[status(thm)],[c_2653])).

cnf(c_2659,plain,
    ( m1_subset_1(sK4(X0,sK0(sK5,k3_tarski(sK6))),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r2_hidden(sK0(sK5,k3_tarski(sK6)),k3_tarski(X0)) != iProver_top
    | r2_hidden(sK1(sK5,k3_tarski(sK6)),sK4(X0,sK0(sK5,k3_tarski(sK6)))) = iProver_top
    | v13_waybel_0(sK4(X0,sK0(sK5,k3_tarski(sK6))),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_784,c_2654])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_786,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,k3_tarski(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1702,plain,
    ( r2_hidden(X0,sK4(X1,X2)) != iProver_top
    | r2_hidden(X2,k3_tarski(X1)) != iProver_top
    | r2_hidden(X0,k3_tarski(X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_785,c_786])).

cnf(c_2900,plain,
    ( m1_subset_1(sK4(X0,sK0(sK5,k3_tarski(sK6))),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r2_hidden(sK0(sK5,k3_tarski(sK6)),k3_tarski(X0)) != iProver_top
    | r2_hidden(sK1(sK5,k3_tarski(sK6)),k3_tarski(X0)) = iProver_top
    | v13_waybel_0(sK4(X0,sK0(sK5,k3_tarski(sK6))),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2659,c_1702])).

cnf(c_11413,plain,
    ( r2_hidden(sK4(X0,sK0(sK5,k3_tarski(sK6))),sK6) != iProver_top
    | r2_hidden(sK0(sK5,k3_tarski(sK6)),k3_tarski(X0)) != iProver_top
    | r2_hidden(sK1(sK5,k3_tarski(sK6)),k3_tarski(X0)) = iProver_top
    | v13_waybel_0(sK4(X0,sK0(sK5,k3_tarski(sK6))),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1148,c_2900])).

cnf(c_12028,plain,
    ( r2_hidden(sK4(sK6,sK0(sK5,k3_tarski(sK6))),sK6) != iProver_top
    | r2_hidden(sK0(sK5,k3_tarski(sK6)),k3_tarski(sK6)) != iProver_top
    | r2_hidden(sK1(sK5,k3_tarski(sK6)),k3_tarski(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1420,c_11413])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(sK1(X1,X0),X0)
    | v13_waybel_0(X0,X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_321,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(sK1(X1,X0),X0)
    | v13_waybel_0(X0,X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_18])).

cnf(c_322,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(sK1(sK5,X0),X0)
    | v13_waybel_0(X0,sK5) ),
    inference(unflattening,[status(thm)],[c_321])).

cnf(c_773,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r2_hidden(sK1(sK5,X0),X0) != iProver_top
    | v13_waybel_0(X0,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_322])).

cnf(c_1692,plain,
    ( r2_hidden(sK1(sK5,k3_tarski(sK6)),k3_tarski(sK6)) != iProver_top
    | v13_waybel_0(k3_tarski(sK6),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1685,c_773])).

cnf(c_880,plain,
    ( ~ r2_hidden(X0,k3_tarski(sK6))
    | r2_hidden(sK4(sK6,X0),sK6) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1586,plain,
    ( r2_hidden(sK4(sK6,sK0(sK5,k3_tarski(sK6))),sK6)
    | ~ r2_hidden(sK0(sK5,k3_tarski(sK6)),k3_tarski(sK6)) ),
    inference(instantiation,[status(thm)],[c_880])).

cnf(c_1589,plain,
    ( r2_hidden(sK4(sK6,sK0(sK5,k3_tarski(sK6))),sK6) = iProver_top
    | r2_hidden(sK0(sK5,k3_tarski(sK6)),k3_tarski(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1586])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(sK0(X1,X0),X0)
    | v13_waybel_0(X0,X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_306,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(sK0(X1,X0),X0)
    | v13_waybel_0(X0,X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_18])).

cnf(c_307,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | r2_hidden(sK0(sK5,X0),X0)
    | v13_waybel_0(X0,sK5) ),
    inference(unflattening,[status(thm)],[c_306])).

cnf(c_1585,plain,
    ( ~ m1_subset_1(k3_tarski(sK6),k1_zfmisc_1(u1_struct_0(sK5)))
    | r2_hidden(sK0(sK5,k3_tarski(sK6)),k3_tarski(sK6))
    | v13_waybel_0(k3_tarski(sK6),sK5) ),
    inference(instantiation,[status(thm)],[c_307])).

cnf(c_1587,plain,
    ( m1_subset_1(k3_tarski(sK6),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r2_hidden(sK0(sK5,k3_tarski(sK6)),k3_tarski(sK6)) = iProver_top
    | v13_waybel_0(k3_tarski(sK6),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1585])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12028,c_1692,c_1589,c_1587,c_1294,c_1014,c_979,c_888,c_497,c_24,c_20,c_17])).


%------------------------------------------------------------------------------
