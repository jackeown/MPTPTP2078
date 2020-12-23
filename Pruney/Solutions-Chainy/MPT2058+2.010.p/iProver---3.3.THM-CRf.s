%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:16 EST 2020

% Result     : Theorem 2.84s
% Output     : CNFRefutation 2.84s
% Verified   : 
% Statistics : Number of formulae       :  250 (1407 expanded)
%              Number of clauses        :  156 ( 310 expanded)
%              Number of leaves         :   21 ( 389 expanded)
%              Depth                    :   31
%              Number of atoms          : 1472 (12522 expanded)
%              Number of equality atoms :  254 ( 452 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal clause size      :   26 (   6 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f41,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f40])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f41,f42])).

fof(f57,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f67,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f68,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)
              <=> r1_waybel_7(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
              & ~ v1_xboole_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)
                <=> r1_waybel_7(X0,X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)
              <~> r1_waybel_7(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)
              <~> r1_waybel_7(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f50,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_waybel_7(X0,X1,X2)
                | ~ r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) )
              & ( r1_waybel_7(X0,X1,X2)
                | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f51,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_waybel_7(X0,X1,X2)
                | ~ r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) )
              & ( r1_waybel_7(X0,X1,X2)
                | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f50])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_waybel_7(X0,X1,X2)
            | ~ r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) )
          & ( r1_waybel_7(X0,X1,X2)
            | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( ~ r1_waybel_7(X0,X1,sK4)
          | ~ r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),sK4) )
        & ( r1_waybel_7(X0,X1,sK4)
          | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),sK4) )
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_waybel_7(X0,X1,X2)
                | ~ r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) )
              & ( r1_waybel_7(X0,X1,X2)
                | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
     => ( ? [X2] :
            ( ( ~ r1_waybel_7(X0,sK3,X2)
              | ~ r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),sK3),X2) )
            & ( r1_waybel_7(X0,sK3,X2)
              | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),sK3),X2) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
        & v13_waybel_0(sK3,k3_yellow_1(k2_struct_0(X0)))
        & v2_waybel_0(sK3,k3_yellow_1(k2_struct_0(X0)))
        & v1_subset_1(sK3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
        & ~ v1_xboole_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r1_waybel_7(X0,X1,X2)
                  | ~ r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) )
                & ( r1_waybel_7(X0,X1,X2)
                  | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_waybel_7(sK2,X1,X2)
                | ~ r3_waybel_9(sK2,k3_yellow19(sK2,k2_struct_0(sK2),X1),X2) )
              & ( r1_waybel_7(sK2,X1,X2)
                | r3_waybel_9(sK2,k3_yellow19(sK2,k2_struct_0(sK2),X1),X2) )
              & m1_subset_1(X2,u1_struct_0(sK2)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK2)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK2)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK2)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK2))))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
    ( ( ~ r1_waybel_7(sK2,sK3,sK4)
      | ~ r3_waybel_9(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3),sK4) )
    & ( r1_waybel_7(sK2,sK3,sK4)
      | r3_waybel_9(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3),sK4) )
    & m1_subset_1(sK4,u1_struct_0(sK2))
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK2)))))
    & v13_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK2)))
    & v2_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK2)))
    & v1_subset_1(sK3,u1_struct_0(k3_yellow_1(k2_struct_0(sK2))))
    & ~ v1_xboole_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f51,f54,f53,f52])).

fof(f83,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f44])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f45])).

fof(f47,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK1(X0,X1,X2),X1)
            | ~ r2_hidden(sK1(X0,X1,X2),X0)
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
              & r2_hidden(sK1(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f46,f47])).

fof(f58,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f105,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f58])).

fof(f81,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f56,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f86,plain,(
    v2_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f55])).

fof(f10,axiom,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f101,plain,(
    v2_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) ),
    inference(definition_unfolding,[],[f86,f71])).

fof(f87,plain,(
    v13_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f55])).

fof(f100,plain,(
    v13_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) ),
    inference(definition_unfolding,[],[f87,f71])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v7_waybel_0(k3_yellow19(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( v7_waybel_0(k3_yellow19(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
      | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | ~ v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f77,f71,f71,f71,f71])).

fof(f85,plain,(
    v1_subset_1(sK3,u1_struct_0(k3_yellow_1(k2_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f55])).

fof(f102,plain,(
    v1_subset_1(sK3,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))) ),
    inference(definition_unfolding,[],[f85,f71])).

fof(f84,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f88,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK2))))) ),
    inference(cnf_transformation,[],[f55])).

fof(f99,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))))) ),
    inference(definition_unfolding,[],[f88,f71])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
      | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f73,f71,f71,f71])).

fof(f91,plain,
    ( ~ r1_waybel_7(sK2,sK3,sK4)
    | ~ r3_waybel_9(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3),sK4) ),
    inference(cnf_transformation,[],[f55])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r3_waybel_9(X0,X1,X2)
              <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_waybel_9(X0,X1,X2)
              <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_waybel_9(X0,X1,X2)
              <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_waybel_9(X0,X1,X2)
                  | ~ r1_waybel_7(X0,k2_yellow19(X0,X1),X2) )
                & ( r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
                  | ~ r3_waybel_9(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( r3_waybel_9(X0,X1,X2)
      | ~ r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f82,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f89,plain,(
    m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f55])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
         => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f98,plain,(
    ! [X0,X1] :
      ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | ~ v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f80,f71,f71,f71,f71])).

fof(f90,plain,
    ( r1_waybel_7(sK2,sK3,sK4)
    | r3_waybel_9(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3),sK4) ),
    inference(cnf_transformation,[],[f55])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k3_yellow19(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k3_yellow19(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
      | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f72,f71,f71,f71])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v4_orders_2(k3_yellow19(X0,X1,X2))
        & v3_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v4_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v4_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( v4_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( v4_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v4_orders_2(k3_yellow19(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( v4_orders_2(k3_yellow19(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
      | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f75,f71,f71,f71])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_4494,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_11,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_12,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_32,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_623,plain,
    ( l1_struct_0(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_32])).

cnf(c_624,plain,
    ( l1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_623])).

cnf(c_1112,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_624])).

cnf(c_1113,plain,
    ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unflattening,[status(thm)],[c_1112])).

cnf(c_4479,plain,
    ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1113])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_4485,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_5481,plain,
    ( k7_subset_1(u1_struct_0(sK2),k2_struct_0(sK2),X0) = k4_xboole_0(k2_struct_0(sK2),X0) ),
    inference(superposition,[status(thm)],[c_4479,c_4485])).

cnf(c_9,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_4486,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_8,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_4505,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4486,c_8])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1)
    | k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0)) = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1152,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0)) = X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_624])).

cnf(c_1153,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k7_subset_1(u1_struct_0(sK2),k2_struct_0(sK2),k7_subset_1(u1_struct_0(sK2),k2_struct_0(sK2),X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_1152])).

cnf(c_4478,plain,
    ( k7_subset_1(u1_struct_0(sK2),k2_struct_0(sK2),k7_subset_1(u1_struct_0(sK2),k2_struct_0(sK2),X0)) = X0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1153])).

cnf(c_4960,plain,
    ( k7_subset_1(u1_struct_0(sK2),k2_struct_0(sK2),k7_subset_1(u1_struct_0(sK2),k2_struct_0(sK2),u1_struct_0(sK2))) = u1_struct_0(sK2) ),
    inference(superposition,[status(thm)],[c_4505,c_4478])).

cnf(c_5906,plain,
    ( k7_subset_1(u1_struct_0(sK2),k2_struct_0(sK2),k4_xboole_0(k2_struct_0(sK2),u1_struct_0(sK2))) = u1_struct_0(sK2) ),
    inference(demodulation,[status(thm)],[c_5481,c_4960])).

cnf(c_6063,plain,
    ( k4_xboole_0(k2_struct_0(sK2),k4_xboole_0(k2_struct_0(sK2),u1_struct_0(sK2))) = u1_struct_0(sK2) ),
    inference(superposition,[status(thm)],[c_5481,c_5906])).

cnf(c_7,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_4487,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_6225,plain,
    ( r2_hidden(X0,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X0,k2_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6063,c_4487])).

cnf(c_6712,plain,
    ( r2_hidden(sK0(u1_struct_0(sK2)),k2_struct_0(sK2)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4494,c_6225])).

cnf(c_34,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_35,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_37,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_13,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_74,plain,
    ( v2_struct_0(X0) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_76,plain,
    ( v2_struct_0(sK2) = iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_74])).

cnf(c_77,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_79,plain,
    ( l1_pre_topc(sK2) != iProver_top
    | l1_struct_0(sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_77])).

cnf(c_6739,plain,
    ( r2_hidden(sK0(u1_struct_0(sK2)),k2_struct_0(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6712,c_35,c_37,c_76,c_79])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_4493,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_6744,plain,
    ( v1_xboole_0(k2_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6739,c_4493])).

cnf(c_29,negated_conjecture,
    ( v2_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_28,negated_conjecture,
    ( v13_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_19,plain,
    ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v7_waybel_0(k3_yellow19(X2,X1,X0))
    | v2_struct_0(X2)
    | ~ l1_struct_0(X2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_30,negated_conjecture,
    ( v1_subset_1(sK3,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_451,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v7_waybel_0(k3_yellow19(X2,X1,X0))
    | v2_struct_0(X2)
    | ~ l1_struct_0(X2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_30])).

cnf(c_452,plain,
    ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(X1,X0,sK3))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(sK3)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(unflattening,[status(thm)],[c_451])).

cnf(c_31,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_456,plain,
    ( v1_xboole_0(X0)
    | ~ l1_struct_0(X1)
    | v2_struct_0(X1)
    | v7_waybel_0(k3_yellow19(X1,X0,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v13_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_452,c_31])).

cnf(c_457,plain,
    ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(X1,X0,sK3))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(renaming,[status(thm)],[c_456])).

cnf(c_1119,plain,
    ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(X1,X0,sK3))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_457,c_624])).

cnf(c_1120,plain,
    ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK2,X0,sK3))
    | v2_struct_0(sK2)
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(unflattening,[status(thm)],[c_1119])).

cnf(c_1124,plain,
    ( v7_waybel_0(k3_yellow19(sK2,X0,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v13_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1120,c_34])).

cnf(c_1125,plain,
    ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK2,X0,sK3))
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(renaming,[status(thm)],[c_1124])).

cnf(c_1649,plain,
    ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK2,X0,sK3))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_1125])).

cnf(c_1927,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK2,X0,sK3))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_1649])).

cnf(c_3011,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK2,X0,sK3))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(equality_resolution_simp,[status(thm)],[c_1927])).

cnf(c_4471,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
    | v7_waybel_0(k3_yellow19(sK2,X0,sK3)) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3011])).

cnf(c_4863,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(k2_struct_0(sK2)))
    | m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))))) != iProver_top
    | v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) = iProver_top
    | v1_xboole_0(k2_struct_0(sK2)) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4471])).

cnf(c_5982,plain,
    ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))))) != iProver_top
    | v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) = iProver_top
    | v1_xboole_0(k2_struct_0(sK2)) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4863])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))))) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_42,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_80,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_82,plain,
    ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | l1_struct_0(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_80])).

cnf(c_15,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | l1_waybel_0(k3_yellow19(X2,X1,X0),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v2_struct_0(X2)
    | ~ l1_struct_0(X2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_24,negated_conjecture,
    ( ~ r1_waybel_7(sK2,sK3,sK4)
    | ~ r3_waybel_9(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3),sK4) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_255,plain,
    ( ~ r1_waybel_7(sK2,sK3,sK4)
    | ~ r3_waybel_9(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3),sK4) ),
    inference(prop_impl,[status(thm)],[c_24])).

cnf(c_21,plain,
    ( ~ r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
    | r3_waybel_9(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_33,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_574,plain,
    ( ~ r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
    | r3_waybel_9(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_33])).

cnf(c_575,plain,
    ( ~ r1_waybel_7(sK2,k2_yellow19(sK2,X0),X1)
    | r3_waybel_9(sK2,X0,X1)
    | ~ l1_waybel_0(X0,sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_574])).

cnf(c_579,plain,
    ( ~ r1_waybel_7(sK2,k2_yellow19(sK2,X0),X1)
    | r3_waybel_9(sK2,X0,X1)
    | ~ l1_waybel_0(X0,sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_575,c_34,c_32])).

cnf(c_952,plain,
    ( ~ r1_waybel_7(sK2,k2_yellow19(sK2,X0),X1)
    | ~ r1_waybel_7(sK2,sK3,sK4)
    | ~ l1_waybel_0(X0,sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != X0
    | sK4 != X1
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_255,c_579])).

cnf(c_953,plain,
    ( ~ r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
    | ~ r1_waybel_7(sK2,sK3,sK4)
    | ~ l1_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3),sK2)
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) ),
    inference(unflattening,[status(thm)],[c_952])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_955,plain,
    ( ~ l1_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3),sK2)
    | ~ r1_waybel_7(sK2,sK3,sK4)
    | ~ r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
    | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_953,c_26])).

cnf(c_956,plain,
    ( ~ r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
    | ~ r1_waybel_7(sK2,sK3,sK4)
    | ~ l1_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3),sK2)
    | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) ),
    inference(renaming,[status(thm)],[c_955])).

cnf(c_992,plain,
    ( ~ r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
    | ~ r1_waybel_7(sK2,sK3,sK4)
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | v2_struct_0(X2)
    | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | ~ l1_struct_0(X2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != k3_yellow19(X2,X1,X0)
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_956])).

cnf(c_993,plain,
    ( ~ r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
    | ~ r1_waybel_7(sK2,sK3,sK4)
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | v2_struct_0(sK2)
    | ~ l1_struct_0(sK2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != k3_yellow19(sK2,X1,X0) ),
    inference(unflattening,[status(thm)],[c_992])).

cnf(c_78,plain,
    ( ~ l1_pre_topc(sK2)
    | l1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_997,plain,
    ( ~ r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
    | ~ r1_waybel_7(sK2,sK3,sK4)
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != k3_yellow19(sK2,X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_993,c_34,c_32,c_78])).

cnf(c_1604,plain,
    ( ~ r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
    | ~ r1_waybel_7(sK2,sK3,sK4)
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != k3_yellow19(sK2,X1,X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X1))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_997,c_28])).

cnf(c_1605,plain,
    ( ~ r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
    | ~ r1_waybel_7(sK2,sK3,sK4)
    | ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | v1_xboole_0(X0)
    | v1_xboole_0(sK3)
    | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != k3_yellow19(sK2,X0,sK3)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_1604])).

cnf(c_1609,plain,
    ( v1_xboole_0(X0)
    | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | ~ r1_waybel_7(sK2,sK3,sK4)
    | ~ r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
    | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != k3_yellow19(sK2,X0,sK3)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1605,c_31])).

cnf(c_1610,plain,
    ( ~ r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
    | ~ r1_waybel_7(sK2,sK3,sK4)
    | ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | v1_xboole_0(X0)
    | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != k3_yellow19(sK2,X0,sK3)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(renaming,[status(thm)],[c_1609])).

cnf(c_1953,plain,
    ( ~ r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
    | ~ r1_waybel_7(sK2,sK3,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | v1_xboole_0(X0)
    | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != k3_yellow19(sK2,X0,sK3)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_1610])).

cnf(c_3007,plain,
    ( ~ r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
    | ~ r1_waybel_7(sK2,sK3,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | v1_xboole_0(X0)
    | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != k3_yellow19(sK2,X0,sK3)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(equality_resolution_simp,[status(thm)],[c_1953])).

cnf(c_4004,plain,
    ( ~ r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
    | ~ r1_waybel_7(sK2,sK3,sK4)
    | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_3007])).

cnf(c_4472,plain,
    ( r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4) != iProver_top
    | r1_waybel_7(sK2,sK3,sK4) != iProver_top
    | v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) != iProver_top
    | v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) != iProver_top
    | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4004])).

cnf(c_23,plain,
    ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_490,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_30])).

cnf(c_491,plain,
    ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ v13_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | v1_xboole_0(sK3)
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK3)) = sK3
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) ),
    inference(unflattening,[status(thm)],[c_490])).

cnf(c_495,plain,
    ( ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | ~ v13_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK3)) = sK3
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_491,c_31])).

cnf(c_496,plain,
    ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ v13_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK3)) = sK3
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) ),
    inference(renaming,[status(thm)],[c_495])).

cnf(c_1090,plain,
    ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ v13_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | v2_struct_0(X0)
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK3)) = sK3
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_496,c_624])).

cnf(c_1091,plain,
    ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(sK2))))
    | ~ v13_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(sK2))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))))
    | v2_struct_0(sK2)
    | k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)) = sK3
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) ),
    inference(unflattening,[status(thm)],[c_1090])).

cnf(c_1093,plain,
    ( k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)) = sK3
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1091,c_34,c_29,c_28,c_27])).

cnf(c_3018,plain,
    ( k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)) = sK3 ),
    inference(equality_resolution_simp,[status(thm)],[c_1093])).

cnf(c_4619,plain,
    ( r1_waybel_7(sK2,sK3,sK4) != iProver_top
    | v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) != iProver_top
    | v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) != iProver_top
    | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4472,c_3018])).

cnf(c_25,negated_conjecture,
    ( r1_waybel_7(sK2,sK3,sK4)
    | r3_waybel_9(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3),sK4) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_257,plain,
    ( r1_waybel_7(sK2,sK3,sK4)
    | r3_waybel_9(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3),sK4) ),
    inference(prop_impl,[status(thm)],[c_25])).

cnf(c_22,plain,
    ( r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
    | ~ r3_waybel_9(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_541,plain,
    ( r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
    | ~ r3_waybel_9(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_33])).

cnf(c_542,plain,
    ( r1_waybel_7(sK2,k2_yellow19(sK2,X0),X1)
    | ~ r3_waybel_9(sK2,X0,X1)
    | ~ l1_waybel_0(X0,sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_541])).

cnf(c_546,plain,
    ( r1_waybel_7(sK2,k2_yellow19(sK2,X0),X1)
    | ~ r3_waybel_9(sK2,X0,X1)
    | ~ l1_waybel_0(X0,sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_542,c_34,c_32])).

cnf(c_926,plain,
    ( r1_waybel_7(sK2,k2_yellow19(sK2,X0),X1)
    | r1_waybel_7(sK2,sK3,sK4)
    | ~ l1_waybel_0(X0,sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != X0
    | sK4 != X1
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_257,c_546])).

cnf(c_927,plain,
    ( r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
    | r1_waybel_7(sK2,sK3,sK4)
    | ~ l1_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3),sK2)
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) ),
    inference(unflattening,[status(thm)],[c_926])).

cnf(c_929,plain,
    ( ~ l1_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3),sK2)
    | r1_waybel_7(sK2,sK3,sK4)
    | r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
    | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_927,c_26])).

cnf(c_930,plain,
    ( r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
    | r1_waybel_7(sK2,sK3,sK4)
    | ~ l1_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3),sK2)
    | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) ),
    inference(renaming,[status(thm)],[c_929])).

cnf(c_1040,plain,
    ( r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
    | r1_waybel_7(sK2,sK3,sK4)
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | v2_struct_0(X2)
    | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | ~ l1_struct_0(X2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != k3_yellow19(X2,X1,X0)
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_930])).

cnf(c_1041,plain,
    ( r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
    | r1_waybel_7(sK2,sK3,sK4)
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | v2_struct_0(sK2)
    | ~ l1_struct_0(sK2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != k3_yellow19(sK2,X1,X0) ),
    inference(unflattening,[status(thm)],[c_1040])).

cnf(c_1045,plain,
    ( r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
    | r1_waybel_7(sK2,sK3,sK4)
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != k3_yellow19(sK2,X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1041,c_34,c_32,c_78])).

cnf(c_1559,plain,
    ( r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
    | r1_waybel_7(sK2,sK3,sK4)
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != k3_yellow19(sK2,X1,X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X1))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1045,c_28])).

cnf(c_1560,plain,
    ( r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
    | r1_waybel_7(sK2,sK3,sK4)
    | ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | v1_xboole_0(X0)
    | v1_xboole_0(sK3)
    | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != k3_yellow19(sK2,X0,sK3)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_1559])).

cnf(c_1564,plain,
    ( v1_xboole_0(X0)
    | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | r1_waybel_7(sK2,sK3,sK4)
    | r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
    | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != k3_yellow19(sK2,X0,sK3)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1560,c_31])).

cnf(c_1565,plain,
    ( r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
    | r1_waybel_7(sK2,sK3,sK4)
    | ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | v1_xboole_0(X0)
    | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != k3_yellow19(sK2,X0,sK3)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(renaming,[status(thm)],[c_1564])).

cnf(c_1991,plain,
    ( r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
    | r1_waybel_7(sK2,sK3,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | v1_xboole_0(X0)
    | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != k3_yellow19(sK2,X0,sK3)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_1565])).

cnf(c_3003,plain,
    ( r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
    | r1_waybel_7(sK2,sK3,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | v1_xboole_0(X0)
    | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != k3_yellow19(sK2,X0,sK3)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(equality_resolution_simp,[status(thm)],[c_1991])).

cnf(c_4005,plain,
    ( r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
    | r1_waybel_7(sK2,sK3,sK4)
    | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_3003])).

cnf(c_4474,plain,
    ( r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4) = iProver_top
    | r1_waybel_7(sK2,sK3,sK4) = iProver_top
    | v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) != iProver_top
    | v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) != iProver_top
    | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4005])).

cnf(c_4596,plain,
    ( r1_waybel_7(sK2,sK3,sK4) = iProver_top
    | v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) != iProver_top
    | v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) != iProver_top
    | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4474,c_3018])).

cnf(c_4625,plain,
    ( v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) != iProver_top
    | v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) != iProver_top
    | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4619,c_4596])).

cnf(c_16,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v2_struct_0(X2)
    | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
    | ~ l1_struct_0(X2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1197,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v2_struct_0(X2)
    | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_624])).

cnf(c_1198,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_struct_0(k3_yellow19(sK2,X1,X0))
    | v2_struct_0(sK2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(unflattening,[status(thm)],[c_1197])).

cnf(c_1202,plain,
    ( ~ v2_struct_0(k3_yellow19(sK2,X1,X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1198,c_34])).

cnf(c_1203,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_struct_0(k3_yellow19(sK2,X1,X0))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(renaming,[status(thm)],[c_1202])).

cnf(c_1499,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_struct_0(k3_yellow19(sK2,X1,X0))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X1))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1203,c_28])).

cnf(c_1500,plain,
    ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v2_struct_0(k3_yellow19(sK2,X0,sK3))
    | v1_xboole_0(X0)
    | v1_xboole_0(sK3)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_1499])).

cnf(c_1504,plain,
    ( v1_xboole_0(X0)
    | ~ v2_struct_0(k3_yellow19(sK2,X0,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1500,c_31])).

cnf(c_1505,plain,
    ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v2_struct_0(k3_yellow19(sK2,X0,sK3))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(renaming,[status(thm)],[c_1504])).

cnf(c_2052,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v2_struct_0(k3_yellow19(sK2,X0,sK3))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_1505])).

cnf(c_2995,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v2_struct_0(k3_yellow19(sK2,X0,sK3))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(equality_resolution_simp,[status(thm)],[c_2052])).

cnf(c_4477,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
    | v2_struct_0(k3_yellow19(sK2,X0,sK3)) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2995])).

cnf(c_5100,plain,
    ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))))) != iProver_top
    | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) != iProver_top
    | v1_xboole_0(k2_struct_0(sK2)) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4477])).

cnf(c_5411,plain,
    ( v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) != iProver_top
    | v1_xboole_0(k2_struct_0(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5100,c_37,c_42,c_79,c_82])).

cnf(c_4003,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v1_xboole_0(X0)
    | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != k3_yellow19(sK2,X0,sK3)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_3007])).

cnf(c_4473,plain,
    ( k3_yellow19(sK2,k2_struct_0(sK2),sK3) != k3_yellow19(sK2,X0,sK3)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4003])).

cnf(c_5135,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(k2_struct_0(sK2)))
    | m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))))) != iProver_top
    | v1_xboole_0(k2_struct_0(sK2)) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4473])).

cnf(c_5417,plain,
    ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))))) != iProver_top
    | v1_xboole_0(k2_struct_0(sK2)) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_5135])).

cnf(c_5419,plain,
    ( v1_xboole_0(k2_struct_0(sK2)) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5417,c_37,c_42,c_79,c_82])).

cnf(c_17,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v4_orders_2(k3_yellow19(X2,X1,X0))
    | v2_struct_0(X2)
    | ~ l1_struct_0(X2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1164,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v4_orders_2(k3_yellow19(X2,X1,X0))
    | v2_struct_0(X2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_624])).

cnf(c_1165,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | v4_orders_2(k3_yellow19(sK2,X1,X0))
    | v2_struct_0(sK2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(unflattening,[status(thm)],[c_1164])).

cnf(c_1169,plain,
    ( v4_orders_2(k3_yellow19(sK2,X1,X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1165,c_34])).

cnf(c_1170,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | v4_orders_2(k3_yellow19(sK2,X1,X0))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(renaming,[status(thm)],[c_1169])).

cnf(c_1529,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | v4_orders_2(k3_yellow19(sK2,X1,X0))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X1))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1170,c_28])).

cnf(c_1530,plain,
    ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(sK2,X0,sK3))
    | v1_xboole_0(X0)
    | v1_xboole_0(sK3)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_1529])).

cnf(c_1534,plain,
    ( v1_xboole_0(X0)
    | v4_orders_2(k3_yellow19(sK2,X0,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1530,c_31])).

cnf(c_1535,plain,
    ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(sK2,X0,sK3))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(renaming,[status(thm)],[c_1534])).

cnf(c_2029,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(sK2,X0,sK3))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_1535])).

cnf(c_2999,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(sK2,X0,sK3))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(equality_resolution_simp,[status(thm)],[c_2029])).

cnf(c_4476,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
    | v4_orders_2(k3_yellow19(sK2,X0,sK3)) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2999])).

cnf(c_5143,plain,
    ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))))) != iProver_top
    | v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) = iProver_top
    | v1_xboole_0(k2_struct_0(sK2)) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4476])).

cnf(c_5471,plain,
    ( v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) = iProver_top
    | v1_xboole_0(k2_struct_0(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5143,c_37,c_42,c_79,c_82])).

cnf(c_5984,plain,
    ( v1_xboole_0(k2_struct_0(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5982,c_37,c_42,c_79,c_82,c_4625,c_5411,c_5419,c_5471])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6744,c_5984])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 09:47:57 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 2.84/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.84/0.98  
% 2.84/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.84/0.98  
% 2.84/0.98  ------  iProver source info
% 2.84/0.98  
% 2.84/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.84/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.84/0.98  git: non_committed_changes: false
% 2.84/0.98  git: last_make_outside_of_git: false
% 2.84/0.98  
% 2.84/0.98  ------ 
% 2.84/0.98  
% 2.84/0.98  ------ Input Options
% 2.84/0.98  
% 2.84/0.98  --out_options                           all
% 2.84/0.98  --tptp_safe_out                         true
% 2.84/0.98  --problem_path                          ""
% 2.84/0.98  --include_path                          ""
% 2.84/0.98  --clausifier                            res/vclausify_rel
% 2.84/0.98  --clausifier_options                    --mode clausify
% 2.84/0.98  --stdin                                 false
% 2.84/0.98  --stats_out                             all
% 2.84/0.98  
% 2.84/0.98  ------ General Options
% 2.84/0.98  
% 2.84/0.98  --fof                                   false
% 2.84/0.98  --time_out_real                         305.
% 2.84/0.98  --time_out_virtual                      -1.
% 2.84/0.98  --symbol_type_check                     false
% 2.84/0.98  --clausify_out                          false
% 2.84/0.98  --sig_cnt_out                           false
% 2.84/0.98  --trig_cnt_out                          false
% 2.84/0.98  --trig_cnt_out_tolerance                1.
% 2.84/0.98  --trig_cnt_out_sk_spl                   false
% 2.84/0.98  --abstr_cl_out                          false
% 2.84/0.98  
% 2.84/0.98  ------ Global Options
% 2.84/0.98  
% 2.84/0.98  --schedule                              default
% 2.84/0.98  --add_important_lit                     false
% 2.84/0.98  --prop_solver_per_cl                    1000
% 2.84/0.98  --min_unsat_core                        false
% 2.84/0.98  --soft_assumptions                      false
% 2.84/0.98  --soft_lemma_size                       3
% 2.84/0.98  --prop_impl_unit_size                   0
% 2.84/0.98  --prop_impl_unit                        []
% 2.84/0.98  --share_sel_clauses                     true
% 2.84/0.98  --reset_solvers                         false
% 2.84/0.98  --bc_imp_inh                            [conj_cone]
% 2.84/0.98  --conj_cone_tolerance                   3.
% 2.84/0.98  --extra_neg_conj                        none
% 2.84/0.98  --large_theory_mode                     true
% 2.84/0.98  --prolific_symb_bound                   200
% 2.84/0.98  --lt_threshold                          2000
% 2.84/0.98  --clause_weak_htbl                      true
% 2.84/0.98  --gc_record_bc_elim                     false
% 2.84/0.98  
% 2.84/0.98  ------ Preprocessing Options
% 2.84/0.98  
% 2.84/0.98  --preprocessing_flag                    true
% 2.84/0.98  --time_out_prep_mult                    0.1
% 2.84/0.98  --splitting_mode                        input
% 2.84/0.98  --splitting_grd                         true
% 2.84/0.98  --splitting_cvd                         false
% 2.84/0.98  --splitting_cvd_svl                     false
% 2.84/0.98  --splitting_nvd                         32
% 2.84/0.98  --sub_typing                            true
% 2.84/0.98  --prep_gs_sim                           true
% 2.84/0.98  --prep_unflatten                        true
% 2.84/0.98  --prep_res_sim                          true
% 2.84/0.98  --prep_upred                            true
% 2.84/0.98  --prep_sem_filter                       exhaustive
% 2.84/0.98  --prep_sem_filter_out                   false
% 2.84/0.98  --pred_elim                             true
% 2.84/0.98  --res_sim_input                         true
% 2.84/0.98  --eq_ax_congr_red                       true
% 2.84/0.98  --pure_diseq_elim                       true
% 2.84/0.98  --brand_transform                       false
% 2.84/0.98  --non_eq_to_eq                          false
% 2.84/0.98  --prep_def_merge                        true
% 2.84/0.98  --prep_def_merge_prop_impl              false
% 2.84/0.98  --prep_def_merge_mbd                    true
% 2.84/0.98  --prep_def_merge_tr_red                 false
% 2.84/0.98  --prep_def_merge_tr_cl                  false
% 2.84/0.98  --smt_preprocessing                     true
% 2.84/0.98  --smt_ac_axioms                         fast
% 2.84/0.98  --preprocessed_out                      false
% 2.84/0.98  --preprocessed_stats                    false
% 2.84/0.98  
% 2.84/0.98  ------ Abstraction refinement Options
% 2.84/0.98  
% 2.84/0.98  --abstr_ref                             []
% 2.84/0.98  --abstr_ref_prep                        false
% 2.84/0.98  --abstr_ref_until_sat                   false
% 2.84/0.98  --abstr_ref_sig_restrict                funpre
% 2.84/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.84/0.98  --abstr_ref_under                       []
% 2.84/0.98  
% 2.84/0.98  ------ SAT Options
% 2.84/0.98  
% 2.84/0.98  --sat_mode                              false
% 2.84/0.98  --sat_fm_restart_options                ""
% 2.84/0.98  --sat_gr_def                            false
% 2.84/0.98  --sat_epr_types                         true
% 2.84/0.98  --sat_non_cyclic_types                  false
% 2.84/0.98  --sat_finite_models                     false
% 2.84/0.98  --sat_fm_lemmas                         false
% 2.84/0.98  --sat_fm_prep                           false
% 2.84/0.98  --sat_fm_uc_incr                        true
% 2.84/0.98  --sat_out_model                         small
% 2.84/0.98  --sat_out_clauses                       false
% 2.84/0.98  
% 2.84/0.98  ------ QBF Options
% 2.84/0.98  
% 2.84/0.98  --qbf_mode                              false
% 2.84/0.98  --qbf_elim_univ                         false
% 2.84/0.98  --qbf_dom_inst                          none
% 2.84/0.98  --qbf_dom_pre_inst                      false
% 2.84/0.98  --qbf_sk_in                             false
% 2.84/0.98  --qbf_pred_elim                         true
% 2.84/0.98  --qbf_split                             512
% 2.84/0.98  
% 2.84/0.98  ------ BMC1 Options
% 2.84/0.98  
% 2.84/0.98  --bmc1_incremental                      false
% 2.84/0.98  --bmc1_axioms                           reachable_all
% 2.84/0.98  --bmc1_min_bound                        0
% 2.84/0.98  --bmc1_max_bound                        -1
% 2.84/0.98  --bmc1_max_bound_default                -1
% 2.84/0.98  --bmc1_symbol_reachability              true
% 2.84/0.98  --bmc1_property_lemmas                  false
% 2.84/0.98  --bmc1_k_induction                      false
% 2.84/0.98  --bmc1_non_equiv_states                 false
% 2.84/0.98  --bmc1_deadlock                         false
% 2.84/0.98  --bmc1_ucm                              false
% 2.84/0.98  --bmc1_add_unsat_core                   none
% 2.84/0.98  --bmc1_unsat_core_children              false
% 2.84/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.84/0.98  --bmc1_out_stat                         full
% 2.84/0.98  --bmc1_ground_init                      false
% 2.84/0.98  --bmc1_pre_inst_next_state              false
% 2.84/0.98  --bmc1_pre_inst_state                   false
% 2.84/0.98  --bmc1_pre_inst_reach_state             false
% 2.84/0.98  --bmc1_out_unsat_core                   false
% 2.84/0.98  --bmc1_aig_witness_out                  false
% 2.84/0.98  --bmc1_verbose                          false
% 2.84/0.98  --bmc1_dump_clauses_tptp                false
% 2.84/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.84/0.98  --bmc1_dump_file                        -
% 2.84/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.84/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.84/0.98  --bmc1_ucm_extend_mode                  1
% 2.84/0.98  --bmc1_ucm_init_mode                    2
% 2.84/0.98  --bmc1_ucm_cone_mode                    none
% 2.84/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.84/0.98  --bmc1_ucm_relax_model                  4
% 2.84/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.84/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.84/0.98  --bmc1_ucm_layered_model                none
% 2.84/0.98  --bmc1_ucm_max_lemma_size               10
% 2.84/0.98  
% 2.84/0.98  ------ AIG Options
% 2.84/0.98  
% 2.84/0.98  --aig_mode                              false
% 2.84/0.98  
% 2.84/0.98  ------ Instantiation Options
% 2.84/0.98  
% 2.84/0.98  --instantiation_flag                    true
% 2.84/0.98  --inst_sos_flag                         false
% 2.84/0.98  --inst_sos_phase                        true
% 2.84/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.84/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.84/0.98  --inst_lit_sel_side                     num_symb
% 2.84/0.98  --inst_solver_per_active                1400
% 2.84/0.98  --inst_solver_calls_frac                1.
% 2.84/0.98  --inst_passive_queue_type               priority_queues
% 2.84/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.84/0.98  --inst_passive_queues_freq              [25;2]
% 2.84/0.98  --inst_dismatching                      true
% 2.84/0.98  --inst_eager_unprocessed_to_passive     true
% 2.84/0.98  --inst_prop_sim_given                   true
% 2.84/0.98  --inst_prop_sim_new                     false
% 2.84/0.98  --inst_subs_new                         false
% 2.84/0.98  --inst_eq_res_simp                      false
% 2.84/0.98  --inst_subs_given                       false
% 2.84/0.98  --inst_orphan_elimination               true
% 2.84/0.98  --inst_learning_loop_flag               true
% 2.84/0.98  --inst_learning_start                   3000
% 2.84/0.98  --inst_learning_factor                  2
% 2.84/0.98  --inst_start_prop_sim_after_learn       3
% 2.84/0.98  --inst_sel_renew                        solver
% 2.84/0.98  --inst_lit_activity_flag                true
% 2.84/0.98  --inst_restr_to_given                   false
% 2.84/0.98  --inst_activity_threshold               500
% 2.84/0.98  --inst_out_proof                        true
% 2.84/0.98  
% 2.84/0.98  ------ Resolution Options
% 2.84/0.98  
% 2.84/0.98  --resolution_flag                       true
% 2.84/0.98  --res_lit_sel                           adaptive
% 2.84/0.98  --res_lit_sel_side                      none
% 2.84/0.98  --res_ordering                          kbo
% 2.84/0.98  --res_to_prop_solver                    active
% 2.84/0.98  --res_prop_simpl_new                    false
% 2.84/0.98  --res_prop_simpl_given                  true
% 2.84/0.98  --res_passive_queue_type                priority_queues
% 2.84/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.84/0.98  --res_passive_queues_freq               [15;5]
% 2.84/0.98  --res_forward_subs                      full
% 2.84/0.98  --res_backward_subs                     full
% 2.84/0.98  --res_forward_subs_resolution           true
% 2.84/0.98  --res_backward_subs_resolution          true
% 2.84/0.98  --res_orphan_elimination                true
% 2.84/0.98  --res_time_limit                        2.
% 2.84/0.98  --res_out_proof                         true
% 2.84/0.98  
% 2.84/0.98  ------ Superposition Options
% 2.84/0.98  
% 2.84/0.98  --superposition_flag                    true
% 2.84/0.98  --sup_passive_queue_type                priority_queues
% 2.84/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.84/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.84/0.98  --demod_completeness_check              fast
% 2.84/0.98  --demod_use_ground                      true
% 2.84/0.98  --sup_to_prop_solver                    passive
% 2.84/0.98  --sup_prop_simpl_new                    true
% 2.84/0.98  --sup_prop_simpl_given                  true
% 2.84/0.98  --sup_fun_splitting                     false
% 2.84/0.98  --sup_smt_interval                      50000
% 2.84/0.98  
% 2.84/0.98  ------ Superposition Simplification Setup
% 2.84/0.98  
% 2.84/0.98  --sup_indices_passive                   []
% 2.84/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.84/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.84/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.84/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.84/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.84/0.98  --sup_full_bw                           [BwDemod]
% 2.84/0.98  --sup_immed_triv                        [TrivRules]
% 2.84/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.84/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.84/0.98  --sup_immed_bw_main                     []
% 2.84/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.84/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.84/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.84/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.84/0.98  
% 2.84/0.98  ------ Combination Options
% 2.84/0.98  
% 2.84/0.98  --comb_res_mult                         3
% 2.84/0.98  --comb_sup_mult                         2
% 2.84/0.98  --comb_inst_mult                        10
% 2.84/0.98  
% 2.84/0.98  ------ Debug Options
% 2.84/0.98  
% 2.84/0.98  --dbg_backtrace                         false
% 2.84/0.98  --dbg_dump_prop_clauses                 false
% 2.84/0.98  --dbg_dump_prop_clauses_file            -
% 2.84/0.98  --dbg_out_stat                          false
% 2.84/0.98  ------ Parsing...
% 2.84/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.84/0.98  
% 2.84/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe_e 
% 2.84/0.98  
% 2.84/0.98  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.84/0.98  
% 2.84/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.84/0.98  ------ Proving...
% 2.84/0.98  ------ Problem Properties 
% 2.84/0.98  
% 2.84/0.98  
% 2.84/0.98  clauses                                 26
% 2.84/0.98  conjectures                             4
% 2.84/0.98  EPR                                     3
% 2.84/0.98  Horn                                    17
% 2.84/0.98  unary                                   9
% 2.84/0.98  binary                                  6
% 2.84/0.98  lits                                    74
% 2.84/0.98  lits eq                                 15
% 2.84/0.98  fd_pure                                 0
% 2.84/0.98  fd_pseudo                               0
% 2.84/0.98  fd_cond                                 0
% 2.84/0.98  fd_pseudo_cond                          3
% 2.84/0.98  AC symbols                              0
% 2.84/0.98  
% 2.84/0.98  ------ Schedule dynamic 5 is on 
% 2.84/0.98  
% 2.84/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.84/0.98  
% 2.84/0.98  
% 2.84/0.98  ------ 
% 2.84/0.98  Current options:
% 2.84/0.98  ------ 
% 2.84/0.98  
% 2.84/0.98  ------ Input Options
% 2.84/0.98  
% 2.84/0.98  --out_options                           all
% 2.84/0.98  --tptp_safe_out                         true
% 2.84/0.98  --problem_path                          ""
% 2.84/0.98  --include_path                          ""
% 2.84/0.98  --clausifier                            res/vclausify_rel
% 2.84/0.98  --clausifier_options                    --mode clausify
% 2.84/0.98  --stdin                                 false
% 2.84/0.98  --stats_out                             all
% 2.84/0.98  
% 2.84/0.98  ------ General Options
% 2.84/0.98  
% 2.84/0.98  --fof                                   false
% 2.84/0.98  --time_out_real                         305.
% 2.84/0.98  --time_out_virtual                      -1.
% 2.84/0.98  --symbol_type_check                     false
% 2.84/0.98  --clausify_out                          false
% 2.84/0.98  --sig_cnt_out                           false
% 2.84/0.98  --trig_cnt_out                          false
% 2.84/0.98  --trig_cnt_out_tolerance                1.
% 2.84/0.98  --trig_cnt_out_sk_spl                   false
% 2.84/0.98  --abstr_cl_out                          false
% 2.84/0.98  
% 2.84/0.98  ------ Global Options
% 2.84/0.98  
% 2.84/0.98  --schedule                              default
% 2.84/0.98  --add_important_lit                     false
% 2.84/0.98  --prop_solver_per_cl                    1000
% 2.84/0.98  --min_unsat_core                        false
% 2.84/0.98  --soft_assumptions                      false
% 2.84/0.98  --soft_lemma_size                       3
% 2.84/0.98  --prop_impl_unit_size                   0
% 2.84/0.98  --prop_impl_unit                        []
% 2.84/0.98  --share_sel_clauses                     true
% 2.84/0.98  --reset_solvers                         false
% 2.84/0.98  --bc_imp_inh                            [conj_cone]
% 2.84/0.98  --conj_cone_tolerance                   3.
% 2.84/0.98  --extra_neg_conj                        none
% 2.84/0.98  --large_theory_mode                     true
% 2.84/0.98  --prolific_symb_bound                   200
% 2.84/0.98  --lt_threshold                          2000
% 2.84/0.98  --clause_weak_htbl                      true
% 2.84/0.98  --gc_record_bc_elim                     false
% 2.84/0.98  
% 2.84/0.98  ------ Preprocessing Options
% 2.84/0.98  
% 2.84/0.98  --preprocessing_flag                    true
% 2.84/0.98  --time_out_prep_mult                    0.1
% 2.84/0.98  --splitting_mode                        input
% 2.84/0.98  --splitting_grd                         true
% 2.84/0.98  --splitting_cvd                         false
% 2.84/0.98  --splitting_cvd_svl                     false
% 2.84/0.98  --splitting_nvd                         32
% 2.84/0.98  --sub_typing                            true
% 2.84/0.98  --prep_gs_sim                           true
% 2.84/0.98  --prep_unflatten                        true
% 2.84/0.98  --prep_res_sim                          true
% 2.84/0.98  --prep_upred                            true
% 2.84/0.98  --prep_sem_filter                       exhaustive
% 2.84/0.98  --prep_sem_filter_out                   false
% 2.84/0.98  --pred_elim                             true
% 2.84/0.98  --res_sim_input                         true
% 2.84/0.98  --eq_ax_congr_red                       true
% 2.84/0.98  --pure_diseq_elim                       true
% 2.84/0.98  --brand_transform                       false
% 2.84/0.98  --non_eq_to_eq                          false
% 2.84/0.98  --prep_def_merge                        true
% 2.84/0.98  --prep_def_merge_prop_impl              false
% 2.84/0.98  --prep_def_merge_mbd                    true
% 2.84/0.98  --prep_def_merge_tr_red                 false
% 2.84/0.98  --prep_def_merge_tr_cl                  false
% 2.84/0.98  --smt_preprocessing                     true
% 2.84/0.98  --smt_ac_axioms                         fast
% 2.84/0.98  --preprocessed_out                      false
% 2.84/0.98  --preprocessed_stats                    false
% 2.84/0.98  
% 2.84/0.98  ------ Abstraction refinement Options
% 2.84/0.98  
% 2.84/0.98  --abstr_ref                             []
% 2.84/0.98  --abstr_ref_prep                        false
% 2.84/0.98  --abstr_ref_until_sat                   false
% 2.84/0.98  --abstr_ref_sig_restrict                funpre
% 2.84/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.84/0.98  --abstr_ref_under                       []
% 2.84/0.98  
% 2.84/0.98  ------ SAT Options
% 2.84/0.98  
% 2.84/0.98  --sat_mode                              false
% 2.84/0.98  --sat_fm_restart_options                ""
% 2.84/0.98  --sat_gr_def                            false
% 2.84/0.98  --sat_epr_types                         true
% 2.84/0.98  --sat_non_cyclic_types                  false
% 2.84/0.98  --sat_finite_models                     false
% 2.84/0.98  --sat_fm_lemmas                         false
% 2.84/0.98  --sat_fm_prep                           false
% 2.84/0.98  --sat_fm_uc_incr                        true
% 2.84/0.98  --sat_out_model                         small
% 2.84/0.98  --sat_out_clauses                       false
% 2.84/0.98  
% 2.84/0.98  ------ QBF Options
% 2.84/0.98  
% 2.84/0.98  --qbf_mode                              false
% 2.84/0.98  --qbf_elim_univ                         false
% 2.84/0.98  --qbf_dom_inst                          none
% 2.84/0.98  --qbf_dom_pre_inst                      false
% 2.84/0.98  --qbf_sk_in                             false
% 2.84/0.98  --qbf_pred_elim                         true
% 2.84/0.98  --qbf_split                             512
% 2.84/0.98  
% 2.84/0.98  ------ BMC1 Options
% 2.84/0.98  
% 2.84/0.98  --bmc1_incremental                      false
% 2.84/0.98  --bmc1_axioms                           reachable_all
% 2.84/0.98  --bmc1_min_bound                        0
% 2.84/0.98  --bmc1_max_bound                        -1
% 2.84/0.98  --bmc1_max_bound_default                -1
% 2.84/0.98  --bmc1_symbol_reachability              true
% 2.84/0.98  --bmc1_property_lemmas                  false
% 2.84/0.98  --bmc1_k_induction                      false
% 2.84/0.98  --bmc1_non_equiv_states                 false
% 2.84/0.98  --bmc1_deadlock                         false
% 2.84/0.98  --bmc1_ucm                              false
% 2.84/0.98  --bmc1_add_unsat_core                   none
% 2.84/0.98  --bmc1_unsat_core_children              false
% 2.84/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.84/0.98  --bmc1_out_stat                         full
% 2.84/0.98  --bmc1_ground_init                      false
% 2.84/0.98  --bmc1_pre_inst_next_state              false
% 2.84/0.98  --bmc1_pre_inst_state                   false
% 2.84/0.98  --bmc1_pre_inst_reach_state             false
% 2.84/0.98  --bmc1_out_unsat_core                   false
% 2.84/0.98  --bmc1_aig_witness_out                  false
% 2.84/0.98  --bmc1_verbose                          false
% 2.84/0.98  --bmc1_dump_clauses_tptp                false
% 2.84/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.84/0.98  --bmc1_dump_file                        -
% 2.84/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.84/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.84/0.98  --bmc1_ucm_extend_mode                  1
% 2.84/0.98  --bmc1_ucm_init_mode                    2
% 2.84/0.98  --bmc1_ucm_cone_mode                    none
% 2.84/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.84/0.98  --bmc1_ucm_relax_model                  4
% 2.84/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.84/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.84/0.98  --bmc1_ucm_layered_model                none
% 2.84/0.98  --bmc1_ucm_max_lemma_size               10
% 2.84/0.98  
% 2.84/0.98  ------ AIG Options
% 2.84/0.98  
% 2.84/0.98  --aig_mode                              false
% 2.84/0.98  
% 2.84/0.98  ------ Instantiation Options
% 2.84/0.98  
% 2.84/0.98  --instantiation_flag                    true
% 2.84/0.98  --inst_sos_flag                         false
% 2.84/0.98  --inst_sos_phase                        true
% 2.84/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.84/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.84/0.98  --inst_lit_sel_side                     none
% 2.84/0.98  --inst_solver_per_active                1400
% 2.84/0.98  --inst_solver_calls_frac                1.
% 2.84/0.98  --inst_passive_queue_type               priority_queues
% 2.84/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.84/0.98  --inst_passive_queues_freq              [25;2]
% 2.84/0.98  --inst_dismatching                      true
% 2.84/0.98  --inst_eager_unprocessed_to_passive     true
% 2.84/0.98  --inst_prop_sim_given                   true
% 2.84/0.98  --inst_prop_sim_new                     false
% 2.84/0.98  --inst_subs_new                         false
% 2.84/0.98  --inst_eq_res_simp                      false
% 2.84/0.98  --inst_subs_given                       false
% 2.84/0.98  --inst_orphan_elimination               true
% 2.84/0.98  --inst_learning_loop_flag               true
% 2.84/0.98  --inst_learning_start                   3000
% 2.84/0.98  --inst_learning_factor                  2
% 2.84/0.98  --inst_start_prop_sim_after_learn       3
% 2.84/0.98  --inst_sel_renew                        solver
% 2.84/0.98  --inst_lit_activity_flag                true
% 2.84/0.98  --inst_restr_to_given                   false
% 2.84/0.98  --inst_activity_threshold               500
% 2.84/0.98  --inst_out_proof                        true
% 2.84/0.98  
% 2.84/0.98  ------ Resolution Options
% 2.84/0.98  
% 2.84/0.98  --resolution_flag                       false
% 2.84/0.98  --res_lit_sel                           adaptive
% 2.84/0.98  --res_lit_sel_side                      none
% 2.84/0.98  --res_ordering                          kbo
% 2.84/0.98  --res_to_prop_solver                    active
% 2.84/0.98  --res_prop_simpl_new                    false
% 2.84/0.98  --res_prop_simpl_given                  true
% 2.84/0.98  --res_passive_queue_type                priority_queues
% 2.84/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.84/0.98  --res_passive_queues_freq               [15;5]
% 2.84/0.98  --res_forward_subs                      full
% 2.84/0.98  --res_backward_subs                     full
% 2.84/0.98  --res_forward_subs_resolution           true
% 2.84/0.98  --res_backward_subs_resolution          true
% 2.84/0.98  --res_orphan_elimination                true
% 2.84/0.98  --res_time_limit                        2.
% 2.84/0.98  --res_out_proof                         true
% 2.84/0.98  
% 2.84/0.98  ------ Superposition Options
% 2.84/0.98  
% 2.84/0.98  --superposition_flag                    true
% 2.84/0.98  --sup_passive_queue_type                priority_queues
% 2.84/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.84/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.84/0.98  --demod_completeness_check              fast
% 2.84/0.98  --demod_use_ground                      true
% 2.84/0.98  --sup_to_prop_solver                    passive
% 2.84/0.98  --sup_prop_simpl_new                    true
% 2.84/0.98  --sup_prop_simpl_given                  true
% 2.84/0.98  --sup_fun_splitting                     false
% 2.84/0.98  --sup_smt_interval                      50000
% 2.84/0.98  
% 2.84/0.98  ------ Superposition Simplification Setup
% 2.84/0.98  
% 2.84/0.98  --sup_indices_passive                   []
% 2.84/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.84/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.84/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.84/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.84/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.84/0.98  --sup_full_bw                           [BwDemod]
% 2.84/0.98  --sup_immed_triv                        [TrivRules]
% 2.84/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.84/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.84/0.98  --sup_immed_bw_main                     []
% 2.84/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.84/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.84/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.84/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.84/0.98  
% 2.84/0.98  ------ Combination Options
% 2.84/0.98  
% 2.84/0.98  --comb_res_mult                         3
% 2.84/0.98  --comb_sup_mult                         2
% 2.84/0.98  --comb_inst_mult                        10
% 2.84/0.98  
% 2.84/0.98  ------ Debug Options
% 2.84/0.98  
% 2.84/0.98  --dbg_backtrace                         false
% 2.84/0.98  --dbg_dump_prop_clauses                 false
% 2.84/0.98  --dbg_dump_prop_clauses_file            -
% 2.84/0.98  --dbg_out_stat                          false
% 2.84/0.98  
% 2.84/0.98  
% 2.84/0.98  
% 2.84/0.98  
% 2.84/0.98  ------ Proving...
% 2.84/0.98  
% 2.84/0.98  
% 2.84/0.98  % SZS status Theorem for theBenchmark.p
% 2.84/0.98  
% 2.84/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.84/0.98  
% 2.84/0.98  fof(f1,axiom,(
% 2.84/0.98    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.84/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.84/0.98  
% 2.84/0.98  fof(f40,plain,(
% 2.84/0.98    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.84/0.98    inference(nnf_transformation,[],[f1])).
% 2.84/0.98  
% 2.84/0.98  fof(f41,plain,(
% 2.84/0.98    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.84/0.98    inference(rectify,[],[f40])).
% 2.84/0.98  
% 2.84/0.98  fof(f42,plain,(
% 2.84/0.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.84/0.98    introduced(choice_axiom,[])).
% 2.84/0.98  
% 2.84/0.98  fof(f43,plain,(
% 2.84/0.98    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.84/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f41,f42])).
% 2.84/0.98  
% 2.84/0.98  fof(f57,plain,(
% 2.84/0.98    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 2.84/0.98    inference(cnf_transformation,[],[f43])).
% 2.84/0.98  
% 2.84/0.98  fof(f6,axiom,(
% 2.84/0.98    ! [X0] : (l1_struct_0(X0) => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.84/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.84/0.98  
% 2.84/0.98  fof(f23,plain,(
% 2.84/0.98    ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0))),
% 2.84/0.98    inference(ennf_transformation,[],[f6])).
% 2.84/0.98  
% 2.84/0.98  fof(f67,plain,(
% 2.84/0.98    ( ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0)) )),
% 2.84/0.98    inference(cnf_transformation,[],[f23])).
% 2.84/0.98  
% 2.84/0.98  fof(f7,axiom,(
% 2.84/0.98    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.84/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.84/0.98  
% 2.84/0.98  fof(f24,plain,(
% 2.84/0.98    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.84/0.98    inference(ennf_transformation,[],[f7])).
% 2.84/0.98  
% 2.84/0.98  fof(f68,plain,(
% 2.84/0.98    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.84/0.98    inference(cnf_transformation,[],[f24])).
% 2.84/0.98  
% 2.84/0.98  fof(f16,conjecture,(
% 2.84/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <=> r1_waybel_7(X0,X1,X2)))))),
% 2.84/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.84/0.98  
% 2.84/0.98  fof(f17,negated_conjecture,(
% 2.84/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <=> r1_waybel_7(X0,X1,X2)))))),
% 2.84/0.98    inference(negated_conjecture,[],[f16])).
% 2.84/0.98  
% 2.84/0.98  fof(f38,plain,(
% 2.84/0.98    ? [X0] : (? [X1] : (? [X2] : ((r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <~> r1_waybel_7(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.84/0.98    inference(ennf_transformation,[],[f17])).
% 2.84/0.98  
% 2.84/0.98  fof(f39,plain,(
% 2.84/0.98    ? [X0] : (? [X1] : (? [X2] : ((r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <~> r1_waybel_7(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.84/0.98    inference(flattening,[],[f38])).
% 2.84/0.98  
% 2.84/0.98  fof(f50,plain,(
% 2.84/0.98    ? [X0] : (? [X1] : (? [X2] : (((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.84/0.98    inference(nnf_transformation,[],[f39])).
% 2.84/0.98  
% 2.84/0.98  fof(f51,plain,(
% 2.84/0.98    ? [X0] : (? [X1] : (? [X2] : ((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.84/0.98    inference(flattening,[],[f50])).
% 2.84/0.98  
% 2.84/0.98  fof(f54,plain,(
% 2.84/0.98    ( ! [X0,X1] : (? [X2] : ((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & m1_subset_1(X2,u1_struct_0(X0))) => ((~r1_waybel_7(X0,X1,sK4) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),sK4)) & (r1_waybel_7(X0,X1,sK4) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),sK4)) & m1_subset_1(sK4,u1_struct_0(X0)))) )),
% 2.84/0.98    introduced(choice_axiom,[])).
% 2.84/0.98  
% 2.84/0.98  fof(f53,plain,(
% 2.84/0.98    ( ! [X0] : (? [X1] : (? [X2] : ((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => (? [X2] : ((~r1_waybel_7(X0,sK3,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),sK3),X2)) & (r1_waybel_7(X0,sK3,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),sK3),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(sK3,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(sK3,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(sK3,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(sK3))) )),
% 2.84/0.98    introduced(choice_axiom,[])).
% 2.84/0.98  
% 2.84/0.98  fof(f52,plain,(
% 2.84/0.98    ? [X0] : (? [X1] : (? [X2] : ((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~r1_waybel_7(sK2,X1,X2) | ~r3_waybel_9(sK2,k3_yellow19(sK2,k2_struct_0(sK2),X1),X2)) & (r1_waybel_7(sK2,X1,X2) | r3_waybel_9(sK2,k3_yellow19(sK2,k2_struct_0(sK2),X1),X2)) & m1_subset_1(X2,u1_struct_0(sK2))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK2))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK2))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK2))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK2)))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 2.84/0.98    introduced(choice_axiom,[])).
% 2.84/0.98  
% 2.84/0.98  fof(f55,plain,(
% 2.84/0.98    (((~r1_waybel_7(sK2,sK3,sK4) | ~r3_waybel_9(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3),sK4)) & (r1_waybel_7(sK2,sK3,sK4) | r3_waybel_9(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3),sK4)) & m1_subset_1(sK4,u1_struct_0(sK2))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK2))))) & v13_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK2))) & v2_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK2))) & v1_subset_1(sK3,u1_struct_0(k3_yellow_1(k2_struct_0(sK2)))) & ~v1_xboole_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 2.84/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f51,f54,f53,f52])).
% 2.84/0.98  
% 2.84/0.98  fof(f83,plain,(
% 2.84/0.98    l1_pre_topc(sK2)),
% 2.84/0.98    inference(cnf_transformation,[],[f55])).
% 2.84/0.98  
% 2.84/0.98  fof(f5,axiom,(
% 2.84/0.98    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 2.84/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.84/0.98  
% 2.84/0.98  fof(f22,plain,(
% 2.84/0.98    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.84/0.98    inference(ennf_transformation,[],[f5])).
% 2.84/0.98  
% 2.84/0.98  fof(f66,plain,(
% 2.84/0.98    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.84/0.98    inference(cnf_transformation,[],[f22])).
% 2.84/0.98  
% 2.84/0.98  fof(f4,axiom,(
% 2.84/0.98    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 2.84/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.84/0.98  
% 2.84/0.98  fof(f65,plain,(
% 2.84/0.98    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 2.84/0.98    inference(cnf_transformation,[],[f4])).
% 2.84/0.98  
% 2.84/0.98  fof(f3,axiom,(
% 2.84/0.98    ! [X0] : k2_subset_1(X0) = X0),
% 2.84/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.84/0.98  
% 2.84/0.98  fof(f64,plain,(
% 2.84/0.98    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 2.84/0.98    inference(cnf_transformation,[],[f3])).
% 2.84/0.98  
% 2.84/0.98  fof(f9,axiom,(
% 2.84/0.98    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1))),
% 2.84/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.84/0.98  
% 2.84/0.98  fof(f27,plain,(
% 2.84/0.98    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_struct_0(X0))),
% 2.84/0.98    inference(ennf_transformation,[],[f9])).
% 2.84/0.98  
% 2.84/0.98  fof(f70,plain,(
% 2.84/0.98    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0)) )),
% 2.84/0.98    inference(cnf_transformation,[],[f27])).
% 2.84/0.98  
% 2.84/0.98  fof(f2,axiom,(
% 2.84/0.98    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.84/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.84/0.98  
% 2.84/0.98  fof(f44,plain,(
% 2.84/0.98    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.84/0.98    inference(nnf_transformation,[],[f2])).
% 2.84/0.98  
% 2.84/0.98  fof(f45,plain,(
% 2.84/0.98    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.84/0.98    inference(flattening,[],[f44])).
% 2.84/0.98  
% 2.84/0.98  fof(f46,plain,(
% 2.84/0.98    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.84/0.98    inference(rectify,[],[f45])).
% 2.84/0.98  
% 2.84/0.98  fof(f47,plain,(
% 2.84/0.98    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 2.84/0.98    introduced(choice_axiom,[])).
% 2.84/0.98  
% 2.84/0.98  fof(f48,plain,(
% 2.84/0.98    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.84/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f46,f47])).
% 2.84/0.98  
% 2.84/0.98  fof(f58,plain,(
% 2.84/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.84/0.98    inference(cnf_transformation,[],[f48])).
% 2.84/0.98  
% 2.84/0.98  fof(f105,plain,(
% 2.84/0.98    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 2.84/0.98    inference(equality_resolution,[],[f58])).
% 2.84/0.98  
% 2.84/0.98  fof(f81,plain,(
% 2.84/0.98    ~v2_struct_0(sK2)),
% 2.84/0.98    inference(cnf_transformation,[],[f55])).
% 2.84/0.98  
% 2.84/0.98  fof(f8,axiom,(
% 2.84/0.98    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.84/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.84/0.98  
% 2.84/0.98  fof(f25,plain,(
% 2.84/0.98    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.84/0.98    inference(ennf_transformation,[],[f8])).
% 2.84/0.98  
% 2.84/0.98  fof(f26,plain,(
% 2.84/0.98    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.84/0.98    inference(flattening,[],[f25])).
% 2.84/0.98  
% 2.84/0.98  fof(f69,plain,(
% 2.84/0.98    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.84/0.98    inference(cnf_transformation,[],[f26])).
% 2.84/0.98  
% 2.84/0.98  fof(f56,plain,(
% 2.84/0.98    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.84/0.98    inference(cnf_transformation,[],[f43])).
% 2.84/0.98  
% 2.84/0.98  fof(f86,plain,(
% 2.84/0.98    v2_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK2)))),
% 2.84/0.98    inference(cnf_transformation,[],[f55])).
% 2.84/0.98  
% 2.84/0.98  fof(f10,axiom,(
% 2.84/0.98    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))),
% 2.84/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.84/0.98  
% 2.84/0.98  fof(f71,plain,(
% 2.84/0.98    ( ! [X0] : (k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))) )),
% 2.84/0.98    inference(cnf_transformation,[],[f10])).
% 2.84/0.98  
% 2.84/0.98  fof(f101,plain,(
% 2.84/0.98    v2_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(sK2))))),
% 2.84/0.98    inference(definition_unfolding,[],[f86,f71])).
% 2.84/0.98  
% 2.84/0.98  fof(f87,plain,(
% 2.84/0.98    v13_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK2)))),
% 2.84/0.98    inference(cnf_transformation,[],[f55])).
% 2.84/0.98  
% 2.84/0.98  fof(f100,plain,(
% 2.84/0.98    v13_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(sK2))))),
% 2.84/0.98    inference(definition_unfolding,[],[f87,f71])).
% 2.84/0.98  
% 2.84/0.98  fof(f13,axiom,(
% 2.84/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v7_waybel_0(k3_yellow19(X0,X1,X2)) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 2.84/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.84/0.98  
% 2.84/0.98  fof(f19,plain,(
% 2.84/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v7_waybel_0(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 2.84/0.98    inference(pure_predicate_removal,[],[f13])).
% 2.84/0.98  
% 2.84/0.98  fof(f32,plain,(
% 2.84/0.98    ! [X0,X1,X2] : ((v7_waybel_0(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.84/0.98    inference(ennf_transformation,[],[f19])).
% 2.84/0.98  
% 2.84/0.98  fof(f33,plain,(
% 2.84/0.98    ! [X0,X1,X2] : ((v7_waybel_0(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.84/0.98    inference(flattening,[],[f32])).
% 2.84/0.98  
% 2.84/0.98  fof(f77,plain,(
% 2.84/0.98    ( ! [X2,X0,X1] : (v7_waybel_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.84/0.98    inference(cnf_transformation,[],[f33])).
% 2.84/0.98  
% 2.84/0.98  fof(f96,plain,(
% 2.84/0.98    ( ! [X2,X0,X1] : (v7_waybel_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1)))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.84/0.98    inference(definition_unfolding,[],[f77,f71,f71,f71,f71])).
% 2.84/0.98  
% 2.84/0.98  fof(f85,plain,(
% 2.84/0.98    v1_subset_1(sK3,u1_struct_0(k3_yellow_1(k2_struct_0(sK2))))),
% 2.84/0.98    inference(cnf_transformation,[],[f55])).
% 2.84/0.98  
% 2.84/0.98  fof(f102,plain,(
% 2.84/0.98    v1_subset_1(sK3,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))))),
% 2.84/0.98    inference(definition_unfolding,[],[f85,f71])).
% 2.84/0.98  
% 2.84/0.98  fof(f84,plain,(
% 2.84/0.98    ~v1_xboole_0(sK3)),
% 2.84/0.98    inference(cnf_transformation,[],[f55])).
% 2.84/0.98  
% 2.84/0.98  fof(f88,plain,(
% 2.84/0.98    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK2)))))),
% 2.84/0.98    inference(cnf_transformation,[],[f55])).
% 2.84/0.98  
% 2.84/0.98  fof(f99,plain,(
% 2.84/0.98    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))))),
% 2.84/0.98    inference(definition_unfolding,[],[f88,f71])).
% 2.84/0.98  
% 2.84/0.98  fof(f11,axiom,(
% 2.84/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 2.84/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.84/0.98  
% 2.84/0.98  fof(f20,plain,(
% 2.84/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 2.84/0.98    inference(pure_predicate_removal,[],[f11])).
% 2.84/0.98  
% 2.84/0.98  fof(f28,plain,(
% 2.84/0.98    ! [X0,X1,X2] : ((l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.84/0.98    inference(ennf_transformation,[],[f20])).
% 2.84/0.98  
% 2.84/0.98  fof(f29,plain,(
% 2.84/0.98    ! [X0,X1,X2] : ((l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.84/0.98    inference(flattening,[],[f28])).
% 2.84/0.98  
% 2.84/0.98  fof(f73,plain,(
% 2.84/0.98    ( ! [X2,X0,X1] : (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.84/0.98    inference(cnf_transformation,[],[f29])).
% 2.84/0.98  
% 2.84/0.98  fof(f92,plain,(
% 2.84/0.98    ( ! [X2,X0,X1] : (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.84/0.98    inference(definition_unfolding,[],[f73,f71,f71,f71])).
% 2.84/0.98  
% 2.84/0.98  fof(f91,plain,(
% 2.84/0.98    ~r1_waybel_7(sK2,sK3,sK4) | ~r3_waybel_9(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3),sK4)),
% 2.84/0.98    inference(cnf_transformation,[],[f55])).
% 2.84/0.98  
% 2.84/0.98  fof(f14,axiom,(
% 2.84/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,X1,X2) <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2)))))),
% 2.84/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.84/0.98  
% 2.84/0.98  fof(f34,plain,(
% 2.84/0.98    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.84/0.98    inference(ennf_transformation,[],[f14])).
% 2.84/0.98  
% 2.84/0.98  fof(f35,plain,(
% 2.84/0.98    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.84/0.98    inference(flattening,[],[f34])).
% 2.84/0.98  
% 2.84/0.98  fof(f49,plain,(
% 2.84/0.98    ! [X0] : (! [X1] : (! [X2] : (((r3_waybel_9(X0,X1,X2) | ~r1_waybel_7(X0,k2_yellow19(X0,X1),X2)) & (r1_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~r3_waybel_9(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.84/0.98    inference(nnf_transformation,[],[f35])).
% 2.84/0.98  
% 2.84/0.98  fof(f79,plain,(
% 2.84/0.98    ( ! [X2,X0,X1] : (r3_waybel_9(X0,X1,X2) | ~r1_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.84/0.98    inference(cnf_transformation,[],[f49])).
% 2.84/0.98  
% 2.84/0.98  fof(f82,plain,(
% 2.84/0.98    v2_pre_topc(sK2)),
% 2.84/0.98    inference(cnf_transformation,[],[f55])).
% 2.84/0.98  
% 2.84/0.98  fof(f89,plain,(
% 2.84/0.98    m1_subset_1(sK4,u1_struct_0(sK2))),
% 2.84/0.98    inference(cnf_transformation,[],[f55])).
% 2.84/0.98  
% 2.84/0.98  fof(f15,axiom,(
% 2.84/0.98    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 2.84/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.84/0.98  
% 2.84/0.98  fof(f36,plain,(
% 2.84/0.98    ! [X0] : (! [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.84/0.98    inference(ennf_transformation,[],[f15])).
% 2.84/0.98  
% 2.84/0.98  fof(f37,plain,(
% 2.84/0.98    ! [X0] : (! [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.84/0.98    inference(flattening,[],[f36])).
% 2.84/0.98  
% 2.84/0.98  fof(f80,plain,(
% 2.84/0.98    ( ! [X0,X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.84/0.98    inference(cnf_transformation,[],[f37])).
% 2.84/0.98  
% 2.84/0.98  fof(f98,plain,(
% 2.84/0.98    ( ! [X0,X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.84/0.98    inference(definition_unfolding,[],[f80,f71,f71,f71,f71])).
% 2.84/0.98  
% 2.84/0.98  fof(f90,plain,(
% 2.84/0.98    r1_waybel_7(sK2,sK3,sK4) | r3_waybel_9(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3),sK4)),
% 2.84/0.98    inference(cnf_transformation,[],[f55])).
% 2.84/0.98  
% 2.84/0.98  fof(f78,plain,(
% 2.84/0.98    ( ! [X2,X0,X1] : (r1_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.84/0.98    inference(cnf_transformation,[],[f49])).
% 2.84/0.98  
% 2.84/0.98  fof(f72,plain,(
% 2.84/0.98    ( ! [X2,X0,X1] : (~v2_struct_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.84/0.98    inference(cnf_transformation,[],[f29])).
% 2.84/0.98  
% 2.84/0.98  fof(f93,plain,(
% 2.84/0.98    ( ! [X2,X0,X1] : (~v2_struct_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.84/0.98    inference(definition_unfolding,[],[f72,f71,f71,f71])).
% 2.84/0.98  
% 2.84/0.98  fof(f12,axiom,(
% 2.84/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & v3_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 2.84/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.84/0.98  
% 2.84/0.98  fof(f18,plain,(
% 2.84/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 2.84/0.98    inference(pure_predicate_removal,[],[f12])).
% 2.84/0.98  
% 2.84/0.98  fof(f21,plain,(
% 2.84/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 2.84/0.98    inference(pure_predicate_removal,[],[f18])).
% 2.84/0.98  
% 2.84/0.98  fof(f30,plain,(
% 2.84/0.98    ! [X0,X1,X2] : ((v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.84/0.98    inference(ennf_transformation,[],[f21])).
% 2.84/0.98  
% 2.84/0.98  fof(f31,plain,(
% 2.84/0.98    ! [X0,X1,X2] : ((v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.84/0.98    inference(flattening,[],[f30])).
% 2.84/0.98  
% 2.84/0.98  fof(f75,plain,(
% 2.84/0.98    ( ! [X2,X0,X1] : (v4_orders_2(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.84/0.98    inference(cnf_transformation,[],[f31])).
% 2.84/0.98  
% 2.84/0.98  fof(f94,plain,(
% 2.84/0.98    ( ! [X2,X0,X1] : (v4_orders_2(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.84/0.98    inference(definition_unfolding,[],[f75,f71,f71,f71])).
% 2.84/0.98  
% 2.84/0.98  cnf(c_0,plain,
% 2.84/0.98      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 2.84/0.98      inference(cnf_transformation,[],[f57]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_4494,plain,
% 2.84/0.98      ( r2_hidden(sK0(X0),X0) = iProver_top
% 2.84/0.98      | v1_xboole_0(X0) = iProver_top ),
% 2.84/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_11,plain,
% 2.84/0.98      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 2.84/0.98      | ~ l1_struct_0(X0) ),
% 2.84/0.98      inference(cnf_transformation,[],[f67]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_12,plain,
% 2.84/0.98      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 2.84/0.98      inference(cnf_transformation,[],[f68]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_32,negated_conjecture,
% 2.84/0.98      ( l1_pre_topc(sK2) ),
% 2.84/0.98      inference(cnf_transformation,[],[f83]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_623,plain,
% 2.84/0.98      ( l1_struct_0(X0) | sK2 != X0 ),
% 2.84/0.98      inference(resolution_lifted,[status(thm)],[c_12,c_32]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_624,plain,
% 2.84/0.98      ( l1_struct_0(sK2) ),
% 2.84/0.98      inference(unflattening,[status(thm)],[c_623]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_1112,plain,
% 2.84/0.98      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 2.84/0.98      | sK2 != X0 ),
% 2.84/0.98      inference(resolution_lifted,[status(thm)],[c_11,c_624]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_1113,plain,
% 2.84/0.98      ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.84/0.98      inference(unflattening,[status(thm)],[c_1112]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_4479,plain,
% 2.84/0.98      ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 2.84/0.98      inference(predicate_to_equality,[status(thm)],[c_1113]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_10,plain,
% 2.84/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.84/0.98      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 2.84/0.98      inference(cnf_transformation,[],[f66]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_4485,plain,
% 2.84/0.98      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
% 2.84/0.98      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 2.84/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_5481,plain,
% 2.84/0.98      ( k7_subset_1(u1_struct_0(sK2),k2_struct_0(sK2),X0) = k4_xboole_0(k2_struct_0(sK2),X0) ),
% 2.84/0.98      inference(superposition,[status(thm)],[c_4479,c_4485]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_9,plain,
% 2.84/0.98      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 2.84/0.98      inference(cnf_transformation,[],[f65]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_4486,plain,
% 2.84/0.98      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 2.84/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_8,plain,
% 2.84/0.98      ( k2_subset_1(X0) = X0 ),
% 2.84/0.98      inference(cnf_transformation,[],[f64]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_4505,plain,
% 2.84/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.84/0.98      inference(light_normalisation,[status(thm)],[c_4486,c_8]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_14,plain,
% 2.84/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.84/0.98      | ~ l1_struct_0(X1)
% 2.84/0.98      | k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0)) = X0 ),
% 2.84/0.98      inference(cnf_transformation,[],[f70]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_1152,plain,
% 2.84/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.84/0.98      | k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0)) = X0
% 2.84/0.98      | sK2 != X1 ),
% 2.84/0.98      inference(resolution_lifted,[status(thm)],[c_14,c_624]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_1153,plain,
% 2.84/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.84/0.98      | k7_subset_1(u1_struct_0(sK2),k2_struct_0(sK2),k7_subset_1(u1_struct_0(sK2),k2_struct_0(sK2),X0)) = X0 ),
% 2.84/0.98      inference(unflattening,[status(thm)],[c_1152]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_4478,plain,
% 2.84/0.98      ( k7_subset_1(u1_struct_0(sK2),k2_struct_0(sK2),k7_subset_1(u1_struct_0(sK2),k2_struct_0(sK2),X0)) = X0
% 2.84/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 2.84/0.98      inference(predicate_to_equality,[status(thm)],[c_1153]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_4960,plain,
% 2.84/0.98      ( k7_subset_1(u1_struct_0(sK2),k2_struct_0(sK2),k7_subset_1(u1_struct_0(sK2),k2_struct_0(sK2),u1_struct_0(sK2))) = u1_struct_0(sK2) ),
% 2.84/0.98      inference(superposition,[status(thm)],[c_4505,c_4478]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_5906,plain,
% 2.84/0.98      ( k7_subset_1(u1_struct_0(sK2),k2_struct_0(sK2),k4_xboole_0(k2_struct_0(sK2),u1_struct_0(sK2))) = u1_struct_0(sK2) ),
% 2.84/0.98      inference(demodulation,[status(thm)],[c_5481,c_4960]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_6063,plain,
% 2.84/0.98      ( k4_xboole_0(k2_struct_0(sK2),k4_xboole_0(k2_struct_0(sK2),u1_struct_0(sK2))) = u1_struct_0(sK2) ),
% 2.84/0.98      inference(superposition,[status(thm)],[c_5481,c_5906]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_7,plain,
% 2.84/0.98      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 2.84/0.98      inference(cnf_transformation,[],[f105]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_4487,plain,
% 2.84/0.98      ( r2_hidden(X0,X1) = iProver_top
% 2.84/0.98      | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
% 2.84/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_6225,plain,
% 2.84/0.98      ( r2_hidden(X0,u1_struct_0(sK2)) != iProver_top
% 2.84/0.98      | r2_hidden(X0,k2_struct_0(sK2)) = iProver_top ),
% 2.84/0.98      inference(superposition,[status(thm)],[c_6063,c_4487]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_6712,plain,
% 2.84/0.98      ( r2_hidden(sK0(u1_struct_0(sK2)),k2_struct_0(sK2)) = iProver_top
% 2.84/0.98      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 2.84/0.98      inference(superposition,[status(thm)],[c_4494,c_6225]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_34,negated_conjecture,
% 2.84/0.98      ( ~ v2_struct_0(sK2) ),
% 2.84/0.98      inference(cnf_transformation,[],[f81]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_35,plain,
% 2.84/0.98      ( v2_struct_0(sK2) != iProver_top ),
% 2.84/0.98      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_37,plain,
% 2.84/0.98      ( l1_pre_topc(sK2) = iProver_top ),
% 2.84/0.98      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_13,plain,
% 2.84/0.98      ( v2_struct_0(X0)
% 2.84/0.98      | ~ l1_struct_0(X0)
% 2.84/0.98      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.84/0.98      inference(cnf_transformation,[],[f69]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_74,plain,
% 2.84/0.98      ( v2_struct_0(X0) = iProver_top
% 2.84/0.98      | l1_struct_0(X0) != iProver_top
% 2.84/0.98      | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
% 2.84/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_76,plain,
% 2.84/0.98      ( v2_struct_0(sK2) = iProver_top
% 2.84/0.98      | l1_struct_0(sK2) != iProver_top
% 2.84/0.98      | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 2.84/0.98      inference(instantiation,[status(thm)],[c_74]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_77,plain,
% 2.84/0.98      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 2.84/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_79,plain,
% 2.84/0.98      ( l1_pre_topc(sK2) != iProver_top
% 2.84/0.98      | l1_struct_0(sK2) = iProver_top ),
% 2.84/0.98      inference(instantiation,[status(thm)],[c_77]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_6739,plain,
% 2.84/0.98      ( r2_hidden(sK0(u1_struct_0(sK2)),k2_struct_0(sK2)) = iProver_top ),
% 2.84/0.98      inference(global_propositional_subsumption,
% 2.84/0.98                [status(thm)],
% 2.84/0.98                [c_6712,c_35,c_37,c_76,c_79]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_1,plain,
% 2.84/0.98      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.84/0.98      inference(cnf_transformation,[],[f56]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_4493,plain,
% 2.84/0.98      ( r2_hidden(X0,X1) != iProver_top
% 2.84/0.98      | v1_xboole_0(X1) != iProver_top ),
% 2.84/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_6744,plain,
% 2.84/0.98      ( v1_xboole_0(k2_struct_0(sK2)) != iProver_top ),
% 2.84/0.98      inference(superposition,[status(thm)],[c_6739,c_4493]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_29,negated_conjecture,
% 2.84/0.98      ( v2_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) ),
% 2.84/0.98      inference(cnf_transformation,[],[f101]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_28,negated_conjecture,
% 2.84/0.98      ( v13_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) ),
% 2.84/0.98      inference(cnf_transformation,[],[f100]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_19,plain,
% 2.84/0.98      ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
% 2.84/0.98      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.84/0.98      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.84/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.84/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.84/0.98      | v7_waybel_0(k3_yellow19(X2,X1,X0))
% 2.84/0.98      | v2_struct_0(X2)
% 2.84/0.98      | ~ l1_struct_0(X2)
% 2.84/0.98      | v1_xboole_0(X0)
% 2.84/0.98      | v1_xboole_0(X1) ),
% 2.84/0.98      inference(cnf_transformation,[],[f96]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_30,negated_conjecture,
% 2.84/0.98      ( v1_subset_1(sK3,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))) ),
% 2.84/0.98      inference(cnf_transformation,[],[f102]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_451,plain,
% 2.84/0.98      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.84/0.98      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.84/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.84/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.84/0.98      | v7_waybel_0(k3_yellow19(X2,X1,X0))
% 2.84/0.98      | v2_struct_0(X2)
% 2.84/0.98      | ~ l1_struct_0(X2)
% 2.84/0.98      | v1_xboole_0(X0)
% 2.84/0.98      | v1_xboole_0(X1)
% 2.84/0.98      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
% 2.84/0.98      | sK3 != X0 ),
% 2.84/0.98      inference(resolution_lifted,[status(thm)],[c_19,c_30]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_452,plain,
% 2.84/0.98      ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 2.84/0.98      | ~ v13_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 2.84/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.84/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.84/0.98      | v7_waybel_0(k3_yellow19(X1,X0,sK3))
% 2.84/0.98      | v2_struct_0(X1)
% 2.84/0.98      | ~ l1_struct_0(X1)
% 2.84/0.98      | v1_xboole_0(X0)
% 2.84/0.98      | v1_xboole_0(sK3)
% 2.84/0.98      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 2.84/0.98      inference(unflattening,[status(thm)],[c_451]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_31,negated_conjecture,
% 2.84/0.98      ( ~ v1_xboole_0(sK3) ),
% 2.84/0.98      inference(cnf_transformation,[],[f84]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_456,plain,
% 2.84/0.98      ( v1_xboole_0(X0)
% 2.84/0.98      | ~ l1_struct_0(X1)
% 2.84/0.98      | v2_struct_0(X1)
% 2.84/0.98      | v7_waybel_0(k3_yellow19(X1,X0,sK3))
% 2.84/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.84/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.84/0.98      | ~ v13_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 2.84/0.98      | ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 2.84/0.98      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 2.84/0.98      inference(global_propositional_subsumption,
% 2.84/0.98                [status(thm)],
% 2.84/0.98                [c_452,c_31]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_457,plain,
% 2.84/0.98      ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 2.84/0.98      | ~ v13_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 2.84/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.84/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.84/0.98      | v7_waybel_0(k3_yellow19(X1,X0,sK3))
% 2.84/0.98      | v2_struct_0(X1)
% 2.84/0.98      | ~ l1_struct_0(X1)
% 2.84/0.98      | v1_xboole_0(X0)
% 2.84/0.98      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 2.84/0.98      inference(renaming,[status(thm)],[c_456]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_1119,plain,
% 2.84/0.98      ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 2.84/0.98      | ~ v13_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 2.84/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.84/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.84/0.98      | v7_waybel_0(k3_yellow19(X1,X0,sK3))
% 2.84/0.98      | v2_struct_0(X1)
% 2.84/0.98      | v1_xboole_0(X0)
% 2.84/0.98      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 2.84/0.98      | sK2 != X1 ),
% 2.84/0.98      inference(resolution_lifted,[status(thm)],[c_457,c_624]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_1120,plain,
% 2.84/0.98      ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 2.84/0.98      | ~ v13_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 2.84/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.84/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.84/0.98      | v7_waybel_0(k3_yellow19(sK2,X0,sK3))
% 2.84/0.98      | v2_struct_0(sK2)
% 2.84/0.98      | v1_xboole_0(X0)
% 2.84/0.98      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 2.84/0.98      inference(unflattening,[status(thm)],[c_1119]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_1124,plain,
% 2.84/0.98      ( v7_waybel_0(k3_yellow19(sK2,X0,sK3))
% 2.84/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.84/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.84/0.98      | ~ v13_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 2.84/0.98      | ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 2.84/0.98      | v1_xboole_0(X0)
% 2.84/0.98      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 2.84/0.98      inference(global_propositional_subsumption,
% 2.84/0.98                [status(thm)],
% 2.84/0.98                [c_1120,c_34]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_1125,plain,
% 2.84/0.98      ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 2.84/0.98      | ~ v13_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 2.84/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.84/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.84/0.98      | v7_waybel_0(k3_yellow19(sK2,X0,sK3))
% 2.84/0.98      | v1_xboole_0(X0)
% 2.84/0.98      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 2.84/0.98      inference(renaming,[status(thm)],[c_1124]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_1649,plain,
% 2.84/0.98      ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 2.84/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.84/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.84/0.98      | v7_waybel_0(k3_yellow19(sK2,X0,sK3))
% 2.84/0.98      | v1_xboole_0(X0)
% 2.84/0.98      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
% 2.84/0.98      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 2.84/0.98      | sK3 != sK3 ),
% 2.84/0.98      inference(resolution_lifted,[status(thm)],[c_28,c_1125]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_1927,plain,
% 2.84/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.84/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.84/0.98      | v7_waybel_0(k3_yellow19(sK2,X0,sK3))
% 2.84/0.98      | v1_xboole_0(X0)
% 2.84/0.98      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
% 2.84/0.98      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 2.84/0.98      | sK3 != sK3 ),
% 2.84/0.98      inference(resolution_lifted,[status(thm)],[c_29,c_1649]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_3011,plain,
% 2.84/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.84/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.84/0.98      | v7_waybel_0(k3_yellow19(sK2,X0,sK3))
% 2.84/0.98      | v1_xboole_0(X0)
% 2.84/0.98      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
% 2.84/0.98      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 2.84/0.98      inference(equality_resolution_simp,[status(thm)],[c_1927]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_4471,plain,
% 2.84/0.98      ( k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
% 2.84/0.98      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 2.84/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.84/0.98      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
% 2.84/0.98      | v7_waybel_0(k3_yellow19(sK2,X0,sK3)) = iProver_top
% 2.84/0.98      | v1_xboole_0(X0) = iProver_top ),
% 2.84/0.98      inference(predicate_to_equality,[status(thm)],[c_3011]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_4863,plain,
% 2.84/0.98      ( k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(k2_struct_0(sK2)))
% 2.84/0.98      | m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.84/0.98      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))))) != iProver_top
% 2.84/0.98      | v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) = iProver_top
% 2.84/0.98      | v1_xboole_0(k2_struct_0(sK2)) = iProver_top ),
% 2.84/0.98      inference(equality_resolution,[status(thm)],[c_4471]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_5982,plain,
% 2.84/0.98      ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.84/0.98      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))))) != iProver_top
% 2.84/0.98      | v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) = iProver_top
% 2.84/0.98      | v1_xboole_0(k2_struct_0(sK2)) = iProver_top ),
% 2.84/0.98      inference(equality_resolution_simp,[status(thm)],[c_4863]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_27,negated_conjecture,
% 2.84/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))))) ),
% 2.84/0.98      inference(cnf_transformation,[],[f99]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_42,plain,
% 2.84/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))))) = iProver_top ),
% 2.84/0.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_80,plain,
% 2.84/0.98      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 2.84/0.98      | l1_struct_0(X0) != iProver_top ),
% 2.84/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_82,plain,
% 2.84/0.98      ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 2.84/0.98      | l1_struct_0(sK2) != iProver_top ),
% 2.84/0.98      inference(instantiation,[status(thm)],[c_80]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_15,plain,
% 2.84/0.98      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.84/0.98      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.84/0.98      | l1_waybel_0(k3_yellow19(X2,X1,X0),X2)
% 2.84/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.84/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.84/0.98      | v2_struct_0(X2)
% 2.84/0.98      | ~ l1_struct_0(X2)
% 2.84/0.98      | v1_xboole_0(X0)
% 2.84/0.98      | v1_xboole_0(X1) ),
% 2.84/0.98      inference(cnf_transformation,[],[f92]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_24,negated_conjecture,
% 2.84/0.98      ( ~ r1_waybel_7(sK2,sK3,sK4)
% 2.84/0.98      | ~ r3_waybel_9(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3),sK4) ),
% 2.84/0.98      inference(cnf_transformation,[],[f91]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_255,plain,
% 2.84/0.98      ( ~ r1_waybel_7(sK2,sK3,sK4)
% 2.84/0.98      | ~ r3_waybel_9(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3),sK4) ),
% 2.84/0.98      inference(prop_impl,[status(thm)],[c_24]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_21,plain,
% 2.84/0.98      ( ~ r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 2.84/0.98      | r3_waybel_9(X0,X1,X2)
% 2.84/0.98      | ~ l1_waybel_0(X1,X0)
% 2.84/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.84/0.98      | ~ v2_pre_topc(X0)
% 2.84/0.98      | ~ v7_waybel_0(X1)
% 2.84/0.98      | ~ v4_orders_2(X1)
% 2.84/0.98      | v2_struct_0(X0)
% 2.84/0.98      | v2_struct_0(X1)
% 2.84/0.98      | ~ l1_pre_topc(X0) ),
% 2.84/0.98      inference(cnf_transformation,[],[f79]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_33,negated_conjecture,
% 2.84/0.98      ( v2_pre_topc(sK2) ),
% 2.84/0.98      inference(cnf_transformation,[],[f82]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_574,plain,
% 2.84/0.98      ( ~ r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 2.84/0.98      | r3_waybel_9(X0,X1,X2)
% 2.84/0.98      | ~ l1_waybel_0(X1,X0)
% 2.84/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.84/0.98      | ~ v7_waybel_0(X1)
% 2.84/0.98      | ~ v4_orders_2(X1)
% 2.84/0.98      | v2_struct_0(X0)
% 2.84/0.98      | v2_struct_0(X1)
% 2.84/0.98      | ~ l1_pre_topc(X0)
% 2.84/0.98      | sK2 != X0 ),
% 2.84/0.98      inference(resolution_lifted,[status(thm)],[c_21,c_33]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_575,plain,
% 2.84/0.98      ( ~ r1_waybel_7(sK2,k2_yellow19(sK2,X0),X1)
% 2.84/0.98      | r3_waybel_9(sK2,X0,X1)
% 2.84/0.98      | ~ l1_waybel_0(X0,sK2)
% 2.84/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.84/0.98      | ~ v7_waybel_0(X0)
% 2.84/0.98      | ~ v4_orders_2(X0)
% 2.84/0.98      | v2_struct_0(X0)
% 2.84/0.98      | v2_struct_0(sK2)
% 2.84/0.98      | ~ l1_pre_topc(sK2) ),
% 2.84/0.98      inference(unflattening,[status(thm)],[c_574]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_579,plain,
% 2.84/0.98      ( ~ r1_waybel_7(sK2,k2_yellow19(sK2,X0),X1)
% 2.84/0.98      | r3_waybel_9(sK2,X0,X1)
% 2.84/0.98      | ~ l1_waybel_0(X0,sK2)
% 2.84/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.84/0.98      | ~ v7_waybel_0(X0)
% 2.84/0.98      | ~ v4_orders_2(X0)
% 2.84/0.98      | v2_struct_0(X0) ),
% 2.84/0.98      inference(global_propositional_subsumption,
% 2.84/0.98                [status(thm)],
% 2.84/0.98                [c_575,c_34,c_32]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_952,plain,
% 2.84/0.98      ( ~ r1_waybel_7(sK2,k2_yellow19(sK2,X0),X1)
% 2.84/0.98      | ~ r1_waybel_7(sK2,sK3,sK4)
% 2.84/0.98      | ~ l1_waybel_0(X0,sK2)
% 2.84/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.84/0.98      | ~ v7_waybel_0(X0)
% 2.84/0.98      | ~ v4_orders_2(X0)
% 2.84/0.98      | v2_struct_0(X0)
% 2.84/0.98      | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != X0
% 2.84/0.98      | sK4 != X1
% 2.84/0.98      | sK2 != sK2 ),
% 2.84/0.98      inference(resolution_lifted,[status(thm)],[c_255,c_579]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_953,plain,
% 2.84/0.98      ( ~ r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
% 2.84/0.98      | ~ r1_waybel_7(sK2,sK3,sK4)
% 2.84/0.98      | ~ l1_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3),sK2)
% 2.84/0.98      | ~ m1_subset_1(sK4,u1_struct_0(sK2))
% 2.84/0.98      | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.84/0.98      | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.84/0.98      | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) ),
% 2.84/0.98      inference(unflattening,[status(thm)],[c_952]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_26,negated_conjecture,
% 2.84/0.98      ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
% 2.84/0.98      inference(cnf_transformation,[],[f89]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_955,plain,
% 2.84/0.98      ( ~ l1_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3),sK2)
% 2.84/0.98      | ~ r1_waybel_7(sK2,sK3,sK4)
% 2.84/0.98      | ~ r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
% 2.84/0.98      | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.84/0.98      | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.84/0.98      | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) ),
% 2.84/0.98      inference(global_propositional_subsumption,
% 2.84/0.98                [status(thm)],
% 2.84/0.98                [c_953,c_26]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_956,plain,
% 2.84/0.98      ( ~ r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
% 2.84/0.98      | ~ r1_waybel_7(sK2,sK3,sK4)
% 2.84/0.98      | ~ l1_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3),sK2)
% 2.84/0.98      | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.84/0.98      | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.84/0.98      | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) ),
% 2.84/0.98      inference(renaming,[status(thm)],[c_955]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_992,plain,
% 2.84/0.98      ( ~ r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
% 2.84/0.98      | ~ r1_waybel_7(sK2,sK3,sK4)
% 2.84/0.98      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.84/0.98      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.84/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.84/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.84/0.98      | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.84/0.98      | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.84/0.98      | v2_struct_0(X2)
% 2.84/0.98      | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.84/0.98      | ~ l1_struct_0(X2)
% 2.84/0.98      | v1_xboole_0(X0)
% 2.84/0.98      | v1_xboole_0(X1)
% 2.84/0.98      | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != k3_yellow19(X2,X1,X0)
% 2.84/0.98      | sK2 != X2 ),
% 2.84/0.98      inference(resolution_lifted,[status(thm)],[c_15,c_956]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_993,plain,
% 2.84/0.98      ( ~ r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
% 2.84/0.98      | ~ r1_waybel_7(sK2,sK3,sK4)
% 2.84/0.98      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.84/0.98      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.84/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.84/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.84/0.98      | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.84/0.98      | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.84/0.98      | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.84/0.98      | v2_struct_0(sK2)
% 2.84/0.98      | ~ l1_struct_0(sK2)
% 2.84/0.98      | v1_xboole_0(X0)
% 2.84/0.98      | v1_xboole_0(X1)
% 2.84/0.98      | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != k3_yellow19(sK2,X1,X0) ),
% 2.84/0.98      inference(unflattening,[status(thm)],[c_992]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_78,plain,
% 2.84/0.98      ( ~ l1_pre_topc(sK2) | l1_struct_0(sK2) ),
% 2.84/0.98      inference(instantiation,[status(thm)],[c_12]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_997,plain,
% 2.84/0.98      ( ~ r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
% 2.84/0.98      | ~ r1_waybel_7(sK2,sK3,sK4)
% 2.84/0.98      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.84/0.98      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.84/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.84/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.84/0.98      | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.84/0.98      | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.84/0.98      | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.84/0.98      | v1_xboole_0(X0)
% 2.84/0.98      | v1_xboole_0(X1)
% 2.84/0.98      | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != k3_yellow19(sK2,X1,X0) ),
% 2.84/0.98      inference(global_propositional_subsumption,
% 2.84/0.98                [status(thm)],
% 2.84/0.98                [c_993,c_34,c_32,c_78]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_1604,plain,
% 2.84/0.98      ( ~ r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
% 2.84/0.98      | ~ r1_waybel_7(sK2,sK3,sK4)
% 2.84/0.98      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.84/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.84/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.84/0.98      | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.84/0.98      | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.84/0.98      | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.84/0.98      | v1_xboole_0(X0)
% 2.84/0.98      | v1_xboole_0(X1)
% 2.84/0.98      | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != k3_yellow19(sK2,X1,X0)
% 2.84/0.98      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X1))
% 2.84/0.98      | sK3 != X0 ),
% 2.84/0.98      inference(resolution_lifted,[status(thm)],[c_997,c_28]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_1605,plain,
% 2.84/0.98      ( ~ r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
% 2.84/0.98      | ~ r1_waybel_7(sK2,sK3,sK4)
% 2.84/0.98      | ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 2.84/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.84/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.84/0.98      | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.84/0.98      | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.84/0.98      | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.84/0.98      | v1_xboole_0(X0)
% 2.84/0.98      | v1_xboole_0(sK3)
% 2.84/0.98      | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != k3_yellow19(sK2,X0,sK3)
% 2.84/0.98      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.84/0.98      inference(unflattening,[status(thm)],[c_1604]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_1609,plain,
% 2.84/0.98      ( v1_xboole_0(X0)
% 2.84/0.98      | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.84/0.98      | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.84/0.98      | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.84/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.84/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.84/0.98      | ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 2.84/0.98      | ~ r1_waybel_7(sK2,sK3,sK4)
% 2.84/0.98      | ~ r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
% 2.84/0.98      | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != k3_yellow19(sK2,X0,sK3)
% 2.84/0.98      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.84/0.98      inference(global_propositional_subsumption,
% 2.84/0.98                [status(thm)],
% 2.84/0.98                [c_1605,c_31]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_1610,plain,
% 2.84/0.99      ( ~ r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
% 2.84/0.99      | ~ r1_waybel_7(sK2,sK3,sK4)
% 2.84/0.99      | ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 2.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.84/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.84/0.99      | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.84/0.99      | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.84/0.99      | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.84/0.99      | v1_xboole_0(X0)
% 2.84/0.99      | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != k3_yellow19(sK2,X0,sK3)
% 2.84/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.84/0.99      inference(renaming,[status(thm)],[c_1609]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_1953,plain,
% 2.84/0.99      ( ~ r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
% 2.84/0.99      | ~ r1_waybel_7(sK2,sK3,sK4)
% 2.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.84/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.84/0.99      | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.84/0.99      | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.84/0.99      | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.84/0.99      | v1_xboole_0(X0)
% 2.84/0.99      | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != k3_yellow19(sK2,X0,sK3)
% 2.84/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
% 2.84/0.99      | sK3 != sK3 ),
% 2.84/0.99      inference(resolution_lifted,[status(thm)],[c_29,c_1610]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_3007,plain,
% 2.84/0.99      ( ~ r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
% 2.84/0.99      | ~ r1_waybel_7(sK2,sK3,sK4)
% 2.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.84/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.84/0.99      | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.84/0.99      | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.84/0.99      | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.84/0.99      | v1_xboole_0(X0)
% 2.84/0.99      | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != k3_yellow19(sK2,X0,sK3)
% 2.84/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.84/0.99      inference(equality_resolution_simp,[status(thm)],[c_1953]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_4004,plain,
% 2.84/0.99      ( ~ r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
% 2.84/0.99      | ~ r1_waybel_7(sK2,sK3,sK4)
% 2.84/0.99      | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.84/0.99      | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.84/0.99      | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.84/0.99      | sP0_iProver_split ),
% 2.84/0.99      inference(splitting,
% 2.84/0.99                [splitting(split),new_symbols(definition,[])],
% 2.84/0.99                [c_3007]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_4472,plain,
% 2.84/0.99      ( r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4) != iProver_top
% 2.84/0.99      | r1_waybel_7(sK2,sK3,sK4) != iProver_top
% 2.84/0.99      | v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) != iProver_top
% 2.84/0.99      | v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) != iProver_top
% 2.84/0.99      | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) = iProver_top
% 2.84/0.99      | sP0_iProver_split = iProver_top ),
% 2.84/0.99      inference(predicate_to_equality,[status(thm)],[c_4004]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_23,plain,
% 2.84/0.99      ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))
% 2.84/0.99      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 2.84/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 2.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
% 2.84/0.99      | v2_struct_0(X1)
% 2.84/0.99      | ~ l1_struct_0(X1)
% 2.84/0.99      | v1_xboole_0(X0)
% 2.84/0.99      | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0 ),
% 2.84/0.99      inference(cnf_transformation,[],[f98]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_490,plain,
% 2.84/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 2.84/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 2.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
% 2.84/0.99      | v2_struct_0(X1)
% 2.84/0.99      | ~ l1_struct_0(X1)
% 2.84/0.99      | v1_xboole_0(X0)
% 2.84/0.99      | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0
% 2.84/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))
% 2.84/0.99      | sK3 != X0 ),
% 2.84/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_30]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_491,plain,
% 2.84/0.99      ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 2.84/0.99      | ~ v13_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 2.84/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 2.84/0.99      | v2_struct_0(X0)
% 2.84/0.99      | ~ l1_struct_0(X0)
% 2.84/0.99      | v1_xboole_0(sK3)
% 2.84/0.99      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK3)) = sK3
% 2.84/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) ),
% 2.84/0.99      inference(unflattening,[status(thm)],[c_490]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_495,plain,
% 2.84/0.99      ( ~ l1_struct_0(X0)
% 2.84/0.99      | v2_struct_0(X0)
% 2.84/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 2.84/0.99      | ~ v13_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 2.84/0.99      | ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 2.84/0.99      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK3)) = sK3
% 2.84/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) ),
% 2.84/0.99      inference(global_propositional_subsumption,
% 2.84/0.99                [status(thm)],
% 2.84/0.99                [c_491,c_31]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_496,plain,
% 2.84/0.99      ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 2.84/0.99      | ~ v13_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 2.84/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 2.84/0.99      | v2_struct_0(X0)
% 2.84/0.99      | ~ l1_struct_0(X0)
% 2.84/0.99      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK3)) = sK3
% 2.84/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) ),
% 2.84/0.99      inference(renaming,[status(thm)],[c_495]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_1090,plain,
% 2.84/0.99      ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 2.84/0.99      | ~ v13_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 2.84/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 2.84/0.99      | v2_struct_0(X0)
% 2.84/0.99      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK3)) = sK3
% 2.84/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))
% 2.84/0.99      | sK2 != X0 ),
% 2.84/0.99      inference(resolution_lifted,[status(thm)],[c_496,c_624]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_1091,plain,
% 2.84/0.99      ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(sK2))))
% 2.84/0.99      | ~ v13_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(sK2))))
% 2.84/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))))
% 2.84/0.99      | v2_struct_0(sK2)
% 2.84/0.99      | k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)) = sK3
% 2.84/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) ),
% 2.84/0.99      inference(unflattening,[status(thm)],[c_1090]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_1093,plain,
% 2.84/0.99      ( k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)) = sK3
% 2.84/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) ),
% 2.84/0.99      inference(global_propositional_subsumption,
% 2.84/0.99                [status(thm)],
% 2.84/0.99                [c_1091,c_34,c_29,c_28,c_27]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_3018,plain,
% 2.84/0.99      ( k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)) = sK3 ),
% 2.84/0.99      inference(equality_resolution_simp,[status(thm)],[c_1093]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_4619,plain,
% 2.84/0.99      ( r1_waybel_7(sK2,sK3,sK4) != iProver_top
% 2.84/0.99      | v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) != iProver_top
% 2.84/0.99      | v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) != iProver_top
% 2.84/0.99      | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) = iProver_top
% 2.84/0.99      | sP0_iProver_split = iProver_top ),
% 2.84/0.99      inference(light_normalisation,[status(thm)],[c_4472,c_3018]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_25,negated_conjecture,
% 2.84/0.99      ( r1_waybel_7(sK2,sK3,sK4)
% 2.84/0.99      | r3_waybel_9(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3),sK4) ),
% 2.84/0.99      inference(cnf_transformation,[],[f90]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_257,plain,
% 2.84/0.99      ( r1_waybel_7(sK2,sK3,sK4)
% 2.84/0.99      | r3_waybel_9(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3),sK4) ),
% 2.84/0.99      inference(prop_impl,[status(thm)],[c_25]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_22,plain,
% 2.84/0.99      ( r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 2.84/0.99      | ~ r3_waybel_9(X0,X1,X2)
% 2.84/0.99      | ~ l1_waybel_0(X1,X0)
% 2.84/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.84/0.99      | ~ v2_pre_topc(X0)
% 2.84/0.99      | ~ v7_waybel_0(X1)
% 2.84/0.99      | ~ v4_orders_2(X1)
% 2.84/0.99      | v2_struct_0(X0)
% 2.84/0.99      | v2_struct_0(X1)
% 2.84/0.99      | ~ l1_pre_topc(X0) ),
% 2.84/0.99      inference(cnf_transformation,[],[f78]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_541,plain,
% 2.84/0.99      ( r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 2.84/0.99      | ~ r3_waybel_9(X0,X1,X2)
% 2.84/0.99      | ~ l1_waybel_0(X1,X0)
% 2.84/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.84/0.99      | ~ v7_waybel_0(X1)
% 2.84/0.99      | ~ v4_orders_2(X1)
% 2.84/0.99      | v2_struct_0(X0)
% 2.84/0.99      | v2_struct_0(X1)
% 2.84/0.99      | ~ l1_pre_topc(X0)
% 2.84/0.99      | sK2 != X0 ),
% 2.84/0.99      inference(resolution_lifted,[status(thm)],[c_22,c_33]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_542,plain,
% 2.84/0.99      ( r1_waybel_7(sK2,k2_yellow19(sK2,X0),X1)
% 2.84/0.99      | ~ r3_waybel_9(sK2,X0,X1)
% 2.84/0.99      | ~ l1_waybel_0(X0,sK2)
% 2.84/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.84/0.99      | ~ v7_waybel_0(X0)
% 2.84/0.99      | ~ v4_orders_2(X0)
% 2.84/0.99      | v2_struct_0(X0)
% 2.84/0.99      | v2_struct_0(sK2)
% 2.84/0.99      | ~ l1_pre_topc(sK2) ),
% 2.84/0.99      inference(unflattening,[status(thm)],[c_541]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_546,plain,
% 2.84/0.99      ( r1_waybel_7(sK2,k2_yellow19(sK2,X0),X1)
% 2.84/0.99      | ~ r3_waybel_9(sK2,X0,X1)
% 2.84/0.99      | ~ l1_waybel_0(X0,sK2)
% 2.84/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.84/0.99      | ~ v7_waybel_0(X0)
% 2.84/0.99      | ~ v4_orders_2(X0)
% 2.84/0.99      | v2_struct_0(X0) ),
% 2.84/0.99      inference(global_propositional_subsumption,
% 2.84/0.99                [status(thm)],
% 2.84/0.99                [c_542,c_34,c_32]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_926,plain,
% 2.84/0.99      ( r1_waybel_7(sK2,k2_yellow19(sK2,X0),X1)
% 2.84/0.99      | r1_waybel_7(sK2,sK3,sK4)
% 2.84/0.99      | ~ l1_waybel_0(X0,sK2)
% 2.84/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.84/0.99      | ~ v7_waybel_0(X0)
% 2.84/0.99      | ~ v4_orders_2(X0)
% 2.84/0.99      | v2_struct_0(X0)
% 2.84/0.99      | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != X0
% 2.84/0.99      | sK4 != X1
% 2.84/0.99      | sK2 != sK2 ),
% 2.84/0.99      inference(resolution_lifted,[status(thm)],[c_257,c_546]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_927,plain,
% 2.84/0.99      ( r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
% 2.84/0.99      | r1_waybel_7(sK2,sK3,sK4)
% 2.84/0.99      | ~ l1_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3),sK2)
% 2.84/0.99      | ~ m1_subset_1(sK4,u1_struct_0(sK2))
% 2.84/0.99      | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.84/0.99      | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.84/0.99      | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) ),
% 2.84/0.99      inference(unflattening,[status(thm)],[c_926]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_929,plain,
% 2.84/0.99      ( ~ l1_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3),sK2)
% 2.84/0.99      | r1_waybel_7(sK2,sK3,sK4)
% 2.84/0.99      | r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
% 2.84/0.99      | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.84/0.99      | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.84/0.99      | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) ),
% 2.84/0.99      inference(global_propositional_subsumption,
% 2.84/0.99                [status(thm)],
% 2.84/0.99                [c_927,c_26]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_930,plain,
% 2.84/0.99      ( r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
% 2.84/0.99      | r1_waybel_7(sK2,sK3,sK4)
% 2.84/0.99      | ~ l1_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3),sK2)
% 2.84/0.99      | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.84/0.99      | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.84/0.99      | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) ),
% 2.84/0.99      inference(renaming,[status(thm)],[c_929]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_1040,plain,
% 2.84/0.99      ( r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
% 2.84/0.99      | r1_waybel_7(sK2,sK3,sK4)
% 2.84/0.99      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.84/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.84/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.84/0.99      | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.84/0.99      | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.84/0.99      | v2_struct_0(X2)
% 2.84/0.99      | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.84/0.99      | ~ l1_struct_0(X2)
% 2.84/0.99      | v1_xboole_0(X0)
% 2.84/0.99      | v1_xboole_0(X1)
% 2.84/0.99      | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != k3_yellow19(X2,X1,X0)
% 2.84/0.99      | sK2 != X2 ),
% 2.84/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_930]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_1041,plain,
% 2.84/0.99      ( r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
% 2.84/0.99      | r1_waybel_7(sK2,sK3,sK4)
% 2.84/0.99      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.84/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.84/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.84/0.99      | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.84/0.99      | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.84/0.99      | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.84/0.99      | v2_struct_0(sK2)
% 2.84/0.99      | ~ l1_struct_0(sK2)
% 2.84/0.99      | v1_xboole_0(X0)
% 2.84/0.99      | v1_xboole_0(X1)
% 2.84/0.99      | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != k3_yellow19(sK2,X1,X0) ),
% 2.84/0.99      inference(unflattening,[status(thm)],[c_1040]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_1045,plain,
% 2.84/0.99      ( r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
% 2.84/0.99      | r1_waybel_7(sK2,sK3,sK4)
% 2.84/0.99      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.84/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.84/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.84/0.99      | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.84/0.99      | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.84/0.99      | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.84/0.99      | v1_xboole_0(X0)
% 2.84/0.99      | v1_xboole_0(X1)
% 2.84/0.99      | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != k3_yellow19(sK2,X1,X0) ),
% 2.84/0.99      inference(global_propositional_subsumption,
% 2.84/0.99                [status(thm)],
% 2.84/0.99                [c_1041,c_34,c_32,c_78]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_1559,plain,
% 2.84/0.99      ( r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
% 2.84/0.99      | r1_waybel_7(sK2,sK3,sK4)
% 2.84/0.99      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.84/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.84/0.99      | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.84/0.99      | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.84/0.99      | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.84/0.99      | v1_xboole_0(X0)
% 2.84/0.99      | v1_xboole_0(X1)
% 2.84/0.99      | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != k3_yellow19(sK2,X1,X0)
% 2.84/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X1))
% 2.84/0.99      | sK3 != X0 ),
% 2.84/0.99      inference(resolution_lifted,[status(thm)],[c_1045,c_28]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_1560,plain,
% 2.84/0.99      ( r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
% 2.84/0.99      | r1_waybel_7(sK2,sK3,sK4)
% 2.84/0.99      | ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 2.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.84/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.84/0.99      | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.84/0.99      | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.84/0.99      | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.84/0.99      | v1_xboole_0(X0)
% 2.84/0.99      | v1_xboole_0(sK3)
% 2.84/0.99      | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != k3_yellow19(sK2,X0,sK3)
% 2.84/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.84/0.99      inference(unflattening,[status(thm)],[c_1559]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_1564,plain,
% 2.84/0.99      ( v1_xboole_0(X0)
% 2.84/0.99      | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.84/0.99      | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.84/0.99      | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.84/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.84/0.99      | ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 2.84/0.99      | r1_waybel_7(sK2,sK3,sK4)
% 2.84/0.99      | r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
% 2.84/0.99      | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != k3_yellow19(sK2,X0,sK3)
% 2.84/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.84/0.99      inference(global_propositional_subsumption,
% 2.84/0.99                [status(thm)],
% 2.84/0.99                [c_1560,c_31]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_1565,plain,
% 2.84/0.99      ( r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
% 2.84/0.99      | r1_waybel_7(sK2,sK3,sK4)
% 2.84/0.99      | ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 2.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.84/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.84/0.99      | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.84/0.99      | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.84/0.99      | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.84/0.99      | v1_xboole_0(X0)
% 2.84/0.99      | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != k3_yellow19(sK2,X0,sK3)
% 2.84/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.84/0.99      inference(renaming,[status(thm)],[c_1564]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_1991,plain,
% 2.84/0.99      ( r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
% 2.84/0.99      | r1_waybel_7(sK2,sK3,sK4)
% 2.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.84/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.84/0.99      | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.84/0.99      | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.84/0.99      | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.84/0.99      | v1_xboole_0(X0)
% 2.84/0.99      | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != k3_yellow19(sK2,X0,sK3)
% 2.84/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
% 2.84/0.99      | sK3 != sK3 ),
% 2.84/0.99      inference(resolution_lifted,[status(thm)],[c_29,c_1565]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_3003,plain,
% 2.84/0.99      ( r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
% 2.84/0.99      | r1_waybel_7(sK2,sK3,sK4)
% 2.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.84/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.84/0.99      | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.84/0.99      | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.84/0.99      | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.84/0.99      | v1_xboole_0(X0)
% 2.84/0.99      | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != k3_yellow19(sK2,X0,sK3)
% 2.84/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.84/0.99      inference(equality_resolution_simp,[status(thm)],[c_1991]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_4005,plain,
% 2.84/0.99      ( r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
% 2.84/0.99      | r1_waybel_7(sK2,sK3,sK4)
% 2.84/0.99      | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.84/0.99      | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.84/0.99      | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.84/0.99      | sP0_iProver_split ),
% 2.84/0.99      inference(splitting,
% 2.84/0.99                [splitting(split),new_symbols(definition,[])],
% 2.84/0.99                [c_3003]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_4474,plain,
% 2.84/0.99      ( r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4) = iProver_top
% 2.84/0.99      | r1_waybel_7(sK2,sK3,sK4) = iProver_top
% 2.84/0.99      | v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) != iProver_top
% 2.84/0.99      | v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) != iProver_top
% 2.84/0.99      | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) = iProver_top
% 2.84/0.99      | sP0_iProver_split = iProver_top ),
% 2.84/0.99      inference(predicate_to_equality,[status(thm)],[c_4005]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_4596,plain,
% 2.84/0.99      ( r1_waybel_7(sK2,sK3,sK4) = iProver_top
% 2.84/0.99      | v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) != iProver_top
% 2.84/0.99      | v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) != iProver_top
% 2.84/0.99      | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) = iProver_top
% 2.84/0.99      | sP0_iProver_split = iProver_top ),
% 2.84/0.99      inference(light_normalisation,[status(thm)],[c_4474,c_3018]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_4625,plain,
% 2.84/0.99      ( v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) != iProver_top
% 2.84/0.99      | v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) != iProver_top
% 2.84/0.99      | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) = iProver_top
% 2.84/0.99      | sP0_iProver_split = iProver_top ),
% 2.84/0.99      inference(forward_subsumption_resolution,
% 2.84/0.99                [status(thm)],
% 2.84/0.99                [c_4619,c_4596]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_16,plain,
% 2.84/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.84/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.84/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.84/0.99      | v2_struct_0(X2)
% 2.84/0.99      | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
% 2.84/0.99      | ~ l1_struct_0(X2)
% 2.84/0.99      | v1_xboole_0(X0)
% 2.84/0.99      | v1_xboole_0(X1) ),
% 2.84/0.99      inference(cnf_transformation,[],[f93]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_1197,plain,
% 2.84/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.84/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.84/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.84/0.99      | v2_struct_0(X2)
% 2.84/0.99      | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
% 2.84/0.99      | v1_xboole_0(X0)
% 2.84/0.99      | v1_xboole_0(X1)
% 2.84/0.99      | sK2 != X2 ),
% 2.84/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_624]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_1198,plain,
% 2.84/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.84/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.84/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.84/0.99      | ~ v2_struct_0(k3_yellow19(sK2,X1,X0))
% 2.84/0.99      | v2_struct_0(sK2)
% 2.84/0.99      | v1_xboole_0(X0)
% 2.84/0.99      | v1_xboole_0(X1) ),
% 2.84/0.99      inference(unflattening,[status(thm)],[c_1197]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_1202,plain,
% 2.84/0.99      ( ~ v2_struct_0(k3_yellow19(sK2,X1,X0))
% 2.84/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.84/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.84/0.99      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.84/0.99      | v1_xboole_0(X0)
% 2.84/0.99      | v1_xboole_0(X1) ),
% 2.84/0.99      inference(global_propositional_subsumption,
% 2.84/0.99                [status(thm)],
% 2.84/0.99                [c_1198,c_34]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_1203,plain,
% 2.84/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.84/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.84/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.84/0.99      | ~ v2_struct_0(k3_yellow19(sK2,X1,X0))
% 2.84/0.99      | v1_xboole_0(X0)
% 2.84/0.99      | v1_xboole_0(X1) ),
% 2.84/0.99      inference(renaming,[status(thm)],[c_1202]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_1499,plain,
% 2.84/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.84/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.84/0.99      | ~ v2_struct_0(k3_yellow19(sK2,X1,X0))
% 2.84/0.99      | v1_xboole_0(X0)
% 2.84/0.99      | v1_xboole_0(X1)
% 2.84/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X1))
% 2.84/0.99      | sK3 != X0 ),
% 2.84/0.99      inference(resolution_lifted,[status(thm)],[c_1203,c_28]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_1500,plain,
% 2.84/0.99      ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 2.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.84/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.84/0.99      | ~ v2_struct_0(k3_yellow19(sK2,X0,sK3))
% 2.84/0.99      | v1_xboole_0(X0)
% 2.84/0.99      | v1_xboole_0(sK3)
% 2.84/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.84/0.99      inference(unflattening,[status(thm)],[c_1499]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_1504,plain,
% 2.84/0.99      ( v1_xboole_0(X0)
% 2.84/0.99      | ~ v2_struct_0(k3_yellow19(sK2,X0,sK3))
% 2.84/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.84/0.99      | ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 2.84/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.84/0.99      inference(global_propositional_subsumption,
% 2.84/0.99                [status(thm)],
% 2.84/0.99                [c_1500,c_31]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_1505,plain,
% 2.84/0.99      ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 2.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.84/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.84/0.99      | ~ v2_struct_0(k3_yellow19(sK2,X0,sK3))
% 2.84/0.99      | v1_xboole_0(X0)
% 2.84/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.84/0.99      inference(renaming,[status(thm)],[c_1504]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_2052,plain,
% 2.84/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.84/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.84/0.99      | ~ v2_struct_0(k3_yellow19(sK2,X0,sK3))
% 2.84/0.99      | v1_xboole_0(X0)
% 2.84/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
% 2.84/0.99      | sK3 != sK3 ),
% 2.84/0.99      inference(resolution_lifted,[status(thm)],[c_29,c_1505]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_2995,plain,
% 2.84/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.84/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.84/0.99      | ~ v2_struct_0(k3_yellow19(sK2,X0,sK3))
% 2.84/0.99      | v1_xboole_0(X0)
% 2.84/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.84/0.99      inference(equality_resolution_simp,[status(thm)],[c_2052]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_4477,plain,
% 2.84/0.99      ( k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
% 2.84/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.84/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
% 2.84/0.99      | v2_struct_0(k3_yellow19(sK2,X0,sK3)) != iProver_top
% 2.84/0.99      | v1_xboole_0(X0) = iProver_top ),
% 2.84/0.99      inference(predicate_to_equality,[status(thm)],[c_2995]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_5100,plain,
% 2.84/0.99      ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.84/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))))) != iProver_top
% 2.84/0.99      | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) != iProver_top
% 2.84/0.99      | v1_xboole_0(k2_struct_0(sK2)) = iProver_top ),
% 2.84/0.99      inference(equality_resolution,[status(thm)],[c_4477]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_5411,plain,
% 2.84/0.99      ( v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) != iProver_top
% 2.84/0.99      | v1_xboole_0(k2_struct_0(sK2)) = iProver_top ),
% 2.84/0.99      inference(global_propositional_subsumption,
% 2.84/0.99                [status(thm)],
% 2.84/0.99                [c_5100,c_37,c_42,c_79,c_82]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_4003,plain,
% 2.84/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.84/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.84/0.99      | v1_xboole_0(X0)
% 2.84/0.99      | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != k3_yellow19(sK2,X0,sK3)
% 2.84/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
% 2.84/0.99      | ~ sP0_iProver_split ),
% 2.84/0.99      inference(splitting,
% 2.84/0.99                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.84/0.99                [c_3007]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_4473,plain,
% 2.84/0.99      ( k3_yellow19(sK2,k2_struct_0(sK2),sK3) != k3_yellow19(sK2,X0,sK3)
% 2.84/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
% 2.84/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.84/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
% 2.84/0.99      | v1_xboole_0(X0) = iProver_top
% 2.84/0.99      | sP0_iProver_split != iProver_top ),
% 2.84/0.99      inference(predicate_to_equality,[status(thm)],[c_4003]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_5135,plain,
% 2.84/0.99      ( k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(k2_struct_0(sK2)))
% 2.84/0.99      | m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.84/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))))) != iProver_top
% 2.84/0.99      | v1_xboole_0(k2_struct_0(sK2)) = iProver_top
% 2.84/0.99      | sP0_iProver_split != iProver_top ),
% 2.84/0.99      inference(equality_resolution,[status(thm)],[c_4473]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_5417,plain,
% 2.84/0.99      ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.84/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))))) != iProver_top
% 2.84/0.99      | v1_xboole_0(k2_struct_0(sK2)) = iProver_top
% 2.84/0.99      | sP0_iProver_split != iProver_top ),
% 2.84/0.99      inference(equality_resolution_simp,[status(thm)],[c_5135]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_5419,plain,
% 2.84/0.99      ( v1_xboole_0(k2_struct_0(sK2)) = iProver_top
% 2.84/0.99      | sP0_iProver_split != iProver_top ),
% 2.84/0.99      inference(global_propositional_subsumption,
% 2.84/0.99                [status(thm)],
% 2.84/0.99                [c_5417,c_37,c_42,c_79,c_82]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_17,plain,
% 2.84/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.84/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.84/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.84/0.99      | v4_orders_2(k3_yellow19(X2,X1,X0))
% 2.84/0.99      | v2_struct_0(X2)
% 2.84/0.99      | ~ l1_struct_0(X2)
% 2.84/0.99      | v1_xboole_0(X0)
% 2.84/0.99      | v1_xboole_0(X1) ),
% 2.84/0.99      inference(cnf_transformation,[],[f94]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_1164,plain,
% 2.84/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.84/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.84/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.84/0.99      | v4_orders_2(k3_yellow19(X2,X1,X0))
% 2.84/0.99      | v2_struct_0(X2)
% 2.84/0.99      | v1_xboole_0(X0)
% 2.84/0.99      | v1_xboole_0(X1)
% 2.84/0.99      | sK2 != X2 ),
% 2.84/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_624]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_1165,plain,
% 2.84/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.84/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.84/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.84/0.99      | v4_orders_2(k3_yellow19(sK2,X1,X0))
% 2.84/0.99      | v2_struct_0(sK2)
% 2.84/0.99      | v1_xboole_0(X0)
% 2.84/0.99      | v1_xboole_0(X1) ),
% 2.84/0.99      inference(unflattening,[status(thm)],[c_1164]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_1169,plain,
% 2.84/0.99      ( v4_orders_2(k3_yellow19(sK2,X1,X0))
% 2.84/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.84/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.84/0.99      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.84/0.99      | v1_xboole_0(X0)
% 2.84/0.99      | v1_xboole_0(X1) ),
% 2.84/0.99      inference(global_propositional_subsumption,
% 2.84/0.99                [status(thm)],
% 2.84/0.99                [c_1165,c_34]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_1170,plain,
% 2.84/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.84/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.84/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.84/0.99      | v4_orders_2(k3_yellow19(sK2,X1,X0))
% 2.84/0.99      | v1_xboole_0(X0)
% 2.84/0.99      | v1_xboole_0(X1) ),
% 2.84/0.99      inference(renaming,[status(thm)],[c_1169]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_1529,plain,
% 2.84/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.84/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.84/0.99      | v4_orders_2(k3_yellow19(sK2,X1,X0))
% 2.84/0.99      | v1_xboole_0(X0)
% 2.84/0.99      | v1_xboole_0(X1)
% 2.84/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X1))
% 2.84/0.99      | sK3 != X0 ),
% 2.84/0.99      inference(resolution_lifted,[status(thm)],[c_1170,c_28]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_1530,plain,
% 2.84/0.99      ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 2.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.84/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.84/0.99      | v4_orders_2(k3_yellow19(sK2,X0,sK3))
% 2.84/0.99      | v1_xboole_0(X0)
% 2.84/0.99      | v1_xboole_0(sK3)
% 2.84/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.84/0.99      inference(unflattening,[status(thm)],[c_1529]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_1534,plain,
% 2.84/0.99      ( v1_xboole_0(X0)
% 2.84/0.99      | v4_orders_2(k3_yellow19(sK2,X0,sK3))
% 2.84/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.84/0.99      | ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 2.84/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.84/0.99      inference(global_propositional_subsumption,
% 2.84/0.99                [status(thm)],
% 2.84/0.99                [c_1530,c_31]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_1535,plain,
% 2.84/0.99      ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 2.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.84/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.84/0.99      | v4_orders_2(k3_yellow19(sK2,X0,sK3))
% 2.84/0.99      | v1_xboole_0(X0)
% 2.84/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.84/0.99      inference(renaming,[status(thm)],[c_1534]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_2029,plain,
% 2.84/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.84/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.84/0.99      | v4_orders_2(k3_yellow19(sK2,X0,sK3))
% 2.84/0.99      | v1_xboole_0(X0)
% 2.84/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
% 2.84/0.99      | sK3 != sK3 ),
% 2.84/0.99      inference(resolution_lifted,[status(thm)],[c_29,c_1535]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_2999,plain,
% 2.84/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.84/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.84/0.99      | v4_orders_2(k3_yellow19(sK2,X0,sK3))
% 2.84/0.99      | v1_xboole_0(X0)
% 2.84/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.84/0.99      inference(equality_resolution_simp,[status(thm)],[c_2029]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_4476,plain,
% 2.84/0.99      ( k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
% 2.84/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.84/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
% 2.84/0.99      | v4_orders_2(k3_yellow19(sK2,X0,sK3)) = iProver_top
% 2.84/0.99      | v1_xboole_0(X0) = iProver_top ),
% 2.84/0.99      inference(predicate_to_equality,[status(thm)],[c_2999]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_5143,plain,
% 2.84/0.99      ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.84/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))))) != iProver_top
% 2.84/0.99      | v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) = iProver_top
% 2.84/0.99      | v1_xboole_0(k2_struct_0(sK2)) = iProver_top ),
% 2.84/0.99      inference(equality_resolution,[status(thm)],[c_4476]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_5471,plain,
% 2.84/0.99      ( v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) = iProver_top
% 2.84/0.99      | v1_xboole_0(k2_struct_0(sK2)) = iProver_top ),
% 2.84/0.99      inference(global_propositional_subsumption,
% 2.84/0.99                [status(thm)],
% 2.84/0.99                [c_5143,c_37,c_42,c_79,c_82]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_5984,plain,
% 2.84/0.99      ( v1_xboole_0(k2_struct_0(sK2)) = iProver_top ),
% 2.84/0.99      inference(global_propositional_subsumption,
% 2.84/0.99                [status(thm)],
% 2.84/0.99                [c_5982,c_37,c_42,c_79,c_82,c_4625,c_5411,c_5419,c_5471]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(contradiction,plain,
% 2.84/0.99      ( $false ),
% 2.84/0.99      inference(minisat,[status(thm)],[c_6744,c_5984]) ).
% 2.84/0.99  
% 2.84/0.99  
% 2.84/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.84/0.99  
% 2.84/0.99  ------                               Statistics
% 2.84/0.99  
% 2.84/0.99  ------ General
% 2.84/0.99  
% 2.84/0.99  abstr_ref_over_cycles:                  0
% 2.84/0.99  abstr_ref_under_cycles:                 0
% 2.84/0.99  gc_basic_clause_elim:                   0
% 2.84/0.99  forced_gc_time:                         0
% 2.84/0.99  parsing_time:                           0.01
% 2.84/0.99  unif_index_cands_time:                  0.
% 2.84/0.99  unif_index_add_time:                    0.
% 2.84/0.99  orderings_time:                         0.
% 2.84/0.99  out_proof_time:                         0.016
% 2.84/0.99  total_time:                             0.219
% 2.84/0.99  num_of_symbols:                         62
% 2.84/0.99  num_of_terms:                           3754
% 2.84/0.99  
% 2.84/0.99  ------ Preprocessing
% 2.84/0.99  
% 2.84/0.99  num_of_splits:                          2
% 2.84/0.99  num_of_split_atoms:                     1
% 2.84/0.99  num_of_reused_defs:                     1
% 2.84/0.99  num_eq_ax_congr_red:                    24
% 2.84/0.99  num_of_sem_filtered_clauses:            1
% 2.84/0.99  num_of_subtypes:                        0
% 2.84/0.99  monotx_restored_types:                  0
% 2.84/0.99  sat_num_of_epr_types:                   0
% 2.84/0.99  sat_num_of_non_cyclic_types:            0
% 2.84/0.99  sat_guarded_non_collapsed_types:        0
% 2.84/0.99  num_pure_diseq_elim:                    0
% 2.84/0.99  simp_replaced_by:                       0
% 2.84/0.99  res_preprocessed:                       142
% 2.84/0.99  prep_upred:                             0
% 2.84/0.99  prep_unflattend:                        66
% 2.84/0.99  smt_new_axioms:                         0
% 2.84/0.99  pred_elim_cands:                        7
% 2.84/0.99  pred_elim:                              8
% 2.84/0.99  pred_elim_cl:                           9
% 2.84/0.99  pred_elim_cycles:                       23
% 2.84/0.99  merged_defs:                            2
% 2.84/0.99  merged_defs_ncl:                        0
% 2.84/0.99  bin_hyper_res:                          2
% 2.84/0.99  prep_cycles:                            4
% 2.84/0.99  pred_elim_time:                         0.095
% 2.84/0.99  splitting_time:                         0.
% 2.84/0.99  sem_filter_time:                        0.
% 2.84/0.99  monotx_time:                            0.
% 2.84/0.99  subtype_inf_time:                       0.
% 2.84/0.99  
% 2.84/0.99  ------ Problem properties
% 2.84/0.99  
% 2.84/0.99  clauses:                                26
% 2.84/0.99  conjectures:                            4
% 2.84/0.99  epr:                                    3
% 2.84/0.99  horn:                                   17
% 2.84/0.99  ground:                                 9
% 2.84/0.99  unary:                                  9
% 2.84/0.99  binary:                                 6
% 2.84/0.99  lits:                                   74
% 2.84/0.99  lits_eq:                                15
% 2.84/0.99  fd_pure:                                0
% 2.84/0.99  fd_pseudo:                              0
% 2.84/0.99  fd_cond:                                0
% 2.84/0.99  fd_pseudo_cond:                         3
% 2.84/0.99  ac_symbols:                             0
% 2.84/0.99  
% 2.84/0.99  ------ Propositional Solver
% 2.84/0.99  
% 2.84/0.99  prop_solver_calls:                      26
% 2.84/0.99  prop_fast_solver_calls:                 1970
% 2.84/0.99  smt_solver_calls:                       0
% 2.84/0.99  smt_fast_solver_calls:                  0
% 2.84/0.99  prop_num_of_clauses:                    1471
% 2.84/0.99  prop_preprocess_simplified:             5254
% 2.84/0.99  prop_fo_subsumed:                       39
% 2.84/0.99  prop_solver_time:                       0.
% 2.84/0.99  smt_solver_time:                        0.
% 2.84/0.99  smt_fast_solver_time:                   0.
% 2.84/0.99  prop_fast_solver_time:                  0.
% 2.84/0.99  prop_unsat_core_time:                   0.
% 2.84/0.99  
% 2.84/0.99  ------ QBF
% 2.84/0.99  
% 2.84/0.99  qbf_q_res:                              0
% 2.84/0.99  qbf_num_tautologies:                    0
% 2.84/0.99  qbf_prep_cycles:                        0
% 2.84/0.99  
% 2.84/0.99  ------ BMC1
% 2.84/0.99  
% 2.84/0.99  bmc1_current_bound:                     -1
% 2.84/0.99  bmc1_last_solved_bound:                 -1
% 2.84/0.99  bmc1_unsat_core_size:                   -1
% 2.84/0.99  bmc1_unsat_core_parents_size:           -1
% 2.84/0.99  bmc1_merge_next_fun:                    0
% 2.84/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.84/0.99  
% 2.84/0.99  ------ Instantiation
% 2.84/0.99  
% 2.84/0.99  inst_num_of_clauses:                    355
% 2.84/0.99  inst_num_in_passive:                    3
% 2.84/0.99  inst_num_in_active:                     189
% 2.84/0.99  inst_num_in_unprocessed:                163
% 2.84/0.99  inst_num_of_loops:                      200
% 2.84/0.99  inst_num_of_learning_restarts:          0
% 2.84/0.99  inst_num_moves_active_passive:          9
% 2.84/0.99  inst_lit_activity:                      0
% 2.84/0.99  inst_lit_activity_moves:                0
% 2.84/0.99  inst_num_tautologies:                   0
% 2.84/0.99  inst_num_prop_implied:                  0
% 2.84/0.99  inst_num_existing_simplified:           0
% 2.84/0.99  inst_num_eq_res_simplified:             0
% 2.84/0.99  inst_num_child_elim:                    0
% 2.84/0.99  inst_num_of_dismatching_blockings:      120
% 2.84/0.99  inst_num_of_non_proper_insts:           263
% 2.84/0.99  inst_num_of_duplicates:                 0
% 2.84/0.99  inst_inst_num_from_inst_to_res:         0
% 2.84/0.99  inst_dismatching_checking_time:         0.
% 2.84/0.99  
% 2.84/0.99  ------ Resolution
% 2.84/0.99  
% 2.84/0.99  res_num_of_clauses:                     0
% 2.84/0.99  res_num_in_passive:                     0
% 2.84/0.99  res_num_in_active:                      0
% 2.84/0.99  res_num_of_loops:                       146
% 2.84/0.99  res_forward_subset_subsumed:            25
% 2.84/0.99  res_backward_subset_subsumed:           0
% 2.84/0.99  res_forward_subsumed:                   0
% 2.84/0.99  res_backward_subsumed:                  0
% 2.84/0.99  res_forward_subsumption_resolution:     2
% 2.84/0.99  res_backward_subsumption_resolution:    0
% 2.84/0.99  res_clause_to_clause_subsumption:       396
% 2.84/0.99  res_orphan_elimination:                 0
% 2.84/0.99  res_tautology_del:                      22
% 2.84/0.99  res_num_eq_res_simplified:              6
% 2.84/0.99  res_num_sel_changes:                    0
% 2.84/0.99  res_moves_from_active_to_pass:          0
% 2.84/0.99  
% 2.84/0.99  ------ Superposition
% 2.84/0.99  
% 2.84/0.99  sup_time_total:                         0.
% 2.84/0.99  sup_time_generating:                    0.
% 2.84/0.99  sup_time_sim_full:                      0.
% 2.84/0.99  sup_time_sim_immed:                     0.
% 2.84/0.99  
% 2.84/0.99  sup_num_of_clauses:                     53
% 2.84/0.99  sup_num_in_active:                      36
% 2.84/0.99  sup_num_in_passive:                     17
% 2.84/0.99  sup_num_of_loops:                       39
% 2.84/0.99  sup_fw_superposition:                   20
% 2.84/0.99  sup_bw_superposition:                   19
% 2.84/0.99  sup_immediate_simplified:               5
% 2.84/0.99  sup_given_eliminated:                   0
% 2.84/0.99  comparisons_done:                       0
% 2.84/0.99  comparisons_avoided:                    0
% 2.84/0.99  
% 2.84/0.99  ------ Simplifications
% 2.84/0.99  
% 2.84/0.99  
% 2.84/0.99  sim_fw_subset_subsumed:                 0
% 2.84/0.99  sim_bw_subset_subsumed:                 1
% 2.84/0.99  sim_fw_subsumed:                        4
% 2.84/0.99  sim_bw_subsumed:                        1
% 2.84/0.99  sim_fw_subsumption_res:                 1
% 2.84/0.99  sim_bw_subsumption_res:                 0
% 2.84/0.99  sim_tautology_del:                      7
% 2.84/0.99  sim_eq_tautology_del:                   0
% 2.84/0.99  sim_eq_res_simp:                        3
% 2.84/0.99  sim_fw_demodulated:                     1
% 2.84/0.99  sim_bw_demodulated:                     3
% 2.84/0.99  sim_light_normalised:                   3
% 2.84/0.99  sim_joinable_taut:                      0
% 2.84/0.99  sim_joinable_simp:                      0
% 2.84/0.99  sim_ac_normalised:                      0
% 2.84/0.99  sim_smt_subsumption:                    0
% 2.84/0.99  
%------------------------------------------------------------------------------
