%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:14 EST 2020

% Result     : Theorem 2.40s
% Output     : CNFRefutation 2.40s
% Verified   : 
% Statistics : Number of formulae       :  251 (1610 expanded)
%              Number of clauses        :  158 ( 363 expanded)
%              Number of leaves         :   20 ( 441 expanded)
%              Depth                    :   32
%              Number of atoms          : 1463 (13977 expanded)
%              Number of equality atoms :  253 ( 486 expanded)
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

fof(f61,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f51,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_xboole_0(sK2(X0))
        & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0] :
      ( ( ~ v1_xboole_0(sK2(X0))
        & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f27,f51])).

fof(f73,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f72,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f15,conjecture,(
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

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

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
    inference(ennf_transformation,[],[f16])).

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

fof(f54,plain,(
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

fof(f55,plain,(
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
    inference(flattening,[],[f54])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_waybel_7(X0,X1,X2)
            | ~ r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) )
          & ( r1_waybel_7(X0,X1,X2)
            | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( ~ r1_waybel_7(X0,X1,sK5)
          | ~ r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),sK5) )
        & ( r1_waybel_7(X0,X1,sK5)
          | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),sK5) )
        & m1_subset_1(sK5,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
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
            ( ( ~ r1_waybel_7(X0,sK4,X2)
              | ~ r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),sK4),X2) )
            & ( r1_waybel_7(X0,sK4,X2)
              | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),sK4),X2) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
        & v13_waybel_0(sK4,k3_yellow_1(k2_struct_0(X0)))
        & v2_waybel_0(sK4,k3_yellow_1(k2_struct_0(X0)))
        & v1_subset_1(sK4,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
        & ~ v1_xboole_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
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
              ( ( ~ r1_waybel_7(sK3,X1,X2)
                | ~ r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X1),X2) )
              & ( r1_waybel_7(sK3,X1,X2)
                | r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X1),X2) )
              & m1_subset_1(X2,u1_struct_0(sK3)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK3)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK3)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK3)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK3))))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,
    ( ( ~ r1_waybel_7(sK3,sK4,sK5)
      | ~ r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK5) )
    & ( r1_waybel_7(sK3,sK4,sK5)
      | r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK5) )
    & m1_subset_1(sK5,u1_struct_0(sK3))
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK3)))))
    & v13_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3)))
    & v2_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3)))
    & v1_subset_1(sK4,u1_struct_0(k3_yellow_1(k2_struct_0(sK3))))
    & ~ v1_xboole_0(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f55,f58,f57,f56])).

fof(f87,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f59])).

fof(f85,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f59])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f70,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f44])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f45,f46])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f74,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK2(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f60,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f90,plain,(
    v2_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f59])).

fof(f9,axiom,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f105,plain,(
    v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) ),
    inference(definition_unfolding,[],[f90,f75])).

fof(f91,plain,(
    v13_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f59])).

fof(f104,plain,(
    v13_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) ),
    inference(definition_unfolding,[],[f91,f75])).

fof(f12,axiom,(
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

fof(f18,plain,(
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
    inference(pure_predicate_removal,[],[f12])).

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
    inference(ennf_transformation,[],[f18])).

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

fof(f81,plain,(
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

fof(f100,plain,(
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
    inference(definition_unfolding,[],[f81,f75,f75,f75,f75])).

fof(f89,plain,(
    v1_subset_1(sK4,u1_struct_0(k3_yellow_1(k2_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f59])).

fof(f106,plain,(
    v1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) ),
    inference(definition_unfolding,[],[f89,f75])).

fof(f88,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f59])).

fof(f92,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK3))))) ),
    inference(cnf_transformation,[],[f59])).

fof(f103,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))))) ),
    inference(definition_unfolding,[],[f92,f75])).

fof(f10,axiom,(
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

fof(f19,plain,(
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
    inference(pure_predicate_removal,[],[f10])).

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
    inference(ennf_transformation,[],[f19])).

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

fof(f77,plain,(
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

fof(f96,plain,(
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
    inference(definition_unfolding,[],[f77,f75,f75,f75])).

fof(f95,plain,
    ( ~ r1_waybel_7(sK3,sK4,sK5)
    | ~ r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK5) ),
    inference(cnf_transformation,[],[f59])).

fof(f13,axiom,(
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
    inference(ennf_transformation,[],[f13])).

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

fof(f53,plain,(
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

fof(f83,plain,(
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
    inference(cnf_transformation,[],[f53])).

fof(f86,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f59])).

fof(f93,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f59])).

fof(f14,axiom,(
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
    inference(ennf_transformation,[],[f14])).

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

fof(f84,plain,(
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

fof(f102,plain,(
    ! [X0,X1] :
      ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | ~ v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f84,f75,f75,f75,f75])).

fof(f94,plain,
    ( r1_waybel_7(sK3,sK4,sK5)
    | r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK5) ),
    inference(cnf_transformation,[],[f59])).

fof(f82,plain,(
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
    inference(cnf_transformation,[],[f53])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f71,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f76,plain,(
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

fof(f97,plain,(
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
    inference(definition_unfolding,[],[f76,f75,f75,f75])).

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
     => ( v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v4_orders_2(k3_yellow19(X0,X1,X2))
        & v3_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
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
    inference(pure_predicate_removal,[],[f11])).

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
     => ( v4_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f17])).

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
    inference(ennf_transformation,[],[f20])).

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

fof(f79,plain,(
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

fof(f98,plain,(
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
    inference(definition_unfolding,[],[f79,f75,f75,f75])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_4686,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_14,plain,
    ( m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_12,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_32,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_628,plain,
    ( l1_struct_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_32])).

cnf(c_629,plain,
    ( l1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_628])).

cnf(c_1106,plain,
    ( m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_629])).

cnf(c_1107,plain,
    ( m1_subset_1(sK2(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_1106])).

cnf(c_34,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_72,plain,
    ( m1_subset_1(sK2(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ l1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_78,plain,
    ( ~ l1_pre_topc(sK3)
    | l1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1109,plain,
    ( m1_subset_1(sK2(sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1107,c_34,c_32,c_72,c_78])).

cnf(c_4673,plain,
    ( m1_subset_1(sK2(sK3),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1109])).

cnf(c_10,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1135,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_629])).

cnf(c_1136,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_1135])).

cnf(c_4703,plain,
    ( m1_subset_1(sK2(sK3),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4673,c_1136])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_4678,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_5153,plain,
    ( r1_tarski(sK2(sK3),k2_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4703,c_4678])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_4682,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_5705,plain,
    ( r2_hidden(X0,sK2(sK3)) != iProver_top
    | r2_hidden(X0,k2_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5153,c_4682])).

cnf(c_6047,plain,
    ( r2_hidden(sK0(sK2(sK3)),k2_struct_0(sK3)) = iProver_top
    | v1_xboole_0(sK2(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4686,c_5705])).

cnf(c_35,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_37,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_13,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(sK2(X0)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_74,plain,
    ( v2_struct_0(X0) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | v1_xboole_0(sK2(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_76,plain,
    ( v2_struct_0(sK3) = iProver_top
    | l1_struct_0(sK3) != iProver_top
    | v1_xboole_0(sK2(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_74])).

cnf(c_77,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_79,plain,
    ( l1_pre_topc(sK3) != iProver_top
    | l1_struct_0(sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_77])).

cnf(c_6265,plain,
    ( r2_hidden(sK0(sK2(sK3)),k2_struct_0(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6047,c_35,c_37,c_76,c_79])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_4685,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_6270,plain,
    ( v1_xboole_0(k2_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6265,c_4685])).

cnf(c_29,negated_conjecture,
    ( v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_28,negated_conjecture,
    ( v13_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f104])).

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
    inference(cnf_transformation,[],[f100])).

cnf(c_30,negated_conjecture,
    ( v1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_456,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v7_waybel_0(k3_yellow19(X2,X1,X0))
    | v2_struct_0(X2)
    | ~ l1_struct_0(X2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_30])).

cnf(c_457,plain,
    ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(X1,X0,sK4))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(sK4)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(unflattening,[status(thm)],[c_456])).

cnf(c_31,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_461,plain,
    ( v1_xboole_0(X0)
    | ~ l1_struct_0(X1)
    | v2_struct_0(X1)
    | v7_waybel_0(k3_yellow19(X1,X0,sK4))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_457,c_31])).

cnf(c_462,plain,
    ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(X1,X0,sK4))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(renaming,[status(thm)],[c_461])).

cnf(c_1206,plain,
    ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(X1,X0,sK4))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_462,c_629])).

cnf(c_1207,plain,
    ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK3,X0,sK4))
    | v2_struct_0(sK3)
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(unflattening,[status(thm)],[c_1206])).

cnf(c_1211,plain,
    ( v7_waybel_0(k3_yellow19(sK3,X0,sK4))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1207,c_34])).

cnf(c_1212,plain,
    ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK3,X0,sK4))
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(renaming,[status(thm)],[c_1211])).

cnf(c_1658,plain,
    ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK3,X0,sK4))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_1212])).

cnf(c_1936,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK3,X0,sK4))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_1658])).

cnf(c_3019,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK3,X0,sK4))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(equality_resolution_simp,[status(thm)],[c_1936])).

cnf(c_4664,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
    | v7_waybel_0(k3_yellow19(sK3,X0,sK4)) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3019])).

cnf(c_4793,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
    | v7_waybel_0(k3_yellow19(sK3,X0,sK4)) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4664,c_1136])).

cnf(c_5426,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(k2_struct_0(sK3)))
    | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))))) != iProver_top
    | v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) = iProver_top
    | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4793])).

cnf(c_5934,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))))) != iProver_top
    | v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) = iProver_top
    | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_5426])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))))) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_42,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

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
    inference(cnf_transformation,[],[f96])).

cnf(c_24,negated_conjecture,
    ( ~ r1_waybel_7(sK3,sK4,sK5)
    | ~ r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK5) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_264,plain,
    ( ~ r1_waybel_7(sK3,sK4,sK5)
    | ~ r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK5) ),
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
    inference(cnf_transformation,[],[f83])).

cnf(c_33,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_579,plain,
    ( ~ r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
    | r3_waybel_9(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_33])).

cnf(c_580,plain,
    ( ~ r1_waybel_7(sK3,k2_yellow19(sK3,X0),X1)
    | r3_waybel_9(sK3,X0,X1)
    | ~ l1_waybel_0(X0,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_579])).

cnf(c_584,plain,
    ( ~ r1_waybel_7(sK3,k2_yellow19(sK3,X0),X1)
    | r3_waybel_9(sK3,X0,X1)
    | ~ l1_waybel_0(X0,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_580,c_34,c_32])).

cnf(c_957,plain,
    ( ~ r1_waybel_7(sK3,k2_yellow19(sK3,X0),X1)
    | ~ r1_waybel_7(sK3,sK4,sK5)
    | ~ l1_waybel_0(X0,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != X0
    | sK5 != X1
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_264,c_584])).

cnf(c_958,plain,
    ( ~ r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
    | ~ r1_waybel_7(sK3,sK4,sK5)
    | ~ l1_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) ),
    inference(unflattening,[status(thm)],[c_957])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_960,plain,
    ( ~ l1_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK3)
    | ~ r1_waybel_7(sK3,sK4,sK5)
    | ~ r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
    | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_958,c_26])).

cnf(c_961,plain,
    ( ~ r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
    | ~ r1_waybel_7(sK3,sK4,sK5)
    | ~ l1_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK3)
    | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) ),
    inference(renaming,[status(thm)],[c_960])).

cnf(c_997,plain,
    ( ~ r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
    | ~ r1_waybel_7(sK3,sK4,sK5)
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v2_struct_0(X2)
    | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | ~ l1_struct_0(X2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(X2,X1,X0)
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_961])).

cnf(c_998,plain,
    ( ~ r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
    | ~ r1_waybel_7(sK3,sK4,sK5)
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v2_struct_0(sK3)
    | ~ l1_struct_0(sK3)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(sK3,X1,X0) ),
    inference(unflattening,[status(thm)],[c_997])).

cnf(c_1002,plain,
    ( ~ r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
    | ~ r1_waybel_7(sK3,sK4,sK5)
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(sK3,X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_998,c_34,c_32,c_78])).

cnf(c_1613,plain,
    ( ~ r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
    | ~ r1_waybel_7(sK3,sK4,sK5)
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(sK3,X1,X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X1))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1002,c_28])).

cnf(c_1614,plain,
    ( ~ r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
    | ~ r1_waybel_7(sK3,sK4,sK5)
    | ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v1_xboole_0(X0)
    | v1_xboole_0(sK4)
    | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(sK3,X0,sK4)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_1613])).

cnf(c_1618,plain,
    ( v1_xboole_0(X0)
    | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ r1_waybel_7(sK3,sK4,sK5)
    | ~ r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
    | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(sK3,X0,sK4)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1614,c_31])).

cnf(c_1619,plain,
    ( ~ r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
    | ~ r1_waybel_7(sK3,sK4,sK5)
    | ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v1_xboole_0(X0)
    | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(sK3,X0,sK4)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(renaming,[status(thm)],[c_1618])).

cnf(c_1962,plain,
    ( ~ r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
    | ~ r1_waybel_7(sK3,sK4,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v1_xboole_0(X0)
    | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(sK3,X0,sK4)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_1619])).

cnf(c_3015,plain,
    ( ~ r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
    | ~ r1_waybel_7(sK3,sK4,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v1_xboole_0(X0)
    | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(sK3,X0,sK4)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(equality_resolution_simp,[status(thm)],[c_1962])).

cnf(c_4052,plain,
    ( ~ r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
    | ~ r1_waybel_7(sK3,sK4,sK5)
    | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_3015])).

cnf(c_4665,plain,
    ( r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5) != iProver_top
    | r1_waybel_7(sK3,sK4,sK5) != iProver_top
    | v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != iProver_top
    | v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != iProver_top
    | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4052])).

cnf(c_23,plain,
    ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0 ),
    inference(cnf_transformation,[],[f102])).

cnf(c_495,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_30])).

cnf(c_496,plain,
    ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | v1_xboole_0(sK4)
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK4)) = sK4
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) ),
    inference(unflattening,[status(thm)],[c_495])).

cnf(c_500,plain,
    ( ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK4)) = sK4
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_496,c_31])).

cnf(c_501,plain,
    ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK4)) = sK4
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) ),
    inference(renaming,[status(thm)],[c_500])).

cnf(c_1095,plain,
    ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | v2_struct_0(X0)
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK4)) = sK4
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_501,c_629])).

cnf(c_1096,plain,
    ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
    | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))
    | v2_struct_0(sK3)
    | k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) = sK4
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) ),
    inference(unflattening,[status(thm)],[c_1095])).

cnf(c_1098,plain,
    ( k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) = sK4
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1096,c_34,c_29,c_28,c_27])).

cnf(c_3026,plain,
    ( k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) = sK4 ),
    inference(equality_resolution_simp,[status(thm)],[c_1098])).

cnf(c_4806,plain,
    ( r1_waybel_7(sK3,sK4,sK5) != iProver_top
    | v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != iProver_top
    | v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != iProver_top
    | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4665,c_3026])).

cnf(c_25,negated_conjecture,
    ( r1_waybel_7(sK3,sK4,sK5)
    | r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK5) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_266,plain,
    ( r1_waybel_7(sK3,sK4,sK5)
    | r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK5) ),
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
    inference(cnf_transformation,[],[f82])).

cnf(c_546,plain,
    ( r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
    | ~ r3_waybel_9(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_33])).

cnf(c_547,plain,
    ( r1_waybel_7(sK3,k2_yellow19(sK3,X0),X1)
    | ~ r3_waybel_9(sK3,X0,X1)
    | ~ l1_waybel_0(X0,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_546])).

cnf(c_551,plain,
    ( r1_waybel_7(sK3,k2_yellow19(sK3,X0),X1)
    | ~ r3_waybel_9(sK3,X0,X1)
    | ~ l1_waybel_0(X0,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_547,c_34,c_32])).

cnf(c_931,plain,
    ( r1_waybel_7(sK3,k2_yellow19(sK3,X0),X1)
    | r1_waybel_7(sK3,sK4,sK5)
    | ~ l1_waybel_0(X0,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != X0
    | sK5 != X1
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_266,c_551])).

cnf(c_932,plain,
    ( r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
    | r1_waybel_7(sK3,sK4,sK5)
    | ~ l1_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) ),
    inference(unflattening,[status(thm)],[c_931])).

cnf(c_934,plain,
    ( ~ l1_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK3)
    | r1_waybel_7(sK3,sK4,sK5)
    | r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
    | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_932,c_26])).

cnf(c_935,plain,
    ( r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
    | r1_waybel_7(sK3,sK4,sK5)
    | ~ l1_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK3)
    | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) ),
    inference(renaming,[status(thm)],[c_934])).

cnf(c_1045,plain,
    ( r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
    | r1_waybel_7(sK3,sK4,sK5)
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v2_struct_0(X2)
    | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | ~ l1_struct_0(X2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(X2,X1,X0)
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_935])).

cnf(c_1046,plain,
    ( r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
    | r1_waybel_7(sK3,sK4,sK5)
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v2_struct_0(sK3)
    | ~ l1_struct_0(sK3)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(sK3,X1,X0) ),
    inference(unflattening,[status(thm)],[c_1045])).

cnf(c_1050,plain,
    ( r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
    | r1_waybel_7(sK3,sK4,sK5)
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(sK3,X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1046,c_34,c_32,c_78])).

cnf(c_1568,plain,
    ( r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
    | r1_waybel_7(sK3,sK4,sK5)
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(sK3,X1,X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X1))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1050,c_28])).

cnf(c_1569,plain,
    ( r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
    | r1_waybel_7(sK3,sK4,sK5)
    | ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v1_xboole_0(X0)
    | v1_xboole_0(sK4)
    | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(sK3,X0,sK4)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_1568])).

cnf(c_1573,plain,
    ( v1_xboole_0(X0)
    | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | r1_waybel_7(sK3,sK4,sK5)
    | r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
    | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(sK3,X0,sK4)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1569,c_31])).

cnf(c_1574,plain,
    ( r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
    | r1_waybel_7(sK3,sK4,sK5)
    | ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v1_xboole_0(X0)
    | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(sK3,X0,sK4)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(renaming,[status(thm)],[c_1573])).

cnf(c_2000,plain,
    ( r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
    | r1_waybel_7(sK3,sK4,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v1_xboole_0(X0)
    | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(sK3,X0,sK4)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_1574])).

cnf(c_3011,plain,
    ( r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
    | r1_waybel_7(sK3,sK4,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v1_xboole_0(X0)
    | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(sK3,X0,sK4)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(equality_resolution_simp,[status(thm)],[c_2000])).

cnf(c_4053,plain,
    ( r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
    | r1_waybel_7(sK3,sK4,sK5)
    | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_3011])).

cnf(c_4667,plain,
    ( r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5) = iProver_top
    | r1_waybel_7(sK3,sK4,sK5) = iProver_top
    | v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != iProver_top
    | v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != iProver_top
    | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4053])).

cnf(c_4782,plain,
    ( r1_waybel_7(sK3,sK4,sK5) = iProver_top
    | v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != iProver_top
    | v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != iProver_top
    | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4667,c_3026])).

cnf(c_4812,plain,
    ( v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != iProver_top
    | v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != iProver_top
    | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4806,c_4782])).

cnf(c_11,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1128,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_629])).

cnf(c_1129,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(unflattening,[status(thm)],[c_1128])).

cnf(c_4671,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1129])).

cnf(c_4700,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4671,c_1136])).

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
    inference(cnf_transformation,[],[f97])).

cnf(c_1173,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v2_struct_0(X2)
    | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_629])).

cnf(c_1174,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_struct_0(k3_yellow19(sK3,X1,X0))
    | v2_struct_0(sK3)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(unflattening,[status(thm)],[c_1173])).

cnf(c_1178,plain,
    ( ~ v2_struct_0(k3_yellow19(sK3,X1,X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1174,c_34])).

cnf(c_1179,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_struct_0(k3_yellow19(sK3,X1,X0))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(renaming,[status(thm)],[c_1178])).

cnf(c_1508,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_struct_0(k3_yellow19(sK3,X1,X0))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X1))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1179,c_28])).

cnf(c_1509,plain,
    ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v2_struct_0(k3_yellow19(sK3,X0,sK4))
    | v1_xboole_0(X0)
    | v1_xboole_0(sK4)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_1508])).

cnf(c_1513,plain,
    ( v1_xboole_0(X0)
    | ~ v2_struct_0(k3_yellow19(sK3,X0,sK4))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1509,c_31])).

cnf(c_1514,plain,
    ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v2_struct_0(k3_yellow19(sK3,X0,sK4))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(renaming,[status(thm)],[c_1513])).

cnf(c_2061,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v2_struct_0(k3_yellow19(sK3,X0,sK4))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_1514])).

cnf(c_3003,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v2_struct_0(k3_yellow19(sK3,X0,sK4))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(equality_resolution_simp,[status(thm)],[c_2061])).

cnf(c_4670,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
    | v2_struct_0(k3_yellow19(sK3,X0,sK4)) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3003])).

cnf(c_4757,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
    | v2_struct_0(k3_yellow19(sK3,X0,sK4)) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4670,c_1136])).

cnf(c_5260,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))))) != iProver_top
    | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != iProver_top
    | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4757])).

cnf(c_5508,plain,
    ( v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != iProver_top
    | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5260,c_42,c_4700])).

cnf(c_4051,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v1_xboole_0(X0)
    | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(sK3,X0,sK4)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_3015])).

cnf(c_4666,plain,
    ( k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(sK3,X0,sK4)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4051])).

cnf(c_4768,plain,
    ( k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(sK3,X0,sK4)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4666,c_1136])).

cnf(c_5269,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(k2_struct_0(sK3)))
    | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))))) != iProver_top
    | v1_xboole_0(k2_struct_0(sK3)) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4768])).

cnf(c_5589,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))))) != iProver_top
    | v1_xboole_0(k2_struct_0(sK3)) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_5269])).

cnf(c_5591,plain,
    ( v1_xboole_0(k2_struct_0(sK3)) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5589,c_42,c_4700])).

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
    inference(cnf_transformation,[],[f98])).

cnf(c_1140,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v4_orders_2(k3_yellow19(X2,X1,X0))
    | v2_struct_0(X2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_629])).

cnf(c_1141,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | v4_orders_2(k3_yellow19(sK3,X1,X0))
    | v2_struct_0(sK3)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(unflattening,[status(thm)],[c_1140])).

cnf(c_1145,plain,
    ( v4_orders_2(k3_yellow19(sK3,X1,X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1141,c_34])).

cnf(c_1146,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | v4_orders_2(k3_yellow19(sK3,X1,X0))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(renaming,[status(thm)],[c_1145])).

cnf(c_1538,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | v4_orders_2(k3_yellow19(sK3,X1,X0))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X1))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1146,c_28])).

cnf(c_1539,plain,
    ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(sK3,X0,sK4))
    | v1_xboole_0(X0)
    | v1_xboole_0(sK4)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_1538])).

cnf(c_1543,plain,
    ( v1_xboole_0(X0)
    | v4_orders_2(k3_yellow19(sK3,X0,sK4))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1539,c_31])).

cnf(c_1544,plain,
    ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(sK3,X0,sK4))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(renaming,[status(thm)],[c_1543])).

cnf(c_2038,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(sK3,X0,sK4))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_1544])).

cnf(c_3007,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(sK3,X0,sK4))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(equality_resolution_simp,[status(thm)],[c_2038])).

cnf(c_4669,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
    | v4_orders_2(k3_yellow19(sK3,X0,sK4)) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3007])).

cnf(c_4746,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
    | v4_orders_2(k3_yellow19(sK3,X0,sK4)) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4669,c_1136])).

cnf(c_5417,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))))) != iProver_top
    | v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) = iProver_top
    | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4746])).

cnf(c_5928,plain,
    ( v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) = iProver_top
    | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5417,c_42,c_4700])).

cnf(c_5936,plain,
    ( v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5934,c_42,c_4812,c_4700,c_5508,c_5591,c_5928])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6270,c_5936])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:00:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 2.40/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.40/0.99  
% 2.40/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.40/0.99  
% 2.40/0.99  ------  iProver source info
% 2.40/0.99  
% 2.40/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.40/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.40/0.99  git: non_committed_changes: false
% 2.40/0.99  git: last_make_outside_of_git: false
% 2.40/0.99  
% 2.40/0.99  ------ 
% 2.40/0.99  
% 2.40/0.99  ------ Input Options
% 2.40/0.99  
% 2.40/0.99  --out_options                           all
% 2.40/0.99  --tptp_safe_out                         true
% 2.40/0.99  --problem_path                          ""
% 2.40/0.99  --include_path                          ""
% 2.40/0.99  --clausifier                            res/vclausify_rel
% 2.40/0.99  --clausifier_options                    --mode clausify
% 2.40/0.99  --stdin                                 false
% 2.40/0.99  --stats_out                             all
% 2.40/0.99  
% 2.40/0.99  ------ General Options
% 2.40/0.99  
% 2.40/0.99  --fof                                   false
% 2.40/0.99  --time_out_real                         305.
% 2.40/0.99  --time_out_virtual                      -1.
% 2.40/0.99  --symbol_type_check                     false
% 2.40/0.99  --clausify_out                          false
% 2.40/0.99  --sig_cnt_out                           false
% 2.40/0.99  --trig_cnt_out                          false
% 2.40/0.99  --trig_cnt_out_tolerance                1.
% 2.40/0.99  --trig_cnt_out_sk_spl                   false
% 2.40/0.99  --abstr_cl_out                          false
% 2.40/0.99  
% 2.40/0.99  ------ Global Options
% 2.40/0.99  
% 2.40/0.99  --schedule                              default
% 2.40/0.99  --add_important_lit                     false
% 2.40/0.99  --prop_solver_per_cl                    1000
% 2.40/0.99  --min_unsat_core                        false
% 2.40/0.99  --soft_assumptions                      false
% 2.40/0.99  --soft_lemma_size                       3
% 2.40/0.99  --prop_impl_unit_size                   0
% 2.40/0.99  --prop_impl_unit                        []
% 2.40/0.99  --share_sel_clauses                     true
% 2.40/0.99  --reset_solvers                         false
% 2.40/0.99  --bc_imp_inh                            [conj_cone]
% 2.40/0.99  --conj_cone_tolerance                   3.
% 2.40/0.99  --extra_neg_conj                        none
% 2.40/0.99  --large_theory_mode                     true
% 2.40/0.99  --prolific_symb_bound                   200
% 2.40/0.99  --lt_threshold                          2000
% 2.40/0.99  --clause_weak_htbl                      true
% 2.40/0.99  --gc_record_bc_elim                     false
% 2.40/0.99  
% 2.40/0.99  ------ Preprocessing Options
% 2.40/0.99  
% 2.40/0.99  --preprocessing_flag                    true
% 2.40/0.99  --time_out_prep_mult                    0.1
% 2.40/0.99  --splitting_mode                        input
% 2.40/0.99  --splitting_grd                         true
% 2.40/0.99  --splitting_cvd                         false
% 2.40/0.99  --splitting_cvd_svl                     false
% 2.40/0.99  --splitting_nvd                         32
% 2.40/0.99  --sub_typing                            true
% 2.40/0.99  --prep_gs_sim                           true
% 2.40/0.99  --prep_unflatten                        true
% 2.40/0.99  --prep_res_sim                          true
% 2.40/0.99  --prep_upred                            true
% 2.40/0.99  --prep_sem_filter                       exhaustive
% 2.40/0.99  --prep_sem_filter_out                   false
% 2.40/0.99  --pred_elim                             true
% 2.40/0.99  --res_sim_input                         true
% 2.40/0.99  --eq_ax_congr_red                       true
% 2.40/0.99  --pure_diseq_elim                       true
% 2.40/0.99  --brand_transform                       false
% 2.40/0.99  --non_eq_to_eq                          false
% 2.40/0.99  --prep_def_merge                        true
% 2.40/0.99  --prep_def_merge_prop_impl              false
% 2.40/0.99  --prep_def_merge_mbd                    true
% 2.40/0.99  --prep_def_merge_tr_red                 false
% 2.40/0.99  --prep_def_merge_tr_cl                  false
% 2.40/0.99  --smt_preprocessing                     true
% 2.40/0.99  --smt_ac_axioms                         fast
% 2.40/0.99  --preprocessed_out                      false
% 2.40/0.99  --preprocessed_stats                    false
% 2.40/0.99  
% 2.40/0.99  ------ Abstraction refinement Options
% 2.40/0.99  
% 2.40/0.99  --abstr_ref                             []
% 2.40/0.99  --abstr_ref_prep                        false
% 2.40/0.99  --abstr_ref_until_sat                   false
% 2.40/0.99  --abstr_ref_sig_restrict                funpre
% 2.40/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.40/0.99  --abstr_ref_under                       []
% 2.40/0.99  
% 2.40/0.99  ------ SAT Options
% 2.40/0.99  
% 2.40/0.99  --sat_mode                              false
% 2.40/0.99  --sat_fm_restart_options                ""
% 2.40/0.99  --sat_gr_def                            false
% 2.40/0.99  --sat_epr_types                         true
% 2.40/0.99  --sat_non_cyclic_types                  false
% 2.40/0.99  --sat_finite_models                     false
% 2.40/0.99  --sat_fm_lemmas                         false
% 2.40/0.99  --sat_fm_prep                           false
% 2.40/0.99  --sat_fm_uc_incr                        true
% 2.40/0.99  --sat_out_model                         small
% 2.40/0.99  --sat_out_clauses                       false
% 2.40/0.99  
% 2.40/0.99  ------ QBF Options
% 2.40/0.99  
% 2.40/0.99  --qbf_mode                              false
% 2.40/0.99  --qbf_elim_univ                         false
% 2.40/0.99  --qbf_dom_inst                          none
% 2.40/0.99  --qbf_dom_pre_inst                      false
% 2.40/0.99  --qbf_sk_in                             false
% 2.40/0.99  --qbf_pred_elim                         true
% 2.40/0.99  --qbf_split                             512
% 2.40/0.99  
% 2.40/0.99  ------ BMC1 Options
% 2.40/0.99  
% 2.40/0.99  --bmc1_incremental                      false
% 2.40/0.99  --bmc1_axioms                           reachable_all
% 2.40/0.99  --bmc1_min_bound                        0
% 2.40/0.99  --bmc1_max_bound                        -1
% 2.40/0.99  --bmc1_max_bound_default                -1
% 2.40/0.99  --bmc1_symbol_reachability              true
% 2.40/0.99  --bmc1_property_lemmas                  false
% 2.40/0.99  --bmc1_k_induction                      false
% 2.40/0.99  --bmc1_non_equiv_states                 false
% 2.40/0.99  --bmc1_deadlock                         false
% 2.40/0.99  --bmc1_ucm                              false
% 2.40/0.99  --bmc1_add_unsat_core                   none
% 2.40/0.99  --bmc1_unsat_core_children              false
% 2.40/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.40/0.99  --bmc1_out_stat                         full
% 2.40/0.99  --bmc1_ground_init                      false
% 2.40/0.99  --bmc1_pre_inst_next_state              false
% 2.40/0.99  --bmc1_pre_inst_state                   false
% 2.40/0.99  --bmc1_pre_inst_reach_state             false
% 2.40/0.99  --bmc1_out_unsat_core                   false
% 2.40/0.99  --bmc1_aig_witness_out                  false
% 2.40/0.99  --bmc1_verbose                          false
% 2.40/0.99  --bmc1_dump_clauses_tptp                false
% 2.40/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.40/0.99  --bmc1_dump_file                        -
% 2.40/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.40/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.40/0.99  --bmc1_ucm_extend_mode                  1
% 2.40/0.99  --bmc1_ucm_init_mode                    2
% 2.40/0.99  --bmc1_ucm_cone_mode                    none
% 2.40/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.40/0.99  --bmc1_ucm_relax_model                  4
% 2.40/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.40/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.40/0.99  --bmc1_ucm_layered_model                none
% 2.40/0.99  --bmc1_ucm_max_lemma_size               10
% 2.40/0.99  
% 2.40/0.99  ------ AIG Options
% 2.40/0.99  
% 2.40/0.99  --aig_mode                              false
% 2.40/0.99  
% 2.40/0.99  ------ Instantiation Options
% 2.40/0.99  
% 2.40/0.99  --instantiation_flag                    true
% 2.40/0.99  --inst_sos_flag                         false
% 2.40/0.99  --inst_sos_phase                        true
% 2.40/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.40/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.40/0.99  --inst_lit_sel_side                     num_symb
% 2.40/0.99  --inst_solver_per_active                1400
% 2.40/0.99  --inst_solver_calls_frac                1.
% 2.40/0.99  --inst_passive_queue_type               priority_queues
% 2.40/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.40/0.99  --inst_passive_queues_freq              [25;2]
% 2.40/0.99  --inst_dismatching                      true
% 2.40/0.99  --inst_eager_unprocessed_to_passive     true
% 2.40/0.99  --inst_prop_sim_given                   true
% 2.40/0.99  --inst_prop_sim_new                     false
% 2.40/0.99  --inst_subs_new                         false
% 2.40/0.99  --inst_eq_res_simp                      false
% 2.40/0.99  --inst_subs_given                       false
% 2.40/0.99  --inst_orphan_elimination               true
% 2.40/0.99  --inst_learning_loop_flag               true
% 2.40/0.99  --inst_learning_start                   3000
% 2.40/0.99  --inst_learning_factor                  2
% 2.40/0.99  --inst_start_prop_sim_after_learn       3
% 2.40/0.99  --inst_sel_renew                        solver
% 2.40/0.99  --inst_lit_activity_flag                true
% 2.40/0.99  --inst_restr_to_given                   false
% 2.40/0.99  --inst_activity_threshold               500
% 2.40/0.99  --inst_out_proof                        true
% 2.40/0.99  
% 2.40/0.99  ------ Resolution Options
% 2.40/0.99  
% 2.40/0.99  --resolution_flag                       true
% 2.40/0.99  --res_lit_sel                           adaptive
% 2.40/0.99  --res_lit_sel_side                      none
% 2.40/0.99  --res_ordering                          kbo
% 2.40/0.99  --res_to_prop_solver                    active
% 2.40/0.99  --res_prop_simpl_new                    false
% 2.40/0.99  --res_prop_simpl_given                  true
% 2.40/0.99  --res_passive_queue_type                priority_queues
% 2.40/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.40/0.99  --res_passive_queues_freq               [15;5]
% 2.40/0.99  --res_forward_subs                      full
% 2.40/0.99  --res_backward_subs                     full
% 2.40/0.99  --res_forward_subs_resolution           true
% 2.40/0.99  --res_backward_subs_resolution          true
% 2.40/0.99  --res_orphan_elimination                true
% 2.40/0.99  --res_time_limit                        2.
% 2.40/0.99  --res_out_proof                         true
% 2.40/0.99  
% 2.40/0.99  ------ Superposition Options
% 2.40/0.99  
% 2.40/0.99  --superposition_flag                    true
% 2.40/0.99  --sup_passive_queue_type                priority_queues
% 2.40/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.40/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.40/0.99  --demod_completeness_check              fast
% 2.40/0.99  --demod_use_ground                      true
% 2.40/0.99  --sup_to_prop_solver                    passive
% 2.40/0.99  --sup_prop_simpl_new                    true
% 2.40/0.99  --sup_prop_simpl_given                  true
% 2.40/0.99  --sup_fun_splitting                     false
% 2.40/0.99  --sup_smt_interval                      50000
% 2.40/0.99  
% 2.40/0.99  ------ Superposition Simplification Setup
% 2.40/0.99  
% 2.40/0.99  --sup_indices_passive                   []
% 2.40/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.40/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/0.99  --sup_full_bw                           [BwDemod]
% 2.40/0.99  --sup_immed_triv                        [TrivRules]
% 2.40/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.40/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/0.99  --sup_immed_bw_main                     []
% 2.40/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.40/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.40/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.40/0.99  
% 2.40/0.99  ------ Combination Options
% 2.40/0.99  
% 2.40/0.99  --comb_res_mult                         3
% 2.40/0.99  --comb_sup_mult                         2
% 2.40/0.99  --comb_inst_mult                        10
% 2.40/0.99  
% 2.40/0.99  ------ Debug Options
% 2.40/0.99  
% 2.40/0.99  --dbg_backtrace                         false
% 2.40/0.99  --dbg_dump_prop_clauses                 false
% 2.40/0.99  --dbg_dump_prop_clauses_file            -
% 2.40/0.99  --dbg_out_stat                          false
% 2.40/0.99  ------ Parsing...
% 2.40/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.40/0.99  
% 2.40/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe_e 
% 2.40/0.99  
% 2.40/0.99  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.40/0.99  
% 2.40/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.40/0.99  ------ Proving...
% 2.40/0.99  ------ Problem Properties 
% 2.40/0.99  
% 2.40/0.99  
% 2.40/0.99  clauses                                 25
% 2.40/0.99  conjectures                             4
% 2.40/0.99  EPR                                     6
% 2.40/0.99  Horn                                    19
% 2.40/0.99  unary                                   10
% 2.40/0.99  binary                                  6
% 2.40/0.99  lits                                    68
% 2.40/0.99  lits eq                                 11
% 2.40/0.99  fd_pure                                 0
% 2.40/0.99  fd_pseudo                               0
% 2.40/0.99  fd_cond                                 0
% 2.40/0.99  fd_pseudo_cond                          1
% 2.40/0.99  AC symbols                              0
% 2.40/0.99  
% 2.40/0.99  ------ Schedule dynamic 5 is on 
% 2.40/0.99  
% 2.40/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.40/0.99  
% 2.40/0.99  
% 2.40/0.99  ------ 
% 2.40/0.99  Current options:
% 2.40/0.99  ------ 
% 2.40/0.99  
% 2.40/0.99  ------ Input Options
% 2.40/0.99  
% 2.40/0.99  --out_options                           all
% 2.40/0.99  --tptp_safe_out                         true
% 2.40/0.99  --problem_path                          ""
% 2.40/0.99  --include_path                          ""
% 2.40/0.99  --clausifier                            res/vclausify_rel
% 2.40/0.99  --clausifier_options                    --mode clausify
% 2.40/0.99  --stdin                                 false
% 2.40/0.99  --stats_out                             all
% 2.40/0.99  
% 2.40/0.99  ------ General Options
% 2.40/0.99  
% 2.40/0.99  --fof                                   false
% 2.40/0.99  --time_out_real                         305.
% 2.40/0.99  --time_out_virtual                      -1.
% 2.40/0.99  --symbol_type_check                     false
% 2.40/0.99  --clausify_out                          false
% 2.40/0.99  --sig_cnt_out                           false
% 2.40/0.99  --trig_cnt_out                          false
% 2.40/0.99  --trig_cnt_out_tolerance                1.
% 2.40/0.99  --trig_cnt_out_sk_spl                   false
% 2.40/0.99  --abstr_cl_out                          false
% 2.40/0.99  
% 2.40/0.99  ------ Global Options
% 2.40/0.99  
% 2.40/0.99  --schedule                              default
% 2.40/0.99  --add_important_lit                     false
% 2.40/0.99  --prop_solver_per_cl                    1000
% 2.40/0.99  --min_unsat_core                        false
% 2.40/0.99  --soft_assumptions                      false
% 2.40/0.99  --soft_lemma_size                       3
% 2.40/0.99  --prop_impl_unit_size                   0
% 2.40/0.99  --prop_impl_unit                        []
% 2.40/0.99  --share_sel_clauses                     true
% 2.40/0.99  --reset_solvers                         false
% 2.40/0.99  --bc_imp_inh                            [conj_cone]
% 2.40/0.99  --conj_cone_tolerance                   3.
% 2.40/0.99  --extra_neg_conj                        none
% 2.40/0.99  --large_theory_mode                     true
% 2.40/0.99  --prolific_symb_bound                   200
% 2.40/0.99  --lt_threshold                          2000
% 2.40/0.99  --clause_weak_htbl                      true
% 2.40/0.99  --gc_record_bc_elim                     false
% 2.40/0.99  
% 2.40/0.99  ------ Preprocessing Options
% 2.40/0.99  
% 2.40/0.99  --preprocessing_flag                    true
% 2.40/0.99  --time_out_prep_mult                    0.1
% 2.40/0.99  --splitting_mode                        input
% 2.40/0.99  --splitting_grd                         true
% 2.40/0.99  --splitting_cvd                         false
% 2.40/0.99  --splitting_cvd_svl                     false
% 2.40/0.99  --splitting_nvd                         32
% 2.40/0.99  --sub_typing                            true
% 2.40/0.99  --prep_gs_sim                           true
% 2.40/0.99  --prep_unflatten                        true
% 2.40/0.99  --prep_res_sim                          true
% 2.40/0.99  --prep_upred                            true
% 2.40/0.99  --prep_sem_filter                       exhaustive
% 2.40/0.99  --prep_sem_filter_out                   false
% 2.40/0.99  --pred_elim                             true
% 2.40/0.99  --res_sim_input                         true
% 2.40/0.99  --eq_ax_congr_red                       true
% 2.40/0.99  --pure_diseq_elim                       true
% 2.40/0.99  --brand_transform                       false
% 2.40/0.99  --non_eq_to_eq                          false
% 2.40/0.99  --prep_def_merge                        true
% 2.40/0.99  --prep_def_merge_prop_impl              false
% 2.40/0.99  --prep_def_merge_mbd                    true
% 2.40/0.99  --prep_def_merge_tr_red                 false
% 2.40/0.99  --prep_def_merge_tr_cl                  false
% 2.40/0.99  --smt_preprocessing                     true
% 2.40/0.99  --smt_ac_axioms                         fast
% 2.40/0.99  --preprocessed_out                      false
% 2.40/0.99  --preprocessed_stats                    false
% 2.40/0.99  
% 2.40/0.99  ------ Abstraction refinement Options
% 2.40/0.99  
% 2.40/0.99  --abstr_ref                             []
% 2.40/0.99  --abstr_ref_prep                        false
% 2.40/0.99  --abstr_ref_until_sat                   false
% 2.40/0.99  --abstr_ref_sig_restrict                funpre
% 2.40/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.40/0.99  --abstr_ref_under                       []
% 2.40/0.99  
% 2.40/0.99  ------ SAT Options
% 2.40/0.99  
% 2.40/0.99  --sat_mode                              false
% 2.40/0.99  --sat_fm_restart_options                ""
% 2.40/0.99  --sat_gr_def                            false
% 2.40/0.99  --sat_epr_types                         true
% 2.40/0.99  --sat_non_cyclic_types                  false
% 2.40/0.99  --sat_finite_models                     false
% 2.40/0.99  --sat_fm_lemmas                         false
% 2.40/0.99  --sat_fm_prep                           false
% 2.40/0.99  --sat_fm_uc_incr                        true
% 2.40/0.99  --sat_out_model                         small
% 2.40/0.99  --sat_out_clauses                       false
% 2.40/0.99  
% 2.40/0.99  ------ QBF Options
% 2.40/0.99  
% 2.40/0.99  --qbf_mode                              false
% 2.40/0.99  --qbf_elim_univ                         false
% 2.40/0.99  --qbf_dom_inst                          none
% 2.40/0.99  --qbf_dom_pre_inst                      false
% 2.40/0.99  --qbf_sk_in                             false
% 2.40/0.99  --qbf_pred_elim                         true
% 2.40/0.99  --qbf_split                             512
% 2.40/0.99  
% 2.40/0.99  ------ BMC1 Options
% 2.40/0.99  
% 2.40/0.99  --bmc1_incremental                      false
% 2.40/0.99  --bmc1_axioms                           reachable_all
% 2.40/0.99  --bmc1_min_bound                        0
% 2.40/0.99  --bmc1_max_bound                        -1
% 2.40/0.99  --bmc1_max_bound_default                -1
% 2.40/0.99  --bmc1_symbol_reachability              true
% 2.40/0.99  --bmc1_property_lemmas                  false
% 2.40/0.99  --bmc1_k_induction                      false
% 2.40/0.99  --bmc1_non_equiv_states                 false
% 2.40/0.99  --bmc1_deadlock                         false
% 2.40/0.99  --bmc1_ucm                              false
% 2.40/0.99  --bmc1_add_unsat_core                   none
% 2.40/0.99  --bmc1_unsat_core_children              false
% 2.40/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.40/0.99  --bmc1_out_stat                         full
% 2.40/0.99  --bmc1_ground_init                      false
% 2.40/0.99  --bmc1_pre_inst_next_state              false
% 2.40/0.99  --bmc1_pre_inst_state                   false
% 2.40/0.99  --bmc1_pre_inst_reach_state             false
% 2.40/0.99  --bmc1_out_unsat_core                   false
% 2.40/0.99  --bmc1_aig_witness_out                  false
% 2.40/0.99  --bmc1_verbose                          false
% 2.40/0.99  --bmc1_dump_clauses_tptp                false
% 2.40/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.40/0.99  --bmc1_dump_file                        -
% 2.40/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.40/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.40/0.99  --bmc1_ucm_extend_mode                  1
% 2.40/0.99  --bmc1_ucm_init_mode                    2
% 2.40/0.99  --bmc1_ucm_cone_mode                    none
% 2.40/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.40/0.99  --bmc1_ucm_relax_model                  4
% 2.40/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.40/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.40/0.99  --bmc1_ucm_layered_model                none
% 2.40/0.99  --bmc1_ucm_max_lemma_size               10
% 2.40/0.99  
% 2.40/0.99  ------ AIG Options
% 2.40/0.99  
% 2.40/0.99  --aig_mode                              false
% 2.40/0.99  
% 2.40/0.99  ------ Instantiation Options
% 2.40/0.99  
% 2.40/0.99  --instantiation_flag                    true
% 2.40/0.99  --inst_sos_flag                         false
% 2.40/0.99  --inst_sos_phase                        true
% 2.40/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.40/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.40/0.99  --inst_lit_sel_side                     none
% 2.40/0.99  --inst_solver_per_active                1400
% 2.40/0.99  --inst_solver_calls_frac                1.
% 2.40/0.99  --inst_passive_queue_type               priority_queues
% 2.40/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.40/0.99  --inst_passive_queues_freq              [25;2]
% 2.40/0.99  --inst_dismatching                      true
% 2.40/0.99  --inst_eager_unprocessed_to_passive     true
% 2.40/0.99  --inst_prop_sim_given                   true
% 2.40/0.99  --inst_prop_sim_new                     false
% 2.40/0.99  --inst_subs_new                         false
% 2.40/0.99  --inst_eq_res_simp                      false
% 2.40/0.99  --inst_subs_given                       false
% 2.40/0.99  --inst_orphan_elimination               true
% 2.40/0.99  --inst_learning_loop_flag               true
% 2.40/0.99  --inst_learning_start                   3000
% 2.40/0.99  --inst_learning_factor                  2
% 2.40/0.99  --inst_start_prop_sim_after_learn       3
% 2.40/0.99  --inst_sel_renew                        solver
% 2.40/0.99  --inst_lit_activity_flag                true
% 2.40/0.99  --inst_restr_to_given                   false
% 2.40/0.99  --inst_activity_threshold               500
% 2.40/0.99  --inst_out_proof                        true
% 2.40/0.99  
% 2.40/0.99  ------ Resolution Options
% 2.40/0.99  
% 2.40/0.99  --resolution_flag                       false
% 2.40/0.99  --res_lit_sel                           adaptive
% 2.40/0.99  --res_lit_sel_side                      none
% 2.40/0.99  --res_ordering                          kbo
% 2.40/0.99  --res_to_prop_solver                    active
% 2.40/0.99  --res_prop_simpl_new                    false
% 2.40/0.99  --res_prop_simpl_given                  true
% 2.40/0.99  --res_passive_queue_type                priority_queues
% 2.40/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.40/0.99  --res_passive_queues_freq               [15;5]
% 2.40/0.99  --res_forward_subs                      full
% 2.40/0.99  --res_backward_subs                     full
% 2.40/0.99  --res_forward_subs_resolution           true
% 2.40/0.99  --res_backward_subs_resolution          true
% 2.40/0.99  --res_orphan_elimination                true
% 2.40/0.99  --res_time_limit                        2.
% 2.40/0.99  --res_out_proof                         true
% 2.40/0.99  
% 2.40/0.99  ------ Superposition Options
% 2.40/0.99  
% 2.40/0.99  --superposition_flag                    true
% 2.40/0.99  --sup_passive_queue_type                priority_queues
% 2.40/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.40/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.40/0.99  --demod_completeness_check              fast
% 2.40/0.99  --demod_use_ground                      true
% 2.40/0.99  --sup_to_prop_solver                    passive
% 2.40/0.99  --sup_prop_simpl_new                    true
% 2.40/0.99  --sup_prop_simpl_given                  true
% 2.40/0.99  --sup_fun_splitting                     false
% 2.40/0.99  --sup_smt_interval                      50000
% 2.40/0.99  
% 2.40/0.99  ------ Superposition Simplification Setup
% 2.40/0.99  
% 2.40/0.99  --sup_indices_passive                   []
% 2.40/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.40/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/0.99  --sup_full_bw                           [BwDemod]
% 2.40/0.99  --sup_immed_triv                        [TrivRules]
% 2.40/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.40/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/0.99  --sup_immed_bw_main                     []
% 2.40/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.40/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.40/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.40/0.99  
% 2.40/0.99  ------ Combination Options
% 2.40/0.99  
% 2.40/0.99  --comb_res_mult                         3
% 2.40/0.99  --comb_sup_mult                         2
% 2.40/0.99  --comb_inst_mult                        10
% 2.40/0.99  
% 2.40/0.99  ------ Debug Options
% 2.40/0.99  
% 2.40/0.99  --dbg_backtrace                         false
% 2.40/0.99  --dbg_dump_prop_clauses                 false
% 2.40/0.99  --dbg_dump_prop_clauses_file            -
% 2.40/0.99  --dbg_out_stat                          false
% 2.40/0.99  
% 2.40/0.99  
% 2.40/0.99  
% 2.40/0.99  
% 2.40/0.99  ------ Proving...
% 2.40/0.99  
% 2.40/0.99  
% 2.40/0.99  % SZS status Theorem for theBenchmark.p
% 2.40/0.99  
% 2.40/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.40/0.99  
% 2.40/0.99  fof(f1,axiom,(
% 2.40/0.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.40/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/0.99  
% 2.40/0.99  fof(f40,plain,(
% 2.40/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.40/0.99    inference(nnf_transformation,[],[f1])).
% 2.40/0.99  
% 2.40/0.99  fof(f41,plain,(
% 2.40/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.40/0.99    inference(rectify,[],[f40])).
% 2.40/0.99  
% 2.40/0.99  fof(f42,plain,(
% 2.40/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.40/0.99    introduced(choice_axiom,[])).
% 2.40/0.99  
% 2.40/0.99  fof(f43,plain,(
% 2.40/0.99    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.40/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f41,f42])).
% 2.40/0.99  
% 2.40/0.99  fof(f61,plain,(
% 2.40/0.99    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 2.40/0.99    inference(cnf_transformation,[],[f43])).
% 2.40/0.99  
% 2.40/0.99  fof(f8,axiom,(
% 2.40/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ? [X1] : (v1_zfmisc_1(X1) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.40/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/0.99  
% 2.40/0.99  fof(f21,plain,(
% 2.40/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.40/0.99    inference(pure_predicate_removal,[],[f8])).
% 2.40/0.99  
% 2.40/0.99  fof(f26,plain,(
% 2.40/0.99    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.40/0.99    inference(ennf_transformation,[],[f21])).
% 2.40/0.99  
% 2.40/0.99  fof(f27,plain,(
% 2.40/0.99    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.40/0.99    inference(flattening,[],[f26])).
% 2.40/0.99  
% 2.40/0.99  fof(f51,plain,(
% 2.40/0.99    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_xboole_0(sK2(X0)) & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.40/0.99    introduced(choice_axiom,[])).
% 2.40/0.99  
% 2.40/0.99  fof(f52,plain,(
% 2.40/0.99    ! [X0] : ((~v1_xboole_0(sK2(X0)) & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.40/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f27,f51])).
% 2.40/0.99  
% 2.40/0.99  fof(f73,plain,(
% 2.40/0.99    ( ! [X0] : (m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.40/0.99    inference(cnf_transformation,[],[f52])).
% 2.40/0.99  
% 2.40/0.99  fof(f7,axiom,(
% 2.40/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.40/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/0.99  
% 2.40/0.99  fof(f25,plain,(
% 2.40/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.40/0.99    inference(ennf_transformation,[],[f7])).
% 2.40/0.99  
% 2.40/0.99  fof(f72,plain,(
% 2.40/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.40/0.99    inference(cnf_transformation,[],[f25])).
% 2.40/0.99  
% 2.40/0.99  fof(f15,conjecture,(
% 2.40/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <=> r1_waybel_7(X0,X1,X2)))))),
% 2.40/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/0.99  
% 2.40/0.99  fof(f16,negated_conjecture,(
% 2.40/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <=> r1_waybel_7(X0,X1,X2)))))),
% 2.40/0.99    inference(negated_conjecture,[],[f15])).
% 2.40/0.99  
% 2.40/0.99  fof(f38,plain,(
% 2.40/0.99    ? [X0] : (? [X1] : (? [X2] : ((r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <~> r1_waybel_7(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.40/0.99    inference(ennf_transformation,[],[f16])).
% 2.40/0.99  
% 2.40/0.99  fof(f39,plain,(
% 2.40/0.99    ? [X0] : (? [X1] : (? [X2] : ((r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <~> r1_waybel_7(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.40/0.99    inference(flattening,[],[f38])).
% 2.40/0.99  
% 2.40/0.99  fof(f54,plain,(
% 2.40/0.99    ? [X0] : (? [X1] : (? [X2] : (((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.40/0.99    inference(nnf_transformation,[],[f39])).
% 2.40/0.99  
% 2.40/0.99  fof(f55,plain,(
% 2.40/0.99    ? [X0] : (? [X1] : (? [X2] : ((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.40/0.99    inference(flattening,[],[f54])).
% 2.40/0.99  
% 2.40/0.99  fof(f58,plain,(
% 2.40/0.99    ( ! [X0,X1] : (? [X2] : ((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & m1_subset_1(X2,u1_struct_0(X0))) => ((~r1_waybel_7(X0,X1,sK5) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),sK5)) & (r1_waybel_7(X0,X1,sK5) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),sK5)) & m1_subset_1(sK5,u1_struct_0(X0)))) )),
% 2.40/0.99    introduced(choice_axiom,[])).
% 2.40/0.99  
% 2.40/0.99  fof(f57,plain,(
% 2.40/0.99    ( ! [X0] : (? [X1] : (? [X2] : ((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => (? [X2] : ((~r1_waybel_7(X0,sK4,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),sK4),X2)) & (r1_waybel_7(X0,sK4,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),sK4),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(sK4,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(sK4,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(sK4,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(sK4))) )),
% 2.40/0.99    introduced(choice_axiom,[])).
% 2.40/0.99  
% 2.40/0.99  fof(f56,plain,(
% 2.40/0.99    ? [X0] : (? [X1] : (? [X2] : ((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~r1_waybel_7(sK3,X1,X2) | ~r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X1),X2)) & (r1_waybel_7(sK3,X1,X2) | r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X1),X2)) & m1_subset_1(X2,u1_struct_0(sK3))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK3))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK3))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK3))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK3)))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 2.40/0.99    introduced(choice_axiom,[])).
% 2.40/0.99  
% 2.40/0.99  fof(f59,plain,(
% 2.40/0.99    (((~r1_waybel_7(sK3,sK4,sK5) | ~r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK5)) & (r1_waybel_7(sK3,sK4,sK5) | r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK5)) & m1_subset_1(sK5,u1_struct_0(sK3))) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK3))))) & v13_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3))) & v2_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3))) & v1_subset_1(sK4,u1_struct_0(k3_yellow_1(k2_struct_0(sK3)))) & ~v1_xboole_0(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 2.40/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f55,f58,f57,f56])).
% 2.40/0.99  
% 2.40/0.99  fof(f87,plain,(
% 2.40/0.99    l1_pre_topc(sK3)),
% 2.40/0.99    inference(cnf_transformation,[],[f59])).
% 2.40/0.99  
% 2.40/0.99  fof(f85,plain,(
% 2.40/0.99    ~v2_struct_0(sK3)),
% 2.40/0.99    inference(cnf_transformation,[],[f59])).
% 2.40/0.99  
% 2.40/0.99  fof(f5,axiom,(
% 2.40/0.99    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.40/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/0.99  
% 2.40/0.99  fof(f23,plain,(
% 2.40/0.99    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.40/0.99    inference(ennf_transformation,[],[f5])).
% 2.40/0.99  
% 2.40/0.99  fof(f70,plain,(
% 2.40/0.99    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.40/0.99    inference(cnf_transformation,[],[f23])).
% 2.40/0.99  
% 2.40/0.99  fof(f4,axiom,(
% 2.40/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.40/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/0.99  
% 2.40/0.99  fof(f50,plain,(
% 2.40/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.40/0.99    inference(nnf_transformation,[],[f4])).
% 2.40/0.99  
% 2.40/0.99  fof(f68,plain,(
% 2.40/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.40/0.99    inference(cnf_transformation,[],[f50])).
% 2.40/0.99  
% 2.40/0.99  fof(f2,axiom,(
% 2.40/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.40/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/0.99  
% 2.40/0.99  fof(f22,plain,(
% 2.40/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.40/0.99    inference(ennf_transformation,[],[f2])).
% 2.40/0.99  
% 2.40/0.99  fof(f44,plain,(
% 2.40/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.40/0.99    inference(nnf_transformation,[],[f22])).
% 2.40/0.99  
% 2.40/0.99  fof(f45,plain,(
% 2.40/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.40/0.99    inference(rectify,[],[f44])).
% 2.40/0.99  
% 2.40/0.99  fof(f46,plain,(
% 2.40/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 2.40/0.99    introduced(choice_axiom,[])).
% 2.40/0.99  
% 2.40/0.99  fof(f47,plain,(
% 2.40/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.40/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f45,f46])).
% 2.40/0.99  
% 2.40/0.99  fof(f62,plain,(
% 2.40/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.40/0.99    inference(cnf_transformation,[],[f47])).
% 2.40/0.99  
% 2.40/0.99  fof(f74,plain,(
% 2.40/0.99    ( ! [X0] : (~v1_xboole_0(sK2(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.40/0.99    inference(cnf_transformation,[],[f52])).
% 2.40/0.99  
% 2.40/0.99  fof(f60,plain,(
% 2.40/0.99    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.40/0.99    inference(cnf_transformation,[],[f43])).
% 2.40/0.99  
% 2.40/0.99  fof(f90,plain,(
% 2.40/0.99    v2_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3)))),
% 2.40/0.99    inference(cnf_transformation,[],[f59])).
% 2.40/0.99  
% 2.40/0.99  fof(f9,axiom,(
% 2.40/0.99    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))),
% 2.40/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/0.99  
% 2.40/0.99  fof(f75,plain,(
% 2.40/0.99    ( ! [X0] : (k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))) )),
% 2.40/0.99    inference(cnf_transformation,[],[f9])).
% 2.40/0.99  
% 2.40/0.99  fof(f105,plain,(
% 2.40/0.99    v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))),
% 2.40/0.99    inference(definition_unfolding,[],[f90,f75])).
% 2.40/0.99  
% 2.40/0.99  fof(f91,plain,(
% 2.40/0.99    v13_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3)))),
% 2.40/0.99    inference(cnf_transformation,[],[f59])).
% 2.40/0.99  
% 2.40/0.99  fof(f104,plain,(
% 2.40/0.99    v13_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))),
% 2.40/0.99    inference(definition_unfolding,[],[f91,f75])).
% 2.40/0.99  
% 2.40/0.99  fof(f12,axiom,(
% 2.40/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v7_waybel_0(k3_yellow19(X0,X1,X2)) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 2.40/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/0.99  
% 2.40/0.99  fof(f18,plain,(
% 2.40/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v7_waybel_0(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 2.40/0.99    inference(pure_predicate_removal,[],[f12])).
% 2.40/0.99  
% 2.40/0.99  fof(f32,plain,(
% 2.40/0.99    ! [X0,X1,X2] : ((v7_waybel_0(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.40/0.99    inference(ennf_transformation,[],[f18])).
% 2.40/0.99  
% 2.40/0.99  fof(f33,plain,(
% 2.40/0.99    ! [X0,X1,X2] : ((v7_waybel_0(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.40/1.00    inference(flattening,[],[f32])).
% 2.40/1.00  
% 2.40/1.00  fof(f81,plain,(
% 2.40/1.00    ( ! [X2,X0,X1] : (v7_waybel_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.40/1.00    inference(cnf_transformation,[],[f33])).
% 2.40/1.00  
% 2.40/1.00  fof(f100,plain,(
% 2.40/1.00    ( ! [X2,X0,X1] : (v7_waybel_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1)))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.40/1.00    inference(definition_unfolding,[],[f81,f75,f75,f75,f75])).
% 2.40/1.00  
% 2.40/1.00  fof(f89,plain,(
% 2.40/1.00    v1_subset_1(sK4,u1_struct_0(k3_yellow_1(k2_struct_0(sK3))))),
% 2.40/1.00    inference(cnf_transformation,[],[f59])).
% 2.40/1.00  
% 2.40/1.00  fof(f106,plain,(
% 2.40/1.00    v1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))))),
% 2.40/1.00    inference(definition_unfolding,[],[f89,f75])).
% 2.40/1.00  
% 2.40/1.00  fof(f88,plain,(
% 2.40/1.00    ~v1_xboole_0(sK4)),
% 2.40/1.00    inference(cnf_transformation,[],[f59])).
% 2.40/1.00  
% 2.40/1.00  fof(f92,plain,(
% 2.40/1.00    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK3)))))),
% 2.40/1.00    inference(cnf_transformation,[],[f59])).
% 2.40/1.00  
% 2.40/1.00  fof(f103,plain,(
% 2.40/1.00    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))),
% 2.40/1.00    inference(definition_unfolding,[],[f92,f75])).
% 2.40/1.00  
% 2.40/1.00  fof(f10,axiom,(
% 2.40/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 2.40/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/1.00  
% 2.40/1.00  fof(f19,plain,(
% 2.40/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 2.40/1.00    inference(pure_predicate_removal,[],[f10])).
% 2.40/1.00  
% 2.40/1.00  fof(f28,plain,(
% 2.40/1.00    ! [X0,X1,X2] : ((l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.40/1.00    inference(ennf_transformation,[],[f19])).
% 2.40/1.00  
% 2.40/1.00  fof(f29,plain,(
% 2.40/1.00    ! [X0,X1,X2] : ((l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.40/1.00    inference(flattening,[],[f28])).
% 2.40/1.00  
% 2.40/1.00  fof(f77,plain,(
% 2.40/1.00    ( ! [X2,X0,X1] : (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.40/1.00    inference(cnf_transformation,[],[f29])).
% 2.40/1.00  
% 2.40/1.00  fof(f96,plain,(
% 2.40/1.00    ( ! [X2,X0,X1] : (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.40/1.00    inference(definition_unfolding,[],[f77,f75,f75,f75])).
% 2.40/1.00  
% 2.40/1.00  fof(f95,plain,(
% 2.40/1.00    ~r1_waybel_7(sK3,sK4,sK5) | ~r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK5)),
% 2.40/1.00    inference(cnf_transformation,[],[f59])).
% 2.40/1.00  
% 2.40/1.00  fof(f13,axiom,(
% 2.40/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,X1,X2) <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2)))))),
% 2.40/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/1.00  
% 2.40/1.00  fof(f34,plain,(
% 2.40/1.00    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.40/1.00    inference(ennf_transformation,[],[f13])).
% 2.40/1.00  
% 2.40/1.00  fof(f35,plain,(
% 2.40/1.00    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.40/1.00    inference(flattening,[],[f34])).
% 2.40/1.00  
% 2.40/1.00  fof(f53,plain,(
% 2.40/1.00    ! [X0] : (! [X1] : (! [X2] : (((r3_waybel_9(X0,X1,X2) | ~r1_waybel_7(X0,k2_yellow19(X0,X1),X2)) & (r1_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~r3_waybel_9(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.40/1.00    inference(nnf_transformation,[],[f35])).
% 2.40/1.00  
% 2.40/1.00  fof(f83,plain,(
% 2.40/1.00    ( ! [X2,X0,X1] : (r3_waybel_9(X0,X1,X2) | ~r1_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.40/1.00    inference(cnf_transformation,[],[f53])).
% 2.40/1.00  
% 2.40/1.00  fof(f86,plain,(
% 2.40/1.00    v2_pre_topc(sK3)),
% 2.40/1.00    inference(cnf_transformation,[],[f59])).
% 2.40/1.00  
% 2.40/1.00  fof(f93,plain,(
% 2.40/1.00    m1_subset_1(sK5,u1_struct_0(sK3))),
% 2.40/1.00    inference(cnf_transformation,[],[f59])).
% 2.40/1.00  
% 2.40/1.00  fof(f14,axiom,(
% 2.40/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 2.40/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/1.00  
% 2.40/1.00  fof(f36,plain,(
% 2.40/1.00    ! [X0] : (! [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.40/1.00    inference(ennf_transformation,[],[f14])).
% 2.40/1.00  
% 2.40/1.00  fof(f37,plain,(
% 2.40/1.00    ! [X0] : (! [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.40/1.00    inference(flattening,[],[f36])).
% 2.40/1.00  
% 2.40/1.00  fof(f84,plain,(
% 2.40/1.00    ( ! [X0,X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.40/1.00    inference(cnf_transformation,[],[f37])).
% 2.40/1.00  
% 2.40/1.00  fof(f102,plain,(
% 2.40/1.00    ( ! [X0,X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.40/1.00    inference(definition_unfolding,[],[f84,f75,f75,f75,f75])).
% 2.40/1.00  
% 2.40/1.00  fof(f94,plain,(
% 2.40/1.00    r1_waybel_7(sK3,sK4,sK5) | r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK5)),
% 2.40/1.00    inference(cnf_transformation,[],[f59])).
% 2.40/1.00  
% 2.40/1.00  fof(f82,plain,(
% 2.40/1.00    ( ! [X2,X0,X1] : (r1_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.40/1.00    inference(cnf_transformation,[],[f53])).
% 2.40/1.00  
% 2.40/1.00  fof(f6,axiom,(
% 2.40/1.00    ! [X0] : (l1_struct_0(X0) => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.40/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/1.00  
% 2.40/1.00  fof(f24,plain,(
% 2.40/1.00    ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0))),
% 2.40/1.00    inference(ennf_transformation,[],[f6])).
% 2.40/1.00  
% 2.40/1.00  fof(f71,plain,(
% 2.40/1.00    ( ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0)) )),
% 2.40/1.00    inference(cnf_transformation,[],[f24])).
% 2.40/1.00  
% 2.40/1.00  fof(f76,plain,(
% 2.40/1.00    ( ! [X2,X0,X1] : (~v2_struct_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.40/1.00    inference(cnf_transformation,[],[f29])).
% 2.40/1.00  
% 2.40/1.00  fof(f97,plain,(
% 2.40/1.00    ( ! [X2,X0,X1] : (~v2_struct_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.40/1.00    inference(definition_unfolding,[],[f76,f75,f75,f75])).
% 2.40/1.00  
% 2.40/1.00  fof(f11,axiom,(
% 2.40/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & v3_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 2.40/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/1.00  
% 2.40/1.00  fof(f17,plain,(
% 2.40/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 2.40/1.00    inference(pure_predicate_removal,[],[f11])).
% 2.40/1.00  
% 2.40/1.00  fof(f20,plain,(
% 2.40/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 2.40/1.00    inference(pure_predicate_removal,[],[f17])).
% 2.40/1.00  
% 2.40/1.00  fof(f30,plain,(
% 2.40/1.00    ! [X0,X1,X2] : ((v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.40/1.00    inference(ennf_transformation,[],[f20])).
% 2.40/1.00  
% 2.40/1.00  fof(f31,plain,(
% 2.40/1.00    ! [X0,X1,X2] : ((v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.40/1.00    inference(flattening,[],[f30])).
% 2.40/1.00  
% 2.40/1.00  fof(f79,plain,(
% 2.40/1.00    ( ! [X2,X0,X1] : (v4_orders_2(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.40/1.00    inference(cnf_transformation,[],[f31])).
% 2.40/1.00  
% 2.40/1.00  fof(f98,plain,(
% 2.40/1.00    ( ! [X2,X0,X1] : (v4_orders_2(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.40/1.00    inference(definition_unfolding,[],[f79,f75,f75,f75])).
% 2.40/1.00  
% 2.40/1.00  cnf(c_0,plain,
% 2.40/1.00      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 2.40/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_4686,plain,
% 2.40/1.00      ( r2_hidden(sK0(X0),X0) = iProver_top
% 2.40/1.00      | v1_xboole_0(X0) = iProver_top ),
% 2.40/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_14,plain,
% 2.40/1.00      ( m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 2.40/1.00      | v2_struct_0(X0)
% 2.40/1.00      | ~ l1_struct_0(X0) ),
% 2.40/1.00      inference(cnf_transformation,[],[f73]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_12,plain,
% 2.40/1.00      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 2.40/1.00      inference(cnf_transformation,[],[f72]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_32,negated_conjecture,
% 2.40/1.00      ( l1_pre_topc(sK3) ),
% 2.40/1.00      inference(cnf_transformation,[],[f87]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_628,plain,
% 2.40/1.00      ( l1_struct_0(X0) | sK3 != X0 ),
% 2.40/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_32]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_629,plain,
% 2.40/1.00      ( l1_struct_0(sK3) ),
% 2.40/1.00      inference(unflattening,[status(thm)],[c_628]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_1106,plain,
% 2.40/1.00      ( m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 2.40/1.00      | v2_struct_0(X0)
% 2.40/1.00      | sK3 != X0 ),
% 2.40/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_629]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_1107,plain,
% 2.40/1.00      ( m1_subset_1(sK2(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.40/1.00      | v2_struct_0(sK3) ),
% 2.40/1.00      inference(unflattening,[status(thm)],[c_1106]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_34,negated_conjecture,
% 2.40/1.00      ( ~ v2_struct_0(sK3) ),
% 2.40/1.00      inference(cnf_transformation,[],[f85]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_72,plain,
% 2.40/1.00      ( m1_subset_1(sK2(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.40/1.00      | v2_struct_0(sK3)
% 2.40/1.00      | ~ l1_struct_0(sK3) ),
% 2.40/1.00      inference(instantiation,[status(thm)],[c_14]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_78,plain,
% 2.40/1.00      ( ~ l1_pre_topc(sK3) | l1_struct_0(sK3) ),
% 2.40/1.00      inference(instantiation,[status(thm)],[c_12]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_1109,plain,
% 2.40/1.00      ( m1_subset_1(sK2(sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.40/1.00      inference(global_propositional_subsumption,
% 2.40/1.00                [status(thm)],
% 2.40/1.00                [c_1107,c_34,c_32,c_72,c_78]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_4673,plain,
% 2.40/1.00      ( m1_subset_1(sK2(sK3),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 2.40/1.00      inference(predicate_to_equality,[status(thm)],[c_1109]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_10,plain,
% 2.40/1.00      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.40/1.00      inference(cnf_transformation,[],[f70]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_1135,plain,
% 2.40/1.00      ( u1_struct_0(X0) = k2_struct_0(X0) | sK3 != X0 ),
% 2.40/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_629]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_1136,plain,
% 2.40/1.00      ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
% 2.40/1.00      inference(unflattening,[status(thm)],[c_1135]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_4703,plain,
% 2.40/1.00      ( m1_subset_1(sK2(sK3),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top ),
% 2.40/1.00      inference(light_normalisation,[status(thm)],[c_4673,c_1136]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_9,plain,
% 2.40/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.40/1.00      inference(cnf_transformation,[],[f68]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_4678,plain,
% 2.40/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.40/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 2.40/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_5153,plain,
% 2.40/1.00      ( r1_tarski(sK2(sK3),k2_struct_0(sK3)) = iProver_top ),
% 2.40/1.00      inference(superposition,[status(thm)],[c_4703,c_4678]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_4,plain,
% 2.40/1.00      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 2.40/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_4682,plain,
% 2.40/1.00      ( r1_tarski(X0,X1) != iProver_top
% 2.40/1.00      | r2_hidden(X2,X0) != iProver_top
% 2.40/1.00      | r2_hidden(X2,X1) = iProver_top ),
% 2.40/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_5705,plain,
% 2.40/1.00      ( r2_hidden(X0,sK2(sK3)) != iProver_top
% 2.40/1.00      | r2_hidden(X0,k2_struct_0(sK3)) = iProver_top ),
% 2.40/1.00      inference(superposition,[status(thm)],[c_5153,c_4682]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_6047,plain,
% 2.40/1.00      ( r2_hidden(sK0(sK2(sK3)),k2_struct_0(sK3)) = iProver_top
% 2.40/1.00      | v1_xboole_0(sK2(sK3)) = iProver_top ),
% 2.40/1.00      inference(superposition,[status(thm)],[c_4686,c_5705]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_35,plain,
% 2.40/1.00      ( v2_struct_0(sK3) != iProver_top ),
% 2.40/1.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_37,plain,
% 2.40/1.00      ( l1_pre_topc(sK3) = iProver_top ),
% 2.40/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_13,plain,
% 2.40/1.00      ( v2_struct_0(X0) | ~ l1_struct_0(X0) | ~ v1_xboole_0(sK2(X0)) ),
% 2.40/1.00      inference(cnf_transformation,[],[f74]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_74,plain,
% 2.40/1.00      ( v2_struct_0(X0) = iProver_top
% 2.40/1.00      | l1_struct_0(X0) != iProver_top
% 2.40/1.00      | v1_xboole_0(sK2(X0)) != iProver_top ),
% 2.40/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_76,plain,
% 2.40/1.00      ( v2_struct_0(sK3) = iProver_top
% 2.40/1.00      | l1_struct_0(sK3) != iProver_top
% 2.40/1.00      | v1_xboole_0(sK2(sK3)) != iProver_top ),
% 2.40/1.00      inference(instantiation,[status(thm)],[c_74]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_77,plain,
% 2.40/1.00      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 2.40/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_79,plain,
% 2.40/1.00      ( l1_pre_topc(sK3) != iProver_top
% 2.40/1.00      | l1_struct_0(sK3) = iProver_top ),
% 2.40/1.00      inference(instantiation,[status(thm)],[c_77]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_6265,plain,
% 2.40/1.00      ( r2_hidden(sK0(sK2(sK3)),k2_struct_0(sK3)) = iProver_top ),
% 2.40/1.00      inference(global_propositional_subsumption,
% 2.40/1.00                [status(thm)],
% 2.40/1.00                [c_6047,c_35,c_37,c_76,c_79]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_1,plain,
% 2.40/1.00      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.40/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_4685,plain,
% 2.40/1.00      ( r2_hidden(X0,X1) != iProver_top
% 2.40/1.00      | v1_xboole_0(X1) != iProver_top ),
% 2.40/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_6270,plain,
% 2.40/1.00      ( v1_xboole_0(k2_struct_0(sK3)) != iProver_top ),
% 2.40/1.00      inference(superposition,[status(thm)],[c_6265,c_4685]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_29,negated_conjecture,
% 2.40/1.00      ( v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) ),
% 2.40/1.00      inference(cnf_transformation,[],[f105]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_28,negated_conjecture,
% 2.40/1.00      ( v13_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) ),
% 2.40/1.00      inference(cnf_transformation,[],[f104]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_19,plain,
% 2.40/1.00      ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
% 2.40/1.00      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.40/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.40/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.40/1.00      | v7_waybel_0(k3_yellow19(X2,X1,X0))
% 2.40/1.00      | v2_struct_0(X2)
% 2.40/1.00      | ~ l1_struct_0(X2)
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | v1_xboole_0(X1) ),
% 2.40/1.00      inference(cnf_transformation,[],[f100]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_30,negated_conjecture,
% 2.40/1.00      ( v1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) ),
% 2.40/1.00      inference(cnf_transformation,[],[f106]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_456,plain,
% 2.40/1.00      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.40/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.40/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.40/1.00      | v7_waybel_0(k3_yellow19(X2,X1,X0))
% 2.40/1.00      | v2_struct_0(X2)
% 2.40/1.00      | ~ l1_struct_0(X2)
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | v1_xboole_0(X1)
% 2.40/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
% 2.40/1.00      | sK4 != X0 ),
% 2.40/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_30]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_457,plain,
% 2.40/1.00      ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 2.40/1.00      | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 2.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.40/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.40/1.00      | v7_waybel_0(k3_yellow19(X1,X0,sK4))
% 2.40/1.00      | v2_struct_0(X1)
% 2.40/1.00      | ~ l1_struct_0(X1)
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | v1_xboole_0(sK4)
% 2.40/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 2.40/1.00      inference(unflattening,[status(thm)],[c_456]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_31,negated_conjecture,
% 2.40/1.00      ( ~ v1_xboole_0(sK4) ),
% 2.40/1.00      inference(cnf_transformation,[],[f88]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_461,plain,
% 2.40/1.00      ( v1_xboole_0(X0)
% 2.40/1.00      | ~ l1_struct_0(X1)
% 2.40/1.00      | v2_struct_0(X1)
% 2.40/1.00      | v7_waybel_0(k3_yellow19(X1,X0,sK4))
% 2.40/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.40/1.00      | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 2.40/1.00      | ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 2.40/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 2.40/1.00      inference(global_propositional_subsumption,
% 2.40/1.00                [status(thm)],
% 2.40/1.00                [c_457,c_31]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_462,plain,
% 2.40/1.00      ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 2.40/1.00      | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 2.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.40/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.40/1.00      | v7_waybel_0(k3_yellow19(X1,X0,sK4))
% 2.40/1.00      | v2_struct_0(X1)
% 2.40/1.00      | ~ l1_struct_0(X1)
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 2.40/1.00      inference(renaming,[status(thm)],[c_461]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_1206,plain,
% 2.40/1.00      ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 2.40/1.00      | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 2.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.40/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.40/1.00      | v7_waybel_0(k3_yellow19(X1,X0,sK4))
% 2.40/1.00      | v2_struct_0(X1)
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 2.40/1.00      | sK3 != X1 ),
% 2.40/1.00      inference(resolution_lifted,[status(thm)],[c_462,c_629]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_1207,plain,
% 2.40/1.00      ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 2.40/1.00      | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 2.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.40/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.40/1.00      | v7_waybel_0(k3_yellow19(sK3,X0,sK4))
% 2.40/1.00      | v2_struct_0(sK3)
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 2.40/1.00      inference(unflattening,[status(thm)],[c_1206]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_1211,plain,
% 2.40/1.00      ( v7_waybel_0(k3_yellow19(sK3,X0,sK4))
% 2.40/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.40/1.00      | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 2.40/1.00      | ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 2.40/1.00      inference(global_propositional_subsumption,
% 2.40/1.00                [status(thm)],
% 2.40/1.00                [c_1207,c_34]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_1212,plain,
% 2.40/1.00      ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 2.40/1.00      | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 2.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.40/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.40/1.00      | v7_waybel_0(k3_yellow19(sK3,X0,sK4))
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 2.40/1.00      inference(renaming,[status(thm)],[c_1211]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_1658,plain,
% 2.40/1.00      ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 2.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.40/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.40/1.00      | v7_waybel_0(k3_yellow19(sK3,X0,sK4))
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
% 2.40/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 2.40/1.00      | sK4 != sK4 ),
% 2.40/1.00      inference(resolution_lifted,[status(thm)],[c_28,c_1212]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_1936,plain,
% 2.40/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.40/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.40/1.00      | v7_waybel_0(k3_yellow19(sK3,X0,sK4))
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
% 2.40/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 2.40/1.00      | sK4 != sK4 ),
% 2.40/1.00      inference(resolution_lifted,[status(thm)],[c_29,c_1658]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_3019,plain,
% 2.40/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.40/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.40/1.00      | v7_waybel_0(k3_yellow19(sK3,X0,sK4))
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
% 2.40/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 2.40/1.00      inference(equality_resolution_simp,[status(thm)],[c_1936]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_4664,plain,
% 2.40/1.00      ( k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
% 2.40/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 2.40/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.40/1.00      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
% 2.40/1.00      | v7_waybel_0(k3_yellow19(sK3,X0,sK4)) = iProver_top
% 2.40/1.00      | v1_xboole_0(X0) = iProver_top ),
% 2.40/1.00      inference(predicate_to_equality,[status(thm)],[c_3019]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_4793,plain,
% 2.40/1.00      ( k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
% 2.40/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 2.40/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.40/1.00      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
% 2.40/1.00      | v7_waybel_0(k3_yellow19(sK3,X0,sK4)) = iProver_top
% 2.40/1.00      | v1_xboole_0(X0) = iProver_top ),
% 2.40/1.00      inference(light_normalisation,[status(thm)],[c_4664,c_1136]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_5426,plain,
% 2.40/1.00      ( k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(k2_struct_0(sK3)))
% 2.40/1.00      | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.40/1.00      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))))) != iProver_top
% 2.40/1.00      | v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) = iProver_top
% 2.40/1.00      | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
% 2.40/1.00      inference(equality_resolution,[status(thm)],[c_4793]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_5934,plain,
% 2.40/1.00      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.40/1.00      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))))) != iProver_top
% 2.40/1.00      | v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) = iProver_top
% 2.40/1.00      | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
% 2.40/1.00      inference(equality_resolution_simp,[status(thm)],[c_5426]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_27,negated_conjecture,
% 2.40/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))))) ),
% 2.40/1.00      inference(cnf_transformation,[],[f103]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_42,plain,
% 2.40/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))))) = iProver_top ),
% 2.40/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_15,plain,
% 2.40/1.00      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.40/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.40/1.00      | l1_waybel_0(k3_yellow19(X2,X1,X0),X2)
% 2.40/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.40/1.00      | v2_struct_0(X2)
% 2.40/1.00      | ~ l1_struct_0(X2)
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | v1_xboole_0(X1) ),
% 2.40/1.00      inference(cnf_transformation,[],[f96]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_24,negated_conjecture,
% 2.40/1.00      ( ~ r1_waybel_7(sK3,sK4,sK5)
% 2.40/1.00      | ~ r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK5) ),
% 2.40/1.00      inference(cnf_transformation,[],[f95]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_264,plain,
% 2.40/1.00      ( ~ r1_waybel_7(sK3,sK4,sK5)
% 2.40/1.00      | ~ r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK5) ),
% 2.40/1.00      inference(prop_impl,[status(thm)],[c_24]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_21,plain,
% 2.40/1.00      ( ~ r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 2.40/1.00      | r3_waybel_9(X0,X1,X2)
% 2.40/1.00      | ~ l1_waybel_0(X1,X0)
% 2.40/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.40/1.00      | ~ v2_pre_topc(X0)
% 2.40/1.00      | ~ v7_waybel_0(X1)
% 2.40/1.00      | ~ v4_orders_2(X1)
% 2.40/1.00      | v2_struct_0(X0)
% 2.40/1.00      | v2_struct_0(X1)
% 2.40/1.00      | ~ l1_pre_topc(X0) ),
% 2.40/1.00      inference(cnf_transformation,[],[f83]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_33,negated_conjecture,
% 2.40/1.00      ( v2_pre_topc(sK3) ),
% 2.40/1.00      inference(cnf_transformation,[],[f86]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_579,plain,
% 2.40/1.00      ( ~ r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 2.40/1.00      | r3_waybel_9(X0,X1,X2)
% 2.40/1.00      | ~ l1_waybel_0(X1,X0)
% 2.40/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.40/1.00      | ~ v7_waybel_0(X1)
% 2.40/1.00      | ~ v4_orders_2(X1)
% 2.40/1.00      | v2_struct_0(X0)
% 2.40/1.00      | v2_struct_0(X1)
% 2.40/1.00      | ~ l1_pre_topc(X0)
% 2.40/1.00      | sK3 != X0 ),
% 2.40/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_33]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_580,plain,
% 2.40/1.00      ( ~ r1_waybel_7(sK3,k2_yellow19(sK3,X0),X1)
% 2.40/1.00      | r3_waybel_9(sK3,X0,X1)
% 2.40/1.00      | ~ l1_waybel_0(X0,sK3)
% 2.40/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.40/1.00      | ~ v7_waybel_0(X0)
% 2.40/1.00      | ~ v4_orders_2(X0)
% 2.40/1.00      | v2_struct_0(X0)
% 2.40/1.00      | v2_struct_0(sK3)
% 2.40/1.00      | ~ l1_pre_topc(sK3) ),
% 2.40/1.00      inference(unflattening,[status(thm)],[c_579]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_584,plain,
% 2.40/1.00      ( ~ r1_waybel_7(sK3,k2_yellow19(sK3,X0),X1)
% 2.40/1.00      | r3_waybel_9(sK3,X0,X1)
% 2.40/1.00      | ~ l1_waybel_0(X0,sK3)
% 2.40/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.40/1.00      | ~ v7_waybel_0(X0)
% 2.40/1.00      | ~ v4_orders_2(X0)
% 2.40/1.00      | v2_struct_0(X0) ),
% 2.40/1.00      inference(global_propositional_subsumption,
% 2.40/1.00                [status(thm)],
% 2.40/1.00                [c_580,c_34,c_32]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_957,plain,
% 2.40/1.00      ( ~ r1_waybel_7(sK3,k2_yellow19(sK3,X0),X1)
% 2.40/1.00      | ~ r1_waybel_7(sK3,sK4,sK5)
% 2.40/1.00      | ~ l1_waybel_0(X0,sK3)
% 2.40/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.40/1.00      | ~ v7_waybel_0(X0)
% 2.40/1.00      | ~ v4_orders_2(X0)
% 2.40/1.00      | v2_struct_0(X0)
% 2.40/1.00      | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != X0
% 2.40/1.00      | sK5 != X1
% 2.40/1.00      | sK3 != sK3 ),
% 2.40/1.00      inference(resolution_lifted,[status(thm)],[c_264,c_584]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_958,plain,
% 2.40/1.00      ( ~ r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
% 2.40/1.00      | ~ r1_waybel_7(sK3,sK4,sK5)
% 2.40/1.00      | ~ l1_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK3)
% 2.40/1.00      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 2.40/1.00      | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.40/1.00      | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.40/1.00      | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) ),
% 2.40/1.00      inference(unflattening,[status(thm)],[c_957]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_26,negated_conjecture,
% 2.40/1.00      ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 2.40/1.00      inference(cnf_transformation,[],[f93]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_960,plain,
% 2.40/1.00      ( ~ l1_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK3)
% 2.40/1.00      | ~ r1_waybel_7(sK3,sK4,sK5)
% 2.40/1.00      | ~ r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
% 2.40/1.00      | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.40/1.00      | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.40/1.00      | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) ),
% 2.40/1.00      inference(global_propositional_subsumption,
% 2.40/1.00                [status(thm)],
% 2.40/1.00                [c_958,c_26]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_961,plain,
% 2.40/1.00      ( ~ r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
% 2.40/1.00      | ~ r1_waybel_7(sK3,sK4,sK5)
% 2.40/1.00      | ~ l1_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK3)
% 2.40/1.00      | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.40/1.00      | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.40/1.00      | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) ),
% 2.40/1.00      inference(renaming,[status(thm)],[c_960]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_997,plain,
% 2.40/1.00      ( ~ r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
% 2.40/1.00      | ~ r1_waybel_7(sK3,sK4,sK5)
% 2.40/1.00      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.40/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.40/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.40/1.00      | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.40/1.00      | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.40/1.00      | v2_struct_0(X2)
% 2.40/1.00      | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.40/1.00      | ~ l1_struct_0(X2)
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | v1_xboole_0(X1)
% 2.40/1.00      | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(X2,X1,X0)
% 2.40/1.00      | sK3 != X2 ),
% 2.40/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_961]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_998,plain,
% 2.40/1.00      ( ~ r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
% 2.40/1.00      | ~ r1_waybel_7(sK3,sK4,sK5)
% 2.40/1.00      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.40/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.40/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.40/1.00      | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.40/1.00      | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.40/1.00      | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.40/1.00      | v2_struct_0(sK3)
% 2.40/1.00      | ~ l1_struct_0(sK3)
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | v1_xboole_0(X1)
% 2.40/1.00      | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(sK3,X1,X0) ),
% 2.40/1.00      inference(unflattening,[status(thm)],[c_997]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_1002,plain,
% 2.40/1.00      ( ~ r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
% 2.40/1.00      | ~ r1_waybel_7(sK3,sK4,sK5)
% 2.40/1.00      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.40/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.40/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.40/1.00      | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.40/1.00      | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.40/1.00      | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | v1_xboole_0(X1)
% 2.40/1.00      | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(sK3,X1,X0) ),
% 2.40/1.00      inference(global_propositional_subsumption,
% 2.40/1.00                [status(thm)],
% 2.40/1.00                [c_998,c_34,c_32,c_78]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_1613,plain,
% 2.40/1.00      ( ~ r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
% 2.40/1.00      | ~ r1_waybel_7(sK3,sK4,sK5)
% 2.40/1.00      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.40/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.40/1.00      | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.40/1.00      | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.40/1.00      | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | v1_xboole_0(X1)
% 2.40/1.00      | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(sK3,X1,X0)
% 2.40/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X1))
% 2.40/1.00      | sK4 != X0 ),
% 2.40/1.00      inference(resolution_lifted,[status(thm)],[c_1002,c_28]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_1614,plain,
% 2.40/1.00      ( ~ r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
% 2.40/1.00      | ~ r1_waybel_7(sK3,sK4,sK5)
% 2.40/1.00      | ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 2.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.40/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.40/1.00      | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.40/1.00      | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.40/1.00      | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | v1_xboole_0(sK4)
% 2.40/1.00      | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(sK3,X0,sK4)
% 2.40/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.40/1.00      inference(unflattening,[status(thm)],[c_1613]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_1618,plain,
% 2.40/1.00      ( v1_xboole_0(X0)
% 2.40/1.00      | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.40/1.00      | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.40/1.00      | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.40/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.40/1.00      | ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 2.40/1.00      | ~ r1_waybel_7(sK3,sK4,sK5)
% 2.40/1.00      | ~ r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
% 2.40/1.00      | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(sK3,X0,sK4)
% 2.40/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.40/1.00      inference(global_propositional_subsumption,
% 2.40/1.00                [status(thm)],
% 2.40/1.00                [c_1614,c_31]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_1619,plain,
% 2.40/1.00      ( ~ r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
% 2.40/1.00      | ~ r1_waybel_7(sK3,sK4,sK5)
% 2.40/1.00      | ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 2.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.40/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.40/1.00      | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.40/1.00      | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.40/1.00      | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(sK3,X0,sK4)
% 2.40/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.40/1.00      inference(renaming,[status(thm)],[c_1618]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_1962,plain,
% 2.40/1.00      ( ~ r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
% 2.40/1.00      | ~ r1_waybel_7(sK3,sK4,sK5)
% 2.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.40/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.40/1.00      | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.40/1.00      | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.40/1.00      | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(sK3,X0,sK4)
% 2.40/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
% 2.40/1.00      | sK4 != sK4 ),
% 2.40/1.00      inference(resolution_lifted,[status(thm)],[c_29,c_1619]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_3015,plain,
% 2.40/1.00      ( ~ r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
% 2.40/1.00      | ~ r1_waybel_7(sK3,sK4,sK5)
% 2.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.40/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.40/1.00      | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.40/1.00      | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.40/1.00      | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(sK3,X0,sK4)
% 2.40/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.40/1.00      inference(equality_resolution_simp,[status(thm)],[c_1962]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_4052,plain,
% 2.40/1.00      ( ~ r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
% 2.40/1.00      | ~ r1_waybel_7(sK3,sK4,sK5)
% 2.40/1.00      | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.40/1.00      | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.40/1.00      | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.40/1.00      | sP0_iProver_split ),
% 2.40/1.00      inference(splitting,
% 2.40/1.00                [splitting(split),new_symbols(definition,[])],
% 2.40/1.00                [c_3015]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_4665,plain,
% 2.40/1.00      ( r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5) != iProver_top
% 2.40/1.00      | r1_waybel_7(sK3,sK4,sK5) != iProver_top
% 2.40/1.00      | v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != iProver_top
% 2.40/1.00      | v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != iProver_top
% 2.40/1.00      | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) = iProver_top
% 2.40/1.00      | sP0_iProver_split = iProver_top ),
% 2.40/1.00      inference(predicate_to_equality,[status(thm)],[c_4052]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_23,plain,
% 2.40/1.00      ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))
% 2.40/1.00      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 2.40/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 2.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
% 2.40/1.00      | v2_struct_0(X1)
% 2.40/1.00      | ~ l1_struct_0(X1)
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0 ),
% 2.40/1.00      inference(cnf_transformation,[],[f102]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_495,plain,
% 2.40/1.00      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 2.40/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 2.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
% 2.40/1.00      | v2_struct_0(X1)
% 2.40/1.00      | ~ l1_struct_0(X1)
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0
% 2.40/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
% 2.40/1.00      | sK4 != X0 ),
% 2.40/1.00      inference(resolution_lifted,[status(thm)],[c_23,c_30]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_496,plain,
% 2.40/1.00      ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 2.40/1.00      | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 2.40/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 2.40/1.00      | v2_struct_0(X0)
% 2.40/1.00      | ~ l1_struct_0(X0)
% 2.40/1.00      | v1_xboole_0(sK4)
% 2.40/1.00      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK4)) = sK4
% 2.40/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) ),
% 2.40/1.00      inference(unflattening,[status(thm)],[c_495]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_500,plain,
% 2.40/1.00      ( ~ l1_struct_0(X0)
% 2.40/1.00      | v2_struct_0(X0)
% 2.40/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 2.40/1.00      | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 2.40/1.00      | ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 2.40/1.00      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK4)) = sK4
% 2.40/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) ),
% 2.40/1.00      inference(global_propositional_subsumption,
% 2.40/1.00                [status(thm)],
% 2.40/1.00                [c_496,c_31]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_501,plain,
% 2.40/1.00      ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 2.40/1.00      | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 2.40/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 2.40/1.00      | v2_struct_0(X0)
% 2.40/1.00      | ~ l1_struct_0(X0)
% 2.40/1.00      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK4)) = sK4
% 2.40/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) ),
% 2.40/1.00      inference(renaming,[status(thm)],[c_500]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_1095,plain,
% 2.40/1.00      ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 2.40/1.00      | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 2.40/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 2.40/1.00      | v2_struct_0(X0)
% 2.40/1.00      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK4)) = sK4
% 2.40/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
% 2.40/1.00      | sK3 != X0 ),
% 2.40/1.00      inference(resolution_lifted,[status(thm)],[c_501,c_629]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_1096,plain,
% 2.40/1.00      ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
% 2.40/1.00      | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
% 2.40/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))
% 2.40/1.00      | v2_struct_0(sK3)
% 2.40/1.00      | k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) = sK4
% 2.40/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) ),
% 2.40/1.00      inference(unflattening,[status(thm)],[c_1095]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_1098,plain,
% 2.40/1.00      ( k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) = sK4
% 2.40/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) ),
% 2.40/1.00      inference(global_propositional_subsumption,
% 2.40/1.00                [status(thm)],
% 2.40/1.00                [c_1096,c_34,c_29,c_28,c_27]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_3026,plain,
% 2.40/1.00      ( k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) = sK4 ),
% 2.40/1.00      inference(equality_resolution_simp,[status(thm)],[c_1098]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_4806,plain,
% 2.40/1.00      ( r1_waybel_7(sK3,sK4,sK5) != iProver_top
% 2.40/1.00      | v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != iProver_top
% 2.40/1.00      | v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != iProver_top
% 2.40/1.00      | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) = iProver_top
% 2.40/1.00      | sP0_iProver_split = iProver_top ),
% 2.40/1.00      inference(light_normalisation,[status(thm)],[c_4665,c_3026]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_25,negated_conjecture,
% 2.40/1.00      ( r1_waybel_7(sK3,sK4,sK5)
% 2.40/1.00      | r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK5) ),
% 2.40/1.00      inference(cnf_transformation,[],[f94]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_266,plain,
% 2.40/1.00      ( r1_waybel_7(sK3,sK4,sK5)
% 2.40/1.00      | r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK5) ),
% 2.40/1.00      inference(prop_impl,[status(thm)],[c_25]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_22,plain,
% 2.40/1.00      ( r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 2.40/1.00      | ~ r3_waybel_9(X0,X1,X2)
% 2.40/1.00      | ~ l1_waybel_0(X1,X0)
% 2.40/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.40/1.00      | ~ v2_pre_topc(X0)
% 2.40/1.00      | ~ v7_waybel_0(X1)
% 2.40/1.00      | ~ v4_orders_2(X1)
% 2.40/1.00      | v2_struct_0(X0)
% 2.40/1.00      | v2_struct_0(X1)
% 2.40/1.00      | ~ l1_pre_topc(X0) ),
% 2.40/1.00      inference(cnf_transformation,[],[f82]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_546,plain,
% 2.40/1.00      ( r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 2.40/1.00      | ~ r3_waybel_9(X0,X1,X2)
% 2.40/1.00      | ~ l1_waybel_0(X1,X0)
% 2.40/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.40/1.00      | ~ v7_waybel_0(X1)
% 2.40/1.00      | ~ v4_orders_2(X1)
% 2.40/1.00      | v2_struct_0(X0)
% 2.40/1.00      | v2_struct_0(X1)
% 2.40/1.00      | ~ l1_pre_topc(X0)
% 2.40/1.00      | sK3 != X0 ),
% 2.40/1.00      inference(resolution_lifted,[status(thm)],[c_22,c_33]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_547,plain,
% 2.40/1.00      ( r1_waybel_7(sK3,k2_yellow19(sK3,X0),X1)
% 2.40/1.00      | ~ r3_waybel_9(sK3,X0,X1)
% 2.40/1.00      | ~ l1_waybel_0(X0,sK3)
% 2.40/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.40/1.00      | ~ v7_waybel_0(X0)
% 2.40/1.00      | ~ v4_orders_2(X0)
% 2.40/1.00      | v2_struct_0(X0)
% 2.40/1.00      | v2_struct_0(sK3)
% 2.40/1.00      | ~ l1_pre_topc(sK3) ),
% 2.40/1.00      inference(unflattening,[status(thm)],[c_546]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_551,plain,
% 2.40/1.00      ( r1_waybel_7(sK3,k2_yellow19(sK3,X0),X1)
% 2.40/1.00      | ~ r3_waybel_9(sK3,X0,X1)
% 2.40/1.00      | ~ l1_waybel_0(X0,sK3)
% 2.40/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.40/1.00      | ~ v7_waybel_0(X0)
% 2.40/1.00      | ~ v4_orders_2(X0)
% 2.40/1.00      | v2_struct_0(X0) ),
% 2.40/1.00      inference(global_propositional_subsumption,
% 2.40/1.00                [status(thm)],
% 2.40/1.00                [c_547,c_34,c_32]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_931,plain,
% 2.40/1.00      ( r1_waybel_7(sK3,k2_yellow19(sK3,X0),X1)
% 2.40/1.00      | r1_waybel_7(sK3,sK4,sK5)
% 2.40/1.00      | ~ l1_waybel_0(X0,sK3)
% 2.40/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.40/1.00      | ~ v7_waybel_0(X0)
% 2.40/1.00      | ~ v4_orders_2(X0)
% 2.40/1.00      | v2_struct_0(X0)
% 2.40/1.00      | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != X0
% 2.40/1.00      | sK5 != X1
% 2.40/1.00      | sK3 != sK3 ),
% 2.40/1.00      inference(resolution_lifted,[status(thm)],[c_266,c_551]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_932,plain,
% 2.40/1.00      ( r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
% 2.40/1.00      | r1_waybel_7(sK3,sK4,sK5)
% 2.40/1.00      | ~ l1_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK3)
% 2.40/1.00      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 2.40/1.00      | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.40/1.00      | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.40/1.00      | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) ),
% 2.40/1.00      inference(unflattening,[status(thm)],[c_931]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_934,plain,
% 2.40/1.00      ( ~ l1_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK3)
% 2.40/1.00      | r1_waybel_7(sK3,sK4,sK5)
% 2.40/1.00      | r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
% 2.40/1.00      | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.40/1.00      | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.40/1.00      | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) ),
% 2.40/1.00      inference(global_propositional_subsumption,
% 2.40/1.00                [status(thm)],
% 2.40/1.00                [c_932,c_26]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_935,plain,
% 2.40/1.00      ( r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
% 2.40/1.00      | r1_waybel_7(sK3,sK4,sK5)
% 2.40/1.00      | ~ l1_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK3)
% 2.40/1.00      | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.40/1.00      | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.40/1.00      | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) ),
% 2.40/1.00      inference(renaming,[status(thm)],[c_934]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_1045,plain,
% 2.40/1.00      ( r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
% 2.40/1.00      | r1_waybel_7(sK3,sK4,sK5)
% 2.40/1.00      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.40/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.40/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.40/1.00      | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.40/1.00      | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.40/1.00      | v2_struct_0(X2)
% 2.40/1.00      | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.40/1.00      | ~ l1_struct_0(X2)
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | v1_xboole_0(X1)
% 2.40/1.00      | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(X2,X1,X0)
% 2.40/1.00      | sK3 != X2 ),
% 2.40/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_935]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_1046,plain,
% 2.40/1.00      ( r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
% 2.40/1.00      | r1_waybel_7(sK3,sK4,sK5)
% 2.40/1.00      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.40/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.40/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.40/1.00      | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.40/1.00      | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.40/1.00      | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.40/1.00      | v2_struct_0(sK3)
% 2.40/1.00      | ~ l1_struct_0(sK3)
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | v1_xboole_0(X1)
% 2.40/1.00      | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(sK3,X1,X0) ),
% 2.40/1.00      inference(unflattening,[status(thm)],[c_1045]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_1050,plain,
% 2.40/1.00      ( r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
% 2.40/1.00      | r1_waybel_7(sK3,sK4,sK5)
% 2.40/1.00      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.40/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.40/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.40/1.00      | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.40/1.00      | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.40/1.00      | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | v1_xboole_0(X1)
% 2.40/1.00      | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(sK3,X1,X0) ),
% 2.40/1.00      inference(global_propositional_subsumption,
% 2.40/1.00                [status(thm)],
% 2.40/1.00                [c_1046,c_34,c_32,c_78]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_1568,plain,
% 2.40/1.00      ( r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
% 2.40/1.00      | r1_waybel_7(sK3,sK4,sK5)
% 2.40/1.00      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.40/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.40/1.00      | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.40/1.00      | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.40/1.00      | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | v1_xboole_0(X1)
% 2.40/1.00      | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(sK3,X1,X0)
% 2.40/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X1))
% 2.40/1.00      | sK4 != X0 ),
% 2.40/1.00      inference(resolution_lifted,[status(thm)],[c_1050,c_28]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_1569,plain,
% 2.40/1.00      ( r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
% 2.40/1.00      | r1_waybel_7(sK3,sK4,sK5)
% 2.40/1.00      | ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 2.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.40/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.40/1.00      | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.40/1.00      | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.40/1.00      | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | v1_xboole_0(sK4)
% 2.40/1.00      | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(sK3,X0,sK4)
% 2.40/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.40/1.00      inference(unflattening,[status(thm)],[c_1568]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_1573,plain,
% 2.40/1.00      ( v1_xboole_0(X0)
% 2.40/1.00      | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.40/1.00      | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.40/1.00      | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.40/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.40/1.00      | ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 2.40/1.00      | r1_waybel_7(sK3,sK4,sK5)
% 2.40/1.00      | r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
% 2.40/1.00      | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(sK3,X0,sK4)
% 2.40/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.40/1.00      inference(global_propositional_subsumption,
% 2.40/1.00                [status(thm)],
% 2.40/1.00                [c_1569,c_31]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_1574,plain,
% 2.40/1.00      ( r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
% 2.40/1.00      | r1_waybel_7(sK3,sK4,sK5)
% 2.40/1.00      | ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 2.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.40/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.40/1.00      | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.40/1.00      | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.40/1.00      | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(sK3,X0,sK4)
% 2.40/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.40/1.00      inference(renaming,[status(thm)],[c_1573]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_2000,plain,
% 2.40/1.00      ( r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
% 2.40/1.00      | r1_waybel_7(sK3,sK4,sK5)
% 2.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.40/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.40/1.00      | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.40/1.00      | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.40/1.00      | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(sK3,X0,sK4)
% 2.40/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
% 2.40/1.00      | sK4 != sK4 ),
% 2.40/1.00      inference(resolution_lifted,[status(thm)],[c_29,c_1574]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_3011,plain,
% 2.40/1.00      ( r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
% 2.40/1.00      | r1_waybel_7(sK3,sK4,sK5)
% 2.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.40/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.40/1.00      | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.40/1.00      | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.40/1.00      | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(sK3,X0,sK4)
% 2.40/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.40/1.00      inference(equality_resolution_simp,[status(thm)],[c_2000]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_4053,plain,
% 2.40/1.00      ( r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
% 2.40/1.00      | r1_waybel_7(sK3,sK4,sK5)
% 2.40/1.00      | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.40/1.00      | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.40/1.00      | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
% 2.40/1.00      | sP0_iProver_split ),
% 2.40/1.00      inference(splitting,
% 2.40/1.00                [splitting(split),new_symbols(definition,[])],
% 2.40/1.00                [c_3011]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_4667,plain,
% 2.40/1.00      ( r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5) = iProver_top
% 2.40/1.00      | r1_waybel_7(sK3,sK4,sK5) = iProver_top
% 2.40/1.00      | v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != iProver_top
% 2.40/1.00      | v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != iProver_top
% 2.40/1.00      | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) = iProver_top
% 2.40/1.00      | sP0_iProver_split = iProver_top ),
% 2.40/1.00      inference(predicate_to_equality,[status(thm)],[c_4053]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_4782,plain,
% 2.40/1.00      ( r1_waybel_7(sK3,sK4,sK5) = iProver_top
% 2.40/1.00      | v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != iProver_top
% 2.40/1.00      | v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != iProver_top
% 2.40/1.00      | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) = iProver_top
% 2.40/1.00      | sP0_iProver_split = iProver_top ),
% 2.40/1.00      inference(light_normalisation,[status(thm)],[c_4667,c_3026]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_4812,plain,
% 2.40/1.00      ( v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != iProver_top
% 2.40/1.00      | v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != iProver_top
% 2.40/1.00      | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) = iProver_top
% 2.40/1.00      | sP0_iProver_split = iProver_top ),
% 2.40/1.00      inference(forward_subsumption_resolution,
% 2.40/1.00                [status(thm)],
% 2.40/1.00                [c_4806,c_4782]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_11,plain,
% 2.40/1.00      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 2.40/1.00      | ~ l1_struct_0(X0) ),
% 2.40/1.00      inference(cnf_transformation,[],[f71]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_1128,plain,
% 2.40/1.00      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 2.40/1.00      | sK3 != X0 ),
% 2.40/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_629]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_1129,plain,
% 2.40/1.00      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.40/1.00      inference(unflattening,[status(thm)],[c_1128]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_4671,plain,
% 2.40/1.00      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 2.40/1.00      inference(predicate_to_equality,[status(thm)],[c_1129]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_4700,plain,
% 2.40/1.00      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top ),
% 2.40/1.00      inference(light_normalisation,[status(thm)],[c_4671,c_1136]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_16,plain,
% 2.40/1.00      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.40/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.40/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.40/1.00      | v2_struct_0(X2)
% 2.40/1.00      | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
% 2.40/1.00      | ~ l1_struct_0(X2)
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | v1_xboole_0(X1) ),
% 2.40/1.00      inference(cnf_transformation,[],[f97]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_1173,plain,
% 2.40/1.00      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.40/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.40/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.40/1.00      | v2_struct_0(X2)
% 2.40/1.00      | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | v1_xboole_0(X1)
% 2.40/1.00      | sK3 != X2 ),
% 2.40/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_629]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_1174,plain,
% 2.40/1.00      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.40/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.40/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.40/1.00      | ~ v2_struct_0(k3_yellow19(sK3,X1,X0))
% 2.40/1.00      | v2_struct_0(sK3)
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | v1_xboole_0(X1) ),
% 2.40/1.00      inference(unflattening,[status(thm)],[c_1173]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_1178,plain,
% 2.40/1.00      ( ~ v2_struct_0(k3_yellow19(sK3,X1,X0))
% 2.40/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.40/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.40/1.00      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | v1_xboole_0(X1) ),
% 2.40/1.00      inference(global_propositional_subsumption,
% 2.40/1.00                [status(thm)],
% 2.40/1.00                [c_1174,c_34]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_1179,plain,
% 2.40/1.00      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.40/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.40/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.40/1.00      | ~ v2_struct_0(k3_yellow19(sK3,X1,X0))
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | v1_xboole_0(X1) ),
% 2.40/1.00      inference(renaming,[status(thm)],[c_1178]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_1508,plain,
% 2.40/1.00      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.40/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.40/1.00      | ~ v2_struct_0(k3_yellow19(sK3,X1,X0))
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | v1_xboole_0(X1)
% 2.40/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X1))
% 2.40/1.00      | sK4 != X0 ),
% 2.40/1.00      inference(resolution_lifted,[status(thm)],[c_1179,c_28]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_1509,plain,
% 2.40/1.00      ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 2.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.40/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.40/1.00      | ~ v2_struct_0(k3_yellow19(sK3,X0,sK4))
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | v1_xboole_0(sK4)
% 2.40/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.40/1.00      inference(unflattening,[status(thm)],[c_1508]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_1513,plain,
% 2.40/1.00      ( v1_xboole_0(X0)
% 2.40/1.00      | ~ v2_struct_0(k3_yellow19(sK3,X0,sK4))
% 2.40/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.40/1.00      | ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 2.40/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.40/1.00      inference(global_propositional_subsumption,
% 2.40/1.00                [status(thm)],
% 2.40/1.00                [c_1509,c_31]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_1514,plain,
% 2.40/1.00      ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 2.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.40/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.40/1.00      | ~ v2_struct_0(k3_yellow19(sK3,X0,sK4))
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.40/1.00      inference(renaming,[status(thm)],[c_1513]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_2061,plain,
% 2.40/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.40/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.40/1.00      | ~ v2_struct_0(k3_yellow19(sK3,X0,sK4))
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
% 2.40/1.00      | sK4 != sK4 ),
% 2.40/1.00      inference(resolution_lifted,[status(thm)],[c_29,c_1514]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_3003,plain,
% 2.40/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.40/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.40/1.00      | ~ v2_struct_0(k3_yellow19(sK3,X0,sK4))
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.40/1.00      inference(equality_resolution_simp,[status(thm)],[c_2061]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_4670,plain,
% 2.40/1.00      ( k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
% 2.40/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.40/1.00      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
% 2.40/1.00      | v2_struct_0(k3_yellow19(sK3,X0,sK4)) != iProver_top
% 2.40/1.00      | v1_xboole_0(X0) = iProver_top ),
% 2.40/1.00      inference(predicate_to_equality,[status(thm)],[c_3003]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_4757,plain,
% 2.40/1.00      ( k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
% 2.40/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.40/1.00      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
% 2.40/1.00      | v2_struct_0(k3_yellow19(sK3,X0,sK4)) != iProver_top
% 2.40/1.00      | v1_xboole_0(X0) = iProver_top ),
% 2.40/1.00      inference(light_normalisation,[status(thm)],[c_4670,c_1136]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_5260,plain,
% 2.40/1.00      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.40/1.00      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))))) != iProver_top
% 2.40/1.00      | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != iProver_top
% 2.40/1.00      | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
% 2.40/1.00      inference(equality_resolution,[status(thm)],[c_4757]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_5508,plain,
% 2.40/1.00      ( v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != iProver_top
% 2.40/1.00      | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
% 2.40/1.00      inference(global_propositional_subsumption,
% 2.40/1.00                [status(thm)],
% 2.40/1.00                [c_5260,c_42,c_4700]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_4051,plain,
% 2.40/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.40/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(sK3,X0,sK4)
% 2.40/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
% 2.40/1.00      | ~ sP0_iProver_split ),
% 2.40/1.00      inference(splitting,
% 2.40/1.00                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.40/1.00                [c_3015]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_4666,plain,
% 2.40/1.00      ( k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(sK3,X0,sK4)
% 2.40/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
% 2.40/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.40/1.00      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
% 2.40/1.00      | v1_xboole_0(X0) = iProver_top
% 2.40/1.00      | sP0_iProver_split != iProver_top ),
% 2.40/1.00      inference(predicate_to_equality,[status(thm)],[c_4051]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_4768,plain,
% 2.40/1.00      ( k3_yellow19(sK3,k2_struct_0(sK3),sK4) != k3_yellow19(sK3,X0,sK4)
% 2.40/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
% 2.40/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.40/1.00      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
% 2.40/1.00      | v1_xboole_0(X0) = iProver_top
% 2.40/1.00      | sP0_iProver_split != iProver_top ),
% 2.40/1.00      inference(light_normalisation,[status(thm)],[c_4666,c_1136]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_5269,plain,
% 2.40/1.00      ( k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(k2_struct_0(sK3)))
% 2.40/1.00      | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.40/1.00      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))))) != iProver_top
% 2.40/1.00      | v1_xboole_0(k2_struct_0(sK3)) = iProver_top
% 2.40/1.00      | sP0_iProver_split != iProver_top ),
% 2.40/1.00      inference(equality_resolution,[status(thm)],[c_4768]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_5589,plain,
% 2.40/1.00      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.40/1.00      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))))) != iProver_top
% 2.40/1.00      | v1_xboole_0(k2_struct_0(sK3)) = iProver_top
% 2.40/1.00      | sP0_iProver_split != iProver_top ),
% 2.40/1.00      inference(equality_resolution_simp,[status(thm)],[c_5269]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_5591,plain,
% 2.40/1.00      ( v1_xboole_0(k2_struct_0(sK3)) = iProver_top
% 2.40/1.00      | sP0_iProver_split != iProver_top ),
% 2.40/1.00      inference(global_propositional_subsumption,
% 2.40/1.00                [status(thm)],
% 2.40/1.00                [c_5589,c_42,c_4700]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_17,plain,
% 2.40/1.00      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.40/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.40/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.40/1.00      | v4_orders_2(k3_yellow19(X2,X1,X0))
% 2.40/1.00      | v2_struct_0(X2)
% 2.40/1.00      | ~ l1_struct_0(X2)
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | v1_xboole_0(X1) ),
% 2.40/1.00      inference(cnf_transformation,[],[f98]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_1140,plain,
% 2.40/1.00      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.40/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.40/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.40/1.00      | v4_orders_2(k3_yellow19(X2,X1,X0))
% 2.40/1.00      | v2_struct_0(X2)
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | v1_xboole_0(X1)
% 2.40/1.00      | sK3 != X2 ),
% 2.40/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_629]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_1141,plain,
% 2.40/1.00      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.40/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.40/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.40/1.00      | v4_orders_2(k3_yellow19(sK3,X1,X0))
% 2.40/1.00      | v2_struct_0(sK3)
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | v1_xboole_0(X1) ),
% 2.40/1.00      inference(unflattening,[status(thm)],[c_1140]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_1145,plain,
% 2.40/1.00      ( v4_orders_2(k3_yellow19(sK3,X1,X0))
% 2.40/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.40/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.40/1.00      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | v1_xboole_0(X1) ),
% 2.40/1.00      inference(global_propositional_subsumption,
% 2.40/1.00                [status(thm)],
% 2.40/1.00                [c_1141,c_34]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_1146,plain,
% 2.40/1.00      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.40/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.40/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.40/1.00      | v4_orders_2(k3_yellow19(sK3,X1,X0))
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | v1_xboole_0(X1) ),
% 2.40/1.00      inference(renaming,[status(thm)],[c_1145]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_1538,plain,
% 2.40/1.00      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.40/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.40/1.00      | v4_orders_2(k3_yellow19(sK3,X1,X0))
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | v1_xboole_0(X1)
% 2.40/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X1))
% 2.40/1.00      | sK4 != X0 ),
% 2.40/1.00      inference(resolution_lifted,[status(thm)],[c_1146,c_28]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_1539,plain,
% 2.40/1.00      ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 2.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.40/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.40/1.00      | v4_orders_2(k3_yellow19(sK3,X0,sK4))
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | v1_xboole_0(sK4)
% 2.40/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.40/1.00      inference(unflattening,[status(thm)],[c_1538]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_1543,plain,
% 2.40/1.00      ( v1_xboole_0(X0)
% 2.40/1.00      | v4_orders_2(k3_yellow19(sK3,X0,sK4))
% 2.40/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.40/1.00      | ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 2.40/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.40/1.00      inference(global_propositional_subsumption,
% 2.40/1.00                [status(thm)],
% 2.40/1.00                [c_1539,c_31]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_1544,plain,
% 2.40/1.00      ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 2.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.40/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.40/1.00      | v4_orders_2(k3_yellow19(sK3,X0,sK4))
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.40/1.00      inference(renaming,[status(thm)],[c_1543]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_2038,plain,
% 2.40/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.40/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.40/1.00      | v4_orders_2(k3_yellow19(sK3,X0,sK4))
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
% 2.40/1.00      | sK4 != sK4 ),
% 2.40/1.00      inference(resolution_lifted,[status(thm)],[c_29,c_1544]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_3007,plain,
% 2.40/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.40/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.40/1.00      | v4_orders_2(k3_yellow19(sK3,X0,sK4))
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.40/1.00      inference(equality_resolution_simp,[status(thm)],[c_2038]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_4669,plain,
% 2.40/1.00      ( k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
% 2.40/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.40/1.00      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
% 2.40/1.00      | v4_orders_2(k3_yellow19(sK3,X0,sK4)) = iProver_top
% 2.40/1.00      | v1_xboole_0(X0) = iProver_top ),
% 2.40/1.00      inference(predicate_to_equality,[status(thm)],[c_3007]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_4746,plain,
% 2.40/1.00      ( k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
% 2.40/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.40/1.00      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
% 2.40/1.00      | v4_orders_2(k3_yellow19(sK3,X0,sK4)) = iProver_top
% 2.40/1.00      | v1_xboole_0(X0) = iProver_top ),
% 2.40/1.00      inference(light_normalisation,[status(thm)],[c_4669,c_1136]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_5417,plain,
% 2.40/1.00      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.40/1.00      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))))) != iProver_top
% 2.40/1.00      | v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) = iProver_top
% 2.40/1.00      | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
% 2.40/1.00      inference(equality_resolution,[status(thm)],[c_4746]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_5928,plain,
% 2.40/1.00      ( v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) = iProver_top
% 2.40/1.00      | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
% 2.40/1.00      inference(global_propositional_subsumption,
% 2.40/1.00                [status(thm)],
% 2.40/1.00                [c_5417,c_42,c_4700]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_5936,plain,
% 2.40/1.00      ( v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
% 2.40/1.00      inference(global_propositional_subsumption,
% 2.40/1.00                [status(thm)],
% 2.40/1.00                [c_5934,c_42,c_4812,c_4700,c_5508,c_5591,c_5928]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(contradiction,plain,
% 2.40/1.00      ( $false ),
% 2.40/1.00      inference(minisat,[status(thm)],[c_6270,c_5936]) ).
% 2.40/1.00  
% 2.40/1.00  
% 2.40/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.40/1.00  
% 2.40/1.00  ------                               Statistics
% 2.40/1.00  
% 2.40/1.00  ------ General
% 2.40/1.00  
% 2.40/1.00  abstr_ref_over_cycles:                  0
% 2.40/1.00  abstr_ref_under_cycles:                 0
% 2.40/1.00  gc_basic_clause_elim:                   0
% 2.40/1.00  forced_gc_time:                         0
% 2.40/1.00  parsing_time:                           0.012
% 2.40/1.00  unif_index_cands_time:                  0.
% 2.40/1.00  unif_index_add_time:                    0.
% 2.40/1.00  orderings_time:                         0.
% 2.40/1.00  out_proof_time:                         0.02
% 2.40/1.00  total_time:                             0.193
% 2.40/1.00  num_of_symbols:                         61
% 2.40/1.00  num_of_terms:                           2835
% 2.40/1.00  
% 2.40/1.00  ------ Preprocessing
% 2.40/1.00  
% 2.40/1.00  num_of_splits:                          2
% 2.40/1.00  num_of_split_atoms:                     1
% 2.40/1.00  num_of_reused_defs:                     1
% 2.40/1.00  num_eq_ax_congr_red:                    22
% 2.40/1.00  num_of_sem_filtered_clauses:            1
% 2.40/1.00  num_of_subtypes:                        0
% 2.40/1.00  monotx_restored_types:                  0
% 2.40/1.00  sat_num_of_epr_types:                   0
% 2.40/1.00  sat_num_of_non_cyclic_types:            0
% 2.40/1.00  sat_guarded_non_collapsed_types:        0
% 2.40/1.00  num_pure_diseq_elim:                    0
% 2.40/1.00  simp_replaced_by:                       0
% 2.40/1.00  res_preprocessed:                       138
% 2.40/1.00  prep_upred:                             0
% 2.40/1.00  prep_unflattend:                        67
% 2.40/1.00  smt_new_axioms:                         0
% 2.40/1.00  pred_elim_cands:                        8
% 2.40/1.00  pred_elim:                              8
% 2.40/1.00  pred_elim_cl:                           9
% 2.40/1.00  pred_elim_cycles:                       23
% 2.40/1.00  merged_defs:                            10
% 2.40/1.00  merged_defs_ncl:                        0
% 2.40/1.00  bin_hyper_res:                          10
% 2.40/1.00  prep_cycles:                            4
% 2.40/1.00  pred_elim_time:                         0.089
% 2.40/1.00  splitting_time:                         0.
% 2.40/1.00  sem_filter_time:                        0.
% 2.40/1.00  monotx_time:                            0.001
% 2.40/1.00  subtype_inf_time:                       0.
% 2.40/1.00  
% 2.40/1.00  ------ Problem properties
% 2.40/1.00  
% 2.40/1.00  clauses:                                25
% 2.40/1.00  conjectures:                            4
% 2.40/1.00  epr:                                    6
% 2.40/1.00  horn:                                   19
% 2.40/1.00  ground:                                 11
% 2.40/1.00  unary:                                  10
% 2.40/1.00  binary:                                 6
% 2.40/1.00  lits:                                   68
% 2.40/1.00  lits_eq:                                11
% 2.40/1.00  fd_pure:                                0
% 2.40/1.00  fd_pseudo:                              0
% 2.40/1.00  fd_cond:                                0
% 2.40/1.00  fd_pseudo_cond:                         1
% 2.40/1.00  ac_symbols:                             0
% 2.40/1.00  
% 2.40/1.00  ------ Propositional Solver
% 2.40/1.00  
% 2.40/1.00  prop_solver_calls:                      26
% 2.40/1.00  prop_fast_solver_calls:                 1966
% 2.40/1.00  smt_solver_calls:                       0
% 2.40/1.00  smt_fast_solver_calls:                  0
% 2.40/1.00  prop_num_of_clauses:                    1235
% 2.40/1.00  prop_preprocess_simplified:             4658
% 2.40/1.00  prop_fo_subsumed:                       50
% 2.40/1.00  prop_solver_time:                       0.
% 2.40/1.00  smt_solver_time:                        0.
% 2.40/1.00  smt_fast_solver_time:                   0.
% 2.40/1.00  prop_fast_solver_time:                  0.
% 2.40/1.00  prop_unsat_core_time:                   0.
% 2.40/1.00  
% 2.40/1.00  ------ QBF
% 2.40/1.00  
% 2.40/1.00  qbf_q_res:                              0
% 2.40/1.00  qbf_num_tautologies:                    0
% 2.40/1.00  qbf_prep_cycles:                        0
% 2.40/1.00  
% 2.40/1.00  ------ BMC1
% 2.40/1.00  
% 2.40/1.00  bmc1_current_bound:                     -1
% 2.40/1.00  bmc1_last_solved_bound:                 -1
% 2.40/1.00  bmc1_unsat_core_size:                   -1
% 2.40/1.00  bmc1_unsat_core_parents_size:           -1
% 2.40/1.00  bmc1_merge_next_fun:                    0
% 2.40/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.40/1.00  
% 2.40/1.00  ------ Instantiation
% 2.40/1.00  
% 2.40/1.00  inst_num_of_clauses:                    285
% 2.40/1.00  inst_num_in_passive:                    15
% 2.40/1.00  inst_num_in_active:                     159
% 2.40/1.00  inst_num_in_unprocessed:                111
% 2.40/1.00  inst_num_of_loops:                      190
% 2.40/1.00  inst_num_of_learning_restarts:          0
% 2.40/1.00  inst_num_moves_active_passive:          28
% 2.40/1.00  inst_lit_activity:                      0
% 2.40/1.00  inst_lit_activity_moves:                0
% 2.40/1.00  inst_num_tautologies:                   0
% 2.40/1.00  inst_num_prop_implied:                  0
% 2.40/1.00  inst_num_existing_simplified:           0
% 2.40/1.00  inst_num_eq_res_simplified:             0
% 2.40/1.00  inst_num_child_elim:                    0
% 2.40/1.00  inst_num_of_dismatching_blockings:      44
% 2.40/1.00  inst_num_of_non_proper_insts:           203
% 2.40/1.00  inst_num_of_duplicates:                 0
% 2.40/1.00  inst_inst_num_from_inst_to_res:         0
% 2.40/1.00  inst_dismatching_checking_time:         0.
% 2.40/1.00  
% 2.40/1.00  ------ Resolution
% 2.40/1.00  
% 2.40/1.00  res_num_of_clauses:                     0
% 2.40/1.00  res_num_in_passive:                     0
% 2.40/1.00  res_num_in_active:                      0
% 2.40/1.00  res_num_of_loops:                       142
% 2.40/1.00  res_forward_subset_subsumed:            20
% 2.40/1.00  res_backward_subset_subsumed:           0
% 2.40/1.00  res_forward_subsumed:                   0
% 2.40/1.00  res_backward_subsumed:                  0
% 2.40/1.00  res_forward_subsumption_resolution:     2
% 2.40/1.00  res_backward_subsumption_resolution:    0
% 2.40/1.00  res_clause_to_clause_subsumption:       328
% 2.40/1.00  res_orphan_elimination:                 0
% 2.40/1.00  res_tautology_del:                      49
% 2.40/1.00  res_num_eq_res_simplified:              6
% 2.40/1.00  res_num_sel_changes:                    0
% 2.40/1.00  res_moves_from_active_to_pass:          0
% 2.40/1.00  
% 2.40/1.00  ------ Superposition
% 2.40/1.00  
% 2.40/1.00  sup_time_total:                         0.
% 2.40/1.00  sup_time_generating:                    0.
% 2.40/1.00  sup_time_sim_full:                      0.
% 2.40/1.00  sup_time_sim_immed:                     0.
% 2.40/1.00  
% 2.40/1.00  sup_num_of_clauses:                     43
% 2.40/1.00  sup_num_in_active:                      36
% 2.40/1.00  sup_num_in_passive:                     7
% 2.40/1.00  sup_num_of_loops:                       36
% 2.40/1.00  sup_fw_superposition:                   14
% 2.40/1.00  sup_bw_superposition:                   9
% 2.40/1.00  sup_immediate_simplified:               2
% 2.40/1.00  sup_given_eliminated:                   0
% 2.40/1.00  comparisons_done:                       0
% 2.40/1.00  comparisons_avoided:                    0
% 2.40/1.00  
% 2.40/1.00  ------ Simplifications
% 2.40/1.00  
% 2.40/1.00  
% 2.40/1.00  sim_fw_subset_subsumed:                 0
% 2.40/1.00  sim_bw_subset_subsumed:                 1
% 2.40/1.00  sim_fw_subsumed:                        2
% 2.40/1.00  sim_bw_subsumed:                        1
% 2.40/1.00  sim_fw_subsumption_res:                 1
% 2.40/1.00  sim_bw_subsumption_res:                 0
% 2.40/1.00  sim_tautology_del:                      3
% 2.40/1.00  sim_eq_tautology_del:                   1
% 2.40/1.00  sim_eq_res_simp:                        2
% 2.40/1.00  sim_fw_demodulated:                     0
% 2.40/1.00  sim_bw_demodulated:                     0
% 2.40/1.00  sim_light_normalised:                   10
% 2.40/1.00  sim_joinable_taut:                      0
% 2.40/1.00  sim_joinable_simp:                      0
% 2.40/1.00  sim_ac_normalised:                      0
% 2.40/1.00  sim_smt_subsumption:                    0
% 2.40/1.00  
%------------------------------------------------------------------------------
