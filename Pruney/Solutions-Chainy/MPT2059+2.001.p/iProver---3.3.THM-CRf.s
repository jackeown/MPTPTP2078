%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:19 EST 2020

% Result     : Theorem 2.40s
% Output     : CNFRefutation 2.40s
% Verified   : 
% Statistics : Number of formulae       :  230 (1707 expanded)
%              Number of clauses        :  138 ( 341 expanded)
%              Number of leaves         :   20 ( 486 expanded)
%              Depth                    :   28
%              Number of atoms          : 1378 (15383 expanded)
%              Number of equality atoms :  241 ( 558 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal clause size      :   26 (   6 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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
             => ( r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))
              <=> r2_waybel_7(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
               => ( r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))
                <=> r2_waybel_7(X0,X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))
              <~> r2_waybel_7(X0,X1,X2) )
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

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))
              <~> r2_waybel_7(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f54,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r2_waybel_7(X0,X1,X2)
                | ~ r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) )
              & ( r2_waybel_7(X0,X1,X2)
                | r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f55,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r2_waybel_7(X0,X1,X2)
                | ~ r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) )
              & ( r2_waybel_7(X0,X1,X2)
                | r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) )
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
          ( ( ~ r2_waybel_7(X0,X1,X2)
            | ~ r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) )
          & ( r2_waybel_7(X0,X1,X2)
            | r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( ~ r2_waybel_7(X0,X1,sK4)
          | ~ r2_hidden(sK4,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) )
        & ( r2_waybel_7(X0,X1,sK4)
          | r2_hidden(sK4,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) )
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r2_waybel_7(X0,X1,X2)
                | ~ r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) )
              & ( r2_waybel_7(X0,X1,X2)
                | r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
     => ( ? [X2] :
            ( ( ~ r2_waybel_7(X0,sK3,X2)
              | ~ r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),sK3))) )
            & ( r2_waybel_7(X0,sK3,X2)
              | r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),sK3))) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
        & v13_waybel_0(sK3,k3_yellow_1(k2_struct_0(X0)))
        & v2_waybel_0(sK3,k3_yellow_1(k2_struct_0(X0)))
        & v1_subset_1(sK3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
        & ~ v1_xboole_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r2_waybel_7(X0,X1,X2)
                  | ~ r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) )
                & ( r2_waybel_7(X0,X1,X2)
                  | r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) )
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
              ( ( ~ r2_waybel_7(sK2,X1,X2)
                | ~ r2_hidden(X2,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),X1))) )
              & ( r2_waybel_7(sK2,X1,X2)
                | r2_hidden(X2,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),X1))) )
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

fof(f59,plain,
    ( ( ~ r2_waybel_7(sK2,sK3,sK4)
      | ~ r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3))) )
    & ( r2_waybel_7(sK2,sK3,sK4)
      | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3))) )
    & m1_subset_1(sK4,u1_struct_0(sK2))
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK2)))))
    & v13_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK2)))
    & v2_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK2)))
    & v1_subset_1(sK3,u1_struct_0(k3_yellow_1(k2_struct_0(sK2))))
    & ~ v1_xboole_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f55,f58,f57,f56])).

fof(f93,plain,(
    m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f59])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f87,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f59])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r2_hidden(X1,k1_connsp_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,k1_connsp_2(X0,X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,k1_connsp_2(X0,X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,k1_connsp_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f86,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f59])).

fof(f85,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f59])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f73,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
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
    inference(cnf_transformation,[],[f52])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f46,plain,(
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

fof(f47,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f46])).

fof(f48,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f47,f48])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f43,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f42])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f43,f44])).

fof(f60,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f90,plain,(
    v2_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f59])).

fof(f10,axiom,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f105,plain,(
    v2_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) ),
    inference(definition_unfolding,[],[f90,f75])).

fof(f91,plain,(
    v13_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f59])).

fof(f104,plain,(
    v13_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) ),
    inference(definition_unfolding,[],[f91,f75])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f34,plain,(
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

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

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
    inference(cnf_transformation,[],[f35])).

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
    v1_subset_1(sK3,u1_struct_0(k3_yellow_1(k2_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f59])).

fof(f106,plain,(
    v1_subset_1(sK3,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))) ),
    inference(definition_unfolding,[],[f89,f75])).

fof(f88,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f59])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f30,plain,(
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

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

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
    inference(cnf_transformation,[],[f31])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f32,plain,(
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

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

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
    inference(cnf_transformation,[],[f33])).

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

fof(f95,plain,
    ( ~ r2_waybel_7(sK2,sK3,sK4)
    | ~ r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3))) ),
    inference(cnf_transformation,[],[f59])).

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
             => ( r2_hidden(X2,k10_yellow_6(X0,X1))
              <=> r2_waybel_7(X0,k2_yellow19(X0,X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k10_yellow_6(X0,X1))
              <=> r2_waybel_7(X0,k2_yellow19(X0,X1),X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k10_yellow_6(X0,X1))
              <=> r2_waybel_7(X0,k2_yellow19(X0,X1),X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k10_yellow_6(X0,X1))
                  | ~ r2_waybel_7(X0,k2_yellow19(X0,X1),X2) )
                & ( r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
                  | ~ r2_hidden(X2,k10_yellow_6(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
      | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

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
    inference(cnf_transformation,[],[f31])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
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

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

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
    inference(cnf_transformation,[],[f39])).

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

fof(f92,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK2))))) ),
    inference(cnf_transformation,[],[f59])).

fof(f103,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))))) ),
    inference(definition_unfolding,[],[f92,f75])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f94,plain,
    ( r2_waybel_7(sK2,sK3,sK4)
    | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3))) ),
    inference(cnf_transformation,[],[f59])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k10_yellow_6(X0,X1))
      | ~ r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_3309,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_10,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_12,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_32,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_673,plain,
    ( l1_struct_0(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_32])).

cnf(c_674,plain,
    ( l1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_673])).

cnf(c_2167,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_674])).

cnf(c_2168,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_2167])).

cnf(c_3325,plain,
    ( m1_subset_1(sK4,k2_struct_0(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3309,c_2168])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | r2_hidden(X0,k1_connsp_2(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_33,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_615,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | r2_hidden(X0,k1_connsp_2(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_33])).

cnf(c_616,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | r2_hidden(X0,k1_connsp_2(sK2,X0))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_615])).

cnf(c_34,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_620,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | r2_hidden(X0,k1_connsp_2(sK2,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_616,c_34,c_32])).

cnf(c_3306,plain,
    ( m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X0,k1_connsp_2(sK2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_620])).

cnf(c_3359,plain,
    ( m1_subset_1(X0,k2_struct_0(sK2)) != iProver_top
    | r2_hidden(X0,k1_connsp_2(sK2,X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3306,c_2168])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_633,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_33])).

cnf(c_634,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | m1_subset_1(k1_connsp_2(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_633])).

cnf(c_638,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | m1_subset_1(k1_connsp_2(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_634,c_34,c_32])).

cnf(c_3305,plain,
    ( m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k1_connsp_2(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_638])).

cnf(c_3364,plain,
    ( m1_subset_1(X0,k2_struct_0(sK2)) != iProver_top
    | m1_subset_1(k1_connsp_2(sK2,X0),k1_zfmisc_1(k2_struct_0(sK2))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3305,c_2168])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_3310,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3676,plain,
    ( m1_subset_1(X0,k2_struct_0(sK2)) != iProver_top
    | r1_tarski(k1_connsp_2(sK2,X0),k2_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3364,c_3310])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_3314,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4179,plain,
    ( m1_subset_1(X0,k2_struct_0(sK2)) != iProver_top
    | r2_hidden(X1,k1_connsp_2(sK2,X0)) != iProver_top
    | r2_hidden(X1,k2_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3676,c_3314])).

cnf(c_4757,plain,
    ( m1_subset_1(X0,k2_struct_0(sK2)) != iProver_top
    | r2_hidden(X0,k2_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3359,c_4179])).

cnf(c_4786,plain,
    ( r2_hidden(sK4,k2_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3325,c_4757])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_3317,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4865,plain,
    ( v1_xboole_0(k2_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4786,c_3317])).

cnf(c_29,negated_conjecture,
    ( v2_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_28,negated_conjecture,
    ( v13_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) ),
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
    ( v1_subset_1(sK3,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_459,plain,
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

cnf(c_460,plain,
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
    inference(unflattening,[status(thm)],[c_459])).

cnf(c_31,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_464,plain,
    ( v1_xboole_0(X0)
    | ~ l1_struct_0(X1)
    | v2_struct_0(X1)
    | v7_waybel_0(k3_yellow19(X1,X0,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v13_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_460,c_31])).

cnf(c_465,plain,
    ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(X1,X0,sK3))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(renaming,[status(thm)],[c_464])).

cnf(c_1460,plain,
    ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(X1,X0,sK3))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_465])).

cnf(c_1853,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(X1,X0,sK3))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_1460])).

cnf(c_2226,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(X1,X0,sK3))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | sK3 != sK3
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1853,c_674])).

cnf(c_2227,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK2,X0,sK3))
    | v2_struct_0(sK2)
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(unflattening,[status(thm)],[c_2226])).

cnf(c_2231,plain,
    ( v7_waybel_0(k3_yellow19(sK2,X0,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2227,c_34])).

cnf(c_2232,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK2,X0,sK3))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(renaming,[status(thm)],[c_2231])).

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

cnf(c_1388,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v2_struct_0(X2)
    | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
    | ~ l1_struct_0(X2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X1))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_28])).

cnf(c_1389,plain,
    ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k3_yellow19(X1,X0,sK3))
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(sK3)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_1388])).

cnf(c_1393,plain,
    ( v1_xboole_0(X0)
    | ~ l1_struct_0(X1)
    | ~ v2_struct_0(k3_yellow19(X1,X0,sK3))
    | v2_struct_0(X1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1389,c_31])).

cnf(c_1394,plain,
    ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k3_yellow19(X1,X0,sK3))
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(renaming,[status(thm)],[c_1393])).

cnf(c_1914,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k3_yellow19(X1,X0,sK3))
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_1394])).

cnf(c_2199,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k3_yellow19(X1,X0,sK3))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
    | sK3 != sK3
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1914,c_674])).

cnf(c_2200,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v2_struct_0(k3_yellow19(sK2,X0,sK3))
    | v2_struct_0(sK2)
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_2199])).

cnf(c_2204,plain,
    ( ~ v2_struct_0(k3_yellow19(sK2,X0,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2200,c_34])).

cnf(c_2205,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v2_struct_0(k3_yellow19(sK2,X0,sK3))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(renaming,[status(thm)],[c_2204])).

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

cnf(c_1352,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v4_orders_2(k3_yellow19(X2,X1,X0))
    | v2_struct_0(X2)
    | ~ l1_struct_0(X2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X1))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_28])).

cnf(c_1353,plain,
    ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(X1,X0,sK3))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(sK3)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_1352])).

cnf(c_1357,plain,
    ( v1_xboole_0(X0)
    | ~ l1_struct_0(X1)
    | v2_struct_0(X1)
    | v4_orders_2(k3_yellow19(X1,X0,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1353,c_31])).

cnf(c_1358,plain,
    ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(X1,X0,sK3))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(renaming,[status(thm)],[c_1357])).

cnf(c_1943,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(X1,X0,sK3))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_1358])).

cnf(c_2172,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(X1,X0,sK3))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
    | sK3 != sK3
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1943,c_674])).

cnf(c_2173,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(sK2,X0,sK3))
    | v2_struct_0(sK2)
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_2172])).

cnf(c_2177,plain,
    ( v4_orders_2(k3_yellow19(sK2,X0,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2173,c_34])).

cnf(c_2178,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(sK2,X0,sK3))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(renaming,[status(thm)],[c_2177])).

cnf(c_24,negated_conjecture,
    ( ~ r2_waybel_7(sK2,sK3,sK4)
    | ~ r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3))) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_264,plain,
    ( ~ r2_waybel_7(sK2,sK3,sK4)
    | ~ r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3))) ),
    inference(prop_impl,[status(thm)],[c_24])).

cnf(c_22,plain,
    ( r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_549,plain,
    ( r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_33])).

cnf(c_550,plain,
    ( r2_waybel_7(sK2,k2_yellow19(sK2,X0),X1)
    | ~ l1_waybel_0(X0,sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ r2_hidden(X1,k10_yellow_6(sK2,X0))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_549])).

cnf(c_554,plain,
    ( r2_waybel_7(sK2,k2_yellow19(sK2,X0),X1)
    | ~ l1_waybel_0(X0,sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ r2_hidden(X1,k10_yellow_6(sK2,X0))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_550,c_34,c_32])).

cnf(c_1009,plain,
    ( ~ l1_waybel_0(X0,sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ r2_hidden(X1,k10_yellow_6(sK2,X0))
    | ~ r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | k2_yellow19(sK2,X0) != sK3
    | sK4 != X1
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_264,c_554])).

cnf(c_1010,plain,
    ( ~ l1_waybel_0(X0,sK2)
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ r2_hidden(sK4,k10_yellow_6(sK2,X0))
    | ~ r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | k2_yellow19(sK2,X0) != sK3 ),
    inference(unflattening,[status(thm)],[c_1009])).

cnf(c_1014,plain,
    ( ~ l1_waybel_0(X0,sK2)
    | ~ r2_hidden(sK4,k10_yellow_6(sK2,X0))
    | ~ r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | k2_yellow19(sK2,X0) != sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1010,c_26])).

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

cnf(c_1424,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | l1_waybel_0(k3_yellow19(X2,X1,X0),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v2_struct_0(X2)
    | ~ l1_struct_0(X2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X1))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_28])).

cnf(c_1425,plain,
    ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | l1_waybel_0(k3_yellow19(X1,X0,sK3),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(sK3)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_1424])).

cnf(c_1429,plain,
    ( v1_xboole_0(X0)
    | ~ l1_struct_0(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | l1_waybel_0(k3_yellow19(X1,X0,sK3),X1)
    | ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1425,c_31])).

cnf(c_1430,plain,
    ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | l1_waybel_0(k3_yellow19(X1,X0,sK3),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(renaming,[status(thm)],[c_1429])).

cnf(c_1885,plain,
    ( l1_waybel_0(k3_yellow19(X0,X1,sK3),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | v1_xboole_0(X1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X1))
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_1430])).

cnf(c_2043,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ r2_hidden(sK4,k10_yellow_6(sK2,X2))
    | ~ r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)))
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | k3_yellow19(X1,X0,sK3) != X2
    | k2_yellow19(sK2,X2) != sK3
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
    | sK3 != sK3
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1014,c_1885])).

cnf(c_2044,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,X0,sK3)))
    | ~ r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)))
    | ~ v7_waybel_0(k3_yellow19(sK2,X0,sK3))
    | ~ v4_orders_2(k3_yellow19(sK2,X0,sK3))
    | v2_struct_0(k3_yellow19(sK2,X0,sK3))
    | v2_struct_0(sK2)
    | ~ l1_struct_0(sK2)
    | v1_xboole_0(X0)
    | k2_yellow19(sK2,k3_yellow19(sK2,X0,sK3)) != sK3
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_2043])).

cnf(c_78,plain,
    ( ~ l1_pre_topc(sK2)
    | l1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2048,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,X0,sK3)))
    | ~ r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)))
    | ~ v7_waybel_0(k3_yellow19(sK2,X0,sK3))
    | ~ v4_orders_2(k3_yellow19(sK2,X0,sK3))
    | v2_struct_0(k3_yellow19(sK2,X0,sK3))
    | v1_xboole_0(X0)
    | k2_yellow19(sK2,k3_yellow19(sK2,X0,sK3)) != sK3
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2044,c_34,c_32,c_78])).

cnf(c_2264,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,X0,sK3)))
    | ~ r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)))
    | ~ v7_waybel_0(k3_yellow19(sK2,X0,sK3))
    | v2_struct_0(k3_yellow19(sK2,X0,sK3))
    | v1_xboole_0(X0)
    | k2_yellow19(sK2,k3_yellow19(sK2,X0,sK3)) != sK3
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2178,c_2048])).

cnf(c_2279,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,X0,sK3)))
    | ~ r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)))
    | ~ v7_waybel_0(k3_yellow19(sK2,X0,sK3))
    | v1_xboole_0(X0)
    | k2_yellow19(sK2,k3_yellow19(sK2,X0,sK3)) != sK3
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2205,c_2264])).

cnf(c_2296,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,X0,sK3)))
    | ~ r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)))
    | v1_xboole_0(X0)
    | k2_yellow19(sK2,k3_yellow19(sK2,X0,sK3)) != sK3
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(resolution,[status(thm)],[c_2232,c_2279])).

cnf(c_3303,plain,
    ( k2_yellow19(sK2,k3_yellow19(sK2,X0,sK3)) != sK3
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
    | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,X0,sK3))) != iProver_top
    | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3))) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2296])).

cnf(c_3398,plain,
    ( k2_yellow19(sK2,k3_yellow19(sK2,X0,sK3)) != sK3
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
    | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,X0,sK3))) != iProver_top
    | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3))) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3303,c_2168])).

cnf(c_3932,plain,
    ( k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)) != sK3
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(k2_struct_0(sK2)))
    | m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))))) != iProver_top
    | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3))) != iProver_top
    | v1_xboole_0(k2_struct_0(sK2)) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3398])).

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

cnf(c_498,plain,
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

cnf(c_499,plain,
    ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ v13_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | v1_xboole_0(sK3)
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK3)) = sK3
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) ),
    inference(unflattening,[status(thm)],[c_498])).

cnf(c_503,plain,
    ( ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | ~ v13_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK3)) = sK3
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_499,c_31])).

cnf(c_504,plain,
    ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ v13_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK3)) = sK3
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) ),
    inference(renaming,[status(thm)],[c_503])).

cnf(c_1495,plain,
    ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK3)) = sK3
    | k3_lattice3(k1_lattice3(k2_struct_0(X0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK2)))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_504])).

cnf(c_1972,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK3)) = sK3
    | k3_lattice3(k1_lattice3(k2_struct_0(X0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK2)))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_1495])).

cnf(c_2149,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | v2_struct_0(X0)
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK3)) = sK3
    | k3_lattice3(k1_lattice3(k2_struct_0(X0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK2)))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))
    | sK3 != sK3
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1972,c_674])).

cnf(c_2150,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))))
    | v2_struct_0(sK2)
    | k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)) = sK3
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(k2_struct_0(sK2)))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) ),
    inference(unflattening,[status(thm)],[c_2149])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))))) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_506,plain,
    ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(sK2))))
    | ~ v13_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(sK2))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))))
    | v2_struct_0(sK2)
    | ~ l1_struct_0(sK2)
    | k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)) = sK3
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) ),
    inference(instantiation,[status(thm)],[c_504])).

cnf(c_2152,plain,
    ( k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)) = sK3
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2150,c_34,c_32,c_29,c_28,c_27,c_78,c_506])).

cnf(c_2554,plain,
    ( k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)) = sK3 ),
    inference(equality_resolution_simp,[status(thm)],[c_2152])).

cnf(c_3933,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(k2_struct_0(sK2)))
    | sK3 != sK3
    | m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))))) != iProver_top
    | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3))) != iProver_top
    | v1_xboole_0(k2_struct_0(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3932,c_2554])).

cnf(c_3934,plain,
    ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))))) != iProver_top
    | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3))) != iProver_top
    | v1_xboole_0(k2_struct_0(sK2)) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3933])).

cnf(c_42,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_11,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2160,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_674])).

cnf(c_2161,plain,
    ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unflattening,[status(thm)],[c_2160])).

cnf(c_3304,plain,
    ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2161])).

cnf(c_3328,plain,
    ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3304,c_2168])).

cnf(c_25,negated_conjecture,
    ( r2_waybel_7(sK2,sK3,sK4)
    | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3))) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_266,plain,
    ( r2_waybel_7(sK2,sK3,sK4)
    | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3))) ),
    inference(prop_impl,[status(thm)],[c_25])).

cnf(c_21,plain,
    ( ~ r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(X2,k10_yellow_6(X0,X1))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_582,plain,
    ( ~ r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(X2,k10_yellow_6(X0,X1))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_33])).

cnf(c_583,plain,
    ( ~ r2_waybel_7(sK2,k2_yellow19(sK2,X0),X1)
    | ~ l1_waybel_0(X0,sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r2_hidden(X1,k10_yellow_6(sK2,X0))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_582])).

cnf(c_587,plain,
    ( ~ r2_waybel_7(sK2,k2_yellow19(sK2,X0),X1)
    | ~ l1_waybel_0(X0,sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r2_hidden(X1,k10_yellow_6(sK2,X0))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_583,c_34,c_32])).

cnf(c_976,plain,
    ( ~ l1_waybel_0(X0,sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r2_hidden(X1,k10_yellow_6(sK2,X0))
    | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | k2_yellow19(sK2,X0) != sK3
    | sK4 != X1
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_266,c_587])).

cnf(c_977,plain,
    ( ~ l1_waybel_0(X0,sK2)
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | r2_hidden(sK4,k10_yellow_6(sK2,X0))
    | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | k2_yellow19(sK2,X0) != sK3 ),
    inference(unflattening,[status(thm)],[c_976])).

cnf(c_981,plain,
    ( ~ l1_waybel_0(X0,sK2)
    | r2_hidden(sK4,k10_yellow_6(sK2,X0))
    | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | k2_yellow19(sK2,X0) != sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_977,c_26])).

cnf(c_2085,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | r2_hidden(sK4,k10_yellow_6(sK2,X2))
    | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)))
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | k3_yellow19(X1,X0,sK3) != X2
    | k2_yellow19(sK2,X2) != sK3
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
    | sK3 != sK3
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_981,c_1885])).

cnf(c_2086,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,X0,sK3)))
    | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)))
    | ~ v7_waybel_0(k3_yellow19(sK2,X0,sK3))
    | ~ v4_orders_2(k3_yellow19(sK2,X0,sK3))
    | v2_struct_0(k3_yellow19(sK2,X0,sK3))
    | v2_struct_0(sK2)
    | ~ l1_struct_0(sK2)
    | v1_xboole_0(X0)
    | k2_yellow19(sK2,k3_yellow19(sK2,X0,sK3)) != sK3
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_2085])).

cnf(c_2090,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,X0,sK3)))
    | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)))
    | ~ v7_waybel_0(k3_yellow19(sK2,X0,sK3))
    | ~ v4_orders_2(k3_yellow19(sK2,X0,sK3))
    | v2_struct_0(k3_yellow19(sK2,X0,sK3))
    | v1_xboole_0(X0)
    | k2_yellow19(sK2,k3_yellow19(sK2,X0,sK3)) != sK3
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2086,c_34,c_32,c_78])).

cnf(c_2265,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,X0,sK3)))
    | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)))
    | ~ v7_waybel_0(k3_yellow19(sK2,X0,sK3))
    | v2_struct_0(k3_yellow19(sK2,X0,sK3))
    | v1_xboole_0(X0)
    | k2_yellow19(sK2,k3_yellow19(sK2,X0,sK3)) != sK3
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2178,c_2090])).

cnf(c_2278,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,X0,sK3)))
    | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)))
    | ~ v7_waybel_0(k3_yellow19(sK2,X0,sK3))
    | v1_xboole_0(X0)
    | k2_yellow19(sK2,k3_yellow19(sK2,X0,sK3)) != sK3
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2205,c_2265])).

cnf(c_2325,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,X0,sK3)))
    | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)))
    | v1_xboole_0(X0)
    | k2_yellow19(sK2,k3_yellow19(sK2,X0,sK3)) != sK3
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(resolution,[status(thm)],[c_2232,c_2278])).

cnf(c_3302,plain,
    ( k2_yellow19(sK2,k3_yellow19(sK2,X0,sK3)) != sK3
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
    | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,X0,sK3))) = iProver_top
    | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3))) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2325])).

cnf(c_3381,plain,
    ( k2_yellow19(sK2,k3_yellow19(sK2,X0,sK3)) != sK3
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
    | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,X0,sK3))) = iProver_top
    | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3))) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3302,c_2168])).

cnf(c_3945,plain,
    ( k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)) != sK3
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(k2_struct_0(sK2)))
    | m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))))) != iProver_top
    | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3))) = iProver_top
    | v1_xboole_0(k2_struct_0(sK2)) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3381])).

cnf(c_3946,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(k2_struct_0(sK2)))
    | sK3 != sK3
    | m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))))) != iProver_top
    | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3))) = iProver_top
    | v1_xboole_0(k2_struct_0(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3945,c_2554])).

cnf(c_3947,plain,
    ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))))) != iProver_top
    | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3))) = iProver_top
    | v1_xboole_0(k2_struct_0(sK2)) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3946])).

cnf(c_4107,plain,
    ( v1_xboole_0(k2_struct_0(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3934,c_42,c_3328,c_3947])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4865,c_4107])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:01:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.40/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
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
% 2.40/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 11 0s  sf_e  pe_s  pe_e 
% 2.40/0.99  
% 2.40/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.40/0.99  
% 2.40/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.40/0.99  ------ Proving...
% 2.40/0.99  ------ Problem Properties 
% 2.40/0.99  
% 2.40/0.99  
% 2.40/0.99  clauses                                 19
% 2.40/0.99  conjectures                             3
% 2.40/0.99  EPR                                     5
% 2.40/0.99  Horn                                    16
% 2.40/0.99  unary                                   7
% 2.40/0.99  binary                                  8
% 2.40/0.99  lits                                    45
% 2.40/0.99  lits eq                                 9
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
% 2.40/0.99  fof(f16,conjecture,(
% 2.40/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) <=> r2_waybel_7(X0,X1,X2)))))),
% 2.40/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/0.99  
% 2.40/0.99  fof(f17,negated_conjecture,(
% 2.40/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) <=> r2_waybel_7(X0,X1,X2)))))),
% 2.40/0.99    inference(negated_conjecture,[],[f16])).
% 2.40/0.99  
% 2.40/0.99  fof(f40,plain,(
% 2.40/0.99    ? [X0] : (? [X1] : (? [X2] : ((r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) <~> r2_waybel_7(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.40/0.99    inference(ennf_transformation,[],[f17])).
% 2.40/0.99  
% 2.40/0.99  fof(f41,plain,(
% 2.40/0.99    ? [X0] : (? [X1] : (? [X2] : ((r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) <~> r2_waybel_7(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.40/0.99    inference(flattening,[],[f40])).
% 2.40/0.99  
% 2.40/0.99  fof(f54,plain,(
% 2.40/0.99    ? [X0] : (? [X1] : (? [X2] : (((~r2_waybel_7(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & (r2_waybel_7(X0,X1,X2) | r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.40/0.99    inference(nnf_transformation,[],[f41])).
% 2.40/0.99  
% 2.40/0.99  fof(f55,plain,(
% 2.40/0.99    ? [X0] : (? [X1] : (? [X2] : ((~r2_waybel_7(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & (r2_waybel_7(X0,X1,X2) | r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.40/0.99    inference(flattening,[],[f54])).
% 2.40/0.99  
% 2.40/0.99  fof(f58,plain,(
% 2.40/0.99    ( ! [X0,X1] : (? [X2] : ((~r2_waybel_7(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & (r2_waybel_7(X0,X1,X2) | r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & m1_subset_1(X2,u1_struct_0(X0))) => ((~r2_waybel_7(X0,X1,sK4) | ~r2_hidden(sK4,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & (r2_waybel_7(X0,X1,sK4) | r2_hidden(sK4,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & m1_subset_1(sK4,u1_struct_0(X0)))) )),
% 2.40/0.99    introduced(choice_axiom,[])).
% 2.40/0.99  
% 2.40/0.99  fof(f57,plain,(
% 2.40/0.99    ( ! [X0] : (? [X1] : (? [X2] : ((~r2_waybel_7(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & (r2_waybel_7(X0,X1,X2) | r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => (? [X2] : ((~r2_waybel_7(X0,sK3,X2) | ~r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),sK3)))) & (r2_waybel_7(X0,sK3,X2) | r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),sK3)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(sK3,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(sK3,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(sK3,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(sK3))) )),
% 2.40/0.99    introduced(choice_axiom,[])).
% 2.40/0.99  
% 2.40/0.99  fof(f56,plain,(
% 2.40/0.99    ? [X0] : (? [X1] : (? [X2] : ((~r2_waybel_7(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & (r2_waybel_7(X0,X1,X2) | r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~r2_waybel_7(sK2,X1,X2) | ~r2_hidden(X2,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),X1)))) & (r2_waybel_7(sK2,X1,X2) | r2_hidden(X2,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),X1)))) & m1_subset_1(X2,u1_struct_0(sK2))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK2))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK2))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK2))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK2)))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 2.40/0.99    introduced(choice_axiom,[])).
% 2.40/0.99  
% 2.40/0.99  fof(f59,plain,(
% 2.40/0.99    (((~r2_waybel_7(sK2,sK3,sK4) | ~r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)))) & (r2_waybel_7(sK2,sK3,sK4) | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)))) & m1_subset_1(sK4,u1_struct_0(sK2))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK2))))) & v13_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK2))) & v2_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK2))) & v1_subset_1(sK3,u1_struct_0(k3_yellow_1(k2_struct_0(sK2)))) & ~v1_xboole_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 2.40/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f55,f58,f57,f56])).
% 2.40/0.99  
% 2.40/0.99  fof(f93,plain,(
% 2.40/0.99    m1_subset_1(sK4,u1_struct_0(sK2))),
% 2.40/0.99    inference(cnf_transformation,[],[f59])).
% 2.40/0.99  
% 2.40/0.99  fof(f5,axiom,(
% 2.40/0.99    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.40/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/0.99  
% 2.40/0.99  fof(f23,plain,(
% 2.40/0.99    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.40/0.99    inference(ennf_transformation,[],[f5])).
% 2.40/0.99  
% 2.40/0.99  fof(f70,plain,(
% 2.40/0.99    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.40/0.99    inference(cnf_transformation,[],[f23])).
% 2.40/0.99  
% 2.40/0.99  fof(f7,axiom,(
% 2.40/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.40/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/0.99  
% 2.40/0.99  fof(f25,plain,(
% 2.40/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.40/0.99    inference(ennf_transformation,[],[f7])).
% 2.40/0.99  
% 2.40/0.99  fof(f72,plain,(
% 2.40/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.40/0.99    inference(cnf_transformation,[],[f25])).
% 2.40/0.99  
% 2.40/0.99  fof(f87,plain,(
% 2.40/0.99    l1_pre_topc(sK2)),
% 2.40/0.99    inference(cnf_transformation,[],[f59])).
% 2.40/0.99  
% 2.40/0.99  fof(f9,axiom,(
% 2.40/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r2_hidden(X1,k1_connsp_2(X0,X1))))),
% 2.40/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/0.99  
% 2.40/0.99  fof(f28,plain,(
% 2.40/0.99    ! [X0] : (! [X1] : (r2_hidden(X1,k1_connsp_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.40/0.99    inference(ennf_transformation,[],[f9])).
% 2.40/0.99  
% 2.40/0.99  fof(f29,plain,(
% 2.40/0.99    ! [X0] : (! [X1] : (r2_hidden(X1,k1_connsp_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.40/0.99    inference(flattening,[],[f28])).
% 2.40/0.99  
% 2.40/0.99  fof(f74,plain,(
% 2.40/0.99    ( ! [X0,X1] : (r2_hidden(X1,k1_connsp_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.40/0.99    inference(cnf_transformation,[],[f29])).
% 2.40/0.99  
% 2.40/0.99  fof(f86,plain,(
% 2.40/0.99    v2_pre_topc(sK2)),
% 2.40/0.99    inference(cnf_transformation,[],[f59])).
% 2.40/0.99  
% 2.40/0.99  fof(f85,plain,(
% 2.40/0.99    ~v2_struct_0(sK2)),
% 2.40/0.99    inference(cnf_transformation,[],[f59])).
% 2.40/0.99  
% 2.40/0.99  fof(f8,axiom,(
% 2.40/0.99    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.40/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/0.99  
% 2.40/0.99  fof(f26,plain,(
% 2.40/0.99    ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.40/0.99    inference(ennf_transformation,[],[f8])).
% 2.40/0.99  
% 2.40/0.99  fof(f27,plain,(
% 2.40/0.99    ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.40/0.99    inference(flattening,[],[f26])).
% 2.40/0.99  
% 2.40/0.99  fof(f73,plain,(
% 2.40/0.99    ( ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.40/0.99    inference(cnf_transformation,[],[f27])).
% 2.40/0.99  
% 2.40/0.99  fof(f4,axiom,(
% 2.40/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.40/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/0.99  
% 2.40/0.99  fof(f52,plain,(
% 2.40/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.40/0.99    inference(nnf_transformation,[],[f4])).
% 2.40/0.99  
% 2.40/0.99  fof(f68,plain,(
% 2.40/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.40/0.99    inference(cnf_transformation,[],[f52])).
% 2.40/0.99  
% 2.40/0.99  fof(f2,axiom,(
% 2.40/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.40/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/0.99  
% 2.40/0.99  fof(f22,plain,(
% 2.40/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.40/0.99    inference(ennf_transformation,[],[f2])).
% 2.40/0.99  
% 2.40/0.99  fof(f46,plain,(
% 2.40/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.40/0.99    inference(nnf_transformation,[],[f22])).
% 2.40/0.99  
% 2.40/0.99  fof(f47,plain,(
% 2.40/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.40/0.99    inference(rectify,[],[f46])).
% 2.40/0.99  
% 2.40/0.99  fof(f48,plain,(
% 2.40/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 2.40/0.99    introduced(choice_axiom,[])).
% 2.40/0.99  
% 2.40/0.99  fof(f49,plain,(
% 2.40/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.40/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f47,f48])).
% 2.40/0.99  
% 2.40/0.99  fof(f62,plain,(
% 2.40/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.40/0.99    inference(cnf_transformation,[],[f49])).
% 2.40/0.99  
% 2.40/0.99  fof(f1,axiom,(
% 2.40/0.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.40/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/0.99  
% 2.40/0.99  fof(f42,plain,(
% 2.40/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.40/0.99    inference(nnf_transformation,[],[f1])).
% 2.40/0.99  
% 2.40/0.99  fof(f43,plain,(
% 2.40/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.40/0.99    inference(rectify,[],[f42])).
% 2.40/0.99  
% 2.40/0.99  fof(f44,plain,(
% 2.40/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.40/0.99    introduced(choice_axiom,[])).
% 2.40/0.99  
% 2.40/0.99  fof(f45,plain,(
% 2.40/0.99    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.40/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f43,f44])).
% 2.40/0.99  
% 2.40/0.99  fof(f60,plain,(
% 2.40/0.99    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.40/0.99    inference(cnf_transformation,[],[f45])).
% 2.40/0.99  
% 2.40/0.99  fof(f90,plain,(
% 2.40/0.99    v2_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK2)))),
% 2.40/0.99    inference(cnf_transformation,[],[f59])).
% 2.40/0.99  
% 2.40/0.99  fof(f10,axiom,(
% 2.40/0.99    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))),
% 2.40/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/0.99  
% 2.40/0.99  fof(f75,plain,(
% 2.40/0.99    ( ! [X0] : (k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))) )),
% 2.40/0.99    inference(cnf_transformation,[],[f10])).
% 2.40/0.99  
% 2.40/0.99  fof(f105,plain,(
% 2.40/0.99    v2_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(sK2))))),
% 2.40/0.99    inference(definition_unfolding,[],[f90,f75])).
% 2.40/0.99  
% 2.40/0.99  fof(f91,plain,(
% 2.40/0.99    v13_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK2)))),
% 2.40/0.99    inference(cnf_transformation,[],[f59])).
% 2.40/0.99  
% 2.40/0.99  fof(f104,plain,(
% 2.40/0.99    v13_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(sK2))))),
% 2.40/0.99    inference(definition_unfolding,[],[f91,f75])).
% 2.40/0.99  
% 2.40/0.99  fof(f13,axiom,(
% 2.40/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v7_waybel_0(k3_yellow19(X0,X1,X2)) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 2.40/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/0.99  
% 2.40/0.99  fof(f19,plain,(
% 2.40/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v7_waybel_0(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 2.40/0.99    inference(pure_predicate_removal,[],[f13])).
% 2.40/0.99  
% 2.40/0.99  fof(f34,plain,(
% 2.40/0.99    ! [X0,X1,X2] : ((v7_waybel_0(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.40/0.99    inference(ennf_transformation,[],[f19])).
% 2.40/0.99  
% 2.40/0.99  fof(f35,plain,(
% 2.40/0.99    ! [X0,X1,X2] : ((v7_waybel_0(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.40/0.99    inference(flattening,[],[f34])).
% 2.40/0.99  
% 2.40/0.99  fof(f81,plain,(
% 2.40/0.99    ( ! [X2,X0,X1] : (v7_waybel_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.40/0.99    inference(cnf_transformation,[],[f35])).
% 2.40/0.99  
% 2.40/0.99  fof(f100,plain,(
% 2.40/0.99    ( ! [X2,X0,X1] : (v7_waybel_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1)))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.40/0.99    inference(definition_unfolding,[],[f81,f75,f75,f75,f75])).
% 2.40/0.99  
% 2.40/0.99  fof(f89,plain,(
% 2.40/0.99    v1_subset_1(sK3,u1_struct_0(k3_yellow_1(k2_struct_0(sK2))))),
% 2.40/0.99    inference(cnf_transformation,[],[f59])).
% 2.40/0.99  
% 2.40/0.99  fof(f106,plain,(
% 2.40/0.99    v1_subset_1(sK3,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))))),
% 2.40/0.99    inference(definition_unfolding,[],[f89,f75])).
% 2.40/0.99  
% 2.40/0.99  fof(f88,plain,(
% 2.40/0.99    ~v1_xboole_0(sK3)),
% 2.40/0.99    inference(cnf_transformation,[],[f59])).
% 2.40/0.99  
% 2.40/0.99  fof(f11,axiom,(
% 2.40/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 2.40/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/0.99  
% 2.40/0.99  fof(f20,plain,(
% 2.40/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 2.40/0.99    inference(pure_predicate_removal,[],[f11])).
% 2.40/0.99  
% 2.40/0.99  fof(f30,plain,(
% 2.40/0.99    ! [X0,X1,X2] : ((l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.40/0.99    inference(ennf_transformation,[],[f20])).
% 2.40/0.99  
% 2.40/0.99  fof(f31,plain,(
% 2.40/0.99    ! [X0,X1,X2] : ((l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.40/0.99    inference(flattening,[],[f30])).
% 2.40/0.99  
% 2.40/0.99  fof(f76,plain,(
% 2.40/0.99    ( ! [X2,X0,X1] : (~v2_struct_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.40/0.99    inference(cnf_transformation,[],[f31])).
% 2.40/0.99  
% 2.40/0.99  fof(f97,plain,(
% 2.40/0.99    ( ! [X2,X0,X1] : (~v2_struct_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.40/0.99    inference(definition_unfolding,[],[f76,f75,f75,f75])).
% 2.40/0.99  
% 2.40/0.99  fof(f12,axiom,(
% 2.40/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & v3_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 2.40/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/0.99  
% 2.40/0.99  fof(f18,plain,(
% 2.40/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 2.40/0.99    inference(pure_predicate_removal,[],[f12])).
% 2.40/0.99  
% 2.40/0.99  fof(f21,plain,(
% 2.40/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 2.40/0.99    inference(pure_predicate_removal,[],[f18])).
% 2.40/0.99  
% 2.40/0.99  fof(f32,plain,(
% 2.40/0.99    ! [X0,X1,X2] : ((v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.40/0.99    inference(ennf_transformation,[],[f21])).
% 2.40/0.99  
% 2.40/0.99  fof(f33,plain,(
% 2.40/0.99    ! [X0,X1,X2] : ((v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.40/0.99    inference(flattening,[],[f32])).
% 2.40/0.99  
% 2.40/0.99  fof(f79,plain,(
% 2.40/0.99    ( ! [X2,X0,X1] : (v4_orders_2(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.40/0.99    inference(cnf_transformation,[],[f33])).
% 2.40/0.99  
% 2.40/0.99  fof(f98,plain,(
% 2.40/0.99    ( ! [X2,X0,X1] : (v4_orders_2(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.40/0.99    inference(definition_unfolding,[],[f79,f75,f75,f75])).
% 2.40/0.99  
% 2.40/0.99  fof(f95,plain,(
% 2.40/0.99    ~r2_waybel_7(sK2,sK3,sK4) | ~r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)))),
% 2.40/0.99    inference(cnf_transformation,[],[f59])).
% 2.40/0.99  
% 2.40/0.99  fof(f14,axiom,(
% 2.40/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k10_yellow_6(X0,X1)) <=> r2_waybel_7(X0,k2_yellow19(X0,X1),X2)))))),
% 2.40/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/0.99  
% 2.40/0.99  fof(f36,plain,(
% 2.40/0.99    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k10_yellow_6(X0,X1)) <=> r2_waybel_7(X0,k2_yellow19(X0,X1),X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.40/0.99    inference(ennf_transformation,[],[f14])).
% 2.40/0.99  
% 2.40/0.99  fof(f37,plain,(
% 2.40/0.99    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k10_yellow_6(X0,X1)) <=> r2_waybel_7(X0,k2_yellow19(X0,X1),X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.40/0.99    inference(flattening,[],[f36])).
% 2.40/0.99  
% 2.40/0.99  fof(f53,plain,(
% 2.40/0.99    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k10_yellow_6(X0,X1)) | ~r2_waybel_7(X0,k2_yellow19(X0,X1),X2)) & (r2_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.40/0.99    inference(nnf_transformation,[],[f37])).
% 2.40/0.99  
% 2.40/0.99  fof(f82,plain,(
% 2.40/0.99    ( ! [X2,X0,X1] : (r2_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.40/0.99    inference(cnf_transformation,[],[f53])).
% 2.40/0.99  
% 2.40/0.99  fof(f77,plain,(
% 2.40/0.99    ( ! [X2,X0,X1] : (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.40/0.99    inference(cnf_transformation,[],[f31])).
% 2.40/0.99  
% 2.40/0.99  fof(f96,plain,(
% 2.40/0.99    ( ! [X2,X0,X1] : (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.40/0.99    inference(definition_unfolding,[],[f77,f75,f75,f75])).
% 2.40/0.99  
% 2.40/0.99  fof(f15,axiom,(
% 2.40/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 2.40/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/0.99  
% 2.40/0.99  fof(f38,plain,(
% 2.40/0.99    ! [X0] : (! [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.40/0.99    inference(ennf_transformation,[],[f15])).
% 2.40/0.99  
% 2.40/0.99  fof(f39,plain,(
% 2.40/0.99    ! [X0] : (! [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.40/0.99    inference(flattening,[],[f38])).
% 2.40/0.99  
% 2.40/0.99  fof(f84,plain,(
% 2.40/0.99    ( ! [X0,X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.40/0.99    inference(cnf_transformation,[],[f39])).
% 2.40/0.99  
% 2.40/0.99  fof(f102,plain,(
% 2.40/0.99    ( ! [X0,X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.40/0.99    inference(definition_unfolding,[],[f84,f75,f75,f75,f75])).
% 2.40/0.99  
% 2.40/0.99  fof(f92,plain,(
% 2.40/0.99    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK2)))))),
% 2.40/0.99    inference(cnf_transformation,[],[f59])).
% 2.40/0.99  
% 2.40/0.99  fof(f103,plain,(
% 2.40/0.99    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))))),
% 2.40/0.99    inference(definition_unfolding,[],[f92,f75])).
% 2.40/0.99  
% 2.40/0.99  fof(f6,axiom,(
% 2.40/0.99    ! [X0] : (l1_struct_0(X0) => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.40/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/0.99  
% 2.40/0.99  fof(f24,plain,(
% 2.40/0.99    ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0))),
% 2.40/0.99    inference(ennf_transformation,[],[f6])).
% 2.40/0.99  
% 2.40/0.99  fof(f71,plain,(
% 2.40/0.99    ( ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0)) )),
% 2.40/0.99    inference(cnf_transformation,[],[f24])).
% 2.40/1.00  
% 2.40/1.00  fof(f94,plain,(
% 2.40/1.00    r2_waybel_7(sK2,sK3,sK4) | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)))),
% 2.40/1.00    inference(cnf_transformation,[],[f59])).
% 2.40/1.00  
% 2.40/1.00  fof(f83,plain,(
% 2.40/1.00    ( ! [X2,X0,X1] : (r2_hidden(X2,k10_yellow_6(X0,X1)) | ~r2_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.40/1.00    inference(cnf_transformation,[],[f53])).
% 2.40/1.00  
% 2.40/1.00  cnf(c_26,negated_conjecture,
% 2.40/1.00      ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
% 2.40/1.00      inference(cnf_transformation,[],[f93]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_3309,plain,
% 2.40/1.00      ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
% 2.40/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_10,plain,
% 2.40/1.00      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.40/1.00      inference(cnf_transformation,[],[f70]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_12,plain,
% 2.40/1.00      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 2.40/1.00      inference(cnf_transformation,[],[f72]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_32,negated_conjecture,
% 2.40/1.00      ( l1_pre_topc(sK2) ),
% 2.40/1.00      inference(cnf_transformation,[],[f87]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_673,plain,
% 2.40/1.00      ( l1_struct_0(X0) | sK2 != X0 ),
% 2.40/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_32]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_674,plain,
% 2.40/1.00      ( l1_struct_0(sK2) ),
% 2.40/1.00      inference(unflattening,[status(thm)],[c_673]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_2167,plain,
% 2.40/1.00      ( u1_struct_0(X0) = k2_struct_0(X0) | sK2 != X0 ),
% 2.40/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_674]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_2168,plain,
% 2.40/1.00      ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
% 2.40/1.00      inference(unflattening,[status(thm)],[c_2167]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_3325,plain,
% 2.40/1.00      ( m1_subset_1(sK4,k2_struct_0(sK2)) = iProver_top ),
% 2.40/1.00      inference(light_normalisation,[status(thm)],[c_3309,c_2168]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_14,plain,
% 2.40/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.40/1.00      | r2_hidden(X0,k1_connsp_2(X1,X0))
% 2.40/1.00      | v2_struct_0(X1)
% 2.40/1.00      | ~ v2_pre_topc(X1)
% 2.40/1.00      | ~ l1_pre_topc(X1) ),
% 2.40/1.00      inference(cnf_transformation,[],[f74]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_33,negated_conjecture,
% 2.40/1.00      ( v2_pre_topc(sK2) ),
% 2.40/1.00      inference(cnf_transformation,[],[f86]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_615,plain,
% 2.40/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.40/1.00      | r2_hidden(X0,k1_connsp_2(X1,X0))
% 2.40/1.00      | v2_struct_0(X1)
% 2.40/1.00      | ~ l1_pre_topc(X1)
% 2.40/1.00      | sK2 != X1 ),
% 2.40/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_33]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_616,plain,
% 2.40/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.40/1.00      | r2_hidden(X0,k1_connsp_2(sK2,X0))
% 2.40/1.00      | v2_struct_0(sK2)
% 2.40/1.00      | ~ l1_pre_topc(sK2) ),
% 2.40/1.00      inference(unflattening,[status(thm)],[c_615]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_34,negated_conjecture,
% 2.40/1.00      ( ~ v2_struct_0(sK2) ),
% 2.40/1.00      inference(cnf_transformation,[],[f85]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_620,plain,
% 2.40/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.40/1.00      | r2_hidden(X0,k1_connsp_2(sK2,X0)) ),
% 2.40/1.00      inference(global_propositional_subsumption,
% 2.40/1.00                [status(thm)],
% 2.40/1.00                [c_616,c_34,c_32]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_3306,plain,
% 2.40/1.00      ( m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 2.40/1.00      | r2_hidden(X0,k1_connsp_2(sK2,X0)) = iProver_top ),
% 2.40/1.00      inference(predicate_to_equality,[status(thm)],[c_620]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_3359,plain,
% 2.40/1.00      ( m1_subset_1(X0,k2_struct_0(sK2)) != iProver_top
% 2.40/1.00      | r2_hidden(X0,k1_connsp_2(sK2,X0)) = iProver_top ),
% 2.40/1.00      inference(light_normalisation,[status(thm)],[c_3306,c_2168]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_13,plain,
% 2.40/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.40/1.00      | m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.40/1.00      | v2_struct_0(X1)
% 2.40/1.00      | ~ v2_pre_topc(X1)
% 2.40/1.00      | ~ l1_pre_topc(X1) ),
% 2.40/1.00      inference(cnf_transformation,[],[f73]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_633,plain,
% 2.40/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.40/1.00      | m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.40/1.00      | v2_struct_0(X1)
% 2.40/1.00      | ~ l1_pre_topc(X1)
% 2.40/1.00      | sK2 != X1 ),
% 2.40/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_33]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_634,plain,
% 2.40/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.40/1.00      | m1_subset_1(k1_connsp_2(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.40/1.00      | v2_struct_0(sK2)
% 2.40/1.00      | ~ l1_pre_topc(sK2) ),
% 2.40/1.00      inference(unflattening,[status(thm)],[c_633]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_638,plain,
% 2.40/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.40/1.00      | m1_subset_1(k1_connsp_2(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.40/1.00      inference(global_propositional_subsumption,
% 2.40/1.00                [status(thm)],
% 2.40/1.00                [c_634,c_34,c_32]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_3305,plain,
% 2.40/1.00      ( m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 2.40/1.00      | m1_subset_1(k1_connsp_2(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 2.40/1.00      inference(predicate_to_equality,[status(thm)],[c_638]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_3364,plain,
% 2.40/1.00      ( m1_subset_1(X0,k2_struct_0(sK2)) != iProver_top
% 2.40/1.00      | m1_subset_1(k1_connsp_2(sK2,X0),k1_zfmisc_1(k2_struct_0(sK2))) = iProver_top ),
% 2.40/1.00      inference(light_normalisation,[status(thm)],[c_3305,c_2168]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_9,plain,
% 2.40/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.40/1.00      inference(cnf_transformation,[],[f68]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_3310,plain,
% 2.40/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.40/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 2.40/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_3676,plain,
% 2.40/1.00      ( m1_subset_1(X0,k2_struct_0(sK2)) != iProver_top
% 2.40/1.00      | r1_tarski(k1_connsp_2(sK2,X0),k2_struct_0(sK2)) = iProver_top ),
% 2.40/1.00      inference(superposition,[status(thm)],[c_3364,c_3310]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_4,plain,
% 2.40/1.00      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 2.40/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_3314,plain,
% 2.40/1.00      ( r1_tarski(X0,X1) != iProver_top
% 2.40/1.00      | r2_hidden(X2,X0) != iProver_top
% 2.40/1.00      | r2_hidden(X2,X1) = iProver_top ),
% 2.40/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_4179,plain,
% 2.40/1.00      ( m1_subset_1(X0,k2_struct_0(sK2)) != iProver_top
% 2.40/1.00      | r2_hidden(X1,k1_connsp_2(sK2,X0)) != iProver_top
% 2.40/1.00      | r2_hidden(X1,k2_struct_0(sK2)) = iProver_top ),
% 2.40/1.00      inference(superposition,[status(thm)],[c_3676,c_3314]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_4757,plain,
% 2.40/1.00      ( m1_subset_1(X0,k2_struct_0(sK2)) != iProver_top
% 2.40/1.00      | r2_hidden(X0,k2_struct_0(sK2)) = iProver_top ),
% 2.40/1.00      inference(superposition,[status(thm)],[c_3359,c_4179]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_4786,plain,
% 2.40/1.00      ( r2_hidden(sK4,k2_struct_0(sK2)) = iProver_top ),
% 2.40/1.00      inference(superposition,[status(thm)],[c_3325,c_4757]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_1,plain,
% 2.40/1.00      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.40/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_3317,plain,
% 2.40/1.00      ( r2_hidden(X0,X1) != iProver_top
% 2.40/1.00      | v1_xboole_0(X1) != iProver_top ),
% 2.40/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_4865,plain,
% 2.40/1.00      ( v1_xboole_0(k2_struct_0(sK2)) != iProver_top ),
% 2.40/1.00      inference(superposition,[status(thm)],[c_4786,c_3317]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_29,negated_conjecture,
% 2.40/1.00      ( v2_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) ),
% 2.40/1.00      inference(cnf_transformation,[],[f105]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_28,negated_conjecture,
% 2.40/1.00      ( v13_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) ),
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
% 2.40/1.00      ( v1_subset_1(sK3,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))) ),
% 2.40/1.00      inference(cnf_transformation,[],[f106]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_459,plain,
% 2.40/1.00      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.40/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.40/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.40/1.00      | v7_waybel_0(k3_yellow19(X2,X1,X0))
% 2.40/1.00      | v2_struct_0(X2)
% 2.40/1.00      | ~ l1_struct_0(X2)
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | v1_xboole_0(X1)
% 2.40/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
% 2.40/1.00      | sK3 != X0 ),
% 2.40/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_30]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_460,plain,
% 2.40/1.00      ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 2.40/1.00      | ~ v13_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 2.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.40/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.40/1.00      | v7_waybel_0(k3_yellow19(X1,X0,sK3))
% 2.40/1.00      | v2_struct_0(X1)
% 2.40/1.00      | ~ l1_struct_0(X1)
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | v1_xboole_0(sK3)
% 2.40/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 2.40/1.00      inference(unflattening,[status(thm)],[c_459]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_31,negated_conjecture,
% 2.40/1.00      ( ~ v1_xboole_0(sK3) ),
% 2.40/1.00      inference(cnf_transformation,[],[f88]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_464,plain,
% 2.40/1.00      ( v1_xboole_0(X0)
% 2.40/1.00      | ~ l1_struct_0(X1)
% 2.40/1.00      | v2_struct_0(X1)
% 2.40/1.00      | v7_waybel_0(k3_yellow19(X1,X0,sK3))
% 2.40/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.40/1.00      | ~ v13_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 2.40/1.00      | ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 2.40/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 2.40/1.00      inference(global_propositional_subsumption,
% 2.40/1.00                [status(thm)],
% 2.40/1.00                [c_460,c_31]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_465,plain,
% 2.40/1.00      ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 2.40/1.00      | ~ v13_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 2.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.40/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.40/1.00      | v7_waybel_0(k3_yellow19(X1,X0,sK3))
% 2.40/1.00      | v2_struct_0(X1)
% 2.40/1.00      | ~ l1_struct_0(X1)
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 2.40/1.00      inference(renaming,[status(thm)],[c_464]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_1460,plain,
% 2.40/1.00      ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 2.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.40/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.40/1.00      | v7_waybel_0(k3_yellow19(X1,X0,sK3))
% 2.40/1.00      | v2_struct_0(X1)
% 2.40/1.00      | ~ l1_struct_0(X1)
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
% 2.40/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 2.40/1.00      | sK3 != sK3 ),
% 2.40/1.00      inference(resolution_lifted,[status(thm)],[c_28,c_465]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_1853,plain,
% 2.40/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.40/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.40/1.00      | v7_waybel_0(k3_yellow19(X1,X0,sK3))
% 2.40/1.00      | v2_struct_0(X1)
% 2.40/1.00      | ~ l1_struct_0(X1)
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
% 2.40/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 2.40/1.00      | sK3 != sK3 ),
% 2.40/1.00      inference(resolution_lifted,[status(thm)],[c_29,c_1460]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_2226,plain,
% 2.40/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.40/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.40/1.00      | v7_waybel_0(k3_yellow19(X1,X0,sK3))
% 2.40/1.00      | v2_struct_0(X1)
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
% 2.40/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 2.40/1.00      | sK3 != sK3
% 2.40/1.00      | sK2 != X1 ),
% 2.40/1.00      inference(resolution_lifted,[status(thm)],[c_1853,c_674]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_2227,plain,
% 2.40/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.40/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.40/1.00      | v7_waybel_0(k3_yellow19(sK2,X0,sK3))
% 2.40/1.00      | v2_struct_0(sK2)
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
% 2.40/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 2.40/1.00      inference(unflattening,[status(thm)],[c_2226]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_2231,plain,
% 2.40/1.00      ( v7_waybel_0(k3_yellow19(sK2,X0,sK3))
% 2.40/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
% 2.40/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 2.40/1.00      inference(global_propositional_subsumption,
% 2.40/1.00                [status(thm)],
% 2.40/1.00                [c_2227,c_34]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_2232,plain,
% 2.40/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.40/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.40/1.00      | v7_waybel_0(k3_yellow19(sK2,X0,sK3))
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
% 2.40/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 2.40/1.00      inference(renaming,[status(thm)],[c_2231]) ).
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
% 2.40/1.00  cnf(c_1388,plain,
% 2.40/1.00      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.40/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.40/1.00      | v2_struct_0(X2)
% 2.40/1.00      | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
% 2.40/1.00      | ~ l1_struct_0(X2)
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | v1_xboole_0(X1)
% 2.40/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X1))
% 2.40/1.00      | sK3 != X0 ),
% 2.40/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_28]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_1389,plain,
% 2.40/1.00      ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 2.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.40/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.40/1.00      | v2_struct_0(X1)
% 2.40/1.00      | ~ v2_struct_0(k3_yellow19(X1,X0,sK3))
% 2.40/1.00      | ~ l1_struct_0(X1)
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | v1_xboole_0(sK3)
% 2.40/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.40/1.00      inference(unflattening,[status(thm)],[c_1388]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_1393,plain,
% 2.40/1.00      ( v1_xboole_0(X0)
% 2.40/1.00      | ~ l1_struct_0(X1)
% 2.40/1.00      | ~ v2_struct_0(k3_yellow19(X1,X0,sK3))
% 2.40/1.00      | v2_struct_0(X1)
% 2.40/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.40/1.00      | ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 2.40/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.40/1.00      inference(global_propositional_subsumption,
% 2.40/1.00                [status(thm)],
% 2.40/1.00                [c_1389,c_31]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_1394,plain,
% 2.40/1.00      ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 2.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.40/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.40/1.00      | v2_struct_0(X1)
% 2.40/1.00      | ~ v2_struct_0(k3_yellow19(X1,X0,sK3))
% 2.40/1.00      | ~ l1_struct_0(X1)
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.40/1.00      inference(renaming,[status(thm)],[c_1393]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_1914,plain,
% 2.40/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.40/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.40/1.00      | v2_struct_0(X1)
% 2.40/1.00      | ~ v2_struct_0(k3_yellow19(X1,X0,sK3))
% 2.40/1.00      | ~ l1_struct_0(X1)
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
% 2.40/1.00      | sK3 != sK3 ),
% 2.40/1.00      inference(resolution_lifted,[status(thm)],[c_29,c_1394]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_2199,plain,
% 2.40/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.40/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.40/1.00      | v2_struct_0(X1)
% 2.40/1.00      | ~ v2_struct_0(k3_yellow19(X1,X0,sK3))
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
% 2.40/1.00      | sK3 != sK3
% 2.40/1.00      | sK2 != X1 ),
% 2.40/1.00      inference(resolution_lifted,[status(thm)],[c_1914,c_674]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_2200,plain,
% 2.40/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.40/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.40/1.00      | ~ v2_struct_0(k3_yellow19(sK2,X0,sK3))
% 2.40/1.00      | v2_struct_0(sK2)
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.40/1.00      inference(unflattening,[status(thm)],[c_2199]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_2204,plain,
% 2.40/1.00      ( ~ v2_struct_0(k3_yellow19(sK2,X0,sK3))
% 2.40/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.40/1.00      inference(global_propositional_subsumption,
% 2.40/1.00                [status(thm)],
% 2.40/1.00                [c_2200,c_34]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_2205,plain,
% 2.40/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.40/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.40/1.00      | ~ v2_struct_0(k3_yellow19(sK2,X0,sK3))
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.40/1.00      inference(renaming,[status(thm)],[c_2204]) ).
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
% 2.40/1.00  cnf(c_1352,plain,
% 2.40/1.00      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.40/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.40/1.00      | v4_orders_2(k3_yellow19(X2,X1,X0))
% 2.40/1.00      | v2_struct_0(X2)
% 2.40/1.00      | ~ l1_struct_0(X2)
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | v1_xboole_0(X1)
% 2.40/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X1))
% 2.40/1.00      | sK3 != X0 ),
% 2.40/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_28]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_1353,plain,
% 2.40/1.00      ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 2.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.40/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.40/1.00      | v4_orders_2(k3_yellow19(X1,X0,sK3))
% 2.40/1.00      | v2_struct_0(X1)
% 2.40/1.00      | ~ l1_struct_0(X1)
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | v1_xboole_0(sK3)
% 2.40/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.40/1.00      inference(unflattening,[status(thm)],[c_1352]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_1357,plain,
% 2.40/1.00      ( v1_xboole_0(X0)
% 2.40/1.00      | ~ l1_struct_0(X1)
% 2.40/1.00      | v2_struct_0(X1)
% 2.40/1.00      | v4_orders_2(k3_yellow19(X1,X0,sK3))
% 2.40/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.40/1.00      | ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 2.40/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.40/1.00      inference(global_propositional_subsumption,
% 2.40/1.00                [status(thm)],
% 2.40/1.00                [c_1353,c_31]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_1358,plain,
% 2.40/1.00      ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 2.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.40/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.40/1.00      | v4_orders_2(k3_yellow19(X1,X0,sK3))
% 2.40/1.00      | v2_struct_0(X1)
% 2.40/1.00      | ~ l1_struct_0(X1)
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.40/1.00      inference(renaming,[status(thm)],[c_1357]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_1943,plain,
% 2.40/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.40/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.40/1.00      | v4_orders_2(k3_yellow19(X1,X0,sK3))
% 2.40/1.00      | v2_struct_0(X1)
% 2.40/1.00      | ~ l1_struct_0(X1)
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
% 2.40/1.00      | sK3 != sK3 ),
% 2.40/1.00      inference(resolution_lifted,[status(thm)],[c_29,c_1358]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_2172,plain,
% 2.40/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.40/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.40/1.00      | v4_orders_2(k3_yellow19(X1,X0,sK3))
% 2.40/1.00      | v2_struct_0(X1)
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
% 2.40/1.00      | sK3 != sK3
% 2.40/1.00      | sK2 != X1 ),
% 2.40/1.00      inference(resolution_lifted,[status(thm)],[c_1943,c_674]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_2173,plain,
% 2.40/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.40/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.40/1.00      | v4_orders_2(k3_yellow19(sK2,X0,sK3))
% 2.40/1.00      | v2_struct_0(sK2)
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.40/1.00      inference(unflattening,[status(thm)],[c_2172]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_2177,plain,
% 2.40/1.00      ( v4_orders_2(k3_yellow19(sK2,X0,sK3))
% 2.40/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.40/1.00      inference(global_propositional_subsumption,
% 2.40/1.00                [status(thm)],
% 2.40/1.00                [c_2173,c_34]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_2178,plain,
% 2.40/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.40/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.40/1.00      | v4_orders_2(k3_yellow19(sK2,X0,sK3))
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.40/1.00      inference(renaming,[status(thm)],[c_2177]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_24,negated_conjecture,
% 2.40/1.00      ( ~ r2_waybel_7(sK2,sK3,sK4)
% 2.40/1.00      | ~ r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3))) ),
% 2.40/1.00      inference(cnf_transformation,[],[f95]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_264,plain,
% 2.40/1.00      ( ~ r2_waybel_7(sK2,sK3,sK4)
% 2.40/1.00      | ~ r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3))) ),
% 2.40/1.00      inference(prop_impl,[status(thm)],[c_24]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_22,plain,
% 2.40/1.00      ( r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 2.40/1.00      | ~ l1_waybel_0(X1,X0)
% 2.40/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.40/1.00      | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
% 2.40/1.00      | ~ v7_waybel_0(X1)
% 2.40/1.00      | ~ v4_orders_2(X1)
% 2.40/1.00      | v2_struct_0(X0)
% 2.40/1.00      | v2_struct_0(X1)
% 2.40/1.00      | ~ v2_pre_topc(X0)
% 2.40/1.00      | ~ l1_pre_topc(X0) ),
% 2.40/1.00      inference(cnf_transformation,[],[f82]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_549,plain,
% 2.40/1.00      ( r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 2.40/1.00      | ~ l1_waybel_0(X1,X0)
% 2.40/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.40/1.00      | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
% 2.40/1.00      | ~ v7_waybel_0(X1)
% 2.40/1.00      | ~ v4_orders_2(X1)
% 2.40/1.00      | v2_struct_0(X0)
% 2.40/1.00      | v2_struct_0(X1)
% 2.40/1.00      | ~ l1_pre_topc(X0)
% 2.40/1.00      | sK2 != X0 ),
% 2.40/1.00      inference(resolution_lifted,[status(thm)],[c_22,c_33]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_550,plain,
% 2.40/1.00      ( r2_waybel_7(sK2,k2_yellow19(sK2,X0),X1)
% 2.40/1.00      | ~ l1_waybel_0(X0,sK2)
% 2.40/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.40/1.00      | ~ r2_hidden(X1,k10_yellow_6(sK2,X0))
% 2.40/1.00      | ~ v7_waybel_0(X0)
% 2.40/1.00      | ~ v4_orders_2(X0)
% 2.40/1.00      | v2_struct_0(X0)
% 2.40/1.00      | v2_struct_0(sK2)
% 2.40/1.00      | ~ l1_pre_topc(sK2) ),
% 2.40/1.00      inference(unflattening,[status(thm)],[c_549]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_554,plain,
% 2.40/1.00      ( r2_waybel_7(sK2,k2_yellow19(sK2,X0),X1)
% 2.40/1.00      | ~ l1_waybel_0(X0,sK2)
% 2.40/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.40/1.00      | ~ r2_hidden(X1,k10_yellow_6(sK2,X0))
% 2.40/1.00      | ~ v7_waybel_0(X0)
% 2.40/1.00      | ~ v4_orders_2(X0)
% 2.40/1.00      | v2_struct_0(X0) ),
% 2.40/1.00      inference(global_propositional_subsumption,
% 2.40/1.00                [status(thm)],
% 2.40/1.00                [c_550,c_34,c_32]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_1009,plain,
% 2.40/1.00      ( ~ l1_waybel_0(X0,sK2)
% 2.40/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.40/1.00      | ~ r2_hidden(X1,k10_yellow_6(sK2,X0))
% 2.40/1.00      | ~ r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)))
% 2.40/1.00      | ~ v7_waybel_0(X0)
% 2.40/1.00      | ~ v4_orders_2(X0)
% 2.40/1.00      | v2_struct_0(X0)
% 2.40/1.00      | k2_yellow19(sK2,X0) != sK3
% 2.40/1.00      | sK4 != X1
% 2.40/1.00      | sK2 != sK2 ),
% 2.40/1.00      inference(resolution_lifted,[status(thm)],[c_264,c_554]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_1010,plain,
% 2.40/1.00      ( ~ l1_waybel_0(X0,sK2)
% 2.40/1.00      | ~ m1_subset_1(sK4,u1_struct_0(sK2))
% 2.40/1.00      | ~ r2_hidden(sK4,k10_yellow_6(sK2,X0))
% 2.40/1.00      | ~ r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)))
% 2.40/1.00      | ~ v7_waybel_0(X0)
% 2.40/1.00      | ~ v4_orders_2(X0)
% 2.40/1.00      | v2_struct_0(X0)
% 2.40/1.00      | k2_yellow19(sK2,X0) != sK3 ),
% 2.40/1.00      inference(unflattening,[status(thm)],[c_1009]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_1014,plain,
% 2.40/1.00      ( ~ l1_waybel_0(X0,sK2)
% 2.40/1.00      | ~ r2_hidden(sK4,k10_yellow_6(sK2,X0))
% 2.40/1.00      | ~ r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)))
% 2.40/1.00      | ~ v7_waybel_0(X0)
% 2.40/1.00      | ~ v4_orders_2(X0)
% 2.40/1.00      | v2_struct_0(X0)
% 2.40/1.00      | k2_yellow19(sK2,X0) != sK3 ),
% 2.40/1.00      inference(global_propositional_subsumption,
% 2.40/1.00                [status(thm)],
% 2.40/1.00                [c_1010,c_26]) ).
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
% 2.40/1.00  cnf(c_1424,plain,
% 2.40/1.00      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.40/1.00      | l1_waybel_0(k3_yellow19(X2,X1,X0),X2)
% 2.40/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.40/1.00      | v2_struct_0(X2)
% 2.40/1.00      | ~ l1_struct_0(X2)
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | v1_xboole_0(X1)
% 2.40/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X1))
% 2.40/1.00      | sK3 != X0 ),
% 2.40/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_28]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_1425,plain,
% 2.40/1.00      ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 2.40/1.00      | l1_waybel_0(k3_yellow19(X1,X0,sK3),X1)
% 2.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.40/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.40/1.00      | v2_struct_0(X1)
% 2.40/1.00      | ~ l1_struct_0(X1)
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | v1_xboole_0(sK3)
% 2.40/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.40/1.00      inference(unflattening,[status(thm)],[c_1424]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_1429,plain,
% 2.40/1.00      ( v1_xboole_0(X0)
% 2.40/1.00      | ~ l1_struct_0(X1)
% 2.40/1.00      | v2_struct_0(X1)
% 2.40/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.40/1.00      | l1_waybel_0(k3_yellow19(X1,X0,sK3),X1)
% 2.40/1.00      | ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 2.40/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.40/1.00      inference(global_propositional_subsumption,
% 2.40/1.00                [status(thm)],
% 2.40/1.00                [c_1425,c_31]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_1430,plain,
% 2.40/1.00      ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 2.40/1.00      | l1_waybel_0(k3_yellow19(X1,X0,sK3),X1)
% 2.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.40/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.40/1.00      | v2_struct_0(X1)
% 2.40/1.00      | ~ l1_struct_0(X1)
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.40/1.00      inference(renaming,[status(thm)],[c_1429]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_1885,plain,
% 2.40/1.00      ( l1_waybel_0(k3_yellow19(X0,X1,sK3),X0)
% 2.40/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.40/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.40/1.00      | v2_struct_0(X0)
% 2.40/1.00      | ~ l1_struct_0(X0)
% 2.40/1.00      | v1_xboole_0(X1)
% 2.40/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X1))
% 2.40/1.00      | sK3 != sK3 ),
% 2.40/1.00      inference(resolution_lifted,[status(thm)],[c_29,c_1430]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_2043,plain,
% 2.40/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.40/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.40/1.00      | ~ r2_hidden(sK4,k10_yellow_6(sK2,X2))
% 2.40/1.00      | ~ r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)))
% 2.40/1.00      | ~ v7_waybel_0(X2)
% 2.40/1.00      | ~ v4_orders_2(X2)
% 2.40/1.00      | v2_struct_0(X2)
% 2.40/1.00      | v2_struct_0(X1)
% 2.40/1.00      | ~ l1_struct_0(X1)
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | k3_yellow19(X1,X0,sK3) != X2
% 2.40/1.00      | k2_yellow19(sK2,X2) != sK3
% 2.40/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
% 2.40/1.00      | sK3 != sK3
% 2.40/1.00      | sK2 != X1 ),
% 2.40/1.00      inference(resolution_lifted,[status(thm)],[c_1014,c_1885]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_2044,plain,
% 2.40/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.40/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.40/1.00      | ~ r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,X0,sK3)))
% 2.40/1.00      | ~ r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)))
% 2.40/1.00      | ~ v7_waybel_0(k3_yellow19(sK2,X0,sK3))
% 2.40/1.00      | ~ v4_orders_2(k3_yellow19(sK2,X0,sK3))
% 2.40/1.00      | v2_struct_0(k3_yellow19(sK2,X0,sK3))
% 2.40/1.00      | v2_struct_0(sK2)
% 2.40/1.00      | ~ l1_struct_0(sK2)
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | k2_yellow19(sK2,k3_yellow19(sK2,X0,sK3)) != sK3
% 2.40/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.40/1.00      inference(unflattening,[status(thm)],[c_2043]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_78,plain,
% 2.40/1.00      ( ~ l1_pre_topc(sK2) | l1_struct_0(sK2) ),
% 2.40/1.00      inference(instantiation,[status(thm)],[c_12]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_2048,plain,
% 2.40/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.40/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.40/1.00      | ~ r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,X0,sK3)))
% 2.40/1.00      | ~ r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)))
% 2.40/1.00      | ~ v7_waybel_0(k3_yellow19(sK2,X0,sK3))
% 2.40/1.00      | ~ v4_orders_2(k3_yellow19(sK2,X0,sK3))
% 2.40/1.00      | v2_struct_0(k3_yellow19(sK2,X0,sK3))
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | k2_yellow19(sK2,k3_yellow19(sK2,X0,sK3)) != sK3
% 2.40/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.40/1.00      inference(global_propositional_subsumption,
% 2.40/1.00                [status(thm)],
% 2.40/1.00                [c_2044,c_34,c_32,c_78]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_2264,plain,
% 2.40/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.40/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.40/1.00      | ~ r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,X0,sK3)))
% 2.40/1.00      | ~ r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)))
% 2.40/1.00      | ~ v7_waybel_0(k3_yellow19(sK2,X0,sK3))
% 2.40/1.00      | v2_struct_0(k3_yellow19(sK2,X0,sK3))
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | k2_yellow19(sK2,k3_yellow19(sK2,X0,sK3)) != sK3
% 2.40/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.40/1.00      inference(backward_subsumption_resolution,
% 2.40/1.00                [status(thm)],
% 2.40/1.00                [c_2178,c_2048]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_2279,plain,
% 2.40/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.40/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.40/1.00      | ~ r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,X0,sK3)))
% 2.40/1.00      | ~ r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)))
% 2.40/1.00      | ~ v7_waybel_0(k3_yellow19(sK2,X0,sK3))
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | k2_yellow19(sK2,k3_yellow19(sK2,X0,sK3)) != sK3
% 2.40/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.40/1.00      inference(backward_subsumption_resolution,
% 2.40/1.00                [status(thm)],
% 2.40/1.00                [c_2205,c_2264]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_2296,plain,
% 2.40/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.40/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.40/1.00      | ~ r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,X0,sK3)))
% 2.40/1.00      | ~ r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)))
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | k2_yellow19(sK2,k3_yellow19(sK2,X0,sK3)) != sK3
% 2.40/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
% 2.40/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 2.40/1.00      inference(resolution,[status(thm)],[c_2232,c_2279]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_3303,plain,
% 2.40/1.00      ( k2_yellow19(sK2,k3_yellow19(sK2,X0,sK3)) != sK3
% 2.40/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
% 2.40/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 2.40/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.40/1.00      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
% 2.40/1.00      | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,X0,sK3))) != iProver_top
% 2.40/1.00      | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3))) != iProver_top
% 2.40/1.00      | v1_xboole_0(X0) = iProver_top ),
% 2.40/1.00      inference(predicate_to_equality,[status(thm)],[c_2296]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_3398,plain,
% 2.40/1.00      ( k2_yellow19(sK2,k3_yellow19(sK2,X0,sK3)) != sK3
% 2.40/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
% 2.40/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 2.40/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 2.40/1.00      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
% 2.40/1.00      | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,X0,sK3))) != iProver_top
% 2.40/1.00      | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3))) != iProver_top
% 2.40/1.00      | v1_xboole_0(X0) = iProver_top ),
% 2.40/1.00      inference(light_normalisation,[status(thm)],[c_3303,c_2168]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_3932,plain,
% 2.40/1.00      ( k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)) != sK3
% 2.40/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(k2_struct_0(sK2)))
% 2.40/1.00      | m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 2.40/1.00      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))))) != iProver_top
% 2.40/1.00      | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3))) != iProver_top
% 2.40/1.00      | v1_xboole_0(k2_struct_0(sK2)) = iProver_top ),
% 2.40/1.00      inference(equality_resolution,[status(thm)],[c_3398]) ).
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
% 2.40/1.00  cnf(c_498,plain,
% 2.40/1.00      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 2.40/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 2.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
% 2.40/1.00      | v2_struct_0(X1)
% 2.40/1.00      | ~ l1_struct_0(X1)
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0
% 2.40/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))
% 2.40/1.00      | sK3 != X0 ),
% 2.40/1.00      inference(resolution_lifted,[status(thm)],[c_23,c_30]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_499,plain,
% 2.40/1.00      ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 2.40/1.00      | ~ v13_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 2.40/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 2.40/1.00      | v2_struct_0(X0)
% 2.40/1.00      | ~ l1_struct_0(X0)
% 2.40/1.00      | v1_xboole_0(sK3)
% 2.40/1.00      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK3)) = sK3
% 2.40/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) ),
% 2.40/1.00      inference(unflattening,[status(thm)],[c_498]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_503,plain,
% 2.40/1.00      ( ~ l1_struct_0(X0)
% 2.40/1.00      | v2_struct_0(X0)
% 2.40/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 2.40/1.00      | ~ v13_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 2.40/1.00      | ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 2.40/1.00      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK3)) = sK3
% 2.40/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) ),
% 2.40/1.00      inference(global_propositional_subsumption,
% 2.40/1.00                [status(thm)],
% 2.40/1.00                [c_499,c_31]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_504,plain,
% 2.40/1.00      ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 2.40/1.00      | ~ v13_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 2.40/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 2.40/1.00      | v2_struct_0(X0)
% 2.40/1.00      | ~ l1_struct_0(X0)
% 2.40/1.00      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK3)) = sK3
% 2.40/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) ),
% 2.40/1.00      inference(renaming,[status(thm)],[c_503]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_1495,plain,
% 2.40/1.00      ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 2.40/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 2.40/1.00      | v2_struct_0(X0)
% 2.40/1.00      | ~ l1_struct_0(X0)
% 2.40/1.00      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK3)) = sK3
% 2.40/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(X0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK2)))
% 2.40/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))
% 2.40/1.00      | sK3 != sK3 ),
% 2.40/1.00      inference(resolution_lifted,[status(thm)],[c_28,c_504]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_1972,plain,
% 2.40/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 2.40/1.00      | v2_struct_0(X0)
% 2.40/1.00      | ~ l1_struct_0(X0)
% 2.40/1.00      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK3)) = sK3
% 2.40/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(X0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK2)))
% 2.40/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))
% 2.40/1.00      | sK3 != sK3 ),
% 2.40/1.00      inference(resolution_lifted,[status(thm)],[c_29,c_1495]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_2149,plain,
% 2.40/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 2.40/1.00      | v2_struct_0(X0)
% 2.40/1.00      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK3)) = sK3
% 2.40/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(X0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK2)))
% 2.40/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))
% 2.40/1.00      | sK3 != sK3
% 2.40/1.00      | sK2 != X0 ),
% 2.40/1.00      inference(resolution_lifted,[status(thm)],[c_1972,c_674]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_2150,plain,
% 2.40/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))))
% 2.40/1.00      | v2_struct_0(sK2)
% 2.40/1.00      | k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)) = sK3
% 2.40/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(k2_struct_0(sK2)))
% 2.40/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) ),
% 2.40/1.00      inference(unflattening,[status(thm)],[c_2149]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_27,negated_conjecture,
% 2.40/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))))) ),
% 2.40/1.00      inference(cnf_transformation,[],[f103]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_506,plain,
% 2.40/1.00      ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(sK2))))
% 2.40/1.00      | ~ v13_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(sK2))))
% 2.40/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))))
% 2.40/1.00      | v2_struct_0(sK2)
% 2.40/1.00      | ~ l1_struct_0(sK2)
% 2.40/1.00      | k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)) = sK3
% 2.40/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) ),
% 2.40/1.00      inference(instantiation,[status(thm)],[c_504]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_2152,plain,
% 2.40/1.00      ( k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)) = sK3
% 2.40/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) ),
% 2.40/1.00      inference(global_propositional_subsumption,
% 2.40/1.00                [status(thm)],
% 2.40/1.00                [c_2150,c_34,c_32,c_29,c_28,c_27,c_78,c_506]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_2554,plain,
% 2.40/1.00      ( k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)) = sK3 ),
% 2.40/1.00      inference(equality_resolution_simp,[status(thm)],[c_2152]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_3933,plain,
% 2.40/1.00      ( k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(k2_struct_0(sK2)))
% 2.40/1.00      | sK3 != sK3
% 2.40/1.00      | m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 2.40/1.00      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))))) != iProver_top
% 2.40/1.00      | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3))) != iProver_top
% 2.40/1.00      | v1_xboole_0(k2_struct_0(sK2)) = iProver_top ),
% 2.40/1.00      inference(light_normalisation,[status(thm)],[c_3932,c_2554]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_3934,plain,
% 2.40/1.00      ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 2.40/1.00      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))))) != iProver_top
% 2.40/1.00      | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3))) != iProver_top
% 2.40/1.00      | v1_xboole_0(k2_struct_0(sK2)) = iProver_top ),
% 2.40/1.00      inference(equality_resolution_simp,[status(thm)],[c_3933]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_42,plain,
% 2.40/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))))) = iProver_top ),
% 2.40/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_11,plain,
% 2.40/1.00      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 2.40/1.00      | ~ l1_struct_0(X0) ),
% 2.40/1.00      inference(cnf_transformation,[],[f71]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_2160,plain,
% 2.40/1.00      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 2.40/1.00      | sK2 != X0 ),
% 2.40/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_674]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_2161,plain,
% 2.40/1.00      ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.40/1.00      inference(unflattening,[status(thm)],[c_2160]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_3304,plain,
% 2.40/1.00      ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 2.40/1.00      inference(predicate_to_equality,[status(thm)],[c_2161]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_3328,plain,
% 2.40/1.00      ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) = iProver_top ),
% 2.40/1.00      inference(light_normalisation,[status(thm)],[c_3304,c_2168]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_25,negated_conjecture,
% 2.40/1.00      ( r2_waybel_7(sK2,sK3,sK4)
% 2.40/1.00      | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3))) ),
% 2.40/1.00      inference(cnf_transformation,[],[f94]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_266,plain,
% 2.40/1.00      ( r2_waybel_7(sK2,sK3,sK4)
% 2.40/1.00      | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3))) ),
% 2.40/1.00      inference(prop_impl,[status(thm)],[c_25]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_21,plain,
% 2.40/1.00      ( ~ r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 2.40/1.00      | ~ l1_waybel_0(X1,X0)
% 2.40/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.40/1.00      | r2_hidden(X2,k10_yellow_6(X0,X1))
% 2.40/1.00      | ~ v7_waybel_0(X1)
% 2.40/1.00      | ~ v4_orders_2(X1)
% 2.40/1.00      | v2_struct_0(X0)
% 2.40/1.00      | v2_struct_0(X1)
% 2.40/1.00      | ~ v2_pre_topc(X0)
% 2.40/1.00      | ~ l1_pre_topc(X0) ),
% 2.40/1.00      inference(cnf_transformation,[],[f83]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_582,plain,
% 2.40/1.00      ( ~ r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 2.40/1.00      | ~ l1_waybel_0(X1,X0)
% 2.40/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.40/1.00      | r2_hidden(X2,k10_yellow_6(X0,X1))
% 2.40/1.00      | ~ v7_waybel_0(X1)
% 2.40/1.00      | ~ v4_orders_2(X1)
% 2.40/1.00      | v2_struct_0(X0)
% 2.40/1.00      | v2_struct_0(X1)
% 2.40/1.00      | ~ l1_pre_topc(X0)
% 2.40/1.00      | sK2 != X0 ),
% 2.40/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_33]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_583,plain,
% 2.40/1.00      ( ~ r2_waybel_7(sK2,k2_yellow19(sK2,X0),X1)
% 2.40/1.00      | ~ l1_waybel_0(X0,sK2)
% 2.40/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.40/1.00      | r2_hidden(X1,k10_yellow_6(sK2,X0))
% 2.40/1.00      | ~ v7_waybel_0(X0)
% 2.40/1.00      | ~ v4_orders_2(X0)
% 2.40/1.00      | v2_struct_0(X0)
% 2.40/1.00      | v2_struct_0(sK2)
% 2.40/1.00      | ~ l1_pre_topc(sK2) ),
% 2.40/1.00      inference(unflattening,[status(thm)],[c_582]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_587,plain,
% 2.40/1.00      ( ~ r2_waybel_7(sK2,k2_yellow19(sK2,X0),X1)
% 2.40/1.00      | ~ l1_waybel_0(X0,sK2)
% 2.40/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.40/1.00      | r2_hidden(X1,k10_yellow_6(sK2,X0))
% 2.40/1.00      | ~ v7_waybel_0(X0)
% 2.40/1.00      | ~ v4_orders_2(X0)
% 2.40/1.00      | v2_struct_0(X0) ),
% 2.40/1.00      inference(global_propositional_subsumption,
% 2.40/1.00                [status(thm)],
% 2.40/1.00                [c_583,c_34,c_32]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_976,plain,
% 2.40/1.00      ( ~ l1_waybel_0(X0,sK2)
% 2.40/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.40/1.00      | r2_hidden(X1,k10_yellow_6(sK2,X0))
% 2.40/1.00      | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)))
% 2.40/1.00      | ~ v7_waybel_0(X0)
% 2.40/1.00      | ~ v4_orders_2(X0)
% 2.40/1.00      | v2_struct_0(X0)
% 2.40/1.00      | k2_yellow19(sK2,X0) != sK3
% 2.40/1.00      | sK4 != X1
% 2.40/1.00      | sK2 != sK2 ),
% 2.40/1.00      inference(resolution_lifted,[status(thm)],[c_266,c_587]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_977,plain,
% 2.40/1.00      ( ~ l1_waybel_0(X0,sK2)
% 2.40/1.00      | ~ m1_subset_1(sK4,u1_struct_0(sK2))
% 2.40/1.00      | r2_hidden(sK4,k10_yellow_6(sK2,X0))
% 2.40/1.00      | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)))
% 2.40/1.00      | ~ v7_waybel_0(X0)
% 2.40/1.00      | ~ v4_orders_2(X0)
% 2.40/1.00      | v2_struct_0(X0)
% 2.40/1.00      | k2_yellow19(sK2,X0) != sK3 ),
% 2.40/1.00      inference(unflattening,[status(thm)],[c_976]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_981,plain,
% 2.40/1.00      ( ~ l1_waybel_0(X0,sK2)
% 2.40/1.00      | r2_hidden(sK4,k10_yellow_6(sK2,X0))
% 2.40/1.00      | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)))
% 2.40/1.00      | ~ v7_waybel_0(X0)
% 2.40/1.00      | ~ v4_orders_2(X0)
% 2.40/1.00      | v2_struct_0(X0)
% 2.40/1.00      | k2_yellow19(sK2,X0) != sK3 ),
% 2.40/1.00      inference(global_propositional_subsumption,
% 2.40/1.00                [status(thm)],
% 2.40/1.00                [c_977,c_26]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_2085,plain,
% 2.40/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.40/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.40/1.00      | r2_hidden(sK4,k10_yellow_6(sK2,X2))
% 2.40/1.00      | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)))
% 2.40/1.00      | ~ v7_waybel_0(X2)
% 2.40/1.00      | ~ v4_orders_2(X2)
% 2.40/1.00      | v2_struct_0(X2)
% 2.40/1.00      | v2_struct_0(X1)
% 2.40/1.00      | ~ l1_struct_0(X1)
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | k3_yellow19(X1,X0,sK3) != X2
% 2.40/1.00      | k2_yellow19(sK2,X2) != sK3
% 2.40/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
% 2.40/1.00      | sK3 != sK3
% 2.40/1.00      | sK2 != X1 ),
% 2.40/1.00      inference(resolution_lifted,[status(thm)],[c_981,c_1885]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_2086,plain,
% 2.40/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.40/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.40/1.00      | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,X0,sK3)))
% 2.40/1.00      | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)))
% 2.40/1.00      | ~ v7_waybel_0(k3_yellow19(sK2,X0,sK3))
% 2.40/1.00      | ~ v4_orders_2(k3_yellow19(sK2,X0,sK3))
% 2.40/1.00      | v2_struct_0(k3_yellow19(sK2,X0,sK3))
% 2.40/1.00      | v2_struct_0(sK2)
% 2.40/1.00      | ~ l1_struct_0(sK2)
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | k2_yellow19(sK2,k3_yellow19(sK2,X0,sK3)) != sK3
% 2.40/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.40/1.00      inference(unflattening,[status(thm)],[c_2085]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_2090,plain,
% 2.40/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.40/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.40/1.00      | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,X0,sK3)))
% 2.40/1.00      | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)))
% 2.40/1.00      | ~ v7_waybel_0(k3_yellow19(sK2,X0,sK3))
% 2.40/1.00      | ~ v4_orders_2(k3_yellow19(sK2,X0,sK3))
% 2.40/1.00      | v2_struct_0(k3_yellow19(sK2,X0,sK3))
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | k2_yellow19(sK2,k3_yellow19(sK2,X0,sK3)) != sK3
% 2.40/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.40/1.00      inference(global_propositional_subsumption,
% 2.40/1.00                [status(thm)],
% 2.40/1.00                [c_2086,c_34,c_32,c_78]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_2265,plain,
% 2.40/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.40/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.40/1.00      | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,X0,sK3)))
% 2.40/1.00      | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)))
% 2.40/1.00      | ~ v7_waybel_0(k3_yellow19(sK2,X0,sK3))
% 2.40/1.00      | v2_struct_0(k3_yellow19(sK2,X0,sK3))
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | k2_yellow19(sK2,k3_yellow19(sK2,X0,sK3)) != sK3
% 2.40/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.40/1.00      inference(backward_subsumption_resolution,
% 2.40/1.00                [status(thm)],
% 2.40/1.00                [c_2178,c_2090]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_2278,plain,
% 2.40/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.40/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.40/1.00      | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,X0,sK3)))
% 2.40/1.00      | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)))
% 2.40/1.00      | ~ v7_waybel_0(k3_yellow19(sK2,X0,sK3))
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | k2_yellow19(sK2,k3_yellow19(sK2,X0,sK3)) != sK3
% 2.40/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.40/1.00      inference(backward_subsumption_resolution,
% 2.40/1.00                [status(thm)],
% 2.40/1.00                [c_2205,c_2265]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_2325,plain,
% 2.40/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.40/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.40/1.00      | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,X0,sK3)))
% 2.40/1.00      | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)))
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | k2_yellow19(sK2,k3_yellow19(sK2,X0,sK3)) != sK3
% 2.40/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
% 2.40/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 2.40/1.00      inference(resolution,[status(thm)],[c_2232,c_2278]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_3302,plain,
% 2.40/1.00      ( k2_yellow19(sK2,k3_yellow19(sK2,X0,sK3)) != sK3
% 2.40/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
% 2.40/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 2.40/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.40/1.00      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
% 2.40/1.00      | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,X0,sK3))) = iProver_top
% 2.40/1.00      | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3))) = iProver_top
% 2.40/1.00      | v1_xboole_0(X0) = iProver_top ),
% 2.40/1.00      inference(predicate_to_equality,[status(thm)],[c_2325]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_3381,plain,
% 2.40/1.00      ( k2_yellow19(sK2,k3_yellow19(sK2,X0,sK3)) != sK3
% 2.40/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
% 2.40/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 2.40/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 2.40/1.00      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
% 2.40/1.00      | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,X0,sK3))) = iProver_top
% 2.40/1.00      | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3))) = iProver_top
% 2.40/1.00      | v1_xboole_0(X0) = iProver_top ),
% 2.40/1.00      inference(light_normalisation,[status(thm)],[c_3302,c_2168]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_3945,plain,
% 2.40/1.00      ( k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)) != sK3
% 2.40/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(k2_struct_0(sK2)))
% 2.40/1.00      | m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 2.40/1.00      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))))) != iProver_top
% 2.40/1.00      | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3))) = iProver_top
% 2.40/1.00      | v1_xboole_0(k2_struct_0(sK2)) = iProver_top ),
% 2.40/1.00      inference(equality_resolution,[status(thm)],[c_3381]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_3946,plain,
% 2.40/1.00      ( k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(k2_struct_0(sK2)))
% 2.40/1.00      | sK3 != sK3
% 2.40/1.00      | m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 2.40/1.00      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))))) != iProver_top
% 2.40/1.00      | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3))) = iProver_top
% 2.40/1.00      | v1_xboole_0(k2_struct_0(sK2)) = iProver_top ),
% 2.40/1.00      inference(light_normalisation,[status(thm)],[c_3945,c_2554]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_3947,plain,
% 2.40/1.00      ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 2.40/1.00      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))))) != iProver_top
% 2.40/1.00      | r2_hidden(sK4,k10_yellow_6(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3))) = iProver_top
% 2.40/1.00      | v1_xboole_0(k2_struct_0(sK2)) = iProver_top ),
% 2.40/1.00      inference(equality_resolution_simp,[status(thm)],[c_3946]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_4107,plain,
% 2.40/1.00      ( v1_xboole_0(k2_struct_0(sK2)) = iProver_top ),
% 2.40/1.00      inference(global_propositional_subsumption,
% 2.40/1.00                [status(thm)],
% 2.40/1.00                [c_3934,c_42,c_3328,c_3947]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(contradiction,plain,
% 2.40/1.00      ( $false ),
% 2.40/1.00      inference(minisat,[status(thm)],[c_4865,c_4107]) ).
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
% 2.40/1.00  parsing_time:                           0.026
% 2.40/1.00  unif_index_cands_time:                  0.
% 2.40/1.00  unif_index_add_time:                    0.
% 2.40/1.00  orderings_time:                         0.
% 2.40/1.00  out_proof_time:                         0.016
% 2.40/1.00  total_time:                             0.187
% 2.40/1.00  num_of_symbols:                         60
% 2.40/1.00  num_of_terms:                           2858
% 2.40/1.00  
% 2.40/1.00  ------ Preprocessing
% 2.40/1.00  
% 2.40/1.00  num_of_splits:                          0
% 2.40/1.00  num_of_split_atoms:                     0
% 2.40/1.00  num_of_reused_defs:                     0
% 2.40/1.00  num_eq_ax_congr_red:                    22
% 2.40/1.00  num_of_sem_filtered_clauses:            1
% 2.40/1.00  num_of_subtypes:                        0
% 2.40/1.00  monotx_restored_types:                  0
% 2.40/1.00  sat_num_of_epr_types:                   0
% 2.40/1.00  sat_num_of_non_cyclic_types:            0
% 2.40/1.00  sat_guarded_non_collapsed_types:        0
% 2.40/1.00  num_pure_diseq_elim:                    0
% 2.40/1.00  simp_replaced_by:                       0
% 2.40/1.00  res_preprocessed:                       118
% 2.40/1.00  prep_upred:                             0
% 2.40/1.00  prep_unflattend:                        58
% 2.40/1.00  smt_new_axioms:                         0
% 2.40/1.00  pred_elim_cands:                        4
% 2.40/1.00  pred_elim:                              11
% 2.40/1.00  pred_elim_cl:                           13
% 2.40/1.00  pred_elim_cycles:                       22
% 2.40/1.00  merged_defs:                            10
% 2.40/1.00  merged_defs_ncl:                        0
% 2.40/1.00  bin_hyper_res:                          10
% 2.40/1.00  prep_cycles:                            4
% 2.40/1.00  pred_elim_time:                         0.07
% 2.40/1.00  splitting_time:                         0.
% 2.40/1.00  sem_filter_time:                        0.
% 2.40/1.00  monotx_time:                            0.001
% 2.40/1.00  subtype_inf_time:                       0.
% 2.40/1.00  
% 2.40/1.00  ------ Problem properties
% 2.40/1.00  
% 2.40/1.00  clauses:                                19
% 2.40/1.00  conjectures:                            3
% 2.40/1.00  epr:                                    5
% 2.40/1.00  horn:                                   16
% 2.40/1.00  ground:                                 6
% 2.40/1.00  unary:                                  7
% 2.40/1.00  binary:                                 8
% 2.40/1.00  lits:                                   45
% 2.40/1.00  lits_eq:                                9
% 2.40/1.00  fd_pure:                                0
% 2.40/1.00  fd_pseudo:                              0
% 2.40/1.00  fd_cond:                                0
% 2.40/1.00  fd_pseudo_cond:                         1
% 2.40/1.00  ac_symbols:                             0
% 2.40/1.00  
% 2.40/1.00  ------ Propositional Solver
% 2.40/1.00  
% 2.40/1.00  prop_solver_calls:                      27
% 2.40/1.00  prop_fast_solver_calls:                 1530
% 2.40/1.00  smt_solver_calls:                       0
% 2.40/1.00  smt_fast_solver_calls:                  0
% 2.40/1.00  prop_num_of_clauses:                    1207
% 2.40/1.00  prop_preprocess_simplified:             4191
% 2.40/1.00  prop_fo_subsumed:                       49
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
% 2.40/1.00  inst_num_of_clauses:                    275
% 2.40/1.00  inst_num_in_passive:                    127
% 2.40/1.00  inst_num_in_active:                     142
% 2.40/1.00  inst_num_in_unprocessed:                8
% 2.40/1.00  inst_num_of_loops:                      170
% 2.40/1.00  inst_num_of_learning_restarts:          0
% 2.40/1.00  inst_num_moves_active_passive:          24
% 2.40/1.00  inst_lit_activity:                      0
% 2.40/1.00  inst_lit_activity_moves:                0
% 2.40/1.00  inst_num_tautologies:                   0
% 2.40/1.00  inst_num_prop_implied:                  0
% 2.40/1.00  inst_num_existing_simplified:           0
% 2.40/1.00  inst_num_eq_res_simplified:             0
% 2.40/1.00  inst_num_child_elim:                    0
% 2.40/1.00  inst_num_of_dismatching_blockings:      43
% 2.40/1.00  inst_num_of_non_proper_insts:           211
% 2.40/1.00  inst_num_of_duplicates:                 0
% 2.40/1.00  inst_inst_num_from_inst_to_res:         0
% 2.40/1.00  inst_dismatching_checking_time:         0.
% 2.40/1.00  
% 2.40/1.00  ------ Resolution
% 2.40/1.00  
% 2.40/1.00  res_num_of_clauses:                     0
% 2.40/1.00  res_num_in_passive:                     0
% 2.40/1.00  res_num_in_active:                      0
% 2.40/1.00  res_num_of_loops:                       122
% 2.40/1.00  res_forward_subset_subsumed:            18
% 2.40/1.00  res_backward_subset_subsumed:           4
% 2.40/1.00  res_forward_subsumed:                   0
% 2.40/1.00  res_backward_subsumed:                  0
% 2.40/1.00  res_forward_subsumption_resolution:     2
% 2.40/1.00  res_backward_subsumption_resolution:    4
% 2.40/1.00  res_clause_to_clause_subsumption:       216
% 2.40/1.00  res_orphan_elimination:                 0
% 2.40/1.00  res_tautology_del:                      47
% 2.40/1.00  res_num_eq_res_simplified:              1
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
% 2.40/1.00  sup_num_of_clauses:                     41
% 2.40/1.00  sup_num_in_active:                      33
% 2.40/1.00  sup_num_in_passive:                     8
% 2.40/1.00  sup_num_of_loops:                       32
% 2.40/1.00  sup_fw_superposition:                   19
% 2.40/1.00  sup_bw_superposition:                   7
% 2.40/1.00  sup_immediate_simplified:               3
% 2.40/1.00  sup_given_eliminated:                   0
% 2.40/1.00  comparisons_done:                       0
% 2.40/1.00  comparisons_avoided:                    0
% 2.40/1.00  
% 2.40/1.00  ------ Simplifications
% 2.40/1.00  
% 2.40/1.00  
% 2.40/1.00  sim_fw_subset_subsumed:                 0
% 2.40/1.00  sim_bw_subset_subsumed:                 0
% 2.40/1.00  sim_fw_subsumed:                        2
% 2.40/1.00  sim_bw_subsumed:                        0
% 2.40/1.00  sim_fw_subsumption_res:                 0
% 2.40/1.00  sim_bw_subsumption_res:                 0
% 2.40/1.00  sim_tautology_del:                      2
% 2.40/1.00  sim_eq_tautology_del:                   1
% 2.40/1.00  sim_eq_res_simp:                        2
% 2.40/1.00  sim_fw_demodulated:                     0
% 2.40/1.00  sim_bw_demodulated:                     0
% 2.40/1.00  sim_light_normalised:                   8
% 2.40/1.00  sim_joinable_taut:                      0
% 2.40/1.00  sim_joinable_simp:                      0
% 2.40/1.00  sim_ac_normalised:                      0
% 2.40/1.00  sim_smt_subsumption:                    0
% 2.40/1.00  
%------------------------------------------------------------------------------
