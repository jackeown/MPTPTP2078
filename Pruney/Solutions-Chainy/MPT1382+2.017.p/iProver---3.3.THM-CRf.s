%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:18:18 EST 2020

% Result     : Theorem 2.94s
% Output     : CNFRefutation 2.94s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 726 expanded)
%              Number of clauses        :  102 ( 200 expanded)
%              Number of leaves         :   16 ( 216 expanded)
%              Depth                    :   18
%              Number of atoms          :  649 (6268 expanded)
%              Number of equality atoms :  102 ( 150 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f33])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ~ ( ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                        & ~ v1_xboole_0(X3) )
                     => ~ ( r1_tarski(X3,X2)
                          & v3_pre_topc(X3,X0)
                          & m1_connsp_2(X3,X0,X1) ) )
                  & m1_connsp_2(X2,X0,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( ! [X3] :
                        ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                          & ~ v1_xboole_0(X3) )
                       => ~ ( r1_tarski(X3,X2)
                            & v3_pre_topc(X3,X0)
                            & m1_connsp_2(X3,X0,X1) ) )
                    & m1_connsp_2(X2,X0,X1) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r1_tarski(X3,X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_connsp_2(X3,X0,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  | v1_xboole_0(X3) )
              & m1_connsp_2(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r1_tarski(X3,X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_connsp_2(X3,X0,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  | v1_xboole_0(X3) )
              & m1_connsp_2(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r1_tarski(X3,X2)
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_connsp_2(X3,X0,X1)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
              | v1_xboole_0(X3) )
          & m1_connsp_2(X2,X0,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ! [X3] :
            ( ~ r1_tarski(X3,sK4)
            | ~ v3_pre_topc(X3,X0)
            | ~ m1_connsp_2(X3,X0,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
            | v1_xboole_0(X3) )
        & m1_connsp_2(sK4,X0,X1)
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r1_tarski(X3,X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_connsp_2(X3,X0,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  | v1_xboole_0(X3) )
              & m1_connsp_2(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ! [X3] :
                ( ~ r1_tarski(X3,X2)
                | ~ v3_pre_topc(X3,X0)
                | ~ m1_connsp_2(X3,X0,sK3)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                | v1_xboole_0(X3) )
            & m1_connsp_2(X2,X0,sK3)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ! [X3] :
                    ( ~ r1_tarski(X3,X2)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_connsp_2(X3,X0,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                    | v1_xboole_0(X3) )
                & m1_connsp_2(X2,X0,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r1_tarski(X3,X2)
                  | ~ v3_pre_topc(X3,sK2)
                  | ~ m1_connsp_2(X3,sK2,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
                  | v1_xboole_0(X3) )
              & m1_connsp_2(X2,sK2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
          & m1_subset_1(X1,u1_struct_0(sK2)) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ! [X3] :
        ( ~ r1_tarski(X3,sK4)
        | ~ v3_pre_topc(X3,sK2)
        | ~ m1_connsp_2(X3,sK2,sK3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
        | v1_xboole_0(X3) )
    & m1_connsp_2(sK4,sK2,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f32,f45,f44,f43])).

fof(f71,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f46])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ~ r2_hidden(X1,k1_tops_1(X0,X2)) )
                & ( r2_hidden(X1,k1_tops_1(X0,X2))
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f67,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f68,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f69,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( m1_connsp_2(X1,X0,X2)
               => r2_hidden(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,X1)
              | ~ m1_connsp_2(X1,X0,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,X1)
              | ~ m1_connsp_2(X1,X0,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ m1_connsp_2(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f72,plain,(
    m1_connsp_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f70,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f46])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f73,plain,(
    ! [X3] :
      ( ~ r1_tarski(X3,sK4)
      | ~ v3_pre_topc(X3,sK2)
      | ~ m1_connsp_2(X3,sK2,sK3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
      | v1_xboole_0(X3) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( k1_tops_1(X0,X2) = X2
                     => v3_pre_topc(X2,X0) )
                    & ( v3_pre_topc(X3,X1)
                     => k1_tops_1(X1,X3) = X3 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_3335,plain,
    ( r2_hidden(sK0(X0_45,X1_45),X0_45)
    | r1_tarski(X0_45,X1_45) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_3966,plain,
    ( r2_hidden(sK0(X0_45,X1_45),X0_45) = iProver_top
    | r1_tarski(X0_45,X1_45) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3335])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_3330,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_3971,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3330])).

cnf(c_17,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_441,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_26])).

cnf(c_442,plain,
    ( m1_connsp_2(X0,sK2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1,k1_tops_1(sK2,X0))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_441])).

cnf(c_25,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_446,plain,
    ( m1_connsp_2(X0,sK2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1,k1_tops_1(sK2,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_442,c_25,c_24])).

cnf(c_19,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_393,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_26])).

cnf(c_394,plain,
    ( ~ m1_connsp_2(X0,sK2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(X1,X0)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_393])).

cnf(c_398,plain,
    ( ~ m1_connsp_2(X0,sK2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_394,c_25,c_24])).

cnf(c_481,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_tops_1(sK2,X1)) ),
    inference(resolution,[status(thm)],[c_446,c_398])).

cnf(c_3327,plain,
    ( ~ m1_subset_1(X0_45,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_45,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(X0_45,X1_45)
    | ~ r2_hidden(X0_45,k1_tops_1(sK2,X1_45)) ),
    inference(subtyping,[status(esa)],[c_481])).

cnf(c_3974,plain,
    ( m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_45,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(X0_45,X1_45) = iProver_top
    | r2_hidden(X0_45,k1_tops_1(sK2,X1_45)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3327])).

cnf(c_3382,plain,
    ( m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_45,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(X0_45,X1_45) = iProver_top
    | r2_hidden(X0_45,k1_tops_1(sK2,X1_45)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3327])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_873,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_24])).

cnf(c_874,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(k1_tops_1(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unflattening,[status(thm)],[c_873])).

cnf(c_3316,plain,
    ( ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(k1_tops_1(sK2,X0_45),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subtyping,[status(esa)],[c_874])).

cnf(c_3987,plain,
    ( m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(k1_tops_1(sK2,X0_45),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3316])).

cnf(c_6,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_3331,plain,
    ( m1_subset_1(X0_45,X1_45)
    | ~ m1_subset_1(X2_45,k1_zfmisc_1(X1_45))
    | ~ r2_hidden(X0_45,X2_45) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_3970,plain,
    ( m1_subset_1(X0_45,X1_45) = iProver_top
    | m1_subset_1(X2_45,k1_zfmisc_1(X1_45)) != iProver_top
    | r2_hidden(X0_45,X2_45) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3331])).

cnf(c_5088,plain,
    ( m1_subset_1(X0_45,u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(X1_45,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(X0_45,k1_tops_1(sK2,X1_45)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3987,c_3970])).

cnf(c_7007,plain,
    ( m1_subset_1(X1_45,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(X0_45,X1_45) = iProver_top
    | r2_hidden(X0_45,k1_tops_1(sK2,X1_45)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3974,c_3382,c_5088])).

cnf(c_7008,plain,
    ( m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(X1_45,X0_45) = iProver_top
    | r2_hidden(X1_45,k1_tops_1(sK2,X0_45)) != iProver_top ),
    inference(renaming,[status(thm)],[c_7007])).

cnf(c_7016,plain,
    ( r2_hidden(X0_45,k1_tops_1(sK2,sK4)) != iProver_top
    | r2_hidden(X0_45,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3971,c_7008])).

cnf(c_7082,plain,
    ( r2_hidden(sK0(k1_tops_1(sK2,sK4),X0_45),sK4) = iProver_top
    | r1_tarski(k1_tops_1(sK2,sK4),X0_45) = iProver_top ),
    inference(superposition,[status(thm)],[c_3966,c_7016])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_3336,plain,
    ( ~ r2_hidden(sK0(X0_45,X1_45),X1_45)
    | r1_tarski(X0_45,X1_45) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_3965,plain,
    ( r2_hidden(sK0(X0_45,X1_45),X1_45) != iProver_top
    | r1_tarski(X0_45,X1_45) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3336])).

cnf(c_7264,plain,
    ( r1_tarski(k1_tops_1(sK2,sK4),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_7082,c_3965])).

cnf(c_4558,plain,
    ( r1_tarski(X0_45,X0_45) = iProver_top ),
    inference(superposition,[status(thm)],[c_3966,c_3965])).

cnf(c_21,negated_conjecture,
    ( m1_connsp_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_18,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_417,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_26])).

cnf(c_418,plain,
    ( ~ m1_connsp_2(X0,sK2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(X1,k1_tops_1(sK2,X0))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_417])).

cnf(c_422,plain,
    ( ~ m1_connsp_2(X0,sK2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(X1,k1_tops_1(sK2,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_418,c_25,c_24])).

cnf(c_542,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(X0,k1_tops_1(sK2,X1))
    | sK3 != X0
    | sK2 != sK2
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_422])).

cnf(c_543,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(sK3,k1_tops_1(sK2,sK4)) ),
    inference(unflattening,[status(thm)],[c_542])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_545,plain,
    ( r2_hidden(sK3,k1_tops_1(sK2,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_543,c_23,c_22])).

cnf(c_3325,plain,
    ( r2_hidden(sK3,k1_tops_1(sK2,sK4)) ),
    inference(subtyping,[status(esa)],[c_545])).

cnf(c_3976,plain,
    ( r2_hidden(sK3,k1_tops_1(sK2,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3325])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_4,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_206,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_4])).

cnf(c_207,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_206])).

cnf(c_269,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(bin_hyper_res,[status(thm)],[c_7,c_207])).

cnf(c_3328,plain,
    ( ~ r2_hidden(X0_45,X1_45)
    | ~ r1_tarski(X1_45,X2_45)
    | ~ v1_xboole_0(X2_45) ),
    inference(subtyping,[status(esa)],[c_269])).

cnf(c_3973,plain,
    ( r2_hidden(X0_45,X1_45) != iProver_top
    | r1_tarski(X1_45,X2_45) != iProver_top
    | v1_xboole_0(X2_45) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3328])).

cnf(c_5836,plain,
    ( r1_tarski(k1_tops_1(sK2,sK4),X0_45) != iProver_top
    | v1_xboole_0(X0_45) != iProver_top ),
    inference(superposition,[status(thm)],[c_3976,c_3973])).

cnf(c_6895,plain,
    ( v1_xboole_0(k1_tops_1(sK2,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4558,c_5836])).

cnf(c_3346,plain,
    ( ~ r2_hidden(X0_45,X1_45)
    | r2_hidden(X2_45,X3_45)
    | X2_45 != X0_45
    | X3_45 != X1_45 ),
    theory(equality)).

cnf(c_4270,plain,
    ( r2_hidden(X0_45,X1_45)
    | ~ r2_hidden(sK3,k1_tops_1(sK2,sK4))
    | X1_45 != k1_tops_1(sK2,sK4)
    | X0_45 != sK3 ),
    inference(instantiation,[status(thm)],[c_3346])).

cnf(c_4731,plain,
    ( r2_hidden(X0_45,k1_tops_1(sK2,k1_tops_1(sK2,sK4)))
    | ~ r2_hidden(sK3,k1_tops_1(sK2,sK4))
    | X0_45 != sK3
    | k1_tops_1(sK2,k1_tops_1(sK2,sK4)) != k1_tops_1(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_4270])).

cnf(c_4732,plain,
    ( X0_45 != sK3
    | k1_tops_1(sK2,k1_tops_1(sK2,sK4)) != k1_tops_1(sK2,sK4)
    | r2_hidden(X0_45,k1_tops_1(sK2,k1_tops_1(sK2,sK4))) = iProver_top
    | r2_hidden(sK3,k1_tops_1(sK2,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4731])).

cnf(c_4734,plain,
    ( k1_tops_1(sK2,k1_tops_1(sK2,sK4)) != k1_tops_1(sK2,sK4)
    | sK3 != sK3
    | r2_hidden(sK3,k1_tops_1(sK2,k1_tops_1(sK2,sK4))) = iProver_top
    | r2_hidden(sK3,k1_tops_1(sK2,sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4732])).

cnf(c_20,negated_conjecture,
    ( ~ m1_connsp_2(X0,sK2,sK3)
    | ~ v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X0,sK4)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_515,plain,
    ( ~ v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1,k1_tops_1(sK2,X2))
    | ~ r1_tarski(X0,sK4)
    | v1_xboole_0(X0)
    | X2 != X0
    | sK3 != X1
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_446])).

cnf(c_516,plain,
    ( ~ v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ r2_hidden(sK3,k1_tops_1(sK2,X0))
    | ~ r1_tarski(X0,sK4)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_515])).

cnf(c_520,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v3_pre_topc(X0,sK2)
    | ~ r2_hidden(sK3,k1_tops_1(sK2,X0))
    | ~ r1_tarski(X0,sK4)
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_516,c_23])).

cnf(c_521,plain,
    ( ~ v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK3,k1_tops_1(sK2,X0))
    | ~ r1_tarski(X0,sK4)
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_520])).

cnf(c_3326,plain,
    ( ~ v3_pre_topc(X0_45,sK2)
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK3,k1_tops_1(sK2,X0_45))
    | ~ r1_tarski(X0_45,sK4)
    | v1_xboole_0(X0_45) ),
    inference(subtyping,[status(esa)],[c_521])).

cnf(c_4314,plain,
    ( ~ v3_pre_topc(k1_tops_1(sK2,sK4),sK2)
    | ~ m1_subset_1(k1_tops_1(sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK3,k1_tops_1(sK2,k1_tops_1(sK2,sK4)))
    | ~ r1_tarski(k1_tops_1(sK2,sK4),sK4)
    | v1_xboole_0(k1_tops_1(sK2,sK4)) ),
    inference(instantiation,[status(thm)],[c_3326])).

cnf(c_4318,plain,
    ( v3_pre_topc(k1_tops_1(sK2,sK4),sK2) != iProver_top
    | m1_subset_1(k1_tops_1(sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(sK3,k1_tops_1(sK2,k1_tops_1(sK2,sK4))) != iProver_top
    | r1_tarski(k1_tops_1(sK2,sK4),sK4) != iProver_top
    | v1_xboole_0(k1_tops_1(sK2,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4314])).

cnf(c_16,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_792,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X1,X0) = X0
    | sK2 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_25])).

cnf(c_793,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK2)
    | k1_tops_1(X1,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_792])).

cnf(c_797,plain,
    ( ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X0,X1)
    | k1_tops_1(X1,X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_793,c_24])).

cnf(c_798,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = X0 ),
    inference(renaming,[status(thm)],[c_797])).

cnf(c_855,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_tops_1(X1,X0) = X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_798,c_24])).

cnf(c_856,plain,
    ( ~ v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_tops_1(sK2,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_855])).

cnf(c_3317,plain,
    ( ~ v3_pre_topc(X0_45,sK2)
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1_45,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_tops_1(sK2,X0_45) = X0_45 ),
    inference(subtyping,[status(esa)],[c_856])).

cnf(c_3338,plain,
    ( ~ v3_pre_topc(X0_45,sK2)
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_tops_1(sK2,X0_45) = X0_45
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_3317])).

cnf(c_3339,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_3317])).

cnf(c_3337,plain,
    ( ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_3317])).

cnf(c_3482,plain,
    ( k1_tops_1(sK2,X0_45) = X0_45
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v3_pre_topc(X0_45,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3338,c_3339,c_3337])).

cnf(c_3483,plain,
    ( ~ v3_pre_topc(X0_45,sK2)
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_tops_1(sK2,X0_45) = X0_45 ),
    inference(renaming,[status(thm)],[c_3482])).

cnf(c_4315,plain,
    ( ~ v3_pre_topc(k1_tops_1(sK2,sK4),sK2)
    | ~ m1_subset_1(k1_tops_1(sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_tops_1(sK2,k1_tops_1(sK2,sK4)) = k1_tops_1(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_3483])).

cnf(c_9,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_656,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_25])).

cnf(c_657,plain,
    ( v3_pre_topc(k1_tops_1(sK2,X0),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_656])).

cnf(c_661,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v3_pre_topc(k1_tops_1(sK2,X0),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_657,c_24])).

cnf(c_662,plain,
    ( v3_pre_topc(k1_tops_1(sK2,X0),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(renaming,[status(thm)],[c_661])).

cnf(c_3322,plain,
    ( v3_pre_topc(k1_tops_1(sK2,X0_45),sK2)
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subtyping,[status(esa)],[c_662])).

cnf(c_4185,plain,
    ( v3_pre_topc(k1_tops_1(sK2,sK4),sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_3322])).

cnf(c_4186,plain,
    ( v3_pre_topc(k1_tops_1(sK2,sK4),sK2) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4185])).

cnf(c_4182,plain,
    ( m1_subset_1(k1_tops_1(sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_3316])).

cnf(c_4183,plain,
    ( m1_subset_1(k1_tops_1(sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4182])).

cnf(c_3343,plain,
    ( X0_45 = X0_45 ),
    theory(equality)).

cnf(c_3360,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_3343])).

cnf(c_544,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(sK3,k1_tops_1(sK2,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_543])).

cnf(c_31,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_30,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7264,c_6895,c_4734,c_4318,c_4315,c_4186,c_4185,c_4183,c_4182,c_3360,c_544,c_31,c_22,c_30])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:39:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.94/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.94/1.00  
% 2.94/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.94/1.00  
% 2.94/1.00  ------  iProver source info
% 2.94/1.00  
% 2.94/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.94/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.94/1.00  git: non_committed_changes: false
% 2.94/1.00  git: last_make_outside_of_git: false
% 2.94/1.00  
% 2.94/1.00  ------ 
% 2.94/1.00  
% 2.94/1.00  ------ Input Options
% 2.94/1.00  
% 2.94/1.00  --out_options                           all
% 2.94/1.00  --tptp_safe_out                         true
% 2.94/1.00  --problem_path                          ""
% 2.94/1.00  --include_path                          ""
% 2.94/1.00  --clausifier                            res/vclausify_rel
% 2.94/1.00  --clausifier_options                    --mode clausify
% 2.94/1.00  --stdin                                 false
% 2.94/1.00  --stats_out                             all
% 2.94/1.00  
% 2.94/1.00  ------ General Options
% 2.94/1.00  
% 2.94/1.00  --fof                                   false
% 2.94/1.00  --time_out_real                         305.
% 2.94/1.00  --time_out_virtual                      -1.
% 2.94/1.00  --symbol_type_check                     false
% 2.94/1.00  --clausify_out                          false
% 2.94/1.00  --sig_cnt_out                           false
% 2.94/1.00  --trig_cnt_out                          false
% 2.94/1.00  --trig_cnt_out_tolerance                1.
% 2.94/1.00  --trig_cnt_out_sk_spl                   false
% 2.94/1.00  --abstr_cl_out                          false
% 2.94/1.00  
% 2.94/1.00  ------ Global Options
% 2.94/1.00  
% 2.94/1.00  --schedule                              default
% 2.94/1.00  --add_important_lit                     false
% 2.94/1.00  --prop_solver_per_cl                    1000
% 2.94/1.00  --min_unsat_core                        false
% 2.94/1.00  --soft_assumptions                      false
% 2.94/1.00  --soft_lemma_size                       3
% 2.94/1.00  --prop_impl_unit_size                   0
% 2.94/1.00  --prop_impl_unit                        []
% 2.94/1.00  --share_sel_clauses                     true
% 2.94/1.00  --reset_solvers                         false
% 2.94/1.00  --bc_imp_inh                            [conj_cone]
% 2.94/1.00  --conj_cone_tolerance                   3.
% 2.94/1.00  --extra_neg_conj                        none
% 2.94/1.00  --large_theory_mode                     true
% 2.94/1.00  --prolific_symb_bound                   200
% 2.94/1.00  --lt_threshold                          2000
% 2.94/1.00  --clause_weak_htbl                      true
% 2.94/1.00  --gc_record_bc_elim                     false
% 2.94/1.00  
% 2.94/1.00  ------ Preprocessing Options
% 2.94/1.00  
% 2.94/1.00  --preprocessing_flag                    true
% 2.94/1.00  --time_out_prep_mult                    0.1
% 2.94/1.00  --splitting_mode                        input
% 2.94/1.00  --splitting_grd                         true
% 2.94/1.00  --splitting_cvd                         false
% 2.94/1.00  --splitting_cvd_svl                     false
% 2.94/1.00  --splitting_nvd                         32
% 2.94/1.00  --sub_typing                            true
% 2.94/1.00  --prep_gs_sim                           true
% 2.94/1.00  --prep_unflatten                        true
% 2.94/1.00  --prep_res_sim                          true
% 2.94/1.00  --prep_upred                            true
% 2.94/1.00  --prep_sem_filter                       exhaustive
% 2.94/1.00  --prep_sem_filter_out                   false
% 2.94/1.00  --pred_elim                             true
% 2.94/1.00  --res_sim_input                         true
% 2.94/1.00  --eq_ax_congr_red                       true
% 2.94/1.00  --pure_diseq_elim                       true
% 2.94/1.00  --brand_transform                       false
% 2.94/1.00  --non_eq_to_eq                          false
% 2.94/1.00  --prep_def_merge                        true
% 2.94/1.00  --prep_def_merge_prop_impl              false
% 2.94/1.00  --prep_def_merge_mbd                    true
% 2.94/1.00  --prep_def_merge_tr_red                 false
% 2.94/1.00  --prep_def_merge_tr_cl                  false
% 2.94/1.00  --smt_preprocessing                     true
% 2.94/1.00  --smt_ac_axioms                         fast
% 2.94/1.00  --preprocessed_out                      false
% 2.94/1.00  --preprocessed_stats                    false
% 2.94/1.00  
% 2.94/1.00  ------ Abstraction refinement Options
% 2.94/1.00  
% 2.94/1.00  --abstr_ref                             []
% 2.94/1.00  --abstr_ref_prep                        false
% 2.94/1.00  --abstr_ref_until_sat                   false
% 2.94/1.00  --abstr_ref_sig_restrict                funpre
% 2.94/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.94/1.00  --abstr_ref_under                       []
% 2.94/1.00  
% 2.94/1.00  ------ SAT Options
% 2.94/1.00  
% 2.94/1.00  --sat_mode                              false
% 2.94/1.00  --sat_fm_restart_options                ""
% 2.94/1.00  --sat_gr_def                            false
% 2.94/1.00  --sat_epr_types                         true
% 2.94/1.00  --sat_non_cyclic_types                  false
% 2.94/1.00  --sat_finite_models                     false
% 2.94/1.00  --sat_fm_lemmas                         false
% 2.94/1.00  --sat_fm_prep                           false
% 2.94/1.00  --sat_fm_uc_incr                        true
% 2.94/1.00  --sat_out_model                         small
% 2.94/1.00  --sat_out_clauses                       false
% 2.94/1.00  
% 2.94/1.00  ------ QBF Options
% 2.94/1.00  
% 2.94/1.00  --qbf_mode                              false
% 2.94/1.00  --qbf_elim_univ                         false
% 2.94/1.00  --qbf_dom_inst                          none
% 2.94/1.00  --qbf_dom_pre_inst                      false
% 2.94/1.00  --qbf_sk_in                             false
% 2.94/1.00  --qbf_pred_elim                         true
% 2.94/1.00  --qbf_split                             512
% 2.94/1.00  
% 2.94/1.00  ------ BMC1 Options
% 2.94/1.00  
% 2.94/1.00  --bmc1_incremental                      false
% 2.94/1.00  --bmc1_axioms                           reachable_all
% 2.94/1.00  --bmc1_min_bound                        0
% 2.94/1.00  --bmc1_max_bound                        -1
% 2.94/1.00  --bmc1_max_bound_default                -1
% 2.94/1.00  --bmc1_symbol_reachability              true
% 2.94/1.00  --bmc1_property_lemmas                  false
% 2.94/1.00  --bmc1_k_induction                      false
% 2.94/1.00  --bmc1_non_equiv_states                 false
% 2.94/1.00  --bmc1_deadlock                         false
% 2.94/1.00  --bmc1_ucm                              false
% 2.94/1.00  --bmc1_add_unsat_core                   none
% 2.94/1.00  --bmc1_unsat_core_children              false
% 2.94/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.94/1.00  --bmc1_out_stat                         full
% 2.94/1.00  --bmc1_ground_init                      false
% 2.94/1.00  --bmc1_pre_inst_next_state              false
% 2.94/1.00  --bmc1_pre_inst_state                   false
% 2.94/1.00  --bmc1_pre_inst_reach_state             false
% 2.94/1.00  --bmc1_out_unsat_core                   false
% 2.94/1.00  --bmc1_aig_witness_out                  false
% 2.94/1.00  --bmc1_verbose                          false
% 2.94/1.00  --bmc1_dump_clauses_tptp                false
% 2.94/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.94/1.00  --bmc1_dump_file                        -
% 2.94/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.94/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.94/1.00  --bmc1_ucm_extend_mode                  1
% 2.94/1.00  --bmc1_ucm_init_mode                    2
% 2.94/1.00  --bmc1_ucm_cone_mode                    none
% 2.94/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.94/1.00  --bmc1_ucm_relax_model                  4
% 2.94/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.94/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.94/1.00  --bmc1_ucm_layered_model                none
% 2.94/1.00  --bmc1_ucm_max_lemma_size               10
% 2.94/1.00  
% 2.94/1.00  ------ AIG Options
% 2.94/1.00  
% 2.94/1.00  --aig_mode                              false
% 2.94/1.00  
% 2.94/1.00  ------ Instantiation Options
% 2.94/1.00  
% 2.94/1.00  --instantiation_flag                    true
% 2.94/1.00  --inst_sos_flag                         false
% 2.94/1.00  --inst_sos_phase                        true
% 2.94/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.94/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.94/1.00  --inst_lit_sel_side                     num_symb
% 2.94/1.00  --inst_solver_per_active                1400
% 2.94/1.00  --inst_solver_calls_frac                1.
% 2.94/1.00  --inst_passive_queue_type               priority_queues
% 2.94/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.94/1.00  --inst_passive_queues_freq              [25;2]
% 2.94/1.00  --inst_dismatching                      true
% 2.94/1.00  --inst_eager_unprocessed_to_passive     true
% 2.94/1.00  --inst_prop_sim_given                   true
% 2.94/1.00  --inst_prop_sim_new                     false
% 2.94/1.00  --inst_subs_new                         false
% 2.94/1.00  --inst_eq_res_simp                      false
% 2.94/1.00  --inst_subs_given                       false
% 2.94/1.00  --inst_orphan_elimination               true
% 2.94/1.00  --inst_learning_loop_flag               true
% 2.94/1.00  --inst_learning_start                   3000
% 2.94/1.00  --inst_learning_factor                  2
% 2.94/1.00  --inst_start_prop_sim_after_learn       3
% 2.94/1.00  --inst_sel_renew                        solver
% 2.94/1.00  --inst_lit_activity_flag                true
% 2.94/1.00  --inst_restr_to_given                   false
% 2.94/1.00  --inst_activity_threshold               500
% 2.94/1.00  --inst_out_proof                        true
% 2.94/1.00  
% 2.94/1.00  ------ Resolution Options
% 2.94/1.00  
% 2.94/1.00  --resolution_flag                       true
% 2.94/1.00  --res_lit_sel                           adaptive
% 2.94/1.00  --res_lit_sel_side                      none
% 2.94/1.00  --res_ordering                          kbo
% 2.94/1.00  --res_to_prop_solver                    active
% 2.94/1.00  --res_prop_simpl_new                    false
% 2.94/1.00  --res_prop_simpl_given                  true
% 2.94/1.00  --res_passive_queue_type                priority_queues
% 2.94/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.94/1.00  --res_passive_queues_freq               [15;5]
% 2.94/1.00  --res_forward_subs                      full
% 2.94/1.00  --res_backward_subs                     full
% 2.94/1.00  --res_forward_subs_resolution           true
% 2.94/1.00  --res_backward_subs_resolution          true
% 2.94/1.00  --res_orphan_elimination                true
% 2.94/1.00  --res_time_limit                        2.
% 2.94/1.00  --res_out_proof                         true
% 2.94/1.00  
% 2.94/1.00  ------ Superposition Options
% 2.94/1.00  
% 2.94/1.00  --superposition_flag                    true
% 2.94/1.00  --sup_passive_queue_type                priority_queues
% 2.94/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.94/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.94/1.00  --demod_completeness_check              fast
% 2.94/1.00  --demod_use_ground                      true
% 2.94/1.00  --sup_to_prop_solver                    passive
% 2.94/1.00  --sup_prop_simpl_new                    true
% 2.94/1.00  --sup_prop_simpl_given                  true
% 2.94/1.00  --sup_fun_splitting                     false
% 2.94/1.00  --sup_smt_interval                      50000
% 2.94/1.00  
% 2.94/1.00  ------ Superposition Simplification Setup
% 2.94/1.00  
% 2.94/1.00  --sup_indices_passive                   []
% 2.94/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.94/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.94/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.94/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.94/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.94/1.00  --sup_full_bw                           [BwDemod]
% 2.94/1.00  --sup_immed_triv                        [TrivRules]
% 2.94/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.94/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.94/1.00  --sup_immed_bw_main                     []
% 2.94/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.94/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.94/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.94/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.94/1.00  
% 2.94/1.00  ------ Combination Options
% 2.94/1.00  
% 2.94/1.00  --comb_res_mult                         3
% 2.94/1.00  --comb_sup_mult                         2
% 2.94/1.00  --comb_inst_mult                        10
% 2.94/1.00  
% 2.94/1.00  ------ Debug Options
% 2.94/1.00  
% 2.94/1.00  --dbg_backtrace                         false
% 2.94/1.00  --dbg_dump_prop_clauses                 false
% 2.94/1.00  --dbg_dump_prop_clauses_file            -
% 2.94/1.00  --dbg_out_stat                          false
% 2.94/1.00  ------ Parsing...
% 2.94/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.94/1.00  
% 2.94/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 2.94/1.00  
% 2.94/1.00  ------ Preprocessing... gs_s  sp: 4 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.94/1.00  
% 2.94/1.00  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.94/1.00  ------ Proving...
% 2.94/1.00  ------ Problem Properties 
% 2.94/1.00  
% 2.94/1.00  
% 2.94/1.00  clauses                                 27
% 2.94/1.00  conjectures                             2
% 2.94/1.00  EPR                                     6
% 2.94/1.00  Horn                                    24
% 2.94/1.00  unary                                   4
% 2.94/1.00  binary                                  11
% 2.94/1.00  lits                                    70
% 2.94/1.00  lits eq                                 2
% 2.94/1.00  fd_pure                                 0
% 2.94/1.00  fd_pseudo                               0
% 2.94/1.00  fd_cond                                 0
% 2.94/1.00  fd_pseudo_cond                          0
% 2.94/1.00  AC symbols                              0
% 2.94/1.00  
% 2.94/1.00  ------ Schedule dynamic 5 is on 
% 2.94/1.00  
% 2.94/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.94/1.00  
% 2.94/1.00  
% 2.94/1.00  ------ 
% 2.94/1.00  Current options:
% 2.94/1.00  ------ 
% 2.94/1.00  
% 2.94/1.00  ------ Input Options
% 2.94/1.00  
% 2.94/1.00  --out_options                           all
% 2.94/1.00  --tptp_safe_out                         true
% 2.94/1.00  --problem_path                          ""
% 2.94/1.00  --include_path                          ""
% 2.94/1.00  --clausifier                            res/vclausify_rel
% 2.94/1.00  --clausifier_options                    --mode clausify
% 2.94/1.00  --stdin                                 false
% 2.94/1.00  --stats_out                             all
% 2.94/1.00  
% 2.94/1.00  ------ General Options
% 2.94/1.00  
% 2.94/1.00  --fof                                   false
% 2.94/1.00  --time_out_real                         305.
% 2.94/1.00  --time_out_virtual                      -1.
% 2.94/1.00  --symbol_type_check                     false
% 2.94/1.00  --clausify_out                          false
% 2.94/1.00  --sig_cnt_out                           false
% 2.94/1.00  --trig_cnt_out                          false
% 2.94/1.00  --trig_cnt_out_tolerance                1.
% 2.94/1.00  --trig_cnt_out_sk_spl                   false
% 2.94/1.00  --abstr_cl_out                          false
% 2.94/1.00  
% 2.94/1.00  ------ Global Options
% 2.94/1.00  
% 2.94/1.00  --schedule                              default
% 2.94/1.00  --add_important_lit                     false
% 2.94/1.00  --prop_solver_per_cl                    1000
% 2.94/1.00  --min_unsat_core                        false
% 2.94/1.00  --soft_assumptions                      false
% 2.94/1.00  --soft_lemma_size                       3
% 2.94/1.00  --prop_impl_unit_size                   0
% 2.94/1.00  --prop_impl_unit                        []
% 2.94/1.00  --share_sel_clauses                     true
% 2.94/1.00  --reset_solvers                         false
% 2.94/1.00  --bc_imp_inh                            [conj_cone]
% 2.94/1.00  --conj_cone_tolerance                   3.
% 2.94/1.00  --extra_neg_conj                        none
% 2.94/1.00  --large_theory_mode                     true
% 2.94/1.00  --prolific_symb_bound                   200
% 2.94/1.00  --lt_threshold                          2000
% 2.94/1.00  --clause_weak_htbl                      true
% 2.94/1.00  --gc_record_bc_elim                     false
% 2.94/1.00  
% 2.94/1.00  ------ Preprocessing Options
% 2.94/1.00  
% 2.94/1.00  --preprocessing_flag                    true
% 2.94/1.00  --time_out_prep_mult                    0.1
% 2.94/1.00  --splitting_mode                        input
% 2.94/1.00  --splitting_grd                         true
% 2.94/1.00  --splitting_cvd                         false
% 2.94/1.00  --splitting_cvd_svl                     false
% 2.94/1.00  --splitting_nvd                         32
% 2.94/1.00  --sub_typing                            true
% 2.94/1.00  --prep_gs_sim                           true
% 2.94/1.00  --prep_unflatten                        true
% 2.94/1.00  --prep_res_sim                          true
% 2.94/1.00  --prep_upred                            true
% 2.94/1.00  --prep_sem_filter                       exhaustive
% 2.94/1.00  --prep_sem_filter_out                   false
% 2.94/1.00  --pred_elim                             true
% 2.94/1.00  --res_sim_input                         true
% 2.94/1.00  --eq_ax_congr_red                       true
% 2.94/1.00  --pure_diseq_elim                       true
% 2.94/1.00  --brand_transform                       false
% 2.94/1.00  --non_eq_to_eq                          false
% 2.94/1.00  --prep_def_merge                        true
% 2.94/1.00  --prep_def_merge_prop_impl              false
% 2.94/1.00  --prep_def_merge_mbd                    true
% 2.94/1.00  --prep_def_merge_tr_red                 false
% 2.94/1.00  --prep_def_merge_tr_cl                  false
% 2.94/1.00  --smt_preprocessing                     true
% 2.94/1.00  --smt_ac_axioms                         fast
% 2.94/1.00  --preprocessed_out                      false
% 2.94/1.00  --preprocessed_stats                    false
% 2.94/1.00  
% 2.94/1.00  ------ Abstraction refinement Options
% 2.94/1.00  
% 2.94/1.00  --abstr_ref                             []
% 2.94/1.00  --abstr_ref_prep                        false
% 2.94/1.00  --abstr_ref_until_sat                   false
% 2.94/1.00  --abstr_ref_sig_restrict                funpre
% 2.94/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.94/1.00  --abstr_ref_under                       []
% 2.94/1.00  
% 2.94/1.00  ------ SAT Options
% 2.94/1.00  
% 2.94/1.00  --sat_mode                              false
% 2.94/1.00  --sat_fm_restart_options                ""
% 2.94/1.00  --sat_gr_def                            false
% 2.94/1.00  --sat_epr_types                         true
% 2.94/1.00  --sat_non_cyclic_types                  false
% 2.94/1.00  --sat_finite_models                     false
% 2.94/1.00  --sat_fm_lemmas                         false
% 2.94/1.00  --sat_fm_prep                           false
% 2.94/1.00  --sat_fm_uc_incr                        true
% 2.94/1.00  --sat_out_model                         small
% 2.94/1.00  --sat_out_clauses                       false
% 2.94/1.00  
% 2.94/1.00  ------ QBF Options
% 2.94/1.00  
% 2.94/1.00  --qbf_mode                              false
% 2.94/1.00  --qbf_elim_univ                         false
% 2.94/1.00  --qbf_dom_inst                          none
% 2.94/1.00  --qbf_dom_pre_inst                      false
% 2.94/1.00  --qbf_sk_in                             false
% 2.94/1.00  --qbf_pred_elim                         true
% 2.94/1.00  --qbf_split                             512
% 2.94/1.00  
% 2.94/1.00  ------ BMC1 Options
% 2.94/1.00  
% 2.94/1.00  --bmc1_incremental                      false
% 2.94/1.00  --bmc1_axioms                           reachable_all
% 2.94/1.00  --bmc1_min_bound                        0
% 2.94/1.00  --bmc1_max_bound                        -1
% 2.94/1.00  --bmc1_max_bound_default                -1
% 2.94/1.00  --bmc1_symbol_reachability              true
% 2.94/1.00  --bmc1_property_lemmas                  false
% 2.94/1.00  --bmc1_k_induction                      false
% 2.94/1.00  --bmc1_non_equiv_states                 false
% 2.94/1.00  --bmc1_deadlock                         false
% 2.94/1.00  --bmc1_ucm                              false
% 2.94/1.00  --bmc1_add_unsat_core                   none
% 2.94/1.00  --bmc1_unsat_core_children              false
% 2.94/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.94/1.00  --bmc1_out_stat                         full
% 2.94/1.00  --bmc1_ground_init                      false
% 2.94/1.00  --bmc1_pre_inst_next_state              false
% 2.94/1.00  --bmc1_pre_inst_state                   false
% 2.94/1.00  --bmc1_pre_inst_reach_state             false
% 2.94/1.00  --bmc1_out_unsat_core                   false
% 2.94/1.00  --bmc1_aig_witness_out                  false
% 2.94/1.00  --bmc1_verbose                          false
% 2.94/1.00  --bmc1_dump_clauses_tptp                false
% 2.94/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.94/1.00  --bmc1_dump_file                        -
% 2.94/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.94/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.94/1.00  --bmc1_ucm_extend_mode                  1
% 2.94/1.00  --bmc1_ucm_init_mode                    2
% 2.94/1.00  --bmc1_ucm_cone_mode                    none
% 2.94/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.94/1.00  --bmc1_ucm_relax_model                  4
% 2.94/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.94/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.94/1.00  --bmc1_ucm_layered_model                none
% 2.94/1.00  --bmc1_ucm_max_lemma_size               10
% 2.94/1.00  
% 2.94/1.00  ------ AIG Options
% 2.94/1.00  
% 2.94/1.00  --aig_mode                              false
% 2.94/1.00  
% 2.94/1.00  ------ Instantiation Options
% 2.94/1.00  
% 2.94/1.00  --instantiation_flag                    true
% 2.94/1.00  --inst_sos_flag                         false
% 2.94/1.00  --inst_sos_phase                        true
% 2.94/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.94/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.94/1.00  --inst_lit_sel_side                     none
% 2.94/1.00  --inst_solver_per_active                1400
% 2.94/1.00  --inst_solver_calls_frac                1.
% 2.94/1.00  --inst_passive_queue_type               priority_queues
% 2.94/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.94/1.00  --inst_passive_queues_freq              [25;2]
% 2.94/1.00  --inst_dismatching                      true
% 2.94/1.00  --inst_eager_unprocessed_to_passive     true
% 2.94/1.00  --inst_prop_sim_given                   true
% 2.94/1.00  --inst_prop_sim_new                     false
% 2.94/1.00  --inst_subs_new                         false
% 2.94/1.00  --inst_eq_res_simp                      false
% 2.94/1.00  --inst_subs_given                       false
% 2.94/1.00  --inst_orphan_elimination               true
% 2.94/1.00  --inst_learning_loop_flag               true
% 2.94/1.00  --inst_learning_start                   3000
% 2.94/1.00  --inst_learning_factor                  2
% 2.94/1.00  --inst_start_prop_sim_after_learn       3
% 2.94/1.00  --inst_sel_renew                        solver
% 2.94/1.00  --inst_lit_activity_flag                true
% 2.94/1.00  --inst_restr_to_given                   false
% 2.94/1.00  --inst_activity_threshold               500
% 2.94/1.00  --inst_out_proof                        true
% 2.94/1.00  
% 2.94/1.00  ------ Resolution Options
% 2.94/1.00  
% 2.94/1.00  --resolution_flag                       false
% 2.94/1.00  --res_lit_sel                           adaptive
% 2.94/1.00  --res_lit_sel_side                      none
% 2.94/1.00  --res_ordering                          kbo
% 2.94/1.00  --res_to_prop_solver                    active
% 2.94/1.00  --res_prop_simpl_new                    false
% 2.94/1.00  --res_prop_simpl_given                  true
% 2.94/1.00  --res_passive_queue_type                priority_queues
% 2.94/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.94/1.00  --res_passive_queues_freq               [15;5]
% 2.94/1.00  --res_forward_subs                      full
% 2.94/1.00  --res_backward_subs                     full
% 2.94/1.00  --res_forward_subs_resolution           true
% 2.94/1.00  --res_backward_subs_resolution          true
% 2.94/1.00  --res_orphan_elimination                true
% 2.94/1.00  --res_time_limit                        2.
% 2.94/1.00  --res_out_proof                         true
% 2.94/1.00  
% 2.94/1.00  ------ Superposition Options
% 2.94/1.00  
% 2.94/1.00  --superposition_flag                    true
% 2.94/1.00  --sup_passive_queue_type                priority_queues
% 2.94/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.94/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.94/1.00  --demod_completeness_check              fast
% 2.94/1.00  --demod_use_ground                      true
% 2.94/1.00  --sup_to_prop_solver                    passive
% 2.94/1.00  --sup_prop_simpl_new                    true
% 2.94/1.00  --sup_prop_simpl_given                  true
% 2.94/1.00  --sup_fun_splitting                     false
% 2.94/1.00  --sup_smt_interval                      50000
% 2.94/1.00  
% 2.94/1.00  ------ Superposition Simplification Setup
% 2.94/1.00  
% 2.94/1.00  --sup_indices_passive                   []
% 2.94/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.94/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.94/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.94/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.94/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.94/1.00  --sup_full_bw                           [BwDemod]
% 2.94/1.00  --sup_immed_triv                        [TrivRules]
% 2.94/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.94/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.94/1.00  --sup_immed_bw_main                     []
% 2.94/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.94/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.94/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.94/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.94/1.00  
% 2.94/1.00  ------ Combination Options
% 2.94/1.00  
% 2.94/1.00  --comb_res_mult                         3
% 2.94/1.00  --comb_sup_mult                         2
% 2.94/1.00  --comb_inst_mult                        10
% 2.94/1.00  
% 2.94/1.00  ------ Debug Options
% 2.94/1.00  
% 2.94/1.00  --dbg_backtrace                         false
% 2.94/1.00  --dbg_dump_prop_clauses                 false
% 2.94/1.00  --dbg_dump_prop_clauses_file            -
% 2.94/1.00  --dbg_out_stat                          false
% 2.94/1.00  
% 2.94/1.00  
% 2.94/1.00  
% 2.94/1.00  
% 2.94/1.00  ------ Proving...
% 2.94/1.00  
% 2.94/1.00  
% 2.94/1.00  % SZS status Theorem for theBenchmark.p
% 2.94/1.00  
% 2.94/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.94/1.00  
% 2.94/1.00  fof(f1,axiom,(
% 2.94/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.94/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.94/1.00  
% 2.94/1.00  fof(f14,plain,(
% 2.94/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.94/1.00    inference(ennf_transformation,[],[f1])).
% 2.94/1.00  
% 2.94/1.00  fof(f33,plain,(
% 2.94/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.94/1.00    inference(nnf_transformation,[],[f14])).
% 2.94/1.00  
% 2.94/1.00  fof(f34,plain,(
% 2.94/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.94/1.00    inference(rectify,[],[f33])).
% 2.94/1.00  
% 2.94/1.00  fof(f35,plain,(
% 2.94/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.94/1.00    introduced(choice_axiom,[])).
% 2.94/1.00  
% 2.94/1.00  fof(f36,plain,(
% 2.94/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.94/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).
% 2.94/1.00  
% 2.94/1.00  fof(f48,plain,(
% 2.94/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.94/1.00    inference(cnf_transformation,[],[f36])).
% 2.94/1.00  
% 2.94/1.00  fof(f12,conjecture,(
% 2.94/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X3)) => ~(r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1))) & m1_connsp_2(X2,X0,X1)))))),
% 2.94/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.94/1.00  
% 2.94/1.00  fof(f13,negated_conjecture,(
% 2.94/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X3)) => ~(r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1))) & m1_connsp_2(X2,X0,X1)))))),
% 2.94/1.00    inference(negated_conjecture,[],[f12])).
% 2.94/1.00  
% 2.94/1.00  fof(f31,plain,(
% 2.94/1.00    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : ((~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_connsp_2(X3,X0,X1)) | (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X3))) & m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.94/1.00    inference(ennf_transformation,[],[f13])).
% 2.94/1.00  
% 2.94/1.00  fof(f32,plain,(
% 2.94/1.00    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_connsp_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X3)) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.94/1.00    inference(flattening,[],[f31])).
% 2.94/1.00  
% 2.94/1.00  fof(f45,plain,(
% 2.94/1.00    ( ! [X0,X1] : (? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_connsp_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X3)) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (! [X3] : (~r1_tarski(X3,sK4) | ~v3_pre_topc(X3,X0) | ~m1_connsp_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X3)) & m1_connsp_2(sK4,X0,X1) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.94/1.00    introduced(choice_axiom,[])).
% 2.94/1.00  
% 2.94/1.00  fof(f44,plain,(
% 2.94/1.00    ( ! [X0] : (? [X1] : (? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_connsp_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X3)) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_connsp_2(X3,X0,sK3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X3)) & m1_connsp_2(X2,X0,sK3) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK3,u1_struct_0(X0)))) )),
% 2.94/1.00    introduced(choice_axiom,[])).
% 2.94/1.00  
% 2.94/1.00  fof(f43,plain,(
% 2.94/1.00    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_connsp_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X3)) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~v3_pre_topc(X3,sK2) | ~m1_connsp_2(X3,sK2,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) | v1_xboole_0(X3)) & m1_connsp_2(X2,sK2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(X1,u1_struct_0(sK2))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 2.94/1.00    introduced(choice_axiom,[])).
% 2.94/1.00  
% 2.94/1.00  fof(f46,plain,(
% 2.94/1.00    ((! [X3] : (~r1_tarski(X3,sK4) | ~v3_pre_topc(X3,sK2) | ~m1_connsp_2(X3,sK2,sK3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) | v1_xboole_0(X3)) & m1_connsp_2(sK4,sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(sK3,u1_struct_0(sK2))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 2.94/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f32,f45,f44,f43])).
% 2.94/1.00  
% 2.94/1.00  fof(f71,plain,(
% 2.94/1.00    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))),
% 2.94/1.00    inference(cnf_transformation,[],[f46])).
% 2.94/1.00  
% 2.94/1.00  fof(f10,axiom,(
% 2.94/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 2.94/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.94/1.00  
% 2.94/1.00  fof(f27,plain,(
% 2.94/1.00    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.94/1.00    inference(ennf_transformation,[],[f10])).
% 2.94/1.00  
% 2.94/1.00  fof(f28,plain,(
% 2.94/1.00    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.94/1.00    inference(flattening,[],[f27])).
% 2.94/1.00  
% 2.94/1.00  fof(f42,plain,(
% 2.94/1.00    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.94/1.00    inference(nnf_transformation,[],[f28])).
% 2.94/1.00  
% 2.94/1.00  fof(f65,plain,(
% 2.94/1.00    ( ! [X2,X0,X1] : (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.94/1.00    inference(cnf_transformation,[],[f42])).
% 2.94/1.00  
% 2.94/1.00  fof(f67,plain,(
% 2.94/1.00    ~v2_struct_0(sK2)),
% 2.94/1.00    inference(cnf_transformation,[],[f46])).
% 2.94/1.00  
% 2.94/1.00  fof(f68,plain,(
% 2.94/1.00    v2_pre_topc(sK2)),
% 2.94/1.00    inference(cnf_transformation,[],[f46])).
% 2.94/1.00  
% 2.94/1.00  fof(f69,plain,(
% 2.94/1.00    l1_pre_topc(sK2)),
% 2.94/1.00    inference(cnf_transformation,[],[f46])).
% 2.94/1.00  
% 2.94/1.00  fof(f11,axiom,(
% 2.94/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (m1_connsp_2(X1,X0,X2) => r2_hidden(X2,X1)))))),
% 2.94/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.94/1.00  
% 2.94/1.00  fof(f29,plain,(
% 2.94/1.00    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.94/1.00    inference(ennf_transformation,[],[f11])).
% 2.94/1.00  
% 2.94/1.00  fof(f30,plain,(
% 2.94/1.00    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.94/1.00    inference(flattening,[],[f29])).
% 2.94/1.00  
% 2.94/1.00  fof(f66,plain,(
% 2.94/1.00    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.94/1.00    inference(cnf_transformation,[],[f30])).
% 2.94/1.00  
% 2.94/1.00  fof(f6,axiom,(
% 2.94/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.94/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.94/1.00  
% 2.94/1.00  fof(f19,plain,(
% 2.94/1.00    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.94/1.00    inference(ennf_transformation,[],[f6])).
% 2.94/1.00  
% 2.94/1.00  fof(f20,plain,(
% 2.94/1.00    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.94/1.00    inference(flattening,[],[f19])).
% 2.94/1.00  
% 2.94/1.00  fof(f55,plain,(
% 2.94/1.00    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.94/1.00    inference(cnf_transformation,[],[f20])).
% 2.94/1.00  
% 2.94/1.00  fof(f4,axiom,(
% 2.94/1.00    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.94/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.94/1.00  
% 2.94/1.00  fof(f16,plain,(
% 2.94/1.00    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.94/1.00    inference(ennf_transformation,[],[f4])).
% 2.94/1.00  
% 2.94/1.00  fof(f17,plain,(
% 2.94/1.00    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.94/1.00    inference(flattening,[],[f16])).
% 2.94/1.00  
% 2.94/1.00  fof(f53,plain,(
% 2.94/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.94/1.00    inference(cnf_transformation,[],[f17])).
% 2.94/1.00  
% 2.94/1.00  fof(f49,plain,(
% 2.94/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 2.94/1.00    inference(cnf_transformation,[],[f36])).
% 2.94/1.00  
% 2.94/1.00  fof(f72,plain,(
% 2.94/1.00    m1_connsp_2(sK4,sK2,sK3)),
% 2.94/1.00    inference(cnf_transformation,[],[f46])).
% 2.94/1.00  
% 2.94/1.00  fof(f64,plain,(
% 2.94/1.00    ( ! [X2,X0,X1] : (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.94/1.00    inference(cnf_transformation,[],[f42])).
% 2.94/1.00  
% 2.94/1.00  fof(f70,plain,(
% 2.94/1.00    m1_subset_1(sK3,u1_struct_0(sK2))),
% 2.94/1.00    inference(cnf_transformation,[],[f46])).
% 2.94/1.00  
% 2.94/1.00  fof(f5,axiom,(
% 2.94/1.00    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.94/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.94/1.00  
% 2.94/1.00  fof(f18,plain,(
% 2.94/1.00    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.94/1.00    inference(ennf_transformation,[],[f5])).
% 2.94/1.00  
% 2.94/1.00  fof(f54,plain,(
% 2.94/1.00    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.94/1.00    inference(cnf_transformation,[],[f18])).
% 2.94/1.00  
% 2.94/1.00  fof(f3,axiom,(
% 2.94/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.94/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.94/1.00  
% 2.94/1.00  fof(f37,plain,(
% 2.94/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.94/1.00    inference(nnf_transformation,[],[f3])).
% 2.94/1.00  
% 2.94/1.00  fof(f52,plain,(
% 2.94/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.94/1.00    inference(cnf_transformation,[],[f37])).
% 2.94/1.00  
% 2.94/1.00  fof(f73,plain,(
% 2.94/1.00    ( ! [X3] : (~r1_tarski(X3,sK4) | ~v3_pre_topc(X3,sK2) | ~m1_connsp_2(X3,sK2,sK3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) | v1_xboole_0(X3)) )),
% 2.94/1.00    inference(cnf_transformation,[],[f46])).
% 2.94/1.00  
% 2.94/1.00  fof(f9,axiom,(
% 2.94/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 2.94/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.94/1.00  
% 2.94/1.00  fof(f25,plain,(
% 2.94/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.94/1.00    inference(ennf_transformation,[],[f9])).
% 2.94/1.00  
% 2.94/1.00  fof(f26,plain,(
% 2.94/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.94/1.00    inference(flattening,[],[f25])).
% 2.94/1.00  
% 2.94/1.00  fof(f62,plain,(
% 2.94/1.00    ( ! [X2,X0,X3,X1] : (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.94/1.00    inference(cnf_transformation,[],[f26])).
% 2.94/1.00  
% 2.94/1.00  fof(f7,axiom,(
% 2.94/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 2.94/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.94/1.00  
% 2.94/1.00  fof(f21,plain,(
% 2.94/1.00    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.94/1.00    inference(ennf_transformation,[],[f7])).
% 2.94/1.00  
% 2.94/1.00  fof(f22,plain,(
% 2.94/1.00    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.94/1.00    inference(flattening,[],[f21])).
% 2.94/1.00  
% 2.94/1.00  fof(f56,plain,(
% 2.94/1.00    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.94/1.00    inference(cnf_transformation,[],[f22])).
% 2.94/1.00  
% 2.94/1.00  cnf(c_1,plain,
% 2.94/1.00      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 2.94/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_3335,plain,
% 2.94/1.00      ( r2_hidden(sK0(X0_45,X1_45),X0_45) | r1_tarski(X0_45,X1_45) ),
% 2.94/1.00      inference(subtyping,[status(esa)],[c_1]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_3966,plain,
% 2.94/1.00      ( r2_hidden(sK0(X0_45,X1_45),X0_45) = iProver_top
% 2.94/1.00      | r1_tarski(X0_45,X1_45) = iProver_top ),
% 2.94/1.00      inference(predicate_to_equality,[status(thm)],[c_3335]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_22,negated_conjecture,
% 2.94/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.94/1.00      inference(cnf_transformation,[],[f71]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_3330,negated_conjecture,
% 2.94/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.94/1.00      inference(subtyping,[status(esa)],[c_22]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_3971,plain,
% 2.94/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 2.94/1.00      inference(predicate_to_equality,[status(thm)],[c_3330]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_17,plain,
% 2.94/1.00      ( m1_connsp_2(X0,X1,X2)
% 2.94/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.94/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.94/1.00      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 2.94/1.00      | v2_struct_0(X1)
% 2.94/1.00      | ~ v2_pre_topc(X1)
% 2.94/1.00      | ~ l1_pre_topc(X1) ),
% 2.94/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_26,negated_conjecture,
% 2.94/1.00      ( ~ v2_struct_0(sK2) ),
% 2.94/1.00      inference(cnf_transformation,[],[f67]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_441,plain,
% 2.94/1.00      ( m1_connsp_2(X0,X1,X2)
% 2.94/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.94/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.94/1.00      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 2.94/1.00      | ~ v2_pre_topc(X1)
% 2.94/1.00      | ~ l1_pre_topc(X1)
% 2.94/1.00      | sK2 != X1 ),
% 2.94/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_26]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_442,plain,
% 2.94/1.00      ( m1_connsp_2(X0,sK2,X1)
% 2.94/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.94/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.94/1.00      | ~ r2_hidden(X1,k1_tops_1(sK2,X0))
% 2.94/1.00      | ~ v2_pre_topc(sK2)
% 2.94/1.00      | ~ l1_pre_topc(sK2) ),
% 2.94/1.00      inference(unflattening,[status(thm)],[c_441]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_25,negated_conjecture,
% 2.94/1.00      ( v2_pre_topc(sK2) ),
% 2.94/1.00      inference(cnf_transformation,[],[f68]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_24,negated_conjecture,
% 2.94/1.00      ( l1_pre_topc(sK2) ),
% 2.94/1.00      inference(cnf_transformation,[],[f69]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_446,plain,
% 2.94/1.00      ( m1_connsp_2(X0,sK2,X1)
% 2.94/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.94/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.94/1.00      | ~ r2_hidden(X1,k1_tops_1(sK2,X0)) ),
% 2.94/1.00      inference(global_propositional_subsumption,
% 2.94/1.00                [status(thm)],
% 2.94/1.00                [c_442,c_25,c_24]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_19,plain,
% 2.94/1.00      ( ~ m1_connsp_2(X0,X1,X2)
% 2.94/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.94/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.94/1.00      | r2_hidden(X2,X0)
% 2.94/1.00      | v2_struct_0(X1)
% 2.94/1.00      | ~ v2_pre_topc(X1)
% 2.94/1.00      | ~ l1_pre_topc(X1) ),
% 2.94/1.00      inference(cnf_transformation,[],[f66]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_393,plain,
% 2.94/1.00      ( ~ m1_connsp_2(X0,X1,X2)
% 2.94/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.94/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.94/1.00      | r2_hidden(X2,X0)
% 2.94/1.00      | ~ v2_pre_topc(X1)
% 2.94/1.00      | ~ l1_pre_topc(X1)
% 2.94/1.00      | sK2 != X1 ),
% 2.94/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_26]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_394,plain,
% 2.94/1.00      ( ~ m1_connsp_2(X0,sK2,X1)
% 2.94/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.94/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.94/1.00      | r2_hidden(X1,X0)
% 2.94/1.00      | ~ v2_pre_topc(sK2)
% 2.94/1.00      | ~ l1_pre_topc(sK2) ),
% 2.94/1.00      inference(unflattening,[status(thm)],[c_393]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_398,plain,
% 2.94/1.00      ( ~ m1_connsp_2(X0,sK2,X1)
% 2.94/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.94/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.94/1.00      | r2_hidden(X1,X0) ),
% 2.94/1.00      inference(global_propositional_subsumption,
% 2.94/1.00                [status(thm)],
% 2.94/1.00                [c_394,c_25,c_24]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_481,plain,
% 2.94/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.94/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.94/1.00      | r2_hidden(X0,X1)
% 2.94/1.00      | ~ r2_hidden(X0,k1_tops_1(sK2,X1)) ),
% 2.94/1.00      inference(resolution,[status(thm)],[c_446,c_398]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_3327,plain,
% 2.94/1.00      ( ~ m1_subset_1(X0_45,u1_struct_0(sK2))
% 2.94/1.00      | ~ m1_subset_1(X1_45,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.94/1.00      | r2_hidden(X0_45,X1_45)
% 2.94/1.00      | ~ r2_hidden(X0_45,k1_tops_1(sK2,X1_45)) ),
% 2.94/1.00      inference(subtyping,[status(esa)],[c_481]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_3974,plain,
% 2.94/1.00      ( m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top
% 2.94/1.00      | m1_subset_1(X1_45,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.94/1.00      | r2_hidden(X0_45,X1_45) = iProver_top
% 2.94/1.00      | r2_hidden(X0_45,k1_tops_1(sK2,X1_45)) != iProver_top ),
% 2.94/1.00      inference(predicate_to_equality,[status(thm)],[c_3327]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_3382,plain,
% 2.94/1.00      ( m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top
% 2.94/1.00      | m1_subset_1(X1_45,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.94/1.00      | r2_hidden(X0_45,X1_45) = iProver_top
% 2.94/1.00      | r2_hidden(X0_45,k1_tops_1(sK2,X1_45)) != iProver_top ),
% 2.94/1.00      inference(predicate_to_equality,[status(thm)],[c_3327]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_8,plain,
% 2.94/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.94/1.00      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.94/1.00      | ~ l1_pre_topc(X1) ),
% 2.94/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_873,plain,
% 2.94/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.94/1.00      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.94/1.00      | sK2 != X1 ),
% 2.94/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_24]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_874,plain,
% 2.94/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.94/1.00      | m1_subset_1(k1_tops_1(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.94/1.00      inference(unflattening,[status(thm)],[c_873]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_3316,plain,
% 2.94/1.00      ( ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.94/1.00      | m1_subset_1(k1_tops_1(sK2,X0_45),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.94/1.00      inference(subtyping,[status(esa)],[c_874]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_3987,plain,
% 2.94/1.00      ( m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.94/1.00      | m1_subset_1(k1_tops_1(sK2,X0_45),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 2.94/1.00      inference(predicate_to_equality,[status(thm)],[c_3316]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_6,plain,
% 2.94/1.00      ( m1_subset_1(X0,X1)
% 2.94/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.94/1.00      | ~ r2_hidden(X0,X2) ),
% 2.94/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_3331,plain,
% 2.94/1.00      ( m1_subset_1(X0_45,X1_45)
% 2.94/1.00      | ~ m1_subset_1(X2_45,k1_zfmisc_1(X1_45))
% 2.94/1.00      | ~ r2_hidden(X0_45,X2_45) ),
% 2.94/1.00      inference(subtyping,[status(esa)],[c_6]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_3970,plain,
% 2.94/1.00      ( m1_subset_1(X0_45,X1_45) = iProver_top
% 2.94/1.00      | m1_subset_1(X2_45,k1_zfmisc_1(X1_45)) != iProver_top
% 2.94/1.00      | r2_hidden(X0_45,X2_45) != iProver_top ),
% 2.94/1.00      inference(predicate_to_equality,[status(thm)],[c_3331]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_5088,plain,
% 2.94/1.00      ( m1_subset_1(X0_45,u1_struct_0(sK2)) = iProver_top
% 2.94/1.00      | m1_subset_1(X1_45,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.94/1.00      | r2_hidden(X0_45,k1_tops_1(sK2,X1_45)) != iProver_top ),
% 2.94/1.00      inference(superposition,[status(thm)],[c_3987,c_3970]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_7007,plain,
% 2.94/1.00      ( m1_subset_1(X1_45,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.94/1.00      | r2_hidden(X0_45,X1_45) = iProver_top
% 2.94/1.00      | r2_hidden(X0_45,k1_tops_1(sK2,X1_45)) != iProver_top ),
% 2.94/1.00      inference(global_propositional_subsumption,
% 2.94/1.00                [status(thm)],
% 2.94/1.00                [c_3974,c_3382,c_5088]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_7008,plain,
% 2.94/1.00      ( m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.94/1.00      | r2_hidden(X1_45,X0_45) = iProver_top
% 2.94/1.00      | r2_hidden(X1_45,k1_tops_1(sK2,X0_45)) != iProver_top ),
% 2.94/1.00      inference(renaming,[status(thm)],[c_7007]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_7016,plain,
% 2.94/1.00      ( r2_hidden(X0_45,k1_tops_1(sK2,sK4)) != iProver_top
% 2.94/1.00      | r2_hidden(X0_45,sK4) = iProver_top ),
% 2.94/1.00      inference(superposition,[status(thm)],[c_3971,c_7008]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_7082,plain,
% 2.94/1.00      ( r2_hidden(sK0(k1_tops_1(sK2,sK4),X0_45),sK4) = iProver_top
% 2.94/1.00      | r1_tarski(k1_tops_1(sK2,sK4),X0_45) = iProver_top ),
% 2.94/1.00      inference(superposition,[status(thm)],[c_3966,c_7016]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_0,plain,
% 2.94/1.00      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 2.94/1.00      inference(cnf_transformation,[],[f49]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_3336,plain,
% 2.94/1.00      ( ~ r2_hidden(sK0(X0_45,X1_45),X1_45) | r1_tarski(X0_45,X1_45) ),
% 2.94/1.00      inference(subtyping,[status(esa)],[c_0]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_3965,plain,
% 2.94/1.00      ( r2_hidden(sK0(X0_45,X1_45),X1_45) != iProver_top
% 2.94/1.00      | r1_tarski(X0_45,X1_45) = iProver_top ),
% 2.94/1.00      inference(predicate_to_equality,[status(thm)],[c_3336]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_7264,plain,
% 2.94/1.00      ( r1_tarski(k1_tops_1(sK2,sK4),sK4) = iProver_top ),
% 2.94/1.00      inference(superposition,[status(thm)],[c_7082,c_3965]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_4558,plain,
% 2.94/1.00      ( r1_tarski(X0_45,X0_45) = iProver_top ),
% 2.94/1.00      inference(superposition,[status(thm)],[c_3966,c_3965]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_21,negated_conjecture,
% 2.94/1.00      ( m1_connsp_2(sK4,sK2,sK3) ),
% 2.94/1.00      inference(cnf_transformation,[],[f72]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_18,plain,
% 2.94/1.00      ( ~ m1_connsp_2(X0,X1,X2)
% 2.94/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.94/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.94/1.00      | r2_hidden(X2,k1_tops_1(X1,X0))
% 2.94/1.00      | v2_struct_0(X1)
% 2.94/1.00      | ~ v2_pre_topc(X1)
% 2.94/1.00      | ~ l1_pre_topc(X1) ),
% 2.94/1.00      inference(cnf_transformation,[],[f64]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_417,plain,
% 2.94/1.00      ( ~ m1_connsp_2(X0,X1,X2)
% 2.94/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.94/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.94/1.00      | r2_hidden(X2,k1_tops_1(X1,X0))
% 2.94/1.00      | ~ v2_pre_topc(X1)
% 2.94/1.00      | ~ l1_pre_topc(X1)
% 2.94/1.00      | sK2 != X1 ),
% 2.94/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_26]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_418,plain,
% 2.94/1.00      ( ~ m1_connsp_2(X0,sK2,X1)
% 2.94/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.94/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.94/1.00      | r2_hidden(X1,k1_tops_1(sK2,X0))
% 2.94/1.00      | ~ v2_pre_topc(sK2)
% 2.94/1.00      | ~ l1_pre_topc(sK2) ),
% 2.94/1.00      inference(unflattening,[status(thm)],[c_417]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_422,plain,
% 2.94/1.00      ( ~ m1_connsp_2(X0,sK2,X1)
% 2.94/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.94/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.94/1.00      | r2_hidden(X1,k1_tops_1(sK2,X0)) ),
% 2.94/1.00      inference(global_propositional_subsumption,
% 2.94/1.00                [status(thm)],
% 2.94/1.00                [c_418,c_25,c_24]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_542,plain,
% 2.94/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.94/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.94/1.00      | r2_hidden(X0,k1_tops_1(sK2,X1))
% 2.94/1.00      | sK3 != X0
% 2.94/1.00      | sK2 != sK2
% 2.94/1.00      | sK4 != X1 ),
% 2.94/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_422]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_543,plain,
% 2.94/1.00      ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 2.94/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.94/1.00      | r2_hidden(sK3,k1_tops_1(sK2,sK4)) ),
% 2.94/1.00      inference(unflattening,[status(thm)],[c_542]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_23,negated_conjecture,
% 2.94/1.00      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 2.94/1.00      inference(cnf_transformation,[],[f70]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_545,plain,
% 2.94/1.00      ( r2_hidden(sK3,k1_tops_1(sK2,sK4)) ),
% 2.94/1.00      inference(global_propositional_subsumption,
% 2.94/1.00                [status(thm)],
% 2.94/1.00                [c_543,c_23,c_22]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_3325,plain,
% 2.94/1.00      ( r2_hidden(sK3,k1_tops_1(sK2,sK4)) ),
% 2.94/1.00      inference(subtyping,[status(esa)],[c_545]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_3976,plain,
% 2.94/1.00      ( r2_hidden(sK3,k1_tops_1(sK2,sK4)) = iProver_top ),
% 2.94/1.00      inference(predicate_to_equality,[status(thm)],[c_3325]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_7,plain,
% 2.94/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.94/1.00      | ~ r2_hidden(X2,X0)
% 2.94/1.00      | ~ v1_xboole_0(X1) ),
% 2.94/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_4,plain,
% 2.94/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.94/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_206,plain,
% 2.94/1.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.94/1.00      inference(prop_impl,[status(thm)],[c_4]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_207,plain,
% 2.94/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.94/1.00      inference(renaming,[status(thm)],[c_206]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_269,plain,
% 2.94/1.00      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X2) | ~ v1_xboole_0(X2) ),
% 2.94/1.00      inference(bin_hyper_res,[status(thm)],[c_7,c_207]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_3328,plain,
% 2.94/1.00      ( ~ r2_hidden(X0_45,X1_45)
% 2.94/1.00      | ~ r1_tarski(X1_45,X2_45)
% 2.94/1.00      | ~ v1_xboole_0(X2_45) ),
% 2.94/1.00      inference(subtyping,[status(esa)],[c_269]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_3973,plain,
% 2.94/1.00      ( r2_hidden(X0_45,X1_45) != iProver_top
% 2.94/1.00      | r1_tarski(X1_45,X2_45) != iProver_top
% 2.94/1.00      | v1_xboole_0(X2_45) != iProver_top ),
% 2.94/1.00      inference(predicate_to_equality,[status(thm)],[c_3328]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_5836,plain,
% 2.94/1.00      ( r1_tarski(k1_tops_1(sK2,sK4),X0_45) != iProver_top
% 2.94/1.00      | v1_xboole_0(X0_45) != iProver_top ),
% 2.94/1.00      inference(superposition,[status(thm)],[c_3976,c_3973]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_6895,plain,
% 2.94/1.00      ( v1_xboole_0(k1_tops_1(sK2,sK4)) != iProver_top ),
% 2.94/1.00      inference(superposition,[status(thm)],[c_4558,c_5836]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_3346,plain,
% 2.94/1.00      ( ~ r2_hidden(X0_45,X1_45)
% 2.94/1.00      | r2_hidden(X2_45,X3_45)
% 2.94/1.00      | X2_45 != X0_45
% 2.94/1.00      | X3_45 != X1_45 ),
% 2.94/1.00      theory(equality) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_4270,plain,
% 2.94/1.00      ( r2_hidden(X0_45,X1_45)
% 2.94/1.00      | ~ r2_hidden(sK3,k1_tops_1(sK2,sK4))
% 2.94/1.00      | X1_45 != k1_tops_1(sK2,sK4)
% 2.94/1.00      | X0_45 != sK3 ),
% 2.94/1.00      inference(instantiation,[status(thm)],[c_3346]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_4731,plain,
% 2.94/1.00      ( r2_hidden(X0_45,k1_tops_1(sK2,k1_tops_1(sK2,sK4)))
% 2.94/1.00      | ~ r2_hidden(sK3,k1_tops_1(sK2,sK4))
% 2.94/1.00      | X0_45 != sK3
% 2.94/1.00      | k1_tops_1(sK2,k1_tops_1(sK2,sK4)) != k1_tops_1(sK2,sK4) ),
% 2.94/1.00      inference(instantiation,[status(thm)],[c_4270]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_4732,plain,
% 2.94/1.00      ( X0_45 != sK3
% 2.94/1.00      | k1_tops_1(sK2,k1_tops_1(sK2,sK4)) != k1_tops_1(sK2,sK4)
% 2.94/1.00      | r2_hidden(X0_45,k1_tops_1(sK2,k1_tops_1(sK2,sK4))) = iProver_top
% 2.94/1.00      | r2_hidden(sK3,k1_tops_1(sK2,sK4)) != iProver_top ),
% 2.94/1.00      inference(predicate_to_equality,[status(thm)],[c_4731]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_4734,plain,
% 2.94/1.00      ( k1_tops_1(sK2,k1_tops_1(sK2,sK4)) != k1_tops_1(sK2,sK4)
% 2.94/1.00      | sK3 != sK3
% 2.94/1.00      | r2_hidden(sK3,k1_tops_1(sK2,k1_tops_1(sK2,sK4))) = iProver_top
% 2.94/1.00      | r2_hidden(sK3,k1_tops_1(sK2,sK4)) != iProver_top ),
% 2.94/1.00      inference(instantiation,[status(thm)],[c_4732]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_20,negated_conjecture,
% 2.94/1.00      ( ~ m1_connsp_2(X0,sK2,sK3)
% 2.94/1.00      | ~ v3_pre_topc(X0,sK2)
% 2.94/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.94/1.00      | ~ r1_tarski(X0,sK4)
% 2.94/1.00      | v1_xboole_0(X0) ),
% 2.94/1.00      inference(cnf_transformation,[],[f73]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_515,plain,
% 2.94/1.00      ( ~ v3_pre_topc(X0,sK2)
% 2.94/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.94/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.94/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.94/1.00      | ~ r2_hidden(X1,k1_tops_1(sK2,X2))
% 2.94/1.00      | ~ r1_tarski(X0,sK4)
% 2.94/1.00      | v1_xboole_0(X0)
% 2.94/1.00      | X2 != X0
% 2.94/1.00      | sK3 != X1
% 2.94/1.00      | sK2 != sK2 ),
% 2.94/1.00      inference(resolution_lifted,[status(thm)],[c_20,c_446]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_516,plain,
% 2.94/1.00      ( ~ v3_pre_topc(X0,sK2)
% 2.94/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.94/1.00      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 2.94/1.00      | ~ r2_hidden(sK3,k1_tops_1(sK2,X0))
% 2.94/1.00      | ~ r1_tarski(X0,sK4)
% 2.94/1.00      | v1_xboole_0(X0) ),
% 2.94/1.00      inference(unflattening,[status(thm)],[c_515]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_520,plain,
% 2.94/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.94/1.00      | ~ v3_pre_topc(X0,sK2)
% 2.94/1.00      | ~ r2_hidden(sK3,k1_tops_1(sK2,X0))
% 2.94/1.00      | ~ r1_tarski(X0,sK4)
% 2.94/1.00      | v1_xboole_0(X0) ),
% 2.94/1.00      inference(global_propositional_subsumption,
% 2.94/1.00                [status(thm)],
% 2.94/1.00                [c_516,c_23]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_521,plain,
% 2.94/1.00      ( ~ v3_pre_topc(X0,sK2)
% 2.94/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.94/1.00      | ~ r2_hidden(sK3,k1_tops_1(sK2,X0))
% 2.94/1.00      | ~ r1_tarski(X0,sK4)
% 2.94/1.00      | v1_xboole_0(X0) ),
% 2.94/1.00      inference(renaming,[status(thm)],[c_520]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_3326,plain,
% 2.94/1.00      ( ~ v3_pre_topc(X0_45,sK2)
% 2.94/1.00      | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.94/1.00      | ~ r2_hidden(sK3,k1_tops_1(sK2,X0_45))
% 2.94/1.00      | ~ r1_tarski(X0_45,sK4)
% 2.94/1.00      | v1_xboole_0(X0_45) ),
% 2.94/1.00      inference(subtyping,[status(esa)],[c_521]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_4314,plain,
% 2.94/1.00      ( ~ v3_pre_topc(k1_tops_1(sK2,sK4),sK2)
% 2.94/1.00      | ~ m1_subset_1(k1_tops_1(sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.94/1.00      | ~ r2_hidden(sK3,k1_tops_1(sK2,k1_tops_1(sK2,sK4)))
% 2.94/1.00      | ~ r1_tarski(k1_tops_1(sK2,sK4),sK4)
% 2.94/1.00      | v1_xboole_0(k1_tops_1(sK2,sK4)) ),
% 2.94/1.00      inference(instantiation,[status(thm)],[c_3326]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_4318,plain,
% 2.94/1.00      ( v3_pre_topc(k1_tops_1(sK2,sK4),sK2) != iProver_top
% 2.94/1.00      | m1_subset_1(k1_tops_1(sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.94/1.00      | r2_hidden(sK3,k1_tops_1(sK2,k1_tops_1(sK2,sK4))) != iProver_top
% 2.94/1.00      | r1_tarski(k1_tops_1(sK2,sK4),sK4) != iProver_top
% 2.94/1.00      | v1_xboole_0(k1_tops_1(sK2,sK4)) = iProver_top ),
% 2.94/1.00      inference(predicate_to_equality,[status(thm)],[c_4314]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_16,plain,
% 2.94/1.00      ( ~ v3_pre_topc(X0,X1)
% 2.94/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 2.94/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.94/1.00      | ~ v2_pre_topc(X3)
% 2.94/1.00      | ~ l1_pre_topc(X3)
% 2.94/1.00      | ~ l1_pre_topc(X1)
% 2.94/1.00      | k1_tops_1(X1,X0) = X0 ),
% 2.94/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_792,plain,
% 2.94/1.00      ( ~ v3_pre_topc(X0,X1)
% 2.94/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.94/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 2.94/1.00      | ~ l1_pre_topc(X1)
% 2.94/1.00      | ~ l1_pre_topc(X3)
% 2.94/1.00      | k1_tops_1(X1,X0) = X0
% 2.94/1.00      | sK2 != X3 ),
% 2.94/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_25]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_793,plain,
% 2.94/1.00      ( ~ v3_pre_topc(X0,X1)
% 2.94/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.94/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.94/1.00      | ~ l1_pre_topc(X1)
% 2.94/1.00      | ~ l1_pre_topc(sK2)
% 2.94/1.00      | k1_tops_1(X1,X0) = X0 ),
% 2.94/1.00      inference(unflattening,[status(thm)],[c_792]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_797,plain,
% 2.94/1.00      ( ~ l1_pre_topc(X1)
% 2.94/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.94/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.94/1.00      | ~ v3_pre_topc(X0,X1)
% 2.94/1.00      | k1_tops_1(X1,X0) = X0 ),
% 2.94/1.00      inference(global_propositional_subsumption,
% 2.94/1.00                [status(thm)],
% 2.94/1.00                [c_793,c_24]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_798,plain,
% 2.94/1.00      ( ~ v3_pre_topc(X0,X1)
% 2.94/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.94/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.94/1.00      | ~ l1_pre_topc(X1)
% 2.94/1.00      | k1_tops_1(X1,X0) = X0 ),
% 2.94/1.00      inference(renaming,[status(thm)],[c_797]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_855,plain,
% 2.94/1.00      ( ~ v3_pre_topc(X0,X1)
% 2.94/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.94/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.94/1.00      | k1_tops_1(X1,X0) = X0
% 2.94/1.00      | sK2 != X1 ),
% 2.94/1.00      inference(resolution_lifted,[status(thm)],[c_798,c_24]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_856,plain,
% 2.94/1.00      ( ~ v3_pre_topc(X0,sK2)
% 2.94/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.94/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.94/1.00      | k1_tops_1(sK2,X0) = X0 ),
% 2.94/1.00      inference(unflattening,[status(thm)],[c_855]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_3317,plain,
% 2.94/1.00      ( ~ v3_pre_topc(X0_45,sK2)
% 2.94/1.00      | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.94/1.00      | ~ m1_subset_1(X1_45,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.94/1.00      | k1_tops_1(sK2,X0_45) = X0_45 ),
% 2.94/1.00      inference(subtyping,[status(esa)],[c_856]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_3338,plain,
% 2.94/1.00      ( ~ v3_pre_topc(X0_45,sK2)
% 2.94/1.00      | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.94/1.00      | k1_tops_1(sK2,X0_45) = X0_45
% 2.94/1.00      | ~ sP1_iProver_split ),
% 2.94/1.00      inference(splitting,
% 2.94/1.00                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 2.94/1.00                [c_3317]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_3339,plain,
% 2.94/1.00      ( sP1_iProver_split | sP0_iProver_split ),
% 2.94/1.00      inference(splitting,
% 2.94/1.00                [splitting(split),new_symbols(definition,[])],
% 2.94/1.00                [c_3317]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_3337,plain,
% 2.94/1.00      ( ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.94/1.00      | ~ sP0_iProver_split ),
% 2.94/1.00      inference(splitting,
% 2.94/1.00                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.94/1.00                [c_3317]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_3482,plain,
% 2.94/1.00      ( k1_tops_1(sK2,X0_45) = X0_45
% 2.94/1.00      | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.94/1.00      | ~ v3_pre_topc(X0_45,sK2) ),
% 2.94/1.00      inference(global_propositional_subsumption,
% 2.94/1.00                [status(thm)],
% 2.94/1.00                [c_3338,c_3339,c_3337]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_3483,plain,
% 2.94/1.00      ( ~ v3_pre_topc(X0_45,sK2)
% 2.94/1.00      | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.94/1.00      | k1_tops_1(sK2,X0_45) = X0_45 ),
% 2.94/1.00      inference(renaming,[status(thm)],[c_3482]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_4315,plain,
% 2.94/1.00      ( ~ v3_pre_topc(k1_tops_1(sK2,sK4),sK2)
% 2.94/1.00      | ~ m1_subset_1(k1_tops_1(sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.94/1.00      | k1_tops_1(sK2,k1_tops_1(sK2,sK4)) = k1_tops_1(sK2,sK4) ),
% 2.94/1.00      inference(instantiation,[status(thm)],[c_3483]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_9,plain,
% 2.94/1.00      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 2.94/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.94/1.00      | ~ v2_pre_topc(X0)
% 2.94/1.00      | ~ l1_pre_topc(X0) ),
% 2.94/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_656,plain,
% 2.94/1.00      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 2.94/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.94/1.00      | ~ l1_pre_topc(X0)
% 2.94/1.00      | sK2 != X0 ),
% 2.94/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_25]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_657,plain,
% 2.94/1.00      ( v3_pre_topc(k1_tops_1(sK2,X0),sK2)
% 2.94/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.94/1.00      | ~ l1_pre_topc(sK2) ),
% 2.94/1.00      inference(unflattening,[status(thm)],[c_656]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_661,plain,
% 2.94/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.94/1.00      | v3_pre_topc(k1_tops_1(sK2,X0),sK2) ),
% 2.94/1.00      inference(global_propositional_subsumption,
% 2.94/1.00                [status(thm)],
% 2.94/1.00                [c_657,c_24]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_662,plain,
% 2.94/1.00      ( v3_pre_topc(k1_tops_1(sK2,X0),sK2)
% 2.94/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.94/1.00      inference(renaming,[status(thm)],[c_661]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_3322,plain,
% 2.94/1.00      ( v3_pre_topc(k1_tops_1(sK2,X0_45),sK2)
% 2.94/1.00      | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.94/1.00      inference(subtyping,[status(esa)],[c_662]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_4185,plain,
% 2.94/1.00      ( v3_pre_topc(k1_tops_1(sK2,sK4),sK2)
% 2.94/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.94/1.00      inference(instantiation,[status(thm)],[c_3322]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_4186,plain,
% 2.94/1.00      ( v3_pre_topc(k1_tops_1(sK2,sK4),sK2) = iProver_top
% 2.94/1.00      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 2.94/1.00      inference(predicate_to_equality,[status(thm)],[c_4185]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_4182,plain,
% 2.94/1.00      ( m1_subset_1(k1_tops_1(sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.94/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.94/1.00      inference(instantiation,[status(thm)],[c_3316]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_4183,plain,
% 2.94/1.00      ( m1_subset_1(k1_tops_1(sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 2.94/1.00      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 2.94/1.00      inference(predicate_to_equality,[status(thm)],[c_4182]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_3343,plain,( X0_45 = X0_45 ),theory(equality) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_3360,plain,
% 2.94/1.00      ( sK3 = sK3 ),
% 2.94/1.00      inference(instantiation,[status(thm)],[c_3343]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_544,plain,
% 2.94/1.00      ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 2.94/1.00      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.94/1.00      | r2_hidden(sK3,k1_tops_1(sK2,sK4)) = iProver_top ),
% 2.94/1.00      inference(predicate_to_equality,[status(thm)],[c_543]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_31,plain,
% 2.94/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 2.94/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(c_30,plain,
% 2.94/1.00      ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
% 2.94/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.94/1.00  
% 2.94/1.00  cnf(contradiction,plain,
% 2.94/1.00      ( $false ),
% 2.94/1.00      inference(minisat,
% 2.94/1.00                [status(thm)],
% 2.94/1.00                [c_7264,c_6895,c_4734,c_4318,c_4315,c_4186,c_4185,c_4183,
% 2.94/1.00                 c_4182,c_3360,c_544,c_31,c_22,c_30]) ).
% 2.94/1.00  
% 2.94/1.00  
% 2.94/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.94/1.00  
% 2.94/1.00  ------                               Statistics
% 2.94/1.00  
% 2.94/1.00  ------ General
% 2.94/1.00  
% 2.94/1.00  abstr_ref_over_cycles:                  0
% 2.94/1.00  abstr_ref_under_cycles:                 0
% 2.94/1.00  gc_basic_clause_elim:                   0
% 2.94/1.00  forced_gc_time:                         0
% 2.94/1.00  parsing_time:                           0.01
% 2.94/1.00  unif_index_cands_time:                  0.
% 2.94/1.00  unif_index_add_time:                    0.
% 2.94/1.00  orderings_time:                         0.
% 2.94/1.00  out_proof_time:                         0.01
% 2.94/1.00  total_time:                             0.166
% 2.94/1.00  num_of_symbols:                         53
% 2.94/1.00  num_of_terms:                           4728
% 2.94/1.00  
% 2.94/1.00  ------ Preprocessing
% 2.94/1.00  
% 2.94/1.00  num_of_splits:                          4
% 2.94/1.00  num_of_split_atoms:                     3
% 2.94/1.00  num_of_reused_defs:                     1
% 2.94/1.00  num_eq_ax_congr_red:                    20
% 2.94/1.00  num_of_sem_filtered_clauses:            4
% 2.94/1.00  num_of_subtypes:                        2
% 2.94/1.00  monotx_restored_types:                  1
% 2.94/1.00  sat_num_of_epr_types:                   0
% 2.94/1.00  sat_num_of_non_cyclic_types:            0
% 2.94/1.00  sat_guarded_non_collapsed_types:        0
% 2.94/1.00  num_pure_diseq_elim:                    0
% 2.94/1.00  simp_replaced_by:                       0
% 2.94/1.00  res_preprocessed:                       117
% 2.94/1.00  prep_upred:                             0
% 2.94/1.00  prep_unflattend:                        140
% 2.94/1.00  smt_new_axioms:                         0
% 2.94/1.00  pred_elim_cands:                        5
% 2.94/1.00  pred_elim:                              4
% 2.94/1.00  pred_elim_cl:                           3
% 2.94/1.00  pred_elim_cycles:                       14
% 2.94/1.00  merged_defs:                            8
% 2.94/1.00  merged_defs_ncl:                        0
% 2.94/1.00  bin_hyper_res:                          10
% 2.94/1.00  prep_cycles:                            4
% 2.94/1.00  pred_elim_time:                         0.042
% 2.94/1.00  splitting_time:                         0.
% 2.94/1.00  sem_filter_time:                        0.
% 2.94/1.00  monotx_time:                            0.
% 2.94/1.00  subtype_inf_time:                       0.001
% 2.94/1.00  
% 2.94/1.00  ------ Problem properties
% 2.94/1.00  
% 2.94/1.00  clauses:                                27
% 2.94/1.00  conjectures:                            2
% 2.94/1.00  epr:                                    6
% 2.94/1.00  horn:                                   24
% 2.94/1.00  ground:                                 7
% 2.94/1.00  unary:                                  4
% 2.94/1.00  binary:                                 11
% 2.94/1.00  lits:                                   70
% 2.94/1.00  lits_eq:                                2
% 2.94/1.00  fd_pure:                                0
% 2.94/1.00  fd_pseudo:                              0
% 2.94/1.00  fd_cond:                                0
% 2.94/1.00  fd_pseudo_cond:                         0
% 2.94/1.00  ac_symbols:                             0
% 2.94/1.00  
% 2.94/1.00  ------ Propositional Solver
% 2.94/1.00  
% 2.94/1.00  prop_solver_calls:                      27
% 2.94/1.00  prop_fast_solver_calls:                 1536
% 2.94/1.00  smt_solver_calls:                       0
% 2.94/1.00  smt_fast_solver_calls:                  0
% 2.94/1.00  prop_num_of_clauses:                    2091
% 2.94/1.00  prop_preprocess_simplified:             6331
% 2.94/1.00  prop_fo_subsumed:                       58
% 2.94/1.00  prop_solver_time:                       0.
% 2.94/1.00  smt_solver_time:                        0.
% 2.94/1.00  smt_fast_solver_time:                   0.
% 2.94/1.00  prop_fast_solver_time:                  0.
% 2.94/1.00  prop_unsat_core_time:                   0.
% 2.94/1.00  
% 2.94/1.00  ------ QBF
% 2.94/1.00  
% 2.94/1.00  qbf_q_res:                              0
% 2.94/1.00  qbf_num_tautologies:                    0
% 2.94/1.00  qbf_prep_cycles:                        0
% 2.94/1.00  
% 2.94/1.00  ------ BMC1
% 2.94/1.00  
% 2.94/1.00  bmc1_current_bound:                     -1
% 2.94/1.00  bmc1_last_solved_bound:                 -1
% 2.94/1.00  bmc1_unsat_core_size:                   -1
% 2.94/1.00  bmc1_unsat_core_parents_size:           -1
% 2.94/1.00  bmc1_merge_next_fun:                    0
% 2.94/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.94/1.00  
% 2.94/1.00  ------ Instantiation
% 2.94/1.00  
% 2.94/1.00  inst_num_of_clauses:                    463
% 2.94/1.00  inst_num_in_passive:                    96
% 2.94/1.00  inst_num_in_active:                     201
% 2.94/1.00  inst_num_in_unprocessed:                166
% 2.94/1.00  inst_num_of_loops:                      250
% 2.94/1.00  inst_num_of_learning_restarts:          0
% 2.94/1.00  inst_num_moves_active_passive:          47
% 2.94/1.00  inst_lit_activity:                      0
% 2.94/1.00  inst_lit_activity_moves:                0
% 2.94/1.00  inst_num_tautologies:                   0
% 2.94/1.00  inst_num_prop_implied:                  0
% 2.94/1.00  inst_num_existing_simplified:           0
% 2.94/1.00  inst_num_eq_res_simplified:             0
% 2.94/1.00  inst_num_child_elim:                    0
% 2.94/1.00  inst_num_of_dismatching_blockings:      102
% 2.94/1.00  inst_num_of_non_proper_insts:           417
% 2.94/1.00  inst_num_of_duplicates:                 0
% 2.94/1.00  inst_inst_num_from_inst_to_res:         0
% 2.94/1.00  inst_dismatching_checking_time:         0.
% 2.94/1.00  
% 2.94/1.00  ------ Resolution
% 2.94/1.00  
% 2.94/1.00  res_num_of_clauses:                     0
% 2.94/1.00  res_num_in_passive:                     0
% 2.94/1.00  res_num_in_active:                      0
% 2.94/1.00  res_num_of_loops:                       121
% 2.94/1.00  res_forward_subset_subsumed:            9
% 2.94/1.00  res_backward_subset_subsumed:           0
% 2.94/1.00  res_forward_subsumed:                   1
% 2.94/1.00  res_backward_subsumed:                  3
% 2.94/1.00  res_forward_subsumption_resolution:     6
% 2.94/1.00  res_backward_subsumption_resolution:    0
% 2.94/1.00  res_clause_to_clause_subsumption:       821
% 2.94/1.00  res_orphan_elimination:                 0
% 2.94/1.00  res_tautology_del:                      51
% 2.94/1.00  res_num_eq_res_simplified:              0
% 2.94/1.00  res_num_sel_changes:                    0
% 2.94/1.00  res_moves_from_active_to_pass:          0
% 2.94/1.00  
% 2.94/1.00  ------ Superposition
% 2.94/1.00  
% 2.94/1.00  sup_time_total:                         0.
% 2.94/1.00  sup_time_generating:                    0.
% 2.94/1.00  sup_time_sim_full:                      0.
% 2.94/1.00  sup_time_sim_immed:                     0.
% 2.94/1.00  
% 2.94/1.00  sup_num_of_clauses:                     89
% 2.94/1.00  sup_num_in_active:                      49
% 2.94/1.00  sup_num_in_passive:                     40
% 2.94/1.00  sup_num_of_loops:                       48
% 2.94/1.00  sup_fw_superposition:                   58
% 2.94/1.00  sup_bw_superposition:                   22
% 2.94/1.00  sup_immediate_simplified:               7
% 2.94/1.00  sup_given_eliminated:                   0
% 2.94/1.00  comparisons_done:                       0
% 2.94/1.00  comparisons_avoided:                    0
% 2.94/1.00  
% 2.94/1.00  ------ Simplifications
% 2.94/1.00  
% 2.94/1.00  
% 2.94/1.00  sim_fw_subset_subsumed:                 5
% 2.94/1.00  sim_bw_subset_subsumed:                 0
% 2.94/1.00  sim_fw_subsumed:                        1
% 2.94/1.00  sim_bw_subsumed:                        1
% 2.94/1.00  sim_fw_subsumption_res:                 1
% 2.94/1.00  sim_bw_subsumption_res:                 0
% 2.94/1.00  sim_tautology_del:                      2
% 2.94/1.00  sim_eq_tautology_del:                   0
% 2.94/1.00  sim_eq_res_simp:                        0
% 2.94/1.00  sim_fw_demodulated:                     0
% 2.94/1.00  sim_bw_demodulated:                     0
% 2.94/1.00  sim_light_normalised:                   0
% 2.94/1.00  sim_joinable_taut:                      0
% 2.94/1.00  sim_joinable_simp:                      0
% 2.94/1.00  sim_ac_normalised:                      0
% 2.94/1.00  sim_smt_subsumption:                    0
% 2.94/1.00  
%------------------------------------------------------------------------------
