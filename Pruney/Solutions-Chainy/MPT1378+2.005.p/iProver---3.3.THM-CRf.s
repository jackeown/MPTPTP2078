%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:18:10 EST 2020

% Result     : Theorem 11.65s
% Output     : CNFRefutation 11.65s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 351 expanded)
%              Number of clauses        :   49 (  71 expanded)
%              Number of leaves         :   15 ( 128 expanded)
%              Depth                    :   21
%              Number of atoms          :  431 (2622 expanded)
%              Number of equality atoms :   25 (  29 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f15])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f59,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f41])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).

fof(f37,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( m1_connsp_2(X3,X0,X1)
                      & m1_connsp_2(X2,X0,X1) )
                   => m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( ( m1_connsp_2(X3,X0,X1)
                        & m1_connsp_2(X2,X0,X1) )
                     => m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
                  & m1_connsp_2(X3,X0,X1)
                  & m1_connsp_2(X2,X0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
                  & m1_connsp_2(X3,X0,X1)
                  & m1_connsp_2(X2,X0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
          & m1_connsp_2(X3,X0,X1)
          & m1_connsp_2(X2,X0,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,sK4),X0,X1)
        & m1_connsp_2(sK4,X0,X1)
        & m1_connsp_2(X2,X0,X1)
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
              & m1_connsp_2(X3,X0,X1)
              & m1_connsp_2(X2,X0,X1)
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X3] :
            ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(X0),sK3,X3),X0,X1)
            & m1_connsp_2(X3,X0,X1)
            & m1_connsp_2(sK3,X0,X1)
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
                  & m1_connsp_2(X3,X0,X1)
                  & m1_connsp_2(X2,X0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,sK2)
                & m1_connsp_2(X3,X0,sK2)
                & m1_connsp_2(X2,X0,sK2)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
                    & m1_connsp_2(X3,X0,X1)
                    & m1_connsp_2(X2,X0,X1)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK1),X2,X3),sK1,X1)
                  & m1_connsp_2(X3,sK1,X1)
                  & m1_connsp_2(X2,sK1,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) )
          & m1_subset_1(X1,u1_struct_0(sK1)) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK1),sK3,sK4),sK1,sK2)
    & m1_connsp_2(sK4,sK1,sK2)
    & m1_connsp_2(sK3,sK1,sK2)
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f24,f35,f34,f33,f32])).

fof(f52,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f56,plain,(
    m1_connsp_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f51,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f50,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f53,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f36])).

fof(f54,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f36])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f13])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f58,plain,(
    ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK1),sK3,sK4),sK1,sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f55,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_516,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_2898,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | r1_tarski(X3,k4_subset_1(X1,X2,X0))
    | ~ r1_tarski(X4,k2_xboole_0(X2,X0))
    | X3 != X4 ),
    inference(resolution,[status(thm)],[c_516,c_8])).

cnf(c_6,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1700,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(resolution,[status(thm)],[c_6,c_4])).

cnf(c_10686,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | r1_tarski(X3,k4_subset_1(X1,X2,X0))
    | X3 != X2 ),
    inference(resolution,[status(thm)],[c_2898,c_1700])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_19,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_313,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X0))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_19])).

cnf(c_314,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X1,X0)
    | r1_tarski(k1_tops_1(sK1,X1),k1_tops_1(sK1,X0)) ),
    inference(unflattening,[status(thm)],[c_313])).

cnf(c_2661,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X2,k1_tops_1(sK1,X1))
    | r2_hidden(X2,k1_tops_1(sK1,X0))
    | ~ r1_tarski(X1,X0) ),
    inference(resolution,[status(thm)],[c_2,c_314])).

cnf(c_15,negated_conjecture,
    ( m1_connsp_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_11,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_12,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_117,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X0,X1,X2)
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11,c_12])).

cnf(c_118,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_117])).

cnf(c_20,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_234,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_118,c_20])).

cnf(c_235,plain,
    ( ~ m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | r2_hidden(X1,k1_tops_1(sK1,X0))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_234])).

cnf(c_21,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_239,plain,
    ( ~ m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | r2_hidden(X1,k1_tops_1(sK1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_235,c_21,c_19])).

cnf(c_385,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | r2_hidden(X0,k1_tops_1(sK1,X1))
    | sK2 != X0
    | sK3 != X1
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_239])).

cnf(c_386,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
    inference(unflattening,[status(thm)],[c_385])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_388,plain,
    ( r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_386,c_18])).

cnf(c_3120,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(sK2,k1_tops_1(sK1,X0))
    | ~ r1_tarski(sK3,X0) ),
    inference(resolution,[status(thm)],[c_2661,c_388])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_3319,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(sK2,k1_tops_1(sK1,X0))
    | ~ r1_tarski(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3120,c_17])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | m1_subset_1(k4_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_3341,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),X1,X0)))
    | ~ r1_tarski(sK3,k4_subset_1(u1_struct_0(sK1),X1,X0)) ),
    inference(resolution,[status(thm)],[c_3319,c_7])).

cnf(c_13,negated_conjecture,
    ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK1),sK3,sK4),sK1,sK2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_10,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_276,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_20])).

cnf(c_277,plain,
    ( m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X1,k1_tops_1(sK1,X0))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_276])).

cnf(c_281,plain,
    ( m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X1,k1_tops_1(sK1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_277,c_21,c_19])).

cnf(c_356,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X0,k1_tops_1(sK1,X1))
    | k4_subset_1(u1_struct_0(sK1),sK3,sK4) != X1
    | sK2 != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_281])).

cnf(c_357,plain,
    ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) ),
    inference(unflattening,[status(thm)],[c_356])).

cnf(c_359,plain,
    ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_357,c_18])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_964,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1061,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_964])).

cnf(c_1282,plain,
    ( ~ r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_359,c_18,c_17,c_16,c_357,c_1061])).

cnf(c_4394,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(sK3,k4_subset_1(u1_struct_0(sK1),sK3,sK4)) ),
    inference(resolution,[status(thm)],[c_3341,c_1282])).

cnf(c_4401,plain,
    ( ~ r1_tarski(sK3,k4_subset_1(u1_struct_0(sK1),sK3,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4394,c_17,c_16])).

cnf(c_45112,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | sK3 != sK3 ),
    inference(resolution,[status(thm)],[c_10686,c_4401])).

cnf(c_45113,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(equality_resolution_simp,[status(thm)],[c_45112])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_45113,c_16,c_17])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:30:51 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running in FOF mode
% 11.65/2.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.65/2.00  
% 11.65/2.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.65/2.00  
% 11.65/2.00  ------  iProver source info
% 11.65/2.00  
% 11.65/2.00  git: date: 2020-06-30 10:37:57 +0100
% 11.65/2.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.65/2.00  git: non_committed_changes: false
% 11.65/2.00  git: last_make_outside_of_git: false
% 11.65/2.00  
% 11.65/2.00  ------ 
% 11.65/2.00  ------ Parsing...
% 11.65/2.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.65/2.00  
% 11.65/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 11.65/2.00  
% 11.65/2.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.65/2.00  
% 11.65/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.65/2.00  ------ Proving...
% 11.65/2.00  ------ Problem Properties 
% 11.65/2.00  
% 11.65/2.00  
% 11.65/2.00  clauses                                 17
% 11.65/2.00  conjectures                             3
% 11.65/2.00  EPR                                     3
% 11.65/2.00  Horn                                    16
% 11.65/2.00  unary                                   8
% 11.65/2.00  binary                                  4
% 11.65/2.00  lits                                    32
% 11.65/2.00  lits eq                                 4
% 11.65/2.00  fd_pure                                 0
% 11.65/2.00  fd_pseudo                               0
% 11.65/2.00  fd_cond                                 0
% 11.65/2.00  fd_pseudo_cond                          1
% 11.65/2.00  AC symbols                              0
% 11.65/2.00  
% 11.65/2.00  ------ Input Options Time Limit: Unbounded
% 11.65/2.00  
% 11.65/2.00  
% 11.65/2.00  ------ 
% 11.65/2.00  Current options:
% 11.65/2.00  ------ 
% 11.65/2.00  
% 11.65/2.00  
% 11.65/2.00  
% 11.65/2.00  
% 11.65/2.00  ------ Proving...
% 11.65/2.00  
% 11.65/2.00  
% 11.65/2.00  % SZS status Theorem for theBenchmark.p
% 11.65/2.00  
% 11.65/2.00  % SZS output start CNFRefutation for theBenchmark.p
% 11.65/2.00  
% 11.65/2.00  fof(f5,axiom,(
% 11.65/2.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 11.65/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/2.00  
% 11.65/2.00  fof(f15,plain,(
% 11.65/2.00    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 11.65/2.00    inference(ennf_transformation,[],[f5])).
% 11.65/2.00  
% 11.65/2.00  fof(f16,plain,(
% 11.65/2.00    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.65/2.00    inference(flattening,[],[f15])).
% 11.65/2.00  
% 11.65/2.00  fof(f45,plain,(
% 11.65/2.00    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.65/2.00    inference(cnf_transformation,[],[f16])).
% 11.65/2.00  
% 11.65/2.00  fof(f3,axiom,(
% 11.65/2.00    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 11.65/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/2.00  
% 11.65/2.00  fof(f12,plain,(
% 11.65/2.00    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 11.65/2.00    inference(ennf_transformation,[],[f3])).
% 11.65/2.00  
% 11.65/2.00  fof(f43,plain,(
% 11.65/2.00    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 11.65/2.00    inference(cnf_transformation,[],[f12])).
% 11.65/2.00  
% 11.65/2.00  fof(f2,axiom,(
% 11.65/2.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.65/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/2.00  
% 11.65/2.00  fof(f29,plain,(
% 11.65/2.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.65/2.00    inference(nnf_transformation,[],[f2])).
% 11.65/2.00  
% 11.65/2.00  fof(f30,plain,(
% 11.65/2.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.65/2.00    inference(flattening,[],[f29])).
% 11.65/2.00  
% 11.65/2.00  fof(f41,plain,(
% 11.65/2.00    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 11.65/2.00    inference(cnf_transformation,[],[f30])).
% 11.65/2.00  
% 11.65/2.00  fof(f59,plain,(
% 11.65/2.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.65/2.00    inference(equality_resolution,[],[f41])).
% 11.65/2.00  
% 11.65/2.00  fof(f1,axiom,(
% 11.65/2.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 11.65/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/2.00  
% 11.65/2.00  fof(f11,plain,(
% 11.65/2.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 11.65/2.00    inference(ennf_transformation,[],[f1])).
% 11.65/2.00  
% 11.65/2.00  fof(f25,plain,(
% 11.65/2.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 11.65/2.00    inference(nnf_transformation,[],[f11])).
% 11.65/2.00  
% 11.65/2.00  fof(f26,plain,(
% 11.65/2.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 11.65/2.00    inference(rectify,[],[f25])).
% 11.65/2.00  
% 11.65/2.00  fof(f27,plain,(
% 11.65/2.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 11.65/2.00    introduced(choice_axiom,[])).
% 11.65/2.00  
% 11.65/2.00  fof(f28,plain,(
% 11.65/2.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 11.65/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).
% 11.65/2.00  
% 11.65/2.00  fof(f37,plain,(
% 11.65/2.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 11.65/2.00    inference(cnf_transformation,[],[f28])).
% 11.65/2.00  
% 11.65/2.00  fof(f6,axiom,(
% 11.65/2.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 11.65/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/2.00  
% 11.65/2.00  fof(f17,plain,(
% 11.65/2.00    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.65/2.00    inference(ennf_transformation,[],[f6])).
% 11.65/2.00  
% 11.65/2.00  fof(f18,plain,(
% 11.65/2.00    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.65/2.00    inference(flattening,[],[f17])).
% 11.65/2.00  
% 11.65/2.00  fof(f46,plain,(
% 11.65/2.00    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.65/2.00    inference(cnf_transformation,[],[f18])).
% 11.65/2.00  
% 11.65/2.00  fof(f9,conjecture,(
% 11.65/2.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1)) => m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1))))))),
% 11.65/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/2.00  
% 11.65/2.00  fof(f10,negated_conjecture,(
% 11.65/2.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1)) => m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1))))))),
% 11.65/2.00    inference(negated_conjecture,[],[f9])).
% 11.65/2.00  
% 11.65/2.00  fof(f23,plain,(
% 11.65/2.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & (m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 11.65/2.00    inference(ennf_transformation,[],[f10])).
% 11.65/2.00  
% 11.65/2.00  fof(f24,plain,(
% 11.65/2.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 11.65/2.00    inference(flattening,[],[f23])).
% 11.65/2.00  
% 11.65/2.00  fof(f35,plain,(
% 11.65/2.00    ( ! [X2,X0,X1] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,sK4),X0,X1) & m1_connsp_2(sK4,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 11.65/2.00    introduced(choice_axiom,[])).
% 11.65/2.00  
% 11.65/2.00  fof(f34,plain,(
% 11.65/2.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),sK3,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(sK3,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 11.65/2.00    introduced(choice_axiom,[])).
% 11.65/2.00  
% 11.65/2.00  fof(f33,plain,(
% 11.65/2.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,sK2) & m1_connsp_2(X3,X0,sK2) & m1_connsp_2(X2,X0,sK2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK2,u1_struct_0(X0)))) )),
% 11.65/2.00    introduced(choice_axiom,[])).
% 11.65/2.00  
% 11.65/2.00  fof(f32,plain,(
% 11.65/2.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(sK1),X2,X3),sK1,X1) & m1_connsp_2(X3,sK1,X1) & m1_connsp_2(X2,sK1,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X1,u1_struct_0(sK1))) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 11.65/2.00    introduced(choice_axiom,[])).
% 11.65/2.00  
% 11.65/2.00  fof(f36,plain,(
% 11.65/2.00    (((~m1_connsp_2(k4_subset_1(u1_struct_0(sK1),sK3,sK4),sK1,sK2) & m1_connsp_2(sK4,sK1,sK2) & m1_connsp_2(sK3,sK1,sK2) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK2,u1_struct_0(sK1))) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 11.65/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f24,f35,f34,f33,f32])).
% 11.65/2.00  
% 11.65/2.00  fof(f52,plain,(
% 11.65/2.00    l1_pre_topc(sK1)),
% 11.65/2.00    inference(cnf_transformation,[],[f36])).
% 11.65/2.00  
% 11.65/2.00  fof(f56,plain,(
% 11.65/2.00    m1_connsp_2(sK3,sK1,sK2)),
% 11.65/2.00    inference(cnf_transformation,[],[f36])).
% 11.65/2.00  
% 11.65/2.00  fof(f7,axiom,(
% 11.65/2.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 11.65/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/2.00  
% 11.65/2.00  fof(f19,plain,(
% 11.65/2.00    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 11.65/2.00    inference(ennf_transformation,[],[f7])).
% 11.65/2.00  
% 11.65/2.00  fof(f20,plain,(
% 11.65/2.00    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.65/2.00    inference(flattening,[],[f19])).
% 11.65/2.00  
% 11.65/2.00  fof(f31,plain,(
% 11.65/2.00    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.65/2.00    inference(nnf_transformation,[],[f20])).
% 11.65/2.00  
% 11.65/2.00  fof(f47,plain,(
% 11.65/2.00    ( ! [X2,X0,X1] : (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.65/2.00    inference(cnf_transformation,[],[f31])).
% 11.65/2.00  
% 11.65/2.00  fof(f8,axiom,(
% 11.65/2.00    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 11.65/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/2.00  
% 11.65/2.00  fof(f21,plain,(
% 11.65/2.00    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 11.65/2.00    inference(ennf_transformation,[],[f8])).
% 11.65/2.00  
% 11.65/2.00  fof(f22,plain,(
% 11.65/2.00    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.65/2.00    inference(flattening,[],[f21])).
% 11.65/2.00  
% 11.65/2.00  fof(f49,plain,(
% 11.65/2.00    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.65/2.00    inference(cnf_transformation,[],[f22])).
% 11.65/2.00  
% 11.65/2.00  fof(f51,plain,(
% 11.65/2.00    v2_pre_topc(sK1)),
% 11.65/2.00    inference(cnf_transformation,[],[f36])).
% 11.65/2.00  
% 11.65/2.00  fof(f50,plain,(
% 11.65/2.00    ~v2_struct_0(sK1)),
% 11.65/2.00    inference(cnf_transformation,[],[f36])).
% 11.65/2.00  
% 11.65/2.00  fof(f53,plain,(
% 11.65/2.00    m1_subset_1(sK2,u1_struct_0(sK1))),
% 11.65/2.00    inference(cnf_transformation,[],[f36])).
% 11.65/2.00  
% 11.65/2.00  fof(f54,plain,(
% 11.65/2.00    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 11.65/2.00    inference(cnf_transformation,[],[f36])).
% 11.65/2.00  
% 11.65/2.00  fof(f4,axiom,(
% 11.65/2.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 11.65/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/2.00  
% 11.65/2.00  fof(f13,plain,(
% 11.65/2.00    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 11.65/2.00    inference(ennf_transformation,[],[f4])).
% 11.65/2.00  
% 11.65/2.00  fof(f14,plain,(
% 11.65/2.00    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.65/2.00    inference(flattening,[],[f13])).
% 11.65/2.00  
% 11.65/2.00  fof(f44,plain,(
% 11.65/2.00    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.65/2.00    inference(cnf_transformation,[],[f14])).
% 11.65/2.00  
% 11.65/2.00  fof(f58,plain,(
% 11.65/2.00    ~m1_connsp_2(k4_subset_1(u1_struct_0(sK1),sK3,sK4),sK1,sK2)),
% 11.65/2.00    inference(cnf_transformation,[],[f36])).
% 11.65/2.00  
% 11.65/2.00  fof(f48,plain,(
% 11.65/2.00    ( ! [X2,X0,X1] : (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.65/2.00    inference(cnf_transformation,[],[f31])).
% 11.65/2.00  
% 11.65/2.00  fof(f55,plain,(
% 11.65/2.00    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))),
% 11.65/2.00    inference(cnf_transformation,[],[f36])).
% 11.65/2.00  
% 11.65/2.00  cnf(c_516,plain,
% 11.65/2.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.65/2.00      theory(equality) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_8,plain,
% 11.65/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.65/2.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 11.65/2.00      | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
% 11.65/2.00      inference(cnf_transformation,[],[f45]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_2898,plain,
% 11.65/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.65/2.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 11.65/2.00      | r1_tarski(X3,k4_subset_1(X1,X2,X0))
% 11.65/2.00      | ~ r1_tarski(X4,k2_xboole_0(X2,X0))
% 11.65/2.00      | X3 != X4 ),
% 11.65/2.00      inference(resolution,[status(thm)],[c_516,c_8]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_6,plain,
% 11.65/2.00      ( r1_tarski(X0,X1) | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 11.65/2.00      inference(cnf_transformation,[],[f43]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_4,plain,
% 11.65/2.00      ( r1_tarski(X0,X0) ),
% 11.65/2.00      inference(cnf_transformation,[],[f59]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_1700,plain,
% 11.65/2.00      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 11.65/2.00      inference(resolution,[status(thm)],[c_6,c_4]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_10686,plain,
% 11.65/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.65/2.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 11.65/2.00      | r1_tarski(X3,k4_subset_1(X1,X2,X0))
% 11.65/2.00      | X3 != X2 ),
% 11.65/2.00      inference(resolution,[status(thm)],[c_2898,c_1700]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_2,plain,
% 11.65/2.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 11.65/2.00      inference(cnf_transformation,[],[f37]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_9,plain,
% 11.65/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.65/2.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 11.65/2.00      | ~ r1_tarski(X2,X0)
% 11.65/2.00      | r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X0))
% 11.65/2.00      | ~ l1_pre_topc(X1) ),
% 11.65/2.00      inference(cnf_transformation,[],[f46]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_19,negated_conjecture,
% 11.65/2.00      ( l1_pre_topc(sK1) ),
% 11.65/2.00      inference(cnf_transformation,[],[f52]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_313,plain,
% 11.65/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.65/2.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 11.65/2.00      | ~ r1_tarski(X2,X0)
% 11.65/2.00      | r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X0))
% 11.65/2.00      | sK1 != X1 ),
% 11.65/2.00      inference(resolution_lifted,[status(thm)],[c_9,c_19]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_314,plain,
% 11.65/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.65/2.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.65/2.00      | ~ r1_tarski(X1,X0)
% 11.65/2.00      | r1_tarski(k1_tops_1(sK1,X1),k1_tops_1(sK1,X0)) ),
% 11.65/2.00      inference(unflattening,[status(thm)],[c_313]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_2661,plain,
% 11.65/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.65/2.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.65/2.00      | ~ r2_hidden(X2,k1_tops_1(sK1,X1))
% 11.65/2.00      | r2_hidden(X2,k1_tops_1(sK1,X0))
% 11.65/2.00      | ~ r1_tarski(X1,X0) ),
% 11.65/2.00      inference(resolution,[status(thm)],[c_2,c_314]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_15,negated_conjecture,
% 11.65/2.00      ( m1_connsp_2(sK3,sK1,sK2) ),
% 11.65/2.00      inference(cnf_transformation,[],[f56]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_11,plain,
% 11.65/2.00      ( ~ m1_connsp_2(X0,X1,X2)
% 11.65/2.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.65/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.65/2.00      | r2_hidden(X2,k1_tops_1(X1,X0))
% 11.65/2.00      | v2_struct_0(X1)
% 11.65/2.00      | ~ v2_pre_topc(X1)
% 11.65/2.00      | ~ l1_pre_topc(X1) ),
% 11.65/2.00      inference(cnf_transformation,[],[f47]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_12,plain,
% 11.65/2.00      ( ~ m1_connsp_2(X0,X1,X2)
% 11.65/2.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.65/2.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.65/2.00      | v2_struct_0(X1)
% 11.65/2.00      | ~ v2_pre_topc(X1)
% 11.65/2.00      | ~ l1_pre_topc(X1) ),
% 11.65/2.00      inference(cnf_transformation,[],[f49]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_117,plain,
% 11.65/2.00      ( ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.65/2.00      | ~ m1_connsp_2(X0,X1,X2)
% 11.65/2.00      | r2_hidden(X2,k1_tops_1(X1,X0))
% 11.65/2.00      | v2_struct_0(X1)
% 11.65/2.00      | ~ v2_pre_topc(X1)
% 11.65/2.00      | ~ l1_pre_topc(X1) ),
% 11.65/2.00      inference(global_propositional_subsumption,
% 11.65/2.00                [status(thm)],
% 11.65/2.00                [c_11,c_12]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_118,plain,
% 11.65/2.00      ( ~ m1_connsp_2(X0,X1,X2)
% 11.65/2.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.65/2.00      | r2_hidden(X2,k1_tops_1(X1,X0))
% 11.65/2.00      | v2_struct_0(X1)
% 11.65/2.00      | ~ v2_pre_topc(X1)
% 11.65/2.00      | ~ l1_pre_topc(X1) ),
% 11.65/2.00      inference(renaming,[status(thm)],[c_117]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_20,negated_conjecture,
% 11.65/2.00      ( v2_pre_topc(sK1) ),
% 11.65/2.00      inference(cnf_transformation,[],[f51]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_234,plain,
% 11.65/2.00      ( ~ m1_connsp_2(X0,X1,X2)
% 11.65/2.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.65/2.00      | r2_hidden(X2,k1_tops_1(X1,X0))
% 11.65/2.00      | v2_struct_0(X1)
% 11.65/2.00      | ~ l1_pre_topc(X1)
% 11.65/2.00      | sK1 != X1 ),
% 11.65/2.00      inference(resolution_lifted,[status(thm)],[c_118,c_20]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_235,plain,
% 11.65/2.00      ( ~ m1_connsp_2(X0,sK1,X1)
% 11.65/2.00      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 11.65/2.00      | r2_hidden(X1,k1_tops_1(sK1,X0))
% 11.65/2.00      | v2_struct_0(sK1)
% 11.65/2.00      | ~ l1_pre_topc(sK1) ),
% 11.65/2.00      inference(unflattening,[status(thm)],[c_234]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_21,negated_conjecture,
% 11.65/2.00      ( ~ v2_struct_0(sK1) ),
% 11.65/2.00      inference(cnf_transformation,[],[f50]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_239,plain,
% 11.65/2.00      ( ~ m1_connsp_2(X0,sK1,X1)
% 11.65/2.00      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 11.65/2.00      | r2_hidden(X1,k1_tops_1(sK1,X0)) ),
% 11.65/2.00      inference(global_propositional_subsumption,
% 11.65/2.00                [status(thm)],
% 11.65/2.00                [c_235,c_21,c_19]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_385,plain,
% 11.65/2.00      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 11.65/2.00      | r2_hidden(X0,k1_tops_1(sK1,X1))
% 11.65/2.00      | sK2 != X0
% 11.65/2.00      | sK3 != X1
% 11.65/2.00      | sK1 != sK1 ),
% 11.65/2.00      inference(resolution_lifted,[status(thm)],[c_15,c_239]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_386,plain,
% 11.65/2.00      ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 11.65/2.00      | r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
% 11.65/2.00      inference(unflattening,[status(thm)],[c_385]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_18,negated_conjecture,
% 11.65/2.00      ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 11.65/2.00      inference(cnf_transformation,[],[f53]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_388,plain,
% 11.65/2.00      ( r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
% 11.65/2.00      inference(global_propositional_subsumption,
% 11.65/2.00                [status(thm)],
% 11.65/2.00                [c_386,c_18]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_3120,plain,
% 11.65/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.65/2.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.65/2.00      | r2_hidden(sK2,k1_tops_1(sK1,X0))
% 11.65/2.00      | ~ r1_tarski(sK3,X0) ),
% 11.65/2.00      inference(resolution,[status(thm)],[c_2661,c_388]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_17,negated_conjecture,
% 11.65/2.00      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 11.65/2.00      inference(cnf_transformation,[],[f54]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_3319,plain,
% 11.65/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.65/2.00      | r2_hidden(sK2,k1_tops_1(sK1,X0))
% 11.65/2.00      | ~ r1_tarski(sK3,X0) ),
% 11.65/2.00      inference(global_propositional_subsumption,
% 11.65/2.00                [status(thm)],
% 11.65/2.00                [c_3120,c_17]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_7,plain,
% 11.65/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.65/2.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 11.65/2.00      | m1_subset_1(k4_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 11.65/2.00      inference(cnf_transformation,[],[f44]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_3341,plain,
% 11.65/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.65/2.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.65/2.00      | r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),X1,X0)))
% 11.65/2.00      | ~ r1_tarski(sK3,k4_subset_1(u1_struct_0(sK1),X1,X0)) ),
% 11.65/2.00      inference(resolution,[status(thm)],[c_3319,c_7]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_13,negated_conjecture,
% 11.65/2.00      ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK1),sK3,sK4),sK1,sK2) ),
% 11.65/2.00      inference(cnf_transformation,[],[f58]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_10,plain,
% 11.65/2.00      ( m1_connsp_2(X0,X1,X2)
% 11.65/2.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.65/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.65/2.00      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 11.65/2.00      | v2_struct_0(X1)
% 11.65/2.00      | ~ v2_pre_topc(X1)
% 11.65/2.00      | ~ l1_pre_topc(X1) ),
% 11.65/2.00      inference(cnf_transformation,[],[f48]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_276,plain,
% 11.65/2.00      ( m1_connsp_2(X0,X1,X2)
% 11.65/2.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.65/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.65/2.00      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 11.65/2.00      | v2_struct_0(X1)
% 11.65/2.00      | ~ l1_pre_topc(X1)
% 11.65/2.00      | sK1 != X1 ),
% 11.65/2.00      inference(resolution_lifted,[status(thm)],[c_10,c_20]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_277,plain,
% 11.65/2.00      ( m1_connsp_2(X0,sK1,X1)
% 11.65/2.00      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 11.65/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.65/2.00      | ~ r2_hidden(X1,k1_tops_1(sK1,X0))
% 11.65/2.00      | v2_struct_0(sK1)
% 11.65/2.00      | ~ l1_pre_topc(sK1) ),
% 11.65/2.00      inference(unflattening,[status(thm)],[c_276]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_281,plain,
% 11.65/2.00      ( m1_connsp_2(X0,sK1,X1)
% 11.65/2.00      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 11.65/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.65/2.00      | ~ r2_hidden(X1,k1_tops_1(sK1,X0)) ),
% 11.65/2.00      inference(global_propositional_subsumption,
% 11.65/2.00                [status(thm)],
% 11.65/2.00                [c_277,c_21,c_19]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_356,plain,
% 11.65/2.00      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 11.65/2.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.65/2.00      | ~ r2_hidden(X0,k1_tops_1(sK1,X1))
% 11.65/2.00      | k4_subset_1(u1_struct_0(sK1),sK3,sK4) != X1
% 11.65/2.00      | sK2 != X0
% 11.65/2.00      | sK1 != sK1 ),
% 11.65/2.00      inference(resolution_lifted,[status(thm)],[c_13,c_281]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_357,plain,
% 11.65/2.00      ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
% 11.65/2.00      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 11.65/2.00      | ~ r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) ),
% 11.65/2.00      inference(unflattening,[status(thm)],[c_356]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_359,plain,
% 11.65/2.00      ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
% 11.65/2.00      | ~ r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) ),
% 11.65/2.00      inference(global_propositional_subsumption,
% 11.65/2.00                [status(thm)],
% 11.65/2.00                [c_357,c_18]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_16,negated_conjecture,
% 11.65/2.00      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 11.65/2.00      inference(cnf_transformation,[],[f55]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_964,plain,
% 11.65/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.65/2.00      | m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,X0),k1_zfmisc_1(u1_struct_0(sK1)))
% 11.65/2.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 11.65/2.00      inference(instantiation,[status(thm)],[c_7]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_1061,plain,
% 11.65/2.00      ( m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
% 11.65/2.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.65/2.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 11.65/2.00      inference(instantiation,[status(thm)],[c_964]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_1282,plain,
% 11.65/2.00      ( ~ r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) ),
% 11.65/2.00      inference(global_propositional_subsumption,
% 11.65/2.00                [status(thm)],
% 11.65/2.00                [c_359,c_18,c_17,c_16,c_357,c_1061]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_4394,plain,
% 11.65/2.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.65/2.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.65/2.00      | ~ r1_tarski(sK3,k4_subset_1(u1_struct_0(sK1),sK3,sK4)) ),
% 11.65/2.00      inference(resolution,[status(thm)],[c_3341,c_1282]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_4401,plain,
% 11.65/2.00      ( ~ r1_tarski(sK3,k4_subset_1(u1_struct_0(sK1),sK3,sK4)) ),
% 11.65/2.00      inference(global_propositional_subsumption,
% 11.65/2.00                [status(thm)],
% 11.65/2.00                [c_4394,c_17,c_16]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_45112,plain,
% 11.65/2.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.65/2.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.65/2.00      | sK3 != sK3 ),
% 11.65/2.00      inference(resolution,[status(thm)],[c_10686,c_4401]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(c_45113,plain,
% 11.65/2.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 11.65/2.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 11.65/2.00      inference(equality_resolution_simp,[status(thm)],[c_45112]) ).
% 11.65/2.00  
% 11.65/2.00  cnf(contradiction,plain,
% 11.65/2.00      ( $false ),
% 11.65/2.00      inference(minisat,[status(thm)],[c_45113,c_16,c_17]) ).
% 11.65/2.00  
% 11.65/2.00  
% 11.65/2.00  % SZS output end CNFRefutation for theBenchmark.p
% 11.65/2.00  
% 11.65/2.00  ------                               Statistics
% 11.65/2.00  
% 11.65/2.00  ------ Selected
% 11.65/2.00  
% 11.65/2.00  total_time:                             1.409
% 11.65/2.00  
%------------------------------------------------------------------------------
