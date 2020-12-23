%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:18:10 EST 2020

% Result     : Theorem 3.79s
% Output     : CNFRefutation 3.79s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 237 expanded)
%              Number of clauses        :   50 (  56 expanded)
%              Number of leaves         :   14 (  81 expanded)
%              Depth                    :   12
%              Number of atoms          :  408 (1674 expanded)
%              Number of equality atoms :   42 (  47 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f8,conjecture,(
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

fof(f9,negated_conjecture,(
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
    inference(negated_conjecture,[],[f8])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f32,plain,(
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

fof(f31,plain,(
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

fof(f30,plain,(
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

fof(f29,plain,
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

fof(f33,plain,
    ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK1),sK3,sK4),sK1,sK2)
    & m1_connsp_2(sK4,sK1,sK2)
    & m1_connsp_2(sK3,sK1,sK2)
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f21,f32,f31,f30,f29])).

fof(f50,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f33])).

fof(f51,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f33])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f14])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f26])).

fof(f39,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

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

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f48,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f55,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f38])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f22])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).

fof(f34,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f12])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f53,plain,(
    m1_connsp_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f33])).

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

fof(f18,plain,(
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
    inference(flattening,[],[f18])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f47,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f46,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f54,plain,(
    ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK1),sK3,sK4),sK1,sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f49,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_9614,plain,
    ( r1_tarski(sK4,k2_xboole_0(sK3,sK4))
    | ~ r1_tarski(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_473,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_947,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK4,k4_subset_1(u1_struct_0(sK1),X2,X3))
    | k4_subset_1(u1_struct_0(sK1),X2,X3) != X1
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_473])).

cnf(c_1267,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK4,k4_subset_1(u1_struct_0(sK1),sK3,sK4))
    | k4_subset_1(u1_struct_0(sK1),sK3,sK4) != X1
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_947])).

cnf(c_2012,plain,
    ( ~ r1_tarski(sK4,X0)
    | r1_tarski(sK4,k4_subset_1(u1_struct_0(sK1),sK3,sK4))
    | k4_subset_1(u1_struct_0(sK1),sK3,sK4) != X0
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1267])).

cnf(c_4183,plain,
    ( r1_tarski(sK4,k4_subset_1(u1_struct_0(sK1),sK3,sK4))
    | ~ r1_tarski(sK4,k2_xboole_0(sK3,sK4))
    | k4_subset_1(u1_struct_0(sK1),sK3,sK4) != k2_xboole_0(sK3,sK4)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2012])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_740,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_741,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_742,plain,
    ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1754,plain,
    ( k4_subset_1(u1_struct_0(sK1),X0,sK4) = k2_xboole_0(X0,sK4)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_741,c_742])).

cnf(c_1900,plain,
    ( k4_subset_1(u1_struct_0(sK1),sK3,sK4) = k2_xboole_0(sK3,sK4) ),
    inference(superposition,[status(thm)],[c_740,c_1754])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_998,plain,
    ( ~ r1_tarski(X0,sK4)
    | ~ r1_tarski(sK4,X0)
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1639,plain,
    ( ~ r1_tarski(sK4,sK4)
    | sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_998])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_18,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_275,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X0))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_18])).

cnf(c_276,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X1,X0)
    | r1_tarski(k1_tops_1(sK1,X1),k1_tops_1(sK1,X0)) ),
    inference(unflattening,[status(thm)],[c_275])).

cnf(c_790,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK1),X1,X2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X0,k4_subset_1(u1_struct_0(sK1),X1,X2))
    | r1_tarski(k1_tops_1(sK1,X0),k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),X1,X2))) ),
    inference(instantiation,[status(thm)],[c_276])).

cnf(c_865,plain,
    ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK1),X0,X1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(k1_tops_1(sK1,sK4),k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),X0,X1)))
    | ~ r1_tarski(sK4,k4_subset_1(u1_struct_0(sK1),X0,X1)) ),
    inference(instantiation,[status(thm)],[c_790])).

cnf(c_1246,plain,
    ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(k1_tops_1(sK1,sK4),k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4)))
    | ~ r1_tarski(sK4,k4_subset_1(u1_struct_0(sK1),sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_865])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1190,plain,
    ( r1_tarski(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_813,plain,
    ( ~ r2_hidden(sK2,X0)
    | r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4)))
    | ~ r1_tarski(X0,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_825,plain,
    ( r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4)))
    | ~ r2_hidden(sK2,k1_tops_1(sK1,sK4))
    | ~ r1_tarski(k1_tops_1(sK1,sK4),k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_813])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | m1_subset_1(k4_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_772,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_13,negated_conjecture,
    ( m1_connsp_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_11,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_19,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_217,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_19])).

cnf(c_218,plain,
    ( ~ m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(X1,k1_tops_1(sK1,X0))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_217])).

cnf(c_20,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_222,plain,
    ( ~ m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(X1,k1_tops_1(sK1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_218,c_20,c_18])).

cnf(c_331,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(X0,k1_tops_1(sK1,X1))
    | sK2 != X0
    | sK4 != X1
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_222])).

cnf(c_332,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(sK2,k1_tops_1(sK1,sK4)) ),
    inference(unflattening,[status(thm)],[c_331])).

cnf(c_12,negated_conjecture,
    ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK1),sK3,sK4),sK1,sK2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_10,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_241,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_19])).

cnf(c_242,plain,
    ( m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X1,k1_tops_1(sK1,X0))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_241])).

cnf(c_246,plain,
    ( m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X1,k1_tops_1(sK1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_242,c_20,c_18])).

cnf(c_317,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X0,k1_tops_1(sK1,X1))
    | k4_subset_1(u1_struct_0(sK1),sK3,sK4) != X1
    | sK2 != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_246])).

cnf(c_318,plain,
    ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) ),
    inference(unflattening,[status(thm)],[c_317])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9614,c_4183,c_1900,c_1639,c_1246,c_1190,c_825,c_772,c_332,c_318,c_15,c_16,c_17])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:28:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.79/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.79/0.99  
% 3.79/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.79/0.99  
% 3.79/0.99  ------  iProver source info
% 3.79/0.99  
% 3.79/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.79/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.79/0.99  git: non_committed_changes: false
% 3.79/0.99  git: last_make_outside_of_git: false
% 3.79/0.99  
% 3.79/0.99  ------ 
% 3.79/0.99  
% 3.79/0.99  ------ Input Options
% 3.79/0.99  
% 3.79/0.99  --out_options                           all
% 3.79/0.99  --tptp_safe_out                         true
% 3.79/0.99  --problem_path                          ""
% 3.79/0.99  --include_path                          ""
% 3.79/0.99  --clausifier                            res/vclausify_rel
% 3.79/0.99  --clausifier_options                    ""
% 3.79/0.99  --stdin                                 false
% 3.79/0.99  --stats_out                             all
% 3.79/0.99  
% 3.79/0.99  ------ General Options
% 3.79/0.99  
% 3.79/0.99  --fof                                   false
% 3.79/0.99  --time_out_real                         305.
% 3.79/0.99  --time_out_virtual                      -1.
% 3.79/0.99  --symbol_type_check                     false
% 3.79/0.99  --clausify_out                          false
% 3.79/0.99  --sig_cnt_out                           false
% 3.79/0.99  --trig_cnt_out                          false
% 3.79/0.99  --trig_cnt_out_tolerance                1.
% 3.79/0.99  --trig_cnt_out_sk_spl                   false
% 3.79/0.99  --abstr_cl_out                          false
% 3.79/0.99  
% 3.79/0.99  ------ Global Options
% 3.79/0.99  
% 3.79/0.99  --schedule                              default
% 3.79/0.99  --add_important_lit                     false
% 3.79/0.99  --prop_solver_per_cl                    1000
% 3.79/0.99  --min_unsat_core                        false
% 3.79/0.99  --soft_assumptions                      false
% 3.79/0.99  --soft_lemma_size                       3
% 3.79/0.99  --prop_impl_unit_size                   0
% 3.79/0.99  --prop_impl_unit                        []
% 3.79/0.99  --share_sel_clauses                     true
% 3.79/0.99  --reset_solvers                         false
% 3.79/0.99  --bc_imp_inh                            [conj_cone]
% 3.79/0.99  --conj_cone_tolerance                   3.
% 3.79/0.99  --extra_neg_conj                        none
% 3.79/0.99  --large_theory_mode                     true
% 3.79/0.99  --prolific_symb_bound                   200
% 3.79/0.99  --lt_threshold                          2000
% 3.79/0.99  --clause_weak_htbl                      true
% 3.79/0.99  --gc_record_bc_elim                     false
% 3.79/0.99  
% 3.79/0.99  ------ Preprocessing Options
% 3.79/0.99  
% 3.79/0.99  --preprocessing_flag                    true
% 3.79/0.99  --time_out_prep_mult                    0.1
% 3.79/0.99  --splitting_mode                        input
% 3.79/0.99  --splitting_grd                         true
% 3.79/0.99  --splitting_cvd                         false
% 3.79/0.99  --splitting_cvd_svl                     false
% 3.79/0.99  --splitting_nvd                         32
% 3.79/0.99  --sub_typing                            true
% 3.79/0.99  --prep_gs_sim                           true
% 3.79/0.99  --prep_unflatten                        true
% 3.79/0.99  --prep_res_sim                          true
% 3.79/0.99  --prep_upred                            true
% 3.79/0.99  --prep_sem_filter                       exhaustive
% 3.79/0.99  --prep_sem_filter_out                   false
% 3.79/0.99  --pred_elim                             true
% 3.79/0.99  --res_sim_input                         true
% 3.79/0.99  --eq_ax_congr_red                       true
% 3.79/0.99  --pure_diseq_elim                       true
% 3.79/0.99  --brand_transform                       false
% 3.79/0.99  --non_eq_to_eq                          false
% 3.79/0.99  --prep_def_merge                        true
% 3.79/0.99  --prep_def_merge_prop_impl              false
% 3.79/0.99  --prep_def_merge_mbd                    true
% 3.79/0.99  --prep_def_merge_tr_red                 false
% 3.79/0.99  --prep_def_merge_tr_cl                  false
% 3.79/0.99  --smt_preprocessing                     true
% 3.79/0.99  --smt_ac_axioms                         fast
% 3.79/0.99  --preprocessed_out                      false
% 3.79/0.99  --preprocessed_stats                    false
% 3.79/0.99  
% 3.79/0.99  ------ Abstraction refinement Options
% 3.79/0.99  
% 3.79/0.99  --abstr_ref                             []
% 3.79/0.99  --abstr_ref_prep                        false
% 3.79/0.99  --abstr_ref_until_sat                   false
% 3.79/0.99  --abstr_ref_sig_restrict                funpre
% 3.79/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.79/0.99  --abstr_ref_under                       []
% 3.79/0.99  
% 3.79/0.99  ------ SAT Options
% 3.79/0.99  
% 3.79/0.99  --sat_mode                              false
% 3.79/0.99  --sat_fm_restart_options                ""
% 3.79/0.99  --sat_gr_def                            false
% 3.79/0.99  --sat_epr_types                         true
% 3.79/0.99  --sat_non_cyclic_types                  false
% 3.79/0.99  --sat_finite_models                     false
% 3.79/0.99  --sat_fm_lemmas                         false
% 3.79/0.99  --sat_fm_prep                           false
% 3.79/0.99  --sat_fm_uc_incr                        true
% 3.79/0.99  --sat_out_model                         small
% 3.79/0.99  --sat_out_clauses                       false
% 3.79/0.99  
% 3.79/0.99  ------ QBF Options
% 3.79/0.99  
% 3.79/0.99  --qbf_mode                              false
% 3.79/0.99  --qbf_elim_univ                         false
% 3.79/0.99  --qbf_dom_inst                          none
% 3.79/0.99  --qbf_dom_pre_inst                      false
% 3.79/0.99  --qbf_sk_in                             false
% 3.79/0.99  --qbf_pred_elim                         true
% 3.79/0.99  --qbf_split                             512
% 3.79/0.99  
% 3.79/0.99  ------ BMC1 Options
% 3.79/0.99  
% 3.79/0.99  --bmc1_incremental                      false
% 3.79/0.99  --bmc1_axioms                           reachable_all
% 3.79/0.99  --bmc1_min_bound                        0
% 3.79/0.99  --bmc1_max_bound                        -1
% 3.79/0.99  --bmc1_max_bound_default                -1
% 3.79/0.99  --bmc1_symbol_reachability              true
% 3.79/0.99  --bmc1_property_lemmas                  false
% 3.79/0.99  --bmc1_k_induction                      false
% 3.79/0.99  --bmc1_non_equiv_states                 false
% 3.79/0.99  --bmc1_deadlock                         false
% 3.79/0.99  --bmc1_ucm                              false
% 3.79/0.99  --bmc1_add_unsat_core                   none
% 3.79/0.99  --bmc1_unsat_core_children              false
% 3.79/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.79/0.99  --bmc1_out_stat                         full
% 3.79/0.99  --bmc1_ground_init                      false
% 3.79/0.99  --bmc1_pre_inst_next_state              false
% 3.79/0.99  --bmc1_pre_inst_state                   false
% 3.79/0.99  --bmc1_pre_inst_reach_state             false
% 3.79/0.99  --bmc1_out_unsat_core                   false
% 3.79/0.99  --bmc1_aig_witness_out                  false
% 3.79/0.99  --bmc1_verbose                          false
% 3.79/0.99  --bmc1_dump_clauses_tptp                false
% 3.79/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.79/0.99  --bmc1_dump_file                        -
% 3.79/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.79/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.79/0.99  --bmc1_ucm_extend_mode                  1
% 3.79/0.99  --bmc1_ucm_init_mode                    2
% 3.79/0.99  --bmc1_ucm_cone_mode                    none
% 3.79/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.79/0.99  --bmc1_ucm_relax_model                  4
% 3.79/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.79/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.79/0.99  --bmc1_ucm_layered_model                none
% 3.79/0.99  --bmc1_ucm_max_lemma_size               10
% 3.79/0.99  
% 3.79/0.99  ------ AIG Options
% 3.79/0.99  
% 3.79/0.99  --aig_mode                              false
% 3.79/0.99  
% 3.79/0.99  ------ Instantiation Options
% 3.79/0.99  
% 3.79/0.99  --instantiation_flag                    true
% 3.79/0.99  --inst_sos_flag                         true
% 3.79/0.99  --inst_sos_phase                        true
% 3.79/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.79/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.79/0.99  --inst_lit_sel_side                     num_symb
% 3.79/0.99  --inst_solver_per_active                1400
% 3.79/0.99  --inst_solver_calls_frac                1.
% 3.79/0.99  --inst_passive_queue_type               priority_queues
% 3.79/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.79/0.99  --inst_passive_queues_freq              [25;2]
% 3.79/0.99  --inst_dismatching                      true
% 3.79/0.99  --inst_eager_unprocessed_to_passive     true
% 3.79/0.99  --inst_prop_sim_given                   true
% 3.79/0.99  --inst_prop_sim_new                     false
% 3.79/0.99  --inst_subs_new                         false
% 3.79/0.99  --inst_eq_res_simp                      false
% 3.79/0.99  --inst_subs_given                       false
% 3.79/0.99  --inst_orphan_elimination               true
% 3.79/0.99  --inst_learning_loop_flag               true
% 3.79/0.99  --inst_learning_start                   3000
% 3.79/0.99  --inst_learning_factor                  2
% 3.79/0.99  --inst_start_prop_sim_after_learn       3
% 3.79/0.99  --inst_sel_renew                        solver
% 3.79/0.99  --inst_lit_activity_flag                true
% 3.79/0.99  --inst_restr_to_given                   false
% 3.79/0.99  --inst_activity_threshold               500
% 3.79/0.99  --inst_out_proof                        true
% 3.79/0.99  
% 3.79/0.99  ------ Resolution Options
% 3.79/0.99  
% 3.79/0.99  --resolution_flag                       true
% 3.79/0.99  --res_lit_sel                           adaptive
% 3.79/0.99  --res_lit_sel_side                      none
% 3.79/0.99  --res_ordering                          kbo
% 3.79/0.99  --res_to_prop_solver                    active
% 3.79/0.99  --res_prop_simpl_new                    false
% 3.79/0.99  --res_prop_simpl_given                  true
% 3.79/0.99  --res_passive_queue_type                priority_queues
% 3.79/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.79/0.99  --res_passive_queues_freq               [15;5]
% 3.79/0.99  --res_forward_subs                      full
% 3.79/0.99  --res_backward_subs                     full
% 3.79/0.99  --res_forward_subs_resolution           true
% 3.79/0.99  --res_backward_subs_resolution          true
% 3.79/0.99  --res_orphan_elimination                true
% 3.79/0.99  --res_time_limit                        2.
% 3.79/0.99  --res_out_proof                         true
% 3.79/0.99  
% 3.79/0.99  ------ Superposition Options
% 3.79/0.99  
% 3.79/0.99  --superposition_flag                    true
% 3.79/0.99  --sup_passive_queue_type                priority_queues
% 3.79/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.79/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.79/0.99  --demod_completeness_check              fast
% 3.79/0.99  --demod_use_ground                      true
% 3.79/0.99  --sup_to_prop_solver                    passive
% 3.79/0.99  --sup_prop_simpl_new                    true
% 3.79/0.99  --sup_prop_simpl_given                  true
% 3.79/0.99  --sup_fun_splitting                     true
% 3.79/0.99  --sup_smt_interval                      50000
% 3.79/0.99  
% 3.79/0.99  ------ Superposition Simplification Setup
% 3.79/0.99  
% 3.79/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.79/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.79/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.79/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.79/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.79/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.79/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.79/0.99  --sup_immed_triv                        [TrivRules]
% 3.79/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.79/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.79/0.99  --sup_immed_bw_main                     []
% 3.79/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.79/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.79/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.79/0.99  --sup_input_bw                          []
% 3.79/0.99  
% 3.79/0.99  ------ Combination Options
% 3.79/0.99  
% 3.79/0.99  --comb_res_mult                         3
% 3.79/0.99  --comb_sup_mult                         2
% 3.79/0.99  --comb_inst_mult                        10
% 3.79/0.99  
% 3.79/0.99  ------ Debug Options
% 3.79/0.99  
% 3.79/0.99  --dbg_backtrace                         false
% 3.79/0.99  --dbg_dump_prop_clauses                 false
% 3.79/0.99  --dbg_dump_prop_clauses_file            -
% 3.79/0.99  --dbg_out_stat                          false
% 3.79/0.99  ------ Parsing...
% 3.79/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.79/0.99  
% 3.79/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 3.79/0.99  
% 3.79/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.79/0.99  
% 3.79/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.79/0.99  ------ Proving...
% 3.79/0.99  ------ Problem Properties 
% 3.79/0.99  
% 3.79/0.99  
% 3.79/0.99  clauses                                 17
% 3.79/0.99  conjectures                             3
% 3.79/0.99  EPR                                     3
% 3.79/0.99  Horn                                    16
% 3.79/0.99  unary                                   8
% 3.79/0.99  binary                                  4
% 3.79/0.99  lits                                    32
% 3.79/0.99  lits eq                                 4
% 3.79/0.99  fd_pure                                 0
% 3.79/0.99  fd_pseudo                               0
% 3.79/0.99  fd_cond                                 0
% 3.79/0.99  fd_pseudo_cond                          1
% 3.79/0.99  AC symbols                              0
% 3.79/0.99  
% 3.79/0.99  ------ Schedule dynamic 5 is on 
% 3.79/0.99  
% 3.79/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.79/0.99  
% 3.79/0.99  
% 3.79/0.99  ------ 
% 3.79/0.99  Current options:
% 3.79/0.99  ------ 
% 3.79/0.99  
% 3.79/0.99  ------ Input Options
% 3.79/0.99  
% 3.79/0.99  --out_options                           all
% 3.79/0.99  --tptp_safe_out                         true
% 3.79/0.99  --problem_path                          ""
% 3.79/0.99  --include_path                          ""
% 3.79/0.99  --clausifier                            res/vclausify_rel
% 3.79/0.99  --clausifier_options                    ""
% 3.79/0.99  --stdin                                 false
% 3.79/0.99  --stats_out                             all
% 3.79/0.99  
% 3.79/0.99  ------ General Options
% 3.79/0.99  
% 3.79/0.99  --fof                                   false
% 3.79/0.99  --time_out_real                         305.
% 3.79/0.99  --time_out_virtual                      -1.
% 3.79/0.99  --symbol_type_check                     false
% 3.79/0.99  --clausify_out                          false
% 3.79/0.99  --sig_cnt_out                           false
% 3.79/0.99  --trig_cnt_out                          false
% 3.79/0.99  --trig_cnt_out_tolerance                1.
% 3.79/0.99  --trig_cnt_out_sk_spl                   false
% 3.79/0.99  --abstr_cl_out                          false
% 3.79/0.99  
% 3.79/0.99  ------ Global Options
% 3.79/0.99  
% 3.79/0.99  --schedule                              default
% 3.79/0.99  --add_important_lit                     false
% 3.79/0.99  --prop_solver_per_cl                    1000
% 3.79/0.99  --min_unsat_core                        false
% 3.79/0.99  --soft_assumptions                      false
% 3.79/0.99  --soft_lemma_size                       3
% 3.79/0.99  --prop_impl_unit_size                   0
% 3.79/0.99  --prop_impl_unit                        []
% 3.79/0.99  --share_sel_clauses                     true
% 3.79/0.99  --reset_solvers                         false
% 3.79/0.99  --bc_imp_inh                            [conj_cone]
% 3.79/0.99  --conj_cone_tolerance                   3.
% 3.79/0.99  --extra_neg_conj                        none
% 3.79/0.99  --large_theory_mode                     true
% 3.79/0.99  --prolific_symb_bound                   200
% 3.79/0.99  --lt_threshold                          2000
% 3.79/0.99  --clause_weak_htbl                      true
% 3.79/0.99  --gc_record_bc_elim                     false
% 3.79/0.99  
% 3.79/0.99  ------ Preprocessing Options
% 3.79/0.99  
% 3.79/0.99  --preprocessing_flag                    true
% 3.79/0.99  --time_out_prep_mult                    0.1
% 3.79/0.99  --splitting_mode                        input
% 3.79/0.99  --splitting_grd                         true
% 3.79/0.99  --splitting_cvd                         false
% 3.79/0.99  --splitting_cvd_svl                     false
% 3.79/0.99  --splitting_nvd                         32
% 3.79/0.99  --sub_typing                            true
% 3.79/0.99  --prep_gs_sim                           true
% 3.79/0.99  --prep_unflatten                        true
% 3.79/0.99  --prep_res_sim                          true
% 3.79/0.99  --prep_upred                            true
% 3.79/0.99  --prep_sem_filter                       exhaustive
% 3.79/0.99  --prep_sem_filter_out                   false
% 3.79/0.99  --pred_elim                             true
% 3.79/0.99  --res_sim_input                         true
% 3.79/0.99  --eq_ax_congr_red                       true
% 3.79/0.99  --pure_diseq_elim                       true
% 3.79/0.99  --brand_transform                       false
% 3.79/0.99  --non_eq_to_eq                          false
% 3.79/0.99  --prep_def_merge                        true
% 3.79/0.99  --prep_def_merge_prop_impl              false
% 3.79/0.99  --prep_def_merge_mbd                    true
% 3.79/0.99  --prep_def_merge_tr_red                 false
% 3.79/0.99  --prep_def_merge_tr_cl                  false
% 3.79/0.99  --smt_preprocessing                     true
% 3.79/0.99  --smt_ac_axioms                         fast
% 3.79/0.99  --preprocessed_out                      false
% 3.79/0.99  --preprocessed_stats                    false
% 3.79/0.99  
% 3.79/0.99  ------ Abstraction refinement Options
% 3.79/0.99  
% 3.79/0.99  --abstr_ref                             []
% 3.79/0.99  --abstr_ref_prep                        false
% 3.79/0.99  --abstr_ref_until_sat                   false
% 3.79/0.99  --abstr_ref_sig_restrict                funpre
% 3.79/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.79/0.99  --abstr_ref_under                       []
% 3.79/0.99  
% 3.79/0.99  ------ SAT Options
% 3.79/0.99  
% 3.79/0.99  --sat_mode                              false
% 3.79/0.99  --sat_fm_restart_options                ""
% 3.79/0.99  --sat_gr_def                            false
% 3.79/0.99  --sat_epr_types                         true
% 3.79/0.99  --sat_non_cyclic_types                  false
% 3.79/0.99  --sat_finite_models                     false
% 3.79/0.99  --sat_fm_lemmas                         false
% 3.79/0.99  --sat_fm_prep                           false
% 3.79/0.99  --sat_fm_uc_incr                        true
% 3.79/0.99  --sat_out_model                         small
% 3.79/0.99  --sat_out_clauses                       false
% 3.79/0.99  
% 3.79/0.99  ------ QBF Options
% 3.79/0.99  
% 3.79/0.99  --qbf_mode                              false
% 3.79/0.99  --qbf_elim_univ                         false
% 3.79/0.99  --qbf_dom_inst                          none
% 3.79/0.99  --qbf_dom_pre_inst                      false
% 3.79/0.99  --qbf_sk_in                             false
% 3.79/0.99  --qbf_pred_elim                         true
% 3.79/0.99  --qbf_split                             512
% 3.79/0.99  
% 3.79/0.99  ------ BMC1 Options
% 3.79/0.99  
% 3.79/0.99  --bmc1_incremental                      false
% 3.79/0.99  --bmc1_axioms                           reachable_all
% 3.79/0.99  --bmc1_min_bound                        0
% 3.79/0.99  --bmc1_max_bound                        -1
% 3.79/0.99  --bmc1_max_bound_default                -1
% 3.79/0.99  --bmc1_symbol_reachability              true
% 3.79/0.99  --bmc1_property_lemmas                  false
% 3.79/0.99  --bmc1_k_induction                      false
% 3.79/0.99  --bmc1_non_equiv_states                 false
% 3.79/0.99  --bmc1_deadlock                         false
% 3.79/0.99  --bmc1_ucm                              false
% 3.79/0.99  --bmc1_add_unsat_core                   none
% 3.79/0.99  --bmc1_unsat_core_children              false
% 3.79/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.79/0.99  --bmc1_out_stat                         full
% 3.79/0.99  --bmc1_ground_init                      false
% 3.79/0.99  --bmc1_pre_inst_next_state              false
% 3.79/0.99  --bmc1_pre_inst_state                   false
% 3.79/0.99  --bmc1_pre_inst_reach_state             false
% 3.79/0.99  --bmc1_out_unsat_core                   false
% 3.79/0.99  --bmc1_aig_witness_out                  false
% 3.79/0.99  --bmc1_verbose                          false
% 3.79/0.99  --bmc1_dump_clauses_tptp                false
% 3.79/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.79/0.99  --bmc1_dump_file                        -
% 3.79/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.79/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.79/0.99  --bmc1_ucm_extend_mode                  1
% 3.79/0.99  --bmc1_ucm_init_mode                    2
% 3.79/0.99  --bmc1_ucm_cone_mode                    none
% 3.79/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.79/0.99  --bmc1_ucm_relax_model                  4
% 3.79/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.79/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.79/0.99  --bmc1_ucm_layered_model                none
% 3.79/0.99  --bmc1_ucm_max_lemma_size               10
% 3.79/0.99  
% 3.79/0.99  ------ AIG Options
% 3.79/0.99  
% 3.79/0.99  --aig_mode                              false
% 3.79/0.99  
% 3.79/0.99  ------ Instantiation Options
% 3.79/0.99  
% 3.79/0.99  --instantiation_flag                    true
% 3.79/0.99  --inst_sos_flag                         true
% 3.79/0.99  --inst_sos_phase                        true
% 3.79/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.79/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.79/0.99  --inst_lit_sel_side                     none
% 3.79/0.99  --inst_solver_per_active                1400
% 3.79/0.99  --inst_solver_calls_frac                1.
% 3.79/0.99  --inst_passive_queue_type               priority_queues
% 3.79/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.79/0.99  --inst_passive_queues_freq              [25;2]
% 3.79/0.99  --inst_dismatching                      true
% 3.79/0.99  --inst_eager_unprocessed_to_passive     true
% 3.79/0.99  --inst_prop_sim_given                   true
% 3.79/0.99  --inst_prop_sim_new                     false
% 3.79/0.99  --inst_subs_new                         false
% 3.79/0.99  --inst_eq_res_simp                      false
% 3.79/0.99  --inst_subs_given                       false
% 3.79/0.99  --inst_orphan_elimination               true
% 3.79/0.99  --inst_learning_loop_flag               true
% 3.79/0.99  --inst_learning_start                   3000
% 3.79/0.99  --inst_learning_factor                  2
% 3.79/0.99  --inst_start_prop_sim_after_learn       3
% 3.79/0.99  --inst_sel_renew                        solver
% 3.79/0.99  --inst_lit_activity_flag                true
% 3.79/0.99  --inst_restr_to_given                   false
% 3.79/0.99  --inst_activity_threshold               500
% 3.79/0.99  --inst_out_proof                        true
% 3.79/0.99  
% 3.79/0.99  ------ Resolution Options
% 3.79/0.99  
% 3.79/0.99  --resolution_flag                       false
% 3.79/0.99  --res_lit_sel                           adaptive
% 3.79/0.99  --res_lit_sel_side                      none
% 3.79/0.99  --res_ordering                          kbo
% 3.79/0.99  --res_to_prop_solver                    active
% 3.79/0.99  --res_prop_simpl_new                    false
% 3.79/0.99  --res_prop_simpl_given                  true
% 3.79/0.99  --res_passive_queue_type                priority_queues
% 3.79/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.79/0.99  --res_passive_queues_freq               [15;5]
% 3.79/0.99  --res_forward_subs                      full
% 3.79/0.99  --res_backward_subs                     full
% 3.79/0.99  --res_forward_subs_resolution           true
% 3.79/0.99  --res_backward_subs_resolution          true
% 3.79/0.99  --res_orphan_elimination                true
% 3.79/0.99  --res_time_limit                        2.
% 3.79/0.99  --res_out_proof                         true
% 3.79/0.99  
% 3.79/0.99  ------ Superposition Options
% 3.79/0.99  
% 3.79/0.99  --superposition_flag                    true
% 3.79/0.99  --sup_passive_queue_type                priority_queues
% 3.79/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.79/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.79/0.99  --demod_completeness_check              fast
% 3.79/0.99  --demod_use_ground                      true
% 3.79/0.99  --sup_to_prop_solver                    passive
% 3.79/0.99  --sup_prop_simpl_new                    true
% 3.79/0.99  --sup_prop_simpl_given                  true
% 3.79/0.99  --sup_fun_splitting                     true
% 3.79/0.99  --sup_smt_interval                      50000
% 3.79/0.99  
% 3.79/0.99  ------ Superposition Simplification Setup
% 3.79/0.99  
% 3.79/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.79/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.79/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.79/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.79/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.79/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.79/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.79/0.99  --sup_immed_triv                        [TrivRules]
% 3.79/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.79/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.79/0.99  --sup_immed_bw_main                     []
% 3.79/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.79/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.79/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.79/0.99  --sup_input_bw                          []
% 3.79/0.99  
% 3.79/0.99  ------ Combination Options
% 3.79/0.99  
% 3.79/0.99  --comb_res_mult                         3
% 3.79/0.99  --comb_sup_mult                         2
% 3.79/0.99  --comb_inst_mult                        10
% 3.79/0.99  
% 3.79/0.99  ------ Debug Options
% 3.79/0.99  
% 3.79/0.99  --dbg_backtrace                         false
% 3.79/0.99  --dbg_dump_prop_clauses                 false
% 3.79/0.99  --dbg_dump_prop_clauses_file            -
% 3.79/0.99  --dbg_out_stat                          false
% 3.79/0.99  
% 3.79/0.99  
% 3.79/0.99  
% 3.79/0.99  
% 3.79/0.99  ------ Proving...
% 3.79/0.99  
% 3.79/0.99  
% 3.79/0.99  % SZS status Theorem for theBenchmark.p
% 3.79/0.99  
% 3.79/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.79/0.99  
% 3.79/0.99  fof(f3,axiom,(
% 3.79/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 3.79/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/0.99  
% 3.79/0.99  fof(f11,plain,(
% 3.79/0.99    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 3.79/0.99    inference(ennf_transformation,[],[f3])).
% 3.79/0.99  
% 3.79/0.99  fof(f40,plain,(
% 3.79/0.99    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 3.79/0.99    inference(cnf_transformation,[],[f11])).
% 3.79/0.99  
% 3.79/0.99  fof(f8,conjecture,(
% 3.79/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1)) => m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1))))))),
% 3.79/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/0.99  
% 3.79/0.99  fof(f9,negated_conjecture,(
% 3.79/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1)) => m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1))))))),
% 3.79/0.99    inference(negated_conjecture,[],[f8])).
% 3.79/0.99  
% 3.79/0.99  fof(f20,plain,(
% 3.79/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & (m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.79/0.99    inference(ennf_transformation,[],[f9])).
% 3.79/0.99  
% 3.79/0.99  fof(f21,plain,(
% 3.79/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.79/0.99    inference(flattening,[],[f20])).
% 3.79/0.99  
% 3.79/0.99  fof(f32,plain,(
% 3.79/0.99    ( ! [X2,X0,X1] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,sK4),X0,X1) & m1_connsp_2(sK4,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.79/0.99    introduced(choice_axiom,[])).
% 3.79/0.99  
% 3.79/0.99  fof(f31,plain,(
% 3.79/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),sK3,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(sK3,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.79/0.99    introduced(choice_axiom,[])).
% 3.79/0.99  
% 3.79/0.99  fof(f30,plain,(
% 3.79/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,sK2) & m1_connsp_2(X3,X0,sK2) & m1_connsp_2(X2,X0,sK2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK2,u1_struct_0(X0)))) )),
% 3.79/0.99    introduced(choice_axiom,[])).
% 3.79/0.99  
% 3.79/0.99  fof(f29,plain,(
% 3.79/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(sK1),X2,X3),sK1,X1) & m1_connsp_2(X3,sK1,X1) & m1_connsp_2(X2,sK1,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X1,u1_struct_0(sK1))) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 3.79/0.99    introduced(choice_axiom,[])).
% 3.79/0.99  
% 3.79/0.99  fof(f33,plain,(
% 3.79/0.99    (((~m1_connsp_2(k4_subset_1(u1_struct_0(sK1),sK3,sK4),sK1,sK2) & m1_connsp_2(sK4,sK1,sK2) & m1_connsp_2(sK3,sK1,sK2) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK2,u1_struct_0(sK1))) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 3.79/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f21,f32,f31,f30,f29])).
% 3.79/0.99  
% 3.79/0.99  fof(f50,plain,(
% 3.79/0.99    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 3.79/0.99    inference(cnf_transformation,[],[f33])).
% 3.79/0.99  
% 3.79/0.99  fof(f51,plain,(
% 3.79/0.99    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))),
% 3.79/0.99    inference(cnf_transformation,[],[f33])).
% 3.79/0.99  
% 3.79/0.99  fof(f5,axiom,(
% 3.79/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 3.79/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/0.99  
% 3.79/0.99  fof(f14,plain,(
% 3.79/0.99    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.79/0.99    inference(ennf_transformation,[],[f5])).
% 3.79/0.99  
% 3.79/0.99  fof(f15,plain,(
% 3.79/0.99    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.79/0.99    inference(flattening,[],[f14])).
% 3.79/0.99  
% 3.79/0.99  fof(f42,plain,(
% 3.79/0.99    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.79/0.99    inference(cnf_transformation,[],[f15])).
% 3.79/0.99  
% 3.79/0.99  fof(f2,axiom,(
% 3.79/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.79/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/0.99  
% 3.79/0.99  fof(f26,plain,(
% 3.79/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.79/0.99    inference(nnf_transformation,[],[f2])).
% 3.79/0.99  
% 3.79/0.99  fof(f27,plain,(
% 3.79/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.79/0.99    inference(flattening,[],[f26])).
% 3.79/0.99  
% 3.79/0.99  fof(f39,plain,(
% 3.79/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.79/0.99    inference(cnf_transformation,[],[f27])).
% 3.79/0.99  
% 3.79/0.99  fof(f6,axiom,(
% 3.79/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 3.79/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/0.99  
% 3.79/0.99  fof(f16,plain,(
% 3.79/0.99    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.79/0.99    inference(ennf_transformation,[],[f6])).
% 3.79/0.99  
% 3.79/0.99  fof(f17,plain,(
% 3.79/0.99    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.79/0.99    inference(flattening,[],[f16])).
% 3.79/0.99  
% 3.79/0.99  fof(f43,plain,(
% 3.79/0.99    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.79/0.99    inference(cnf_transformation,[],[f17])).
% 3.79/0.99  
% 3.79/0.99  fof(f48,plain,(
% 3.79/0.99    l1_pre_topc(sK1)),
% 3.79/0.99    inference(cnf_transformation,[],[f33])).
% 3.79/0.99  
% 3.79/0.99  fof(f38,plain,(
% 3.79/0.99    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.79/0.99    inference(cnf_transformation,[],[f27])).
% 3.79/0.99  
% 3.79/0.99  fof(f55,plain,(
% 3.79/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.79/0.99    inference(equality_resolution,[],[f38])).
% 3.79/0.99  
% 3.79/0.99  fof(f1,axiom,(
% 3.79/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.79/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/0.99  
% 3.79/0.99  fof(f10,plain,(
% 3.79/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.79/0.99    inference(ennf_transformation,[],[f1])).
% 3.79/0.99  
% 3.79/0.99  fof(f22,plain,(
% 3.79/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.79/0.99    inference(nnf_transformation,[],[f10])).
% 3.79/0.99  
% 3.79/0.99  fof(f23,plain,(
% 3.79/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.79/0.99    inference(rectify,[],[f22])).
% 3.79/0.99  
% 3.79/0.99  fof(f24,plain,(
% 3.79/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.79/0.99    introduced(choice_axiom,[])).
% 3.79/0.99  
% 3.79/0.99  fof(f25,plain,(
% 3.79/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.79/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).
% 3.79/0.99  
% 3.79/0.99  fof(f34,plain,(
% 3.79/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.79/0.99    inference(cnf_transformation,[],[f25])).
% 3.79/0.99  
% 3.79/0.99  fof(f4,axiom,(
% 3.79/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 3.79/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/0.99  
% 3.79/0.99  fof(f12,plain,(
% 3.79/0.99    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.79/0.99    inference(ennf_transformation,[],[f4])).
% 3.79/0.99  
% 3.79/0.99  fof(f13,plain,(
% 3.79/0.99    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.79/0.99    inference(flattening,[],[f12])).
% 3.79/0.99  
% 3.79/0.99  fof(f41,plain,(
% 3.79/0.99    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.79/0.99    inference(cnf_transformation,[],[f13])).
% 3.79/0.99  
% 3.79/0.99  fof(f53,plain,(
% 3.79/0.99    m1_connsp_2(sK4,sK1,sK2)),
% 3.79/0.99    inference(cnf_transformation,[],[f33])).
% 3.79/0.99  
% 3.79/0.99  fof(f7,axiom,(
% 3.79/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 3.79/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/0.99  
% 3.79/0.99  fof(f18,plain,(
% 3.79/0.99    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.79/0.99    inference(ennf_transformation,[],[f7])).
% 3.79/0.99  
% 3.79/0.99  fof(f19,plain,(
% 3.79/0.99    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.79/0.99    inference(flattening,[],[f18])).
% 3.79/0.99  
% 3.79/0.99  fof(f28,plain,(
% 3.79/0.99    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.79/0.99    inference(nnf_transformation,[],[f19])).
% 3.79/0.99  
% 3.79/0.99  fof(f44,plain,(
% 3.79/0.99    ( ! [X2,X0,X1] : (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.79/0.99    inference(cnf_transformation,[],[f28])).
% 3.79/0.99  
% 3.79/0.99  fof(f47,plain,(
% 3.79/0.99    v2_pre_topc(sK1)),
% 3.79/0.99    inference(cnf_transformation,[],[f33])).
% 3.79/0.99  
% 3.79/0.99  fof(f46,plain,(
% 3.79/0.99    ~v2_struct_0(sK1)),
% 3.79/0.99    inference(cnf_transformation,[],[f33])).
% 3.79/0.99  
% 3.79/0.99  fof(f54,plain,(
% 3.79/0.99    ~m1_connsp_2(k4_subset_1(u1_struct_0(sK1),sK3,sK4),sK1,sK2)),
% 3.79/0.99    inference(cnf_transformation,[],[f33])).
% 3.79/0.99  
% 3.79/0.99  fof(f45,plain,(
% 3.79/0.99    ( ! [X2,X0,X1] : (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.79/0.99    inference(cnf_transformation,[],[f28])).
% 3.79/0.99  
% 3.79/0.99  fof(f49,plain,(
% 3.79/0.99    m1_subset_1(sK2,u1_struct_0(sK1))),
% 3.79/0.99    inference(cnf_transformation,[],[f33])).
% 3.79/0.99  
% 3.79/0.99  cnf(c_6,plain,
% 3.79/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1)) ),
% 3.79/0.99      inference(cnf_transformation,[],[f40]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_9614,plain,
% 3.79/0.99      ( r1_tarski(sK4,k2_xboole_0(sK3,sK4)) | ~ r1_tarski(sK4,sK4) ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_473,plain,
% 3.79/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.79/0.99      theory(equality) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_947,plain,
% 3.79/0.99      ( ~ r1_tarski(X0,X1)
% 3.79/0.99      | r1_tarski(sK4,k4_subset_1(u1_struct_0(sK1),X2,X3))
% 3.79/0.99      | k4_subset_1(u1_struct_0(sK1),X2,X3) != X1
% 3.79/0.99      | sK4 != X0 ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_473]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_1267,plain,
% 3.79/0.99      ( ~ r1_tarski(X0,X1)
% 3.79/0.99      | r1_tarski(sK4,k4_subset_1(u1_struct_0(sK1),sK3,sK4))
% 3.79/0.99      | k4_subset_1(u1_struct_0(sK1),sK3,sK4) != X1
% 3.79/0.99      | sK4 != X0 ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_947]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_2012,plain,
% 3.79/0.99      ( ~ r1_tarski(sK4,X0)
% 3.79/0.99      | r1_tarski(sK4,k4_subset_1(u1_struct_0(sK1),sK3,sK4))
% 3.79/0.99      | k4_subset_1(u1_struct_0(sK1),sK3,sK4) != X0
% 3.79/0.99      | sK4 != sK4 ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_1267]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_4183,plain,
% 3.79/0.99      ( r1_tarski(sK4,k4_subset_1(u1_struct_0(sK1),sK3,sK4))
% 3.79/0.99      | ~ r1_tarski(sK4,k2_xboole_0(sK3,sK4))
% 3.79/0.99      | k4_subset_1(u1_struct_0(sK1),sK3,sK4) != k2_xboole_0(sK3,sK4)
% 3.79/0.99      | sK4 != sK4 ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_2012]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_16,negated_conjecture,
% 3.79/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 3.79/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_740,plain,
% 3.79/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 3.79/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_15,negated_conjecture,
% 3.79/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 3.79/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_741,plain,
% 3.79/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 3.79/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_8,plain,
% 3.79/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.79/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.79/0.99      | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
% 3.79/0.99      inference(cnf_transformation,[],[f42]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_742,plain,
% 3.79/0.99      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
% 3.79/0.99      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 3.79/0.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.79/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_1754,plain,
% 3.79/0.99      ( k4_subset_1(u1_struct_0(sK1),X0,sK4) = k2_xboole_0(X0,sK4)
% 3.79/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 3.79/0.99      inference(superposition,[status(thm)],[c_741,c_742]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_1900,plain,
% 3.79/0.99      ( k4_subset_1(u1_struct_0(sK1),sK3,sK4) = k2_xboole_0(sK3,sK4) ),
% 3.79/0.99      inference(superposition,[status(thm)],[c_740,c_1754]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_3,plain,
% 3.79/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.79/0.99      inference(cnf_transformation,[],[f39]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_998,plain,
% 3.79/0.99      ( ~ r1_tarski(X0,sK4) | ~ r1_tarski(sK4,X0) | sK4 = X0 ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_1639,plain,
% 3.79/0.99      ( ~ r1_tarski(sK4,sK4) | sK4 = sK4 ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_998]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_9,plain,
% 3.79/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.79/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.79/0.99      | ~ r1_tarski(X2,X0)
% 3.79/0.99      | r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X0))
% 3.79/0.99      | ~ l1_pre_topc(X1) ),
% 3.79/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_18,negated_conjecture,
% 3.79/0.99      ( l1_pre_topc(sK1) ),
% 3.79/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_275,plain,
% 3.79/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.79/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.79/0.99      | ~ r1_tarski(X2,X0)
% 3.79/0.99      | r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X0))
% 3.79/0.99      | sK1 != X1 ),
% 3.79/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_18]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_276,plain,
% 3.79/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.79/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.79/0.99      | ~ r1_tarski(X1,X0)
% 3.79/0.99      | r1_tarski(k1_tops_1(sK1,X1),k1_tops_1(sK1,X0)) ),
% 3.79/0.99      inference(unflattening,[status(thm)],[c_275]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_790,plain,
% 3.79/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.79/0.99      | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK1),X1,X2),k1_zfmisc_1(u1_struct_0(sK1)))
% 3.79/0.99      | ~ r1_tarski(X0,k4_subset_1(u1_struct_0(sK1),X1,X2))
% 3.79/0.99      | r1_tarski(k1_tops_1(sK1,X0),k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),X1,X2))) ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_276]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_865,plain,
% 3.79/0.99      ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK1),X0,X1),k1_zfmisc_1(u1_struct_0(sK1)))
% 3.79/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.79/0.99      | r1_tarski(k1_tops_1(sK1,sK4),k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),X0,X1)))
% 3.79/0.99      | ~ r1_tarski(sK4,k4_subset_1(u1_struct_0(sK1),X0,X1)) ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_790]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_1246,plain,
% 3.79/0.99      ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
% 3.79/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.79/0.99      | r1_tarski(k1_tops_1(sK1,sK4),k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4)))
% 3.79/0.99      | ~ r1_tarski(sK4,k4_subset_1(u1_struct_0(sK1),sK3,sK4)) ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_865]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_4,plain,
% 3.79/0.99      ( r1_tarski(X0,X0) ),
% 3.79/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_1190,plain,
% 3.79/0.99      ( r1_tarski(sK4,sK4) ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_2,plain,
% 3.79/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 3.79/0.99      inference(cnf_transformation,[],[f34]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_813,plain,
% 3.79/0.99      ( ~ r2_hidden(sK2,X0)
% 3.79/0.99      | r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4)))
% 3.79/0.99      | ~ r1_tarski(X0,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_825,plain,
% 3.79/0.99      ( r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4)))
% 3.79/0.99      | ~ r2_hidden(sK2,k1_tops_1(sK1,sK4))
% 3.79/0.99      | ~ r1_tarski(k1_tops_1(sK1,sK4),k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_813]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_7,plain,
% 3.79/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.79/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.79/0.99      | m1_subset_1(k4_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 3.79/0.99      inference(cnf_transformation,[],[f41]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_772,plain,
% 3.79/0.99      ( m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
% 3.79/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.79/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_13,negated_conjecture,
% 3.79/0.99      ( m1_connsp_2(sK4,sK1,sK2) ),
% 3.79/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_11,plain,
% 3.79/0.99      ( ~ m1_connsp_2(X0,X1,X2)
% 3.79/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.79/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.79/0.99      | r2_hidden(X2,k1_tops_1(X1,X0))
% 3.79/0.99      | v2_struct_0(X1)
% 3.79/0.99      | ~ v2_pre_topc(X1)
% 3.79/0.99      | ~ l1_pre_topc(X1) ),
% 3.79/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_19,negated_conjecture,
% 3.79/0.99      ( v2_pre_topc(sK1) ),
% 3.79/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_217,plain,
% 3.79/0.99      ( ~ m1_connsp_2(X0,X1,X2)
% 3.79/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.79/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.79/0.99      | r2_hidden(X2,k1_tops_1(X1,X0))
% 3.79/0.99      | v2_struct_0(X1)
% 3.79/0.99      | ~ l1_pre_topc(X1)
% 3.79/0.99      | sK1 != X1 ),
% 3.79/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_19]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_218,plain,
% 3.79/0.99      ( ~ m1_connsp_2(X0,sK1,X1)
% 3.79/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 3.79/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.79/0.99      | r2_hidden(X1,k1_tops_1(sK1,X0))
% 3.79/0.99      | v2_struct_0(sK1)
% 3.79/0.99      | ~ l1_pre_topc(sK1) ),
% 3.79/0.99      inference(unflattening,[status(thm)],[c_217]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_20,negated_conjecture,
% 3.79/0.99      ( ~ v2_struct_0(sK1) ),
% 3.79/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_222,plain,
% 3.79/0.99      ( ~ m1_connsp_2(X0,sK1,X1)
% 3.79/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 3.79/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.79/0.99      | r2_hidden(X1,k1_tops_1(sK1,X0)) ),
% 3.79/0.99      inference(global_propositional_subsumption,
% 3.79/0.99                [status(thm)],
% 3.79/0.99                [c_218,c_20,c_18]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_331,plain,
% 3.79/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 3.79/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.79/0.99      | r2_hidden(X0,k1_tops_1(sK1,X1))
% 3.79/0.99      | sK2 != X0
% 3.79/0.99      | sK4 != X1
% 3.79/0.99      | sK1 != sK1 ),
% 3.79/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_222]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_332,plain,
% 3.79/0.99      ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 3.79/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.79/0.99      | r2_hidden(sK2,k1_tops_1(sK1,sK4)) ),
% 3.79/0.99      inference(unflattening,[status(thm)],[c_331]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_12,negated_conjecture,
% 3.79/0.99      ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK1),sK3,sK4),sK1,sK2) ),
% 3.79/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_10,plain,
% 3.79/0.99      ( m1_connsp_2(X0,X1,X2)
% 3.79/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.79/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.79/0.99      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 3.79/0.99      | v2_struct_0(X1)
% 3.79/0.99      | ~ v2_pre_topc(X1)
% 3.79/0.99      | ~ l1_pre_topc(X1) ),
% 3.79/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_241,plain,
% 3.79/0.99      ( m1_connsp_2(X0,X1,X2)
% 3.79/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.79/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.79/0.99      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 3.79/0.99      | v2_struct_0(X1)
% 3.79/0.99      | ~ l1_pre_topc(X1)
% 3.79/0.99      | sK1 != X1 ),
% 3.79/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_19]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_242,plain,
% 3.79/0.99      ( m1_connsp_2(X0,sK1,X1)
% 3.79/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 3.79/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.79/0.99      | ~ r2_hidden(X1,k1_tops_1(sK1,X0))
% 3.79/0.99      | v2_struct_0(sK1)
% 3.79/0.99      | ~ l1_pre_topc(sK1) ),
% 3.79/0.99      inference(unflattening,[status(thm)],[c_241]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_246,plain,
% 3.79/0.99      ( m1_connsp_2(X0,sK1,X1)
% 3.79/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 3.79/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.79/0.99      | ~ r2_hidden(X1,k1_tops_1(sK1,X0)) ),
% 3.79/0.99      inference(global_propositional_subsumption,
% 3.79/0.99                [status(thm)],
% 3.79/0.99                [c_242,c_20,c_18]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_317,plain,
% 3.79/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 3.79/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.79/0.99      | ~ r2_hidden(X0,k1_tops_1(sK1,X1))
% 3.79/0.99      | k4_subset_1(u1_struct_0(sK1),sK3,sK4) != X1
% 3.79/0.99      | sK2 != X0
% 3.79/0.99      | sK1 != sK1 ),
% 3.79/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_246]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_318,plain,
% 3.79/0.99      ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
% 3.79/0.99      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 3.79/0.99      | ~ r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) ),
% 3.79/0.99      inference(unflattening,[status(thm)],[c_317]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_17,negated_conjecture,
% 3.79/0.99      ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 3.79/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(contradiction,plain,
% 3.79/0.99      ( $false ),
% 3.79/0.99      inference(minisat,
% 3.79/0.99                [status(thm)],
% 3.79/0.99                [c_9614,c_4183,c_1900,c_1639,c_1246,c_1190,c_825,c_772,
% 3.79/0.99                 c_332,c_318,c_15,c_16,c_17]) ).
% 3.79/0.99  
% 3.79/0.99  
% 3.79/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.79/0.99  
% 3.79/0.99  ------                               Statistics
% 3.79/0.99  
% 3.79/0.99  ------ General
% 3.79/0.99  
% 3.79/0.99  abstr_ref_over_cycles:                  0
% 3.79/0.99  abstr_ref_under_cycles:                 0
% 3.79/0.99  gc_basic_clause_elim:                   0
% 3.79/0.99  forced_gc_time:                         0
% 3.79/0.99  parsing_time:                           0.007
% 3.79/0.99  unif_index_cands_time:                  0.
% 3.79/0.99  unif_index_add_time:                    0.
% 3.79/0.99  orderings_time:                         0.
% 3.79/0.99  out_proof_time:                         0.008
% 3.79/0.99  total_time:                             0.296
% 3.79/0.99  num_of_symbols:                         48
% 3.79/0.99  num_of_terms:                           10131
% 3.79/0.99  
% 3.79/0.99  ------ Preprocessing
% 3.79/0.99  
% 3.79/0.99  num_of_splits:                          0
% 3.79/0.99  num_of_split_atoms:                     0
% 3.79/0.99  num_of_reused_defs:                     0
% 3.79/0.99  num_eq_ax_congr_red:                    14
% 3.79/0.99  num_of_sem_filtered_clauses:            1
% 3.79/0.99  num_of_subtypes:                        0
% 3.79/0.99  monotx_restored_types:                  0
% 3.79/0.99  sat_num_of_epr_types:                   0
% 3.79/0.99  sat_num_of_non_cyclic_types:            0
% 3.79/0.99  sat_guarded_non_collapsed_types:        0
% 3.79/0.99  num_pure_diseq_elim:                    0
% 3.79/0.99  simp_replaced_by:                       0
% 3.79/0.99  res_preprocessed:                       90
% 3.79/0.99  prep_upred:                             0
% 3.79/0.99  prep_unflattend:                        9
% 3.79/0.99  smt_new_axioms:                         0
% 3.79/0.99  pred_elim_cands:                        3
% 3.79/0.99  pred_elim:                              4
% 3.79/0.99  pred_elim_cl:                           3
% 3.79/0.99  pred_elim_cycles:                       6
% 3.79/0.99  merged_defs:                            0
% 3.79/0.99  merged_defs_ncl:                        0
% 3.79/0.99  bin_hyper_res:                          0
% 3.79/0.99  prep_cycles:                            4
% 3.79/0.99  pred_elim_time:                         0.003
% 3.79/0.99  splitting_time:                         0.
% 3.79/0.99  sem_filter_time:                        0.
% 3.79/0.99  monotx_time:                            0.
% 3.79/0.99  subtype_inf_time:                       0.
% 3.79/0.99  
% 3.79/0.99  ------ Problem properties
% 3.79/0.99  
% 3.79/0.99  clauses:                                17
% 3.79/0.99  conjectures:                            3
% 3.79/0.99  epr:                                    3
% 3.79/0.99  horn:                                   16
% 3.79/0.99  ground:                                 8
% 3.79/0.99  unary:                                  8
% 3.79/0.99  binary:                                 4
% 3.79/0.99  lits:                                   32
% 3.79/0.99  lits_eq:                                4
% 3.79/0.99  fd_pure:                                0
% 3.79/0.99  fd_pseudo:                              0
% 3.79/0.99  fd_cond:                                0
% 3.79/0.99  fd_pseudo_cond:                         1
% 3.79/0.99  ac_symbols:                             0
% 3.79/0.99  
% 3.79/0.99  ------ Propositional Solver
% 3.79/0.99  
% 3.79/0.99  prop_solver_calls:                      31
% 3.79/0.99  prop_fast_solver_calls:                 746
% 3.79/0.99  smt_solver_calls:                       0
% 3.79/0.99  smt_fast_solver_calls:                  0
% 3.79/0.99  prop_num_of_clauses:                    4365
% 3.79/0.99  prop_preprocess_simplified:             7512
% 3.79/0.99  prop_fo_subsumed:                       25
% 3.79/0.99  prop_solver_time:                       0.
% 3.79/0.99  smt_solver_time:                        0.
% 3.79/0.99  smt_fast_solver_time:                   0.
% 3.79/0.99  prop_fast_solver_time:                  0.
% 3.79/0.99  prop_unsat_core_time:                   0.
% 3.79/0.99  
% 3.79/0.99  ------ QBF
% 3.79/0.99  
% 3.79/0.99  qbf_q_res:                              0
% 3.79/0.99  qbf_num_tautologies:                    0
% 3.79/0.99  qbf_prep_cycles:                        0
% 3.79/0.99  
% 3.79/0.99  ------ BMC1
% 3.79/0.99  
% 3.79/0.99  bmc1_current_bound:                     -1
% 3.79/0.99  bmc1_last_solved_bound:                 -1
% 3.79/0.99  bmc1_unsat_core_size:                   -1
% 3.79/0.99  bmc1_unsat_core_parents_size:           -1
% 3.79/0.99  bmc1_merge_next_fun:                    0
% 3.79/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.79/0.99  
% 3.79/0.99  ------ Instantiation
% 3.79/0.99  
% 3.79/0.99  inst_num_of_clauses:                    1099
% 3.79/0.99  inst_num_in_passive:                    203
% 3.79/0.99  inst_num_in_active:                     560
% 3.79/0.99  inst_num_in_unprocessed:                335
% 3.79/0.99  inst_num_of_loops:                      689
% 3.79/0.99  inst_num_of_learning_restarts:          0
% 3.79/0.99  inst_num_moves_active_passive:          125
% 3.79/0.99  inst_lit_activity:                      0
% 3.79/0.99  inst_lit_activity_moves:                0
% 3.79/0.99  inst_num_tautologies:                   0
% 3.79/0.99  inst_num_prop_implied:                  0
% 3.79/0.99  inst_num_existing_simplified:           0
% 3.79/0.99  inst_num_eq_res_simplified:             0
% 3.79/0.99  inst_num_child_elim:                    0
% 3.79/0.99  inst_num_of_dismatching_blockings:      457
% 3.79/0.99  inst_num_of_non_proper_insts:           1466
% 3.79/0.99  inst_num_of_duplicates:                 0
% 3.79/0.99  inst_inst_num_from_inst_to_res:         0
% 3.79/0.99  inst_dismatching_checking_time:         0.
% 3.79/0.99  
% 3.79/0.99  ------ Resolution
% 3.79/0.99  
% 3.79/0.99  res_num_of_clauses:                     0
% 3.79/0.99  res_num_in_passive:                     0
% 3.79/0.99  res_num_in_active:                      0
% 3.79/0.99  res_num_of_loops:                       94
% 3.79/0.99  res_forward_subset_subsumed:            165
% 3.79/0.99  res_backward_subset_subsumed:           0
% 3.79/0.99  res_forward_subsumed:                   0
% 3.79/0.99  res_backward_subsumed:                  0
% 3.79/0.99  res_forward_subsumption_resolution:     0
% 3.79/0.99  res_backward_subsumption_resolution:    0
% 3.79/0.99  res_clause_to_clause_subsumption:       1301
% 3.79/0.99  res_orphan_elimination:                 0
% 3.79/0.99  res_tautology_del:                      129
% 3.79/0.99  res_num_eq_res_simplified:              2
% 3.79/0.99  res_num_sel_changes:                    0
% 3.79/0.99  res_moves_from_active_to_pass:          0
% 3.79/0.99  
% 3.79/0.99  ------ Superposition
% 3.79/0.99  
% 3.79/0.99  sup_time_total:                         0.
% 3.79/0.99  sup_time_generating:                    0.
% 3.79/0.99  sup_time_sim_full:                      0.
% 3.79/0.99  sup_time_sim_immed:                     0.
% 3.79/0.99  
% 3.79/0.99  sup_num_of_clauses:                     391
% 3.79/0.99  sup_num_in_active:                      133
% 3.79/0.99  sup_num_in_passive:                     258
% 3.79/0.99  sup_num_of_loops:                       136
% 3.79/0.99  sup_fw_superposition:                   305
% 3.79/0.99  sup_bw_superposition:                   127
% 3.79/0.99  sup_immediate_simplified:               171
% 3.79/0.99  sup_given_eliminated:                   0
% 3.79/0.99  comparisons_done:                       0
% 3.79/0.99  comparisons_avoided:                    0
% 3.79/0.99  
% 3.79/0.99  ------ Simplifications
% 3.79/0.99  
% 3.79/0.99  
% 3.79/0.99  sim_fw_subset_subsumed:                 4
% 3.79/0.99  sim_bw_subset_subsumed:                 0
% 3.79/0.99  sim_fw_subsumed:                        0
% 3.79/0.99  sim_bw_subsumed:                        0
% 3.79/0.99  sim_fw_subsumption_res:                 0
% 3.79/0.99  sim_bw_subsumption_res:                 0
% 3.79/0.99  sim_tautology_del:                      1
% 3.79/0.99  sim_eq_tautology_del:                   19
% 3.79/0.99  sim_eq_res_simp:                        0
% 3.79/0.99  sim_fw_demodulated:                     0
% 3.79/0.99  sim_bw_demodulated:                     3
% 3.79/0.99  sim_light_normalised:                   167
% 3.79/0.99  sim_joinable_taut:                      0
% 3.79/0.99  sim_joinable_simp:                      0
% 3.79/0.99  sim_ac_normalised:                      0
% 3.79/0.99  sim_smt_subsumption:                    0
% 3.79/0.99  
%------------------------------------------------------------------------------
