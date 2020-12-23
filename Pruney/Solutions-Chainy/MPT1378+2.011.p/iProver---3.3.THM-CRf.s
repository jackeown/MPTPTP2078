%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:18:11 EST 2020

% Result     : Theorem 47.84s
% Output     : CNFRefutation 47.84s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 268 expanded)
%              Number of clauses        :   55 (  67 expanded)
%              Number of leaves         :   15 (  92 expanded)
%              Depth                    :   14
%              Number of atoms          :  457 (1920 expanded)
%              Number of equality atoms :   55 (  58 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f23])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & ~ r2_hidden(sK0(X0,X1,X2),X0) )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( r2_hidden(sK0(X0,X1,X2),X1)
          | r2_hidden(sK0(X0,X1,X2),X0)
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & ~ r2_hidden(sK0(X0,X1,X2),X0) )
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( r2_hidden(sK0(X0,X1,X2),X1)
            | r2_hidden(sK0(X0,X1,X2),X0)
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).

fof(f37,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f56,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f37])).

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
     => ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

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
    inference(ennf_transformation,[],[f9])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f22,f32,f31,f30,f29])).

fof(f49,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f52,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f33])).

fof(f51,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f33])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
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
    inference(ennf_transformation,[],[f4])).

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

fof(f3,axiom,(
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
    inference(ennf_transformation,[],[f3])).

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

fof(f54,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f48,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f47,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f55,plain,(
    ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK1),sK3,sK4),sK1,sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f50,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_169091,plain,
    ( ~ r2_hidden(sK2,k1_tops_1(sK1,sK4))
    | r2_hidden(sK2,k2_xboole_0(X0,k1_tops_1(sK1,sK4))) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_185021,plain,
    ( ~ r2_hidden(sK2,k1_tops_1(sK1,sK4))
    | r2_hidden(sK2,k2_xboole_0(k1_tops_1(sK1,sK3),k1_tops_1(sK1,sK4))) ),
    inference(instantiation,[status(thm)],[c_169091])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k4_subset_1(u1_struct_0(X1),k1_tops_1(X1,X0),k1_tops_1(X1,X2)),k1_tops_1(X1,k4_subset_1(u1_struct_0(X1),X0,X2)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_19,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_318,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k4_subset_1(u1_struct_0(X1),k1_tops_1(X1,X0),k1_tops_1(X1,X2)),k1_tops_1(X1,k4_subset_1(u1_struct_0(X1),X0,X2)))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_19])).

cnf(c_319,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(k4_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,X0),k1_tops_1(sK1,X1)),k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),X0,X1))) ),
    inference(unflattening,[status(thm)],[c_318])).

cnf(c_352,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X2,X3)
    | r2_hidden(X2,X4)
    | k4_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,X0),k1_tops_1(sK1,X1)) != X3
    | k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),X0,X1)) != X4 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_319])).

cnf(c_353,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X2,k4_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,X0),k1_tops_1(sK1,X1)))
    | r2_hidden(X2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),X0,X1))) ),
    inference(unflattening,[status(thm)],[c_352])).

cnf(c_169053,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X1,k4_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,sK3),k1_tops_1(sK1,X0)))
    | r2_hidden(X1,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,X0))) ),
    inference(instantiation,[status(thm)],[c_353])).

cnf(c_169837,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X0,k4_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,sK3),k1_tops_1(sK1,sK4)))
    | r2_hidden(X0,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_169053])).

cnf(c_177878,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK2,k4_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,sK3),k1_tops_1(sK1,sK4)))
    | r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_169837])).

cnf(c_559,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_169859,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK2,k2_xboole_0(X2,k1_tops_1(sK1,sK4)))
    | X1 != k2_xboole_0(X2,k1_tops_1(sK1,sK4))
    | X0 != sK2 ),
    inference(instantiation,[status(thm)],[c_559])).

cnf(c_172241,plain,
    ( r2_hidden(sK2,X0)
    | ~ r2_hidden(sK2,k2_xboole_0(X1,k1_tops_1(sK1,sK4)))
    | X0 != k2_xboole_0(X1,k1_tops_1(sK1,sK4))
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_169859])).

cnf(c_173670,plain,
    ( r2_hidden(sK2,k4_subset_1(u1_struct_0(sK1),X0,k1_tops_1(sK1,sK4)))
    | ~ r2_hidden(sK2,k2_xboole_0(X0,k1_tops_1(sK1,sK4)))
    | k4_subset_1(u1_struct_0(sK1),X0,k1_tops_1(sK1,sK4)) != k2_xboole_0(X0,k1_tops_1(sK1,sK4))
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_172241])).

cnf(c_177877,plain,
    ( r2_hidden(sK2,k4_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,sK3),k1_tops_1(sK1,sK4)))
    | ~ r2_hidden(sK2,k2_xboole_0(k1_tops_1(sK1,sK3),k1_tops_1(sK1,sK4)))
    | k4_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,sK3),k1_tops_1(sK1,sK4)) != k2_xboole_0(k1_tops_1(sK1,sK3),k1_tops_1(sK1,sK4))
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_173670])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_838,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_837,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_333,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_19])).

cnf(c_334,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k1_tops_1(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_333])).

cnf(c_835,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k1_tops_1(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_334])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_839,plain,
    ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1935,plain,
    ( k4_subset_1(u1_struct_0(sK1),X0,k1_tops_1(sK1,X1)) = k2_xboole_0(X0,k1_tops_1(sK1,X1))
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_835,c_839])).

cnf(c_4947,plain,
    ( k4_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,X0),k1_tops_1(sK1,X1)) = k2_xboole_0(k1_tops_1(sK1,X0),k1_tops_1(sK1,X1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_835,c_1935])).

cnf(c_37617,plain,
    ( k4_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,sK3),k1_tops_1(sK1,X0)) = k2_xboole_0(k1_tops_1(sK1,sK3),k1_tops_1(sK1,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_837,c_4947])).

cnf(c_38392,plain,
    ( k4_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,sK3),k1_tops_1(sK1,sK4)) = k2_xboole_0(k1_tops_1(sK1,sK3),k1_tops_1(sK1,sK4)) ),
    inference(superposition,[status(thm)],[c_838,c_37617])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | m1_subset_1(k4_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_977,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k4_subset_1(u1_struct_0(sK1),X0,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1138,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_977])).

cnf(c_557,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1069,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_557])).

cnf(c_14,negated_conjecture,
    ( m1_connsp_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_12,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_20,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_260,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_20])).

cnf(c_261,plain,
    ( ~ m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(X1,k1_tops_1(sK1,X0))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_260])).

cnf(c_21,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_265,plain,
    ( ~ m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(X1,k1_tops_1(sK1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_261,c_21,c_19])).

cnf(c_410,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(X0,k1_tops_1(sK1,X1))
    | sK2 != X0
    | sK4 != X1
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_265])).

cnf(c_411,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(sK2,k1_tops_1(sK1,sK4)) ),
    inference(unflattening,[status(thm)],[c_410])).

cnf(c_13,negated_conjecture,
    ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK1),sK3,sK4),sK1,sK2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_11,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_284,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_20])).

cnf(c_285,plain,
    ( m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X1,k1_tops_1(sK1,X0))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_284])).

cnf(c_289,plain,
    ( m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X1,k1_tops_1(sK1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_285,c_21,c_19])).

cnf(c_396,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X0,k1_tops_1(sK1,X1))
    | k4_subset_1(u1_struct_0(sK1),sK3,sK4) != X1
    | sK2 != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_289])).

cnf(c_397,plain,
    ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) ),
    inference(unflattening,[status(thm)],[c_396])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_185021,c_177878,c_177877,c_38392,c_1138,c_1069,c_411,c_397,c_16,c_17,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:50:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 47.84/6.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 47.84/6.50  
% 47.84/6.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 47.84/6.50  
% 47.84/6.50  ------  iProver source info
% 47.84/6.50  
% 47.84/6.50  git: date: 2020-06-30 10:37:57 +0100
% 47.84/6.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 47.84/6.50  git: non_committed_changes: false
% 47.84/6.50  git: last_make_outside_of_git: false
% 47.84/6.50  
% 47.84/6.50  ------ 
% 47.84/6.50  
% 47.84/6.50  ------ Input Options
% 47.84/6.50  
% 47.84/6.50  --out_options                           all
% 47.84/6.50  --tptp_safe_out                         true
% 47.84/6.50  --problem_path                          ""
% 47.84/6.50  --include_path                          ""
% 47.84/6.50  --clausifier                            res/vclausify_rel
% 47.84/6.50  --clausifier_options                    --mode clausify
% 47.84/6.50  --stdin                                 false
% 47.84/6.50  --stats_out                             all
% 47.84/6.50  
% 47.84/6.50  ------ General Options
% 47.84/6.50  
% 47.84/6.50  --fof                                   false
% 47.84/6.50  --time_out_real                         305.
% 47.84/6.50  --time_out_virtual                      -1.
% 47.84/6.50  --symbol_type_check                     false
% 47.84/6.50  --clausify_out                          false
% 47.84/6.50  --sig_cnt_out                           false
% 47.84/6.50  --trig_cnt_out                          false
% 47.84/6.50  --trig_cnt_out_tolerance                1.
% 47.84/6.50  --trig_cnt_out_sk_spl                   false
% 47.84/6.50  --abstr_cl_out                          false
% 47.84/6.50  
% 47.84/6.50  ------ Global Options
% 47.84/6.50  
% 47.84/6.50  --schedule                              default
% 47.84/6.50  --add_important_lit                     false
% 47.84/6.50  --prop_solver_per_cl                    1000
% 47.84/6.50  --min_unsat_core                        false
% 47.84/6.50  --soft_assumptions                      false
% 47.84/6.50  --soft_lemma_size                       3
% 47.84/6.50  --prop_impl_unit_size                   0
% 47.84/6.50  --prop_impl_unit                        []
% 47.84/6.50  --share_sel_clauses                     true
% 47.84/6.50  --reset_solvers                         false
% 47.84/6.50  --bc_imp_inh                            [conj_cone]
% 47.84/6.50  --conj_cone_tolerance                   3.
% 47.84/6.50  --extra_neg_conj                        none
% 47.84/6.50  --large_theory_mode                     true
% 47.84/6.50  --prolific_symb_bound                   200
% 47.84/6.50  --lt_threshold                          2000
% 47.84/6.50  --clause_weak_htbl                      true
% 47.84/6.50  --gc_record_bc_elim                     false
% 47.84/6.50  
% 47.84/6.50  ------ Preprocessing Options
% 47.84/6.50  
% 47.84/6.50  --preprocessing_flag                    true
% 47.84/6.50  --time_out_prep_mult                    0.1
% 47.84/6.50  --splitting_mode                        input
% 47.84/6.50  --splitting_grd                         true
% 47.84/6.50  --splitting_cvd                         false
% 47.84/6.50  --splitting_cvd_svl                     false
% 47.84/6.50  --splitting_nvd                         32
% 47.84/6.50  --sub_typing                            true
% 47.84/6.50  --prep_gs_sim                           true
% 47.84/6.50  --prep_unflatten                        true
% 47.84/6.50  --prep_res_sim                          true
% 47.84/6.50  --prep_upred                            true
% 47.84/6.50  --prep_sem_filter                       exhaustive
% 47.84/6.50  --prep_sem_filter_out                   false
% 47.84/6.50  --pred_elim                             true
% 47.84/6.50  --res_sim_input                         true
% 47.84/6.50  --eq_ax_congr_red                       true
% 47.84/6.50  --pure_diseq_elim                       true
% 47.84/6.50  --brand_transform                       false
% 47.84/6.50  --non_eq_to_eq                          false
% 47.84/6.50  --prep_def_merge                        true
% 47.84/6.50  --prep_def_merge_prop_impl              false
% 47.84/6.50  --prep_def_merge_mbd                    true
% 47.84/6.50  --prep_def_merge_tr_red                 false
% 47.84/6.50  --prep_def_merge_tr_cl                  false
% 47.84/6.50  --smt_preprocessing                     true
% 47.84/6.50  --smt_ac_axioms                         fast
% 47.84/6.50  --preprocessed_out                      false
% 47.84/6.50  --preprocessed_stats                    false
% 47.84/6.50  
% 47.84/6.50  ------ Abstraction refinement Options
% 47.84/6.50  
% 47.84/6.50  --abstr_ref                             []
% 47.84/6.50  --abstr_ref_prep                        false
% 47.84/6.50  --abstr_ref_until_sat                   false
% 47.84/6.50  --abstr_ref_sig_restrict                funpre
% 47.84/6.50  --abstr_ref_af_restrict_to_split_sk     false
% 47.84/6.50  --abstr_ref_under                       []
% 47.84/6.50  
% 47.84/6.50  ------ SAT Options
% 47.84/6.50  
% 47.84/6.50  --sat_mode                              false
% 47.84/6.50  --sat_fm_restart_options                ""
% 47.84/6.50  --sat_gr_def                            false
% 47.84/6.50  --sat_epr_types                         true
% 47.84/6.50  --sat_non_cyclic_types                  false
% 47.84/6.50  --sat_finite_models                     false
% 47.84/6.50  --sat_fm_lemmas                         false
% 47.84/6.50  --sat_fm_prep                           false
% 47.84/6.50  --sat_fm_uc_incr                        true
% 47.84/6.50  --sat_out_model                         small
% 47.84/6.50  --sat_out_clauses                       false
% 47.84/6.50  
% 47.84/6.50  ------ QBF Options
% 47.84/6.50  
% 47.84/6.50  --qbf_mode                              false
% 47.84/6.50  --qbf_elim_univ                         false
% 47.84/6.50  --qbf_dom_inst                          none
% 47.84/6.50  --qbf_dom_pre_inst                      false
% 47.84/6.50  --qbf_sk_in                             false
% 47.84/6.50  --qbf_pred_elim                         true
% 47.84/6.50  --qbf_split                             512
% 47.84/6.50  
% 47.84/6.50  ------ BMC1 Options
% 47.84/6.50  
% 47.84/6.50  --bmc1_incremental                      false
% 47.84/6.50  --bmc1_axioms                           reachable_all
% 47.84/6.50  --bmc1_min_bound                        0
% 47.84/6.50  --bmc1_max_bound                        -1
% 47.84/6.50  --bmc1_max_bound_default                -1
% 47.84/6.50  --bmc1_symbol_reachability              true
% 47.84/6.50  --bmc1_property_lemmas                  false
% 47.84/6.50  --bmc1_k_induction                      false
% 47.84/6.50  --bmc1_non_equiv_states                 false
% 47.84/6.50  --bmc1_deadlock                         false
% 47.84/6.50  --bmc1_ucm                              false
% 47.84/6.50  --bmc1_add_unsat_core                   none
% 47.84/6.50  --bmc1_unsat_core_children              false
% 47.84/6.50  --bmc1_unsat_core_extrapolate_axioms    false
% 47.84/6.50  --bmc1_out_stat                         full
% 47.84/6.50  --bmc1_ground_init                      false
% 47.84/6.50  --bmc1_pre_inst_next_state              false
% 47.84/6.50  --bmc1_pre_inst_state                   false
% 47.84/6.50  --bmc1_pre_inst_reach_state             false
% 47.84/6.50  --bmc1_out_unsat_core                   false
% 47.84/6.50  --bmc1_aig_witness_out                  false
% 47.84/6.50  --bmc1_verbose                          false
% 47.84/6.50  --bmc1_dump_clauses_tptp                false
% 47.84/6.50  --bmc1_dump_unsat_core_tptp             false
% 47.84/6.50  --bmc1_dump_file                        -
% 47.84/6.50  --bmc1_ucm_expand_uc_limit              128
% 47.84/6.50  --bmc1_ucm_n_expand_iterations          6
% 47.84/6.50  --bmc1_ucm_extend_mode                  1
% 47.84/6.50  --bmc1_ucm_init_mode                    2
% 47.84/6.50  --bmc1_ucm_cone_mode                    none
% 47.84/6.50  --bmc1_ucm_reduced_relation_type        0
% 47.84/6.50  --bmc1_ucm_relax_model                  4
% 47.84/6.50  --bmc1_ucm_full_tr_after_sat            true
% 47.84/6.50  --bmc1_ucm_expand_neg_assumptions       false
% 47.84/6.50  --bmc1_ucm_layered_model                none
% 47.84/6.50  --bmc1_ucm_max_lemma_size               10
% 47.84/6.50  
% 47.84/6.50  ------ AIG Options
% 47.84/6.50  
% 47.84/6.50  --aig_mode                              false
% 47.84/6.50  
% 47.84/6.50  ------ Instantiation Options
% 47.84/6.50  
% 47.84/6.50  --instantiation_flag                    true
% 47.84/6.50  --inst_sos_flag                         false
% 47.84/6.50  --inst_sos_phase                        true
% 47.84/6.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 47.84/6.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 47.84/6.50  --inst_lit_sel_side                     num_symb
% 47.84/6.50  --inst_solver_per_active                1400
% 47.84/6.50  --inst_solver_calls_frac                1.
% 47.84/6.50  --inst_passive_queue_type               priority_queues
% 47.84/6.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 47.84/6.50  --inst_passive_queues_freq              [25;2]
% 47.84/6.50  --inst_dismatching                      true
% 47.84/6.50  --inst_eager_unprocessed_to_passive     true
% 47.84/6.50  --inst_prop_sim_given                   true
% 47.84/6.50  --inst_prop_sim_new                     false
% 47.84/6.50  --inst_subs_new                         false
% 47.84/6.50  --inst_eq_res_simp                      false
% 47.84/6.50  --inst_subs_given                       false
% 47.84/6.50  --inst_orphan_elimination               true
% 47.84/6.50  --inst_learning_loop_flag               true
% 47.84/6.50  --inst_learning_start                   3000
% 47.84/6.50  --inst_learning_factor                  2
% 47.84/6.50  --inst_start_prop_sim_after_learn       3
% 47.84/6.50  --inst_sel_renew                        solver
% 47.84/6.50  --inst_lit_activity_flag                true
% 47.84/6.50  --inst_restr_to_given                   false
% 47.84/6.50  --inst_activity_threshold               500
% 47.84/6.50  --inst_out_proof                        true
% 47.84/6.50  
% 47.84/6.50  ------ Resolution Options
% 47.84/6.50  
% 47.84/6.50  --resolution_flag                       true
% 47.84/6.50  --res_lit_sel                           adaptive
% 47.84/6.50  --res_lit_sel_side                      none
% 47.84/6.50  --res_ordering                          kbo
% 47.84/6.50  --res_to_prop_solver                    active
% 47.84/6.50  --res_prop_simpl_new                    false
% 47.84/6.50  --res_prop_simpl_given                  true
% 47.84/6.50  --res_passive_queue_type                priority_queues
% 47.84/6.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 47.84/6.50  --res_passive_queues_freq               [15;5]
% 47.84/6.50  --res_forward_subs                      full
% 47.84/6.50  --res_backward_subs                     full
% 47.84/6.50  --res_forward_subs_resolution           true
% 47.84/6.50  --res_backward_subs_resolution          true
% 47.84/6.50  --res_orphan_elimination                true
% 47.84/6.50  --res_time_limit                        2.
% 47.84/6.50  --res_out_proof                         true
% 47.84/6.50  
% 47.84/6.50  ------ Superposition Options
% 47.84/6.50  
% 47.84/6.50  --superposition_flag                    true
% 47.84/6.50  --sup_passive_queue_type                priority_queues
% 47.84/6.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 47.84/6.50  --sup_passive_queues_freq               [8;1;4]
% 47.84/6.50  --demod_completeness_check              fast
% 47.84/6.50  --demod_use_ground                      true
% 47.84/6.50  --sup_to_prop_solver                    passive
% 47.84/6.50  --sup_prop_simpl_new                    true
% 47.84/6.50  --sup_prop_simpl_given                  true
% 47.84/6.50  --sup_fun_splitting                     false
% 47.84/6.50  --sup_smt_interval                      50000
% 47.84/6.50  
% 47.84/6.50  ------ Superposition Simplification Setup
% 47.84/6.50  
% 47.84/6.50  --sup_indices_passive                   []
% 47.84/6.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 47.84/6.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 47.84/6.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 47.84/6.50  --sup_full_triv                         [TrivRules;PropSubs]
% 47.84/6.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 47.84/6.50  --sup_full_bw                           [BwDemod]
% 47.84/6.50  --sup_immed_triv                        [TrivRules]
% 47.84/6.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 47.84/6.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 47.84/6.50  --sup_immed_bw_main                     []
% 47.84/6.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 47.84/6.50  --sup_input_triv                        [Unflattening;TrivRules]
% 47.84/6.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 47.84/6.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 47.84/6.50  
% 47.84/6.50  ------ Combination Options
% 47.84/6.50  
% 47.84/6.50  --comb_res_mult                         3
% 47.84/6.50  --comb_sup_mult                         2
% 47.84/6.50  --comb_inst_mult                        10
% 47.84/6.50  
% 47.84/6.50  ------ Debug Options
% 47.84/6.50  
% 47.84/6.50  --dbg_backtrace                         false
% 47.84/6.50  --dbg_dump_prop_clauses                 false
% 47.84/6.50  --dbg_dump_prop_clauses_file            -
% 47.84/6.50  --dbg_out_stat                          false
% 47.84/6.50  ------ Parsing...
% 47.84/6.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 47.84/6.50  
% 47.84/6.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 47.84/6.50  
% 47.84/6.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 47.84/6.50  
% 47.84/6.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 47.84/6.50  ------ Proving...
% 47.84/6.50  ------ Problem Properties 
% 47.84/6.50  
% 47.84/6.50  
% 47.84/6.50  clauses                                 18
% 47.84/6.50  conjectures                             3
% 47.84/6.50  EPR                                     0
% 47.84/6.50  Horn                                    16
% 47.84/6.50  unary                                   7
% 47.84/6.50  binary                                  4
% 47.84/6.50  lits                                    38
% 47.84/6.50  lits eq                                 6
% 47.84/6.50  fd_pure                                 0
% 47.84/6.50  fd_pseudo                               0
% 47.84/6.50  fd_cond                                 0
% 47.84/6.50  fd_pseudo_cond                          3
% 47.84/6.50  AC symbols                              0
% 47.84/6.50  
% 47.84/6.50  ------ Schedule dynamic 5 is on 
% 47.84/6.50  
% 47.84/6.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 47.84/6.50  
% 47.84/6.50  
% 47.84/6.50  ------ 
% 47.84/6.50  Current options:
% 47.84/6.50  ------ 
% 47.84/6.50  
% 47.84/6.50  ------ Input Options
% 47.84/6.50  
% 47.84/6.50  --out_options                           all
% 47.84/6.50  --tptp_safe_out                         true
% 47.84/6.50  --problem_path                          ""
% 47.84/6.50  --include_path                          ""
% 47.84/6.50  --clausifier                            res/vclausify_rel
% 47.84/6.50  --clausifier_options                    --mode clausify
% 47.84/6.50  --stdin                                 false
% 47.84/6.50  --stats_out                             all
% 47.84/6.50  
% 47.84/6.50  ------ General Options
% 47.84/6.50  
% 47.84/6.50  --fof                                   false
% 47.84/6.50  --time_out_real                         305.
% 47.84/6.50  --time_out_virtual                      -1.
% 47.84/6.50  --symbol_type_check                     false
% 47.84/6.50  --clausify_out                          false
% 47.84/6.50  --sig_cnt_out                           false
% 47.84/6.50  --trig_cnt_out                          false
% 47.84/6.50  --trig_cnt_out_tolerance                1.
% 47.84/6.50  --trig_cnt_out_sk_spl                   false
% 47.84/6.50  --abstr_cl_out                          false
% 47.84/6.50  
% 47.84/6.50  ------ Global Options
% 47.84/6.50  
% 47.84/6.50  --schedule                              default
% 47.84/6.50  --add_important_lit                     false
% 47.84/6.50  --prop_solver_per_cl                    1000
% 47.84/6.50  --min_unsat_core                        false
% 47.84/6.50  --soft_assumptions                      false
% 47.84/6.50  --soft_lemma_size                       3
% 47.84/6.50  --prop_impl_unit_size                   0
% 47.84/6.50  --prop_impl_unit                        []
% 47.84/6.50  --share_sel_clauses                     true
% 47.84/6.50  --reset_solvers                         false
% 47.84/6.50  --bc_imp_inh                            [conj_cone]
% 47.84/6.50  --conj_cone_tolerance                   3.
% 47.84/6.50  --extra_neg_conj                        none
% 47.84/6.50  --large_theory_mode                     true
% 47.84/6.50  --prolific_symb_bound                   200
% 47.84/6.50  --lt_threshold                          2000
% 47.84/6.50  --clause_weak_htbl                      true
% 47.84/6.50  --gc_record_bc_elim                     false
% 47.84/6.50  
% 47.84/6.50  ------ Preprocessing Options
% 47.84/6.50  
% 47.84/6.50  --preprocessing_flag                    true
% 47.84/6.50  --time_out_prep_mult                    0.1
% 47.84/6.50  --splitting_mode                        input
% 47.84/6.50  --splitting_grd                         true
% 47.84/6.50  --splitting_cvd                         false
% 47.84/6.50  --splitting_cvd_svl                     false
% 47.84/6.50  --splitting_nvd                         32
% 47.84/6.50  --sub_typing                            true
% 47.84/6.50  --prep_gs_sim                           true
% 47.84/6.50  --prep_unflatten                        true
% 47.84/6.50  --prep_res_sim                          true
% 47.84/6.50  --prep_upred                            true
% 47.84/6.50  --prep_sem_filter                       exhaustive
% 47.84/6.50  --prep_sem_filter_out                   false
% 47.84/6.50  --pred_elim                             true
% 47.84/6.50  --res_sim_input                         true
% 47.84/6.50  --eq_ax_congr_red                       true
% 47.84/6.50  --pure_diseq_elim                       true
% 47.84/6.50  --brand_transform                       false
% 47.84/6.50  --non_eq_to_eq                          false
% 47.84/6.50  --prep_def_merge                        true
% 47.84/6.50  --prep_def_merge_prop_impl              false
% 47.84/6.50  --prep_def_merge_mbd                    true
% 47.84/6.50  --prep_def_merge_tr_red                 false
% 47.84/6.50  --prep_def_merge_tr_cl                  false
% 47.84/6.50  --smt_preprocessing                     true
% 47.84/6.50  --smt_ac_axioms                         fast
% 47.84/6.50  --preprocessed_out                      false
% 47.84/6.50  --preprocessed_stats                    false
% 47.84/6.50  
% 47.84/6.50  ------ Abstraction refinement Options
% 47.84/6.50  
% 47.84/6.50  --abstr_ref                             []
% 47.84/6.50  --abstr_ref_prep                        false
% 47.84/6.50  --abstr_ref_until_sat                   false
% 47.84/6.50  --abstr_ref_sig_restrict                funpre
% 47.84/6.50  --abstr_ref_af_restrict_to_split_sk     false
% 47.84/6.50  --abstr_ref_under                       []
% 47.84/6.50  
% 47.84/6.50  ------ SAT Options
% 47.84/6.50  
% 47.84/6.50  --sat_mode                              false
% 47.84/6.50  --sat_fm_restart_options                ""
% 47.84/6.50  --sat_gr_def                            false
% 47.84/6.50  --sat_epr_types                         true
% 47.84/6.50  --sat_non_cyclic_types                  false
% 47.84/6.50  --sat_finite_models                     false
% 47.84/6.50  --sat_fm_lemmas                         false
% 47.84/6.50  --sat_fm_prep                           false
% 47.84/6.50  --sat_fm_uc_incr                        true
% 47.84/6.50  --sat_out_model                         small
% 47.84/6.50  --sat_out_clauses                       false
% 47.84/6.50  
% 47.84/6.50  ------ QBF Options
% 47.84/6.50  
% 47.84/6.50  --qbf_mode                              false
% 47.84/6.50  --qbf_elim_univ                         false
% 47.84/6.50  --qbf_dom_inst                          none
% 47.84/6.50  --qbf_dom_pre_inst                      false
% 47.84/6.50  --qbf_sk_in                             false
% 47.84/6.50  --qbf_pred_elim                         true
% 47.84/6.50  --qbf_split                             512
% 47.84/6.50  
% 47.84/6.50  ------ BMC1 Options
% 47.84/6.50  
% 47.84/6.50  --bmc1_incremental                      false
% 47.84/6.50  --bmc1_axioms                           reachable_all
% 47.84/6.50  --bmc1_min_bound                        0
% 47.84/6.50  --bmc1_max_bound                        -1
% 47.84/6.50  --bmc1_max_bound_default                -1
% 47.84/6.50  --bmc1_symbol_reachability              true
% 47.84/6.50  --bmc1_property_lemmas                  false
% 47.84/6.50  --bmc1_k_induction                      false
% 47.84/6.50  --bmc1_non_equiv_states                 false
% 47.84/6.50  --bmc1_deadlock                         false
% 47.84/6.50  --bmc1_ucm                              false
% 47.84/6.50  --bmc1_add_unsat_core                   none
% 47.84/6.50  --bmc1_unsat_core_children              false
% 47.84/6.50  --bmc1_unsat_core_extrapolate_axioms    false
% 47.84/6.50  --bmc1_out_stat                         full
% 47.84/6.50  --bmc1_ground_init                      false
% 47.84/6.50  --bmc1_pre_inst_next_state              false
% 47.84/6.50  --bmc1_pre_inst_state                   false
% 47.84/6.50  --bmc1_pre_inst_reach_state             false
% 47.84/6.50  --bmc1_out_unsat_core                   false
% 47.84/6.50  --bmc1_aig_witness_out                  false
% 47.84/6.50  --bmc1_verbose                          false
% 47.84/6.50  --bmc1_dump_clauses_tptp                false
% 47.84/6.50  --bmc1_dump_unsat_core_tptp             false
% 47.84/6.50  --bmc1_dump_file                        -
% 47.84/6.50  --bmc1_ucm_expand_uc_limit              128
% 47.84/6.50  --bmc1_ucm_n_expand_iterations          6
% 47.84/6.50  --bmc1_ucm_extend_mode                  1
% 47.84/6.50  --bmc1_ucm_init_mode                    2
% 47.84/6.50  --bmc1_ucm_cone_mode                    none
% 47.84/6.50  --bmc1_ucm_reduced_relation_type        0
% 47.84/6.50  --bmc1_ucm_relax_model                  4
% 47.84/6.50  --bmc1_ucm_full_tr_after_sat            true
% 47.84/6.50  --bmc1_ucm_expand_neg_assumptions       false
% 47.84/6.50  --bmc1_ucm_layered_model                none
% 47.84/6.50  --bmc1_ucm_max_lemma_size               10
% 47.84/6.50  
% 47.84/6.50  ------ AIG Options
% 47.84/6.50  
% 47.84/6.50  --aig_mode                              false
% 47.84/6.50  
% 47.84/6.50  ------ Instantiation Options
% 47.84/6.50  
% 47.84/6.50  --instantiation_flag                    true
% 47.84/6.50  --inst_sos_flag                         false
% 47.84/6.50  --inst_sos_phase                        true
% 47.84/6.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 47.84/6.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 47.84/6.50  --inst_lit_sel_side                     none
% 47.84/6.50  --inst_solver_per_active                1400
% 47.84/6.50  --inst_solver_calls_frac                1.
% 47.84/6.50  --inst_passive_queue_type               priority_queues
% 47.84/6.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 47.84/6.50  --inst_passive_queues_freq              [25;2]
% 47.84/6.50  --inst_dismatching                      true
% 47.84/6.50  --inst_eager_unprocessed_to_passive     true
% 47.84/6.50  --inst_prop_sim_given                   true
% 47.84/6.50  --inst_prop_sim_new                     false
% 47.84/6.50  --inst_subs_new                         false
% 47.84/6.50  --inst_eq_res_simp                      false
% 47.84/6.50  --inst_subs_given                       false
% 47.84/6.50  --inst_orphan_elimination               true
% 47.84/6.50  --inst_learning_loop_flag               true
% 47.84/6.50  --inst_learning_start                   3000
% 47.84/6.50  --inst_learning_factor                  2
% 47.84/6.50  --inst_start_prop_sim_after_learn       3
% 47.84/6.50  --inst_sel_renew                        solver
% 47.84/6.50  --inst_lit_activity_flag                true
% 47.84/6.50  --inst_restr_to_given                   false
% 47.84/6.50  --inst_activity_threshold               500
% 47.84/6.50  --inst_out_proof                        true
% 47.84/6.50  
% 47.84/6.50  ------ Resolution Options
% 47.84/6.50  
% 47.84/6.50  --resolution_flag                       false
% 47.84/6.50  --res_lit_sel                           adaptive
% 47.84/6.50  --res_lit_sel_side                      none
% 47.84/6.50  --res_ordering                          kbo
% 47.84/6.50  --res_to_prop_solver                    active
% 47.84/6.50  --res_prop_simpl_new                    false
% 47.84/6.50  --res_prop_simpl_given                  true
% 47.84/6.50  --res_passive_queue_type                priority_queues
% 47.84/6.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 47.84/6.50  --res_passive_queues_freq               [15;5]
% 47.84/6.50  --res_forward_subs                      full
% 47.84/6.50  --res_backward_subs                     full
% 47.84/6.50  --res_forward_subs_resolution           true
% 47.84/6.50  --res_backward_subs_resolution          true
% 47.84/6.50  --res_orphan_elimination                true
% 47.84/6.50  --res_time_limit                        2.
% 47.84/6.50  --res_out_proof                         true
% 47.84/6.50  
% 47.84/6.50  ------ Superposition Options
% 47.84/6.50  
% 47.84/6.50  --superposition_flag                    true
% 47.84/6.50  --sup_passive_queue_type                priority_queues
% 47.84/6.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 47.84/6.50  --sup_passive_queues_freq               [8;1;4]
% 47.84/6.50  --demod_completeness_check              fast
% 47.84/6.50  --demod_use_ground                      true
% 47.84/6.50  --sup_to_prop_solver                    passive
% 47.84/6.50  --sup_prop_simpl_new                    true
% 47.84/6.50  --sup_prop_simpl_given                  true
% 47.84/6.50  --sup_fun_splitting                     false
% 47.84/6.50  --sup_smt_interval                      50000
% 47.84/6.50  
% 47.84/6.50  ------ Superposition Simplification Setup
% 47.84/6.50  
% 47.84/6.50  --sup_indices_passive                   []
% 47.84/6.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 47.84/6.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 47.84/6.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 47.84/6.50  --sup_full_triv                         [TrivRules;PropSubs]
% 47.84/6.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 47.84/6.50  --sup_full_bw                           [BwDemod]
% 47.84/6.50  --sup_immed_triv                        [TrivRules]
% 47.84/6.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 47.84/6.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 47.84/6.50  --sup_immed_bw_main                     []
% 47.84/6.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 47.84/6.50  --sup_input_triv                        [Unflattening;TrivRules]
% 47.84/6.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 47.84/6.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 47.84/6.50  
% 47.84/6.50  ------ Combination Options
% 47.84/6.50  
% 47.84/6.50  --comb_res_mult                         3
% 47.84/6.50  --comb_sup_mult                         2
% 47.84/6.50  --comb_inst_mult                        10
% 47.84/6.50  
% 47.84/6.50  ------ Debug Options
% 47.84/6.50  
% 47.84/6.50  --dbg_backtrace                         false
% 47.84/6.50  --dbg_dump_prop_clauses                 false
% 47.84/6.50  --dbg_dump_prop_clauses_file            -
% 47.84/6.50  --dbg_out_stat                          false
% 47.84/6.50  
% 47.84/6.50  
% 47.84/6.50  
% 47.84/6.50  
% 47.84/6.50  ------ Proving...
% 47.84/6.50  
% 47.84/6.50  
% 47.84/6.50  % SZS status Theorem for theBenchmark.p
% 47.84/6.50  
% 47.84/6.50  % SZS output start CNFRefutation for theBenchmark.p
% 47.84/6.50  
% 47.84/6.50  fof(f2,axiom,(
% 47.84/6.50    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 47.84/6.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.84/6.50  
% 47.84/6.50  fof(f23,plain,(
% 47.84/6.50    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 47.84/6.50    inference(nnf_transformation,[],[f2])).
% 47.84/6.50  
% 47.84/6.50  fof(f24,plain,(
% 47.84/6.50    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 47.84/6.50    inference(flattening,[],[f23])).
% 47.84/6.50  
% 47.84/6.50  fof(f25,plain,(
% 47.84/6.50    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 47.84/6.50    inference(rectify,[],[f24])).
% 47.84/6.50  
% 47.84/6.50  fof(f26,plain,(
% 47.84/6.50    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 47.84/6.50    introduced(choice_axiom,[])).
% 47.84/6.50  
% 47.84/6.50  fof(f27,plain,(
% 47.84/6.50    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 47.84/6.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).
% 47.84/6.50  
% 47.84/6.50  fof(f37,plain,(
% 47.84/6.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 47.84/6.50    inference(cnf_transformation,[],[f27])).
% 47.84/6.50  
% 47.84/6.50  fof(f56,plain,(
% 47.84/6.50    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 47.84/6.50    inference(equality_resolution,[],[f37])).
% 47.84/6.50  
% 47.84/6.50  fof(f1,axiom,(
% 47.84/6.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 47.84/6.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.84/6.50  
% 47.84/6.50  fof(f10,plain,(
% 47.84/6.50    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 47.84/6.50    inference(unused_predicate_definition_removal,[],[f1])).
% 47.84/6.50  
% 47.84/6.50  fof(f11,plain,(
% 47.84/6.50    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1))),
% 47.84/6.50    inference(ennf_transformation,[],[f10])).
% 47.84/6.50  
% 47.84/6.50  fof(f34,plain,(
% 47.84/6.50    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 47.84/6.50    inference(cnf_transformation,[],[f11])).
% 47.84/6.50  
% 47.84/6.50  fof(f6,axiom,(
% 47.84/6.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))))))),
% 47.84/6.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.84/6.50  
% 47.84/6.50  fof(f18,plain,(
% 47.84/6.50    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 47.84/6.50    inference(ennf_transformation,[],[f6])).
% 47.84/6.50  
% 47.84/6.50  fof(f44,plain,(
% 47.84/6.50    ( ! [X2,X0,X1] : (r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 47.84/6.50    inference(cnf_transformation,[],[f18])).
% 47.84/6.50  
% 47.84/6.50  fof(f8,conjecture,(
% 47.84/6.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1)) => m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1))))))),
% 47.84/6.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.84/6.50  
% 47.84/6.50  fof(f9,negated_conjecture,(
% 47.84/6.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1)) => m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1))))))),
% 47.84/6.50    inference(negated_conjecture,[],[f8])).
% 47.84/6.50  
% 47.84/6.50  fof(f21,plain,(
% 47.84/6.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & (m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 47.84/6.50    inference(ennf_transformation,[],[f9])).
% 47.84/6.50  
% 47.84/6.50  fof(f22,plain,(
% 47.84/6.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 47.84/6.50    inference(flattening,[],[f21])).
% 47.84/6.50  
% 47.84/6.50  fof(f32,plain,(
% 47.84/6.50    ( ! [X2,X0,X1] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,sK4),X0,X1) & m1_connsp_2(sK4,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 47.84/6.50    introduced(choice_axiom,[])).
% 47.84/6.50  
% 47.84/6.50  fof(f31,plain,(
% 47.84/6.50    ( ! [X0,X1] : (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),sK3,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(sK3,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 47.84/6.50    introduced(choice_axiom,[])).
% 47.84/6.50  
% 47.84/6.50  fof(f30,plain,(
% 47.84/6.50    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,sK2) & m1_connsp_2(X3,X0,sK2) & m1_connsp_2(X2,X0,sK2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK2,u1_struct_0(X0)))) )),
% 47.84/6.50    introduced(choice_axiom,[])).
% 47.84/6.50  
% 47.84/6.50  fof(f29,plain,(
% 47.84/6.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(sK1),X2,X3),sK1,X1) & m1_connsp_2(X3,sK1,X1) & m1_connsp_2(X2,sK1,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X1,u1_struct_0(sK1))) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 47.84/6.50    introduced(choice_axiom,[])).
% 47.84/6.50  
% 47.84/6.50  fof(f33,plain,(
% 47.84/6.50    (((~m1_connsp_2(k4_subset_1(u1_struct_0(sK1),sK3,sK4),sK1,sK2) & m1_connsp_2(sK4,sK1,sK2) & m1_connsp_2(sK3,sK1,sK2) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK2,u1_struct_0(sK1))) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 47.84/6.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f22,f32,f31,f30,f29])).
% 47.84/6.50  
% 47.84/6.50  fof(f49,plain,(
% 47.84/6.50    l1_pre_topc(sK1)),
% 47.84/6.50    inference(cnf_transformation,[],[f33])).
% 47.84/6.50  
% 47.84/6.50  fof(f52,plain,(
% 47.84/6.50    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))),
% 47.84/6.50    inference(cnf_transformation,[],[f33])).
% 47.84/6.50  
% 47.84/6.50  fof(f51,plain,(
% 47.84/6.50    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 47.84/6.50    inference(cnf_transformation,[],[f33])).
% 47.84/6.50  
% 47.84/6.50  fof(f5,axiom,(
% 47.84/6.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 47.84/6.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.84/6.50  
% 47.84/6.50  fof(f16,plain,(
% 47.84/6.50    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 47.84/6.50    inference(ennf_transformation,[],[f5])).
% 47.84/6.50  
% 47.84/6.50  fof(f17,plain,(
% 47.84/6.50    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 47.84/6.50    inference(flattening,[],[f16])).
% 47.84/6.50  
% 47.84/6.50  fof(f43,plain,(
% 47.84/6.50    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 47.84/6.50    inference(cnf_transformation,[],[f17])).
% 47.84/6.50  
% 47.84/6.50  fof(f4,axiom,(
% 47.84/6.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 47.84/6.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.84/6.50  
% 47.84/6.50  fof(f14,plain,(
% 47.84/6.50    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 47.84/6.50    inference(ennf_transformation,[],[f4])).
% 47.84/6.50  
% 47.84/6.50  fof(f15,plain,(
% 47.84/6.50    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 47.84/6.50    inference(flattening,[],[f14])).
% 47.84/6.50  
% 47.84/6.50  fof(f42,plain,(
% 47.84/6.50    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 47.84/6.50    inference(cnf_transformation,[],[f15])).
% 47.84/6.50  
% 47.84/6.50  fof(f3,axiom,(
% 47.84/6.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 47.84/6.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.84/6.50  
% 47.84/6.50  fof(f12,plain,(
% 47.84/6.50    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 47.84/6.50    inference(ennf_transformation,[],[f3])).
% 47.84/6.50  
% 47.84/6.50  fof(f13,plain,(
% 47.84/6.50    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 47.84/6.50    inference(flattening,[],[f12])).
% 47.84/6.50  
% 47.84/6.50  fof(f41,plain,(
% 47.84/6.50    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 47.84/6.50    inference(cnf_transformation,[],[f13])).
% 47.84/6.50  
% 47.84/6.50  fof(f54,plain,(
% 47.84/6.50    m1_connsp_2(sK4,sK1,sK2)),
% 47.84/6.50    inference(cnf_transformation,[],[f33])).
% 47.84/6.50  
% 47.84/6.50  fof(f7,axiom,(
% 47.84/6.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 47.84/6.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.84/6.50  
% 47.84/6.50  fof(f19,plain,(
% 47.84/6.50    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 47.84/6.50    inference(ennf_transformation,[],[f7])).
% 47.84/6.50  
% 47.84/6.50  fof(f20,plain,(
% 47.84/6.50    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 47.84/6.50    inference(flattening,[],[f19])).
% 47.84/6.50  
% 47.84/6.50  fof(f28,plain,(
% 47.84/6.50    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 47.84/6.50    inference(nnf_transformation,[],[f20])).
% 47.84/6.50  
% 47.84/6.50  fof(f45,plain,(
% 47.84/6.50    ( ! [X2,X0,X1] : (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 47.84/6.50    inference(cnf_transformation,[],[f28])).
% 47.84/6.50  
% 47.84/6.50  fof(f48,plain,(
% 47.84/6.50    v2_pre_topc(sK1)),
% 47.84/6.50    inference(cnf_transformation,[],[f33])).
% 47.84/6.50  
% 47.84/6.50  fof(f47,plain,(
% 47.84/6.50    ~v2_struct_0(sK1)),
% 47.84/6.50    inference(cnf_transformation,[],[f33])).
% 47.84/6.50  
% 47.84/6.50  fof(f55,plain,(
% 47.84/6.50    ~m1_connsp_2(k4_subset_1(u1_struct_0(sK1),sK3,sK4),sK1,sK2)),
% 47.84/6.50    inference(cnf_transformation,[],[f33])).
% 47.84/6.50  
% 47.84/6.50  fof(f46,plain,(
% 47.84/6.50    ( ! [X2,X0,X1] : (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 47.84/6.50    inference(cnf_transformation,[],[f28])).
% 47.84/6.50  
% 47.84/6.50  fof(f50,plain,(
% 47.84/6.50    m1_subset_1(sK2,u1_struct_0(sK1))),
% 47.84/6.50    inference(cnf_transformation,[],[f33])).
% 47.84/6.50  
% 47.84/6.50  cnf(c_4,plain,
% 47.84/6.50      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,k2_xboole_0(X2,X1)) ),
% 47.84/6.50      inference(cnf_transformation,[],[f56]) ).
% 47.84/6.50  
% 47.84/6.50  cnf(c_169091,plain,
% 47.84/6.50      ( ~ r2_hidden(sK2,k1_tops_1(sK1,sK4))
% 47.84/6.50      | r2_hidden(sK2,k2_xboole_0(X0,k1_tops_1(sK1,sK4))) ),
% 47.84/6.50      inference(instantiation,[status(thm)],[c_4]) ).
% 47.84/6.50  
% 47.84/6.50  cnf(c_185021,plain,
% 47.84/6.50      ( ~ r2_hidden(sK2,k1_tops_1(sK1,sK4))
% 47.84/6.50      | r2_hidden(sK2,k2_xboole_0(k1_tops_1(sK1,sK3),k1_tops_1(sK1,sK4))) ),
% 47.84/6.50      inference(instantiation,[status(thm)],[c_169091]) ).
% 47.84/6.50  
% 47.84/6.50  cnf(c_0,plain,
% 47.84/6.50      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 47.84/6.50      inference(cnf_transformation,[],[f34]) ).
% 47.84/6.50  
% 47.84/6.50  cnf(c_10,plain,
% 47.84/6.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 47.84/6.50      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 47.84/6.50      | r1_tarski(k4_subset_1(u1_struct_0(X1),k1_tops_1(X1,X0),k1_tops_1(X1,X2)),k1_tops_1(X1,k4_subset_1(u1_struct_0(X1),X0,X2)))
% 47.84/6.50      | ~ l1_pre_topc(X1) ),
% 47.84/6.50      inference(cnf_transformation,[],[f44]) ).
% 47.84/6.50  
% 47.84/6.50  cnf(c_19,negated_conjecture,
% 47.84/6.50      ( l1_pre_topc(sK1) ),
% 47.84/6.50      inference(cnf_transformation,[],[f49]) ).
% 47.84/6.50  
% 47.84/6.50  cnf(c_318,plain,
% 47.84/6.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 47.84/6.50      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 47.84/6.50      | r1_tarski(k4_subset_1(u1_struct_0(X1),k1_tops_1(X1,X0),k1_tops_1(X1,X2)),k1_tops_1(X1,k4_subset_1(u1_struct_0(X1),X0,X2)))
% 47.84/6.50      | sK1 != X1 ),
% 47.84/6.50      inference(resolution_lifted,[status(thm)],[c_10,c_19]) ).
% 47.84/6.50  
% 47.84/6.50  cnf(c_319,plain,
% 47.84/6.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 47.84/6.50      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 47.84/6.50      | r1_tarski(k4_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,X0),k1_tops_1(sK1,X1)),k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),X0,X1))) ),
% 47.84/6.50      inference(unflattening,[status(thm)],[c_318]) ).
% 47.84/6.50  
% 47.84/6.50  cnf(c_352,plain,
% 47.84/6.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 47.84/6.50      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 47.84/6.50      | ~ r2_hidden(X2,X3)
% 47.84/6.50      | r2_hidden(X2,X4)
% 47.84/6.50      | k4_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,X0),k1_tops_1(sK1,X1)) != X3
% 47.84/6.50      | k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),X0,X1)) != X4 ),
% 47.84/6.50      inference(resolution_lifted,[status(thm)],[c_0,c_319]) ).
% 47.84/6.50  
% 47.84/6.50  cnf(c_353,plain,
% 47.84/6.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 47.84/6.50      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 47.84/6.50      | ~ r2_hidden(X2,k4_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,X0),k1_tops_1(sK1,X1)))
% 47.84/6.50      | r2_hidden(X2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),X0,X1))) ),
% 47.84/6.50      inference(unflattening,[status(thm)],[c_352]) ).
% 47.84/6.50  
% 47.84/6.50  cnf(c_169053,plain,
% 47.84/6.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 47.84/6.50      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 47.84/6.50      | ~ r2_hidden(X1,k4_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,sK3),k1_tops_1(sK1,X0)))
% 47.84/6.50      | r2_hidden(X1,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,X0))) ),
% 47.84/6.50      inference(instantiation,[status(thm)],[c_353]) ).
% 47.84/6.50  
% 47.84/6.50  cnf(c_169837,plain,
% 47.84/6.50      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 47.84/6.50      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 47.84/6.50      | ~ r2_hidden(X0,k4_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,sK3),k1_tops_1(sK1,sK4)))
% 47.84/6.50      | r2_hidden(X0,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) ),
% 47.84/6.50      inference(instantiation,[status(thm)],[c_169053]) ).
% 47.84/6.50  
% 47.84/6.50  cnf(c_177878,plain,
% 47.84/6.50      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 47.84/6.50      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 47.84/6.50      | ~ r2_hidden(sK2,k4_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,sK3),k1_tops_1(sK1,sK4)))
% 47.84/6.50      | r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) ),
% 47.84/6.50      inference(instantiation,[status(thm)],[c_169837]) ).
% 47.84/6.50  
% 47.84/6.50  cnf(c_559,plain,
% 47.84/6.50      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 47.84/6.50      theory(equality) ).
% 47.84/6.50  
% 47.84/6.50  cnf(c_169859,plain,
% 47.84/6.50      ( r2_hidden(X0,X1)
% 47.84/6.50      | ~ r2_hidden(sK2,k2_xboole_0(X2,k1_tops_1(sK1,sK4)))
% 47.84/6.50      | X1 != k2_xboole_0(X2,k1_tops_1(sK1,sK4))
% 47.84/6.50      | X0 != sK2 ),
% 47.84/6.50      inference(instantiation,[status(thm)],[c_559]) ).
% 47.84/6.50  
% 47.84/6.50  cnf(c_172241,plain,
% 47.84/6.50      ( r2_hidden(sK2,X0)
% 47.84/6.50      | ~ r2_hidden(sK2,k2_xboole_0(X1,k1_tops_1(sK1,sK4)))
% 47.84/6.50      | X0 != k2_xboole_0(X1,k1_tops_1(sK1,sK4))
% 47.84/6.50      | sK2 != sK2 ),
% 47.84/6.50      inference(instantiation,[status(thm)],[c_169859]) ).
% 47.84/6.50  
% 47.84/6.50  cnf(c_173670,plain,
% 47.84/6.50      ( r2_hidden(sK2,k4_subset_1(u1_struct_0(sK1),X0,k1_tops_1(sK1,sK4)))
% 47.84/6.50      | ~ r2_hidden(sK2,k2_xboole_0(X0,k1_tops_1(sK1,sK4)))
% 47.84/6.50      | k4_subset_1(u1_struct_0(sK1),X0,k1_tops_1(sK1,sK4)) != k2_xboole_0(X0,k1_tops_1(sK1,sK4))
% 47.84/6.50      | sK2 != sK2 ),
% 47.84/6.50      inference(instantiation,[status(thm)],[c_172241]) ).
% 47.84/6.50  
% 47.84/6.50  cnf(c_177877,plain,
% 47.84/6.50      ( r2_hidden(sK2,k4_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,sK3),k1_tops_1(sK1,sK4)))
% 47.84/6.50      | ~ r2_hidden(sK2,k2_xboole_0(k1_tops_1(sK1,sK3),k1_tops_1(sK1,sK4)))
% 47.84/6.50      | k4_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,sK3),k1_tops_1(sK1,sK4)) != k2_xboole_0(k1_tops_1(sK1,sK3),k1_tops_1(sK1,sK4))
% 47.84/6.50      | sK2 != sK2 ),
% 47.84/6.50      inference(instantiation,[status(thm)],[c_173670]) ).
% 47.84/6.50  
% 47.84/6.50  cnf(c_16,negated_conjecture,
% 47.84/6.50      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 47.84/6.50      inference(cnf_transformation,[],[f52]) ).
% 47.84/6.50  
% 47.84/6.50  cnf(c_838,plain,
% 47.84/6.50      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 47.84/6.50      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 47.84/6.50  
% 47.84/6.50  cnf(c_17,negated_conjecture,
% 47.84/6.50      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 47.84/6.50      inference(cnf_transformation,[],[f51]) ).
% 47.84/6.50  
% 47.84/6.50  cnf(c_837,plain,
% 47.84/6.50      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 47.84/6.50      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 47.84/6.50  
% 47.84/6.50  cnf(c_9,plain,
% 47.84/6.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 47.84/6.50      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 47.84/6.50      | ~ l1_pre_topc(X1) ),
% 47.84/6.50      inference(cnf_transformation,[],[f43]) ).
% 47.84/6.50  
% 47.84/6.50  cnf(c_333,plain,
% 47.84/6.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 47.84/6.50      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 47.84/6.50      | sK1 != X1 ),
% 47.84/6.50      inference(resolution_lifted,[status(thm)],[c_9,c_19]) ).
% 47.84/6.50  
% 47.84/6.50  cnf(c_334,plain,
% 47.84/6.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 47.84/6.50      | m1_subset_1(k1_tops_1(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 47.84/6.50      inference(unflattening,[status(thm)],[c_333]) ).
% 47.84/6.50  
% 47.84/6.50  cnf(c_835,plain,
% 47.84/6.50      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 47.84/6.50      | m1_subset_1(k1_tops_1(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 47.84/6.50      inference(predicate_to_equality,[status(thm)],[c_334]) ).
% 47.84/6.50  
% 47.84/6.50  cnf(c_8,plain,
% 47.84/6.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 47.84/6.50      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 47.84/6.50      | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
% 47.84/6.50      inference(cnf_transformation,[],[f42]) ).
% 47.84/6.50  
% 47.84/6.50  cnf(c_839,plain,
% 47.84/6.50      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
% 47.84/6.50      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 47.84/6.50      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 47.84/6.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 47.84/6.50  
% 47.84/6.50  cnf(c_1935,plain,
% 47.84/6.50      ( k4_subset_1(u1_struct_0(sK1),X0,k1_tops_1(sK1,X1)) = k2_xboole_0(X0,k1_tops_1(sK1,X1))
% 47.84/6.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 47.84/6.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 47.84/6.50      inference(superposition,[status(thm)],[c_835,c_839]) ).
% 47.84/6.50  
% 47.84/6.50  cnf(c_4947,plain,
% 47.84/6.50      ( k4_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,X0),k1_tops_1(sK1,X1)) = k2_xboole_0(k1_tops_1(sK1,X0),k1_tops_1(sK1,X1))
% 47.84/6.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 47.84/6.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 47.84/6.50      inference(superposition,[status(thm)],[c_835,c_1935]) ).
% 47.84/6.50  
% 47.84/6.50  cnf(c_37617,plain,
% 47.84/6.50      ( k4_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,sK3),k1_tops_1(sK1,X0)) = k2_xboole_0(k1_tops_1(sK1,sK3),k1_tops_1(sK1,X0))
% 47.84/6.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 47.84/6.50      inference(superposition,[status(thm)],[c_837,c_4947]) ).
% 47.84/6.50  
% 47.84/6.50  cnf(c_38392,plain,
% 47.84/6.50      ( k4_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,sK3),k1_tops_1(sK1,sK4)) = k2_xboole_0(k1_tops_1(sK1,sK3),k1_tops_1(sK1,sK4)) ),
% 47.84/6.50      inference(superposition,[status(thm)],[c_838,c_37617]) ).
% 47.84/6.50  
% 47.84/6.50  cnf(c_7,plain,
% 47.84/6.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 47.84/6.50      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 47.84/6.50      | m1_subset_1(k4_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 47.84/6.50      inference(cnf_transformation,[],[f41]) ).
% 47.84/6.50  
% 47.84/6.50  cnf(c_977,plain,
% 47.84/6.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 47.84/6.50      | m1_subset_1(k4_subset_1(u1_struct_0(sK1),X0,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
% 47.84/6.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 47.84/6.50      inference(instantiation,[status(thm)],[c_7]) ).
% 47.84/6.50  
% 47.84/6.50  cnf(c_1138,plain,
% 47.84/6.50      ( m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
% 47.84/6.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 47.84/6.50      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 47.84/6.50      inference(instantiation,[status(thm)],[c_977]) ).
% 47.84/6.50  
% 47.84/6.50  cnf(c_557,plain,( X0 = X0 ),theory(equality) ).
% 47.84/6.50  
% 47.84/6.50  cnf(c_1069,plain,
% 47.84/6.50      ( sK2 = sK2 ),
% 47.84/6.50      inference(instantiation,[status(thm)],[c_557]) ).
% 47.84/6.50  
% 47.84/6.50  cnf(c_14,negated_conjecture,
% 47.84/6.50      ( m1_connsp_2(sK4,sK1,sK2) ),
% 47.84/6.50      inference(cnf_transformation,[],[f54]) ).
% 47.84/6.50  
% 47.84/6.50  cnf(c_12,plain,
% 47.84/6.50      ( ~ m1_connsp_2(X0,X1,X2)
% 47.84/6.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 47.84/6.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 47.84/6.50      | r2_hidden(X2,k1_tops_1(X1,X0))
% 47.84/6.50      | v2_struct_0(X1)
% 47.84/6.50      | ~ v2_pre_topc(X1)
% 47.84/6.50      | ~ l1_pre_topc(X1) ),
% 47.84/6.50      inference(cnf_transformation,[],[f45]) ).
% 47.84/6.50  
% 47.84/6.50  cnf(c_20,negated_conjecture,
% 47.84/6.50      ( v2_pre_topc(sK1) ),
% 47.84/6.50      inference(cnf_transformation,[],[f48]) ).
% 47.84/6.50  
% 47.84/6.50  cnf(c_260,plain,
% 47.84/6.50      ( ~ m1_connsp_2(X0,X1,X2)
% 47.84/6.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 47.84/6.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 47.84/6.50      | r2_hidden(X2,k1_tops_1(X1,X0))
% 47.84/6.50      | v2_struct_0(X1)
% 47.84/6.50      | ~ l1_pre_topc(X1)
% 47.84/6.50      | sK1 != X1 ),
% 47.84/6.50      inference(resolution_lifted,[status(thm)],[c_12,c_20]) ).
% 47.84/6.50  
% 47.84/6.50  cnf(c_261,plain,
% 47.84/6.50      ( ~ m1_connsp_2(X0,sK1,X1)
% 47.84/6.50      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 47.84/6.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 47.84/6.50      | r2_hidden(X1,k1_tops_1(sK1,X0))
% 47.84/6.50      | v2_struct_0(sK1)
% 47.84/6.50      | ~ l1_pre_topc(sK1) ),
% 47.84/6.50      inference(unflattening,[status(thm)],[c_260]) ).
% 47.84/6.50  
% 47.84/6.50  cnf(c_21,negated_conjecture,
% 47.84/6.50      ( ~ v2_struct_0(sK1) ),
% 47.84/6.50      inference(cnf_transformation,[],[f47]) ).
% 47.84/6.50  
% 47.84/6.50  cnf(c_265,plain,
% 47.84/6.50      ( ~ m1_connsp_2(X0,sK1,X1)
% 47.84/6.50      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 47.84/6.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 47.84/6.50      | r2_hidden(X1,k1_tops_1(sK1,X0)) ),
% 47.84/6.50      inference(global_propositional_subsumption,
% 47.84/6.50                [status(thm)],
% 47.84/6.50                [c_261,c_21,c_19]) ).
% 47.84/6.50  
% 47.84/6.50  cnf(c_410,plain,
% 47.84/6.50      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 47.84/6.50      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 47.84/6.50      | r2_hidden(X0,k1_tops_1(sK1,X1))
% 47.84/6.50      | sK2 != X0
% 47.84/6.50      | sK4 != X1
% 47.84/6.50      | sK1 != sK1 ),
% 47.84/6.50      inference(resolution_lifted,[status(thm)],[c_14,c_265]) ).
% 47.84/6.50  
% 47.84/6.50  cnf(c_411,plain,
% 47.84/6.50      ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 47.84/6.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 47.84/6.50      | r2_hidden(sK2,k1_tops_1(sK1,sK4)) ),
% 47.84/6.50      inference(unflattening,[status(thm)],[c_410]) ).
% 47.84/6.50  
% 47.84/6.50  cnf(c_13,negated_conjecture,
% 47.84/6.50      ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK1),sK3,sK4),sK1,sK2) ),
% 47.84/6.50      inference(cnf_transformation,[],[f55]) ).
% 47.84/6.50  
% 47.84/6.50  cnf(c_11,plain,
% 47.84/6.50      ( m1_connsp_2(X0,X1,X2)
% 47.84/6.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 47.84/6.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 47.84/6.50      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 47.84/6.50      | v2_struct_0(X1)
% 47.84/6.50      | ~ v2_pre_topc(X1)
% 47.84/6.50      | ~ l1_pre_topc(X1) ),
% 47.84/6.50      inference(cnf_transformation,[],[f46]) ).
% 47.84/6.50  
% 47.84/6.50  cnf(c_284,plain,
% 47.84/6.50      ( m1_connsp_2(X0,X1,X2)
% 47.84/6.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 47.84/6.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 47.84/6.50      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 47.84/6.50      | v2_struct_0(X1)
% 47.84/6.50      | ~ l1_pre_topc(X1)
% 47.84/6.50      | sK1 != X1 ),
% 47.84/6.50      inference(resolution_lifted,[status(thm)],[c_11,c_20]) ).
% 47.84/6.50  
% 47.84/6.50  cnf(c_285,plain,
% 47.84/6.50      ( m1_connsp_2(X0,sK1,X1)
% 47.84/6.50      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 47.84/6.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 47.84/6.50      | ~ r2_hidden(X1,k1_tops_1(sK1,X0))
% 47.84/6.50      | v2_struct_0(sK1)
% 47.84/6.50      | ~ l1_pre_topc(sK1) ),
% 47.84/6.50      inference(unflattening,[status(thm)],[c_284]) ).
% 47.84/6.50  
% 47.84/6.50  cnf(c_289,plain,
% 47.84/6.50      ( m1_connsp_2(X0,sK1,X1)
% 47.84/6.50      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 47.84/6.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 47.84/6.50      | ~ r2_hidden(X1,k1_tops_1(sK1,X0)) ),
% 47.84/6.50      inference(global_propositional_subsumption,
% 47.84/6.50                [status(thm)],
% 47.84/6.50                [c_285,c_21,c_19]) ).
% 47.84/6.50  
% 47.84/6.50  cnf(c_396,plain,
% 47.84/6.50      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 47.84/6.50      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 47.84/6.50      | ~ r2_hidden(X0,k1_tops_1(sK1,X1))
% 47.84/6.50      | k4_subset_1(u1_struct_0(sK1),sK3,sK4) != X1
% 47.84/6.50      | sK2 != X0
% 47.84/6.50      | sK1 != sK1 ),
% 47.84/6.50      inference(resolution_lifted,[status(thm)],[c_13,c_289]) ).
% 47.84/6.50  
% 47.84/6.50  cnf(c_397,plain,
% 47.84/6.50      ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
% 47.84/6.50      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 47.84/6.50      | ~ r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) ),
% 47.84/6.50      inference(unflattening,[status(thm)],[c_396]) ).
% 47.84/6.50  
% 47.84/6.50  cnf(c_18,negated_conjecture,
% 47.84/6.50      ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 47.84/6.50      inference(cnf_transformation,[],[f50]) ).
% 47.84/6.50  
% 47.84/6.50  cnf(contradiction,plain,
% 47.84/6.50      ( $false ),
% 47.84/6.50      inference(minisat,
% 47.84/6.50                [status(thm)],
% 47.84/6.50                [c_185021,c_177878,c_177877,c_38392,c_1138,c_1069,c_411,
% 47.84/6.50                 c_397,c_16,c_17,c_18]) ).
% 47.84/6.50  
% 47.84/6.50  
% 47.84/6.50  % SZS output end CNFRefutation for theBenchmark.p
% 47.84/6.50  
% 47.84/6.50  ------                               Statistics
% 47.84/6.50  
% 47.84/6.50  ------ General
% 47.84/6.50  
% 47.84/6.50  abstr_ref_over_cycles:                  0
% 47.84/6.50  abstr_ref_under_cycles:                 0
% 47.84/6.50  gc_basic_clause_elim:                   0
% 47.84/6.50  forced_gc_time:                         0
% 47.84/6.50  parsing_time:                           0.009
% 47.84/6.50  unif_index_cands_time:                  0.
% 47.84/6.50  unif_index_add_time:                    0.
% 47.84/6.50  orderings_time:                         0.
% 47.84/6.50  out_proof_time:                         0.018
% 47.84/6.50  total_time:                             5.924
% 47.84/6.50  num_of_symbols:                         48
% 47.84/6.50  num_of_terms:                           304422
% 47.84/6.50  
% 47.84/6.50  ------ Preprocessing
% 47.84/6.50  
% 47.84/6.50  num_of_splits:                          0
% 47.84/6.50  num_of_split_atoms:                     0
% 47.84/6.50  num_of_reused_defs:                     0
% 47.84/6.50  num_eq_ax_congr_red:                    16
% 47.84/6.50  num_of_sem_filtered_clauses:            1
% 47.84/6.50  num_of_subtypes:                        0
% 47.84/6.50  monotx_restored_types:                  0
% 47.84/6.50  sat_num_of_epr_types:                   0
% 47.84/6.50  sat_num_of_non_cyclic_types:            0
% 47.84/6.50  sat_guarded_non_collapsed_types:        0
% 47.84/6.50  num_pure_diseq_elim:                    0
% 47.84/6.50  simp_replaced_by:                       0
% 47.84/6.50  res_preprocessed:                       93
% 47.84/6.50  prep_upred:                             0
% 47.84/6.50  prep_unflattend:                        14
% 47.84/6.50  smt_new_axioms:                         0
% 47.84/6.50  pred_elim_cands:                        2
% 47.84/6.50  pred_elim:                              5
% 47.84/6.50  pred_elim_cl:                           4
% 47.84/6.50  pred_elim_cycles:                       8
% 47.84/6.50  merged_defs:                            0
% 47.84/6.50  merged_defs_ncl:                        0
% 47.84/6.50  bin_hyper_res:                          0
% 47.84/6.50  prep_cycles:                            4
% 47.84/6.50  pred_elim_time:                         0.005
% 47.84/6.50  splitting_time:                         0.
% 47.84/6.50  sem_filter_time:                        0.
% 47.84/6.50  monotx_time:                            0.
% 47.84/6.50  subtype_inf_time:                       0.
% 47.84/6.50  
% 47.84/6.50  ------ Problem properties
% 47.84/6.50  
% 47.84/6.50  clauses:                                18
% 47.84/6.50  conjectures:                            3
% 47.84/6.50  epr:                                    0
% 47.84/6.50  horn:                                   16
% 47.84/6.50  ground:                                 8
% 47.84/6.50  unary:                                  7
% 47.84/6.50  binary:                                 4
% 47.84/6.50  lits:                                   38
% 47.84/6.50  lits_eq:                                6
% 47.84/6.50  fd_pure:                                0
% 47.84/6.50  fd_pseudo:                              0
% 47.84/6.50  fd_cond:                                0
% 47.84/6.50  fd_pseudo_cond:                         3
% 47.84/6.50  ac_symbols:                             0
% 47.84/6.50  
% 47.84/6.50  ------ Propositional Solver
% 47.84/6.50  
% 47.84/6.50  prop_solver_calls:                      61
% 47.84/6.50  prop_fast_solver_calls:                 1631
% 47.84/6.50  smt_solver_calls:                       0
% 47.84/6.50  smt_fast_solver_calls:                  0
% 47.84/6.50  prop_num_of_clauses:                    59610
% 47.84/6.50  prop_preprocess_simplified:             76333
% 47.84/6.50  prop_fo_subsumed:                       123
% 47.84/6.50  prop_solver_time:                       0.
% 47.84/6.50  smt_solver_time:                        0.
% 47.84/6.50  smt_fast_solver_time:                   0.
% 47.84/6.50  prop_fast_solver_time:                  0.
% 47.84/6.50  prop_unsat_core_time:                   0.006
% 47.84/6.50  
% 47.84/6.50  ------ QBF
% 47.84/6.50  
% 47.84/6.50  qbf_q_res:                              0
% 47.84/6.50  qbf_num_tautologies:                    0
% 47.84/6.50  qbf_prep_cycles:                        0
% 47.84/6.50  
% 47.84/6.50  ------ BMC1
% 47.84/6.50  
% 47.84/6.50  bmc1_current_bound:                     -1
% 47.84/6.50  bmc1_last_solved_bound:                 -1
% 47.84/6.50  bmc1_unsat_core_size:                   -1
% 47.84/6.50  bmc1_unsat_core_parents_size:           -1
% 47.84/6.50  bmc1_merge_next_fun:                    0
% 47.84/6.50  bmc1_unsat_core_clauses_time:           0.
% 47.84/6.50  
% 47.84/6.50  ------ Instantiation
% 47.84/6.50  
% 47.84/6.50  inst_num_of_clauses:                    1141
% 47.84/6.50  inst_num_in_passive:                    525
% 47.84/6.50  inst_num_in_active:                     2815
% 47.84/6.50  inst_num_in_unprocessed:                219
% 47.84/6.50  inst_num_of_loops:                      3418
% 47.84/6.50  inst_num_of_learning_restarts:          1
% 47.84/6.50  inst_num_moves_active_passive:          599
% 47.84/6.50  inst_lit_activity:                      0
% 47.84/6.50  inst_lit_activity_moves:                3
% 47.84/6.50  inst_num_tautologies:                   0
% 47.84/6.50  inst_num_prop_implied:                  0
% 47.84/6.50  inst_num_existing_simplified:           0
% 47.84/6.50  inst_num_eq_res_simplified:             0
% 47.84/6.50  inst_num_child_elim:                    0
% 47.84/6.50  inst_num_of_dismatching_blockings:      50933
% 47.84/6.50  inst_num_of_non_proper_insts:           15630
% 47.84/6.50  inst_num_of_duplicates:                 0
% 47.84/6.50  inst_inst_num_from_inst_to_res:         0
% 47.84/6.50  inst_dismatching_checking_time:         0.
% 47.84/6.50  
% 47.84/6.50  ------ Resolution
% 47.84/6.50  
% 47.84/6.50  res_num_of_clauses:                     26
% 47.84/6.50  res_num_in_passive:                     26
% 47.84/6.50  res_num_in_active:                      0
% 47.84/6.50  res_num_of_loops:                       97
% 47.84/6.50  res_forward_subset_subsumed:            96
% 47.84/6.50  res_backward_subset_subsumed:           0
% 47.84/6.50  res_forward_subsumed:                   0
% 47.84/6.50  res_backward_subsumed:                  0
% 47.84/6.50  res_forward_subsumption_resolution:     0
% 47.84/6.50  res_backward_subsumption_resolution:    0
% 47.84/6.50  res_clause_to_clause_subsumption:       30683
% 47.84/6.50  res_orphan_elimination:                 0
% 47.84/6.50  res_tautology_del:                      82
% 47.84/6.50  res_num_eq_res_simplified:              2
% 47.84/6.50  res_num_sel_changes:                    0
% 47.84/6.50  res_moves_from_active_to_pass:          0
% 47.84/6.50  
% 47.84/6.50  ------ Superposition
% 47.84/6.50  
% 47.84/6.50  sup_time_total:                         0.
% 47.84/6.50  sup_time_generating:                    0.
% 47.84/6.50  sup_time_sim_full:                      0.
% 47.84/6.50  sup_time_sim_immed:                     0.
% 47.84/6.50  
% 47.84/6.50  sup_num_of_clauses:                     9744
% 47.84/6.50  sup_num_in_active:                      679
% 47.84/6.50  sup_num_in_passive:                     9065
% 47.84/6.50  sup_num_of_loops:                       682
% 47.84/6.50  sup_fw_superposition:                   3493
% 47.84/6.50  sup_bw_superposition:                   6883
% 47.84/6.50  sup_immediate_simplified:               1063
% 47.84/6.50  sup_given_eliminated:                   0
% 47.84/6.50  comparisons_done:                       0
% 47.84/6.50  comparisons_avoided:                    0
% 47.84/6.50  
% 47.84/6.50  ------ Simplifications
% 47.84/6.50  
% 47.84/6.50  
% 47.84/6.50  sim_fw_subset_subsumed:                 12
% 47.84/6.50  sim_bw_subset_subsumed:                 0
% 47.84/6.50  sim_fw_subsumed:                        24
% 47.84/6.50  sim_bw_subsumed:                        0
% 47.84/6.50  sim_fw_subsumption_res:                 5
% 47.84/6.50  sim_bw_subsumption_res:                 0
% 47.84/6.50  sim_tautology_del:                      19
% 47.84/6.50  sim_eq_tautology_del:                   28
% 47.84/6.50  sim_eq_res_simp:                        24
% 47.84/6.50  sim_fw_demodulated:                     114
% 47.84/6.50  sim_bw_demodulated:                     3
% 47.84/6.50  sim_light_normalised:                   1122
% 47.84/6.50  sim_joinable_taut:                      0
% 47.84/6.50  sim_joinable_simp:                      0
% 47.84/6.50  sim_ac_normalised:                      0
% 47.84/6.50  sim_smt_subsumption:                    0
% 47.84/6.50  
%------------------------------------------------------------------------------
