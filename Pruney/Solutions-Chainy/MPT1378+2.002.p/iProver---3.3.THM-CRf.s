%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:18:10 EST 2020

% Result     : Theorem 4.07s
% Output     : CNFRefutation 4.07s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 402 expanded)
%              Number of clauses        :   58 (  94 expanded)
%              Number of leaves         :   13 ( 142 expanded)
%              Depth                    :   17
%              Number of atoms          :  432 (2936 expanded)
%              Number of equality atoms :   81 ( 103 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f10])).

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

fof(f31,plain,(
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

fof(f30,plain,(
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

fof(f29,plain,(
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

fof(f28,plain,
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

fof(f32,plain,
    ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK1),sK3,sK4),sK1,sK2)
    & m1_connsp_2(sK4,sK1,sK2)
    & m1_connsp_2(sK3,sK1,sK2)
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f21,f31,f30,f29,f28])).

fof(f51,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f32])).

fof(f52,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f32])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f14])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f12])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

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

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f49,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
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
    inference(flattening,[],[f22])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f23])).

fof(f25,plain,(
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

fof(f26,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).

fof(f35,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f57,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f35])).

fof(f55,plain,(
    ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK1),sK3,sK4),sK1,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

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

fof(f27,plain,(
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

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f48,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f47,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f50,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f32])).

fof(f53,plain,(
    m1_connsp_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_8,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_807,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_803,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_804,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_805,plain,
    ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3960,plain,
    ( k4_subset_1(u1_struct_0(sK1),X0,sK4) = k2_xboole_0(X0,sK4)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_804,c_805])).

cnf(c_4029,plain,
    ( k4_subset_1(u1_struct_0(sK1),sK3,sK4) = k2_xboole_0(sK3,sK4) ),
    inference(superposition,[status(thm)],[c_803,c_3960])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | m1_subset_1(k4_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_806,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k4_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4080,plain,
    ( m1_subset_1(k2_xboole_0(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4029,c_806])).

cnf(c_27,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_28,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4914,plain,
    ( m1_subset_1(k2_xboole_0(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4080,c_27,c_28])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_20,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_296,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X0))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_20])).

cnf(c_297,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X1,X0)
    | r1_tarski(k1_tops_1(sK1,X1),k1_tops_1(sK1,X0)) ),
    inference(unflattening,[status(thm)],[c_296])).

cnf(c_801,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(k1_tops_1(sK1,X1),k1_tops_1(sK1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_297])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_808,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1330,plain,
    ( k2_xboole_0(k1_tops_1(sK1,X0),k1_tops_1(sK1,X1)) = k1_tops_1(sK1,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_801,c_808])).

cnf(c_1338,plain,
    ( k2_xboole_0(k1_tops_1(sK1,sK3),k1_tops_1(sK1,X0)) = k1_tops_1(sK1,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_803,c_1330])).

cnf(c_4921,plain,
    ( k2_xboole_0(k1_tops_1(sK1,sK3),k1_tops_1(sK1,k2_xboole_0(sK3,sK4))) = k1_tops_1(sK1,k2_xboole_0(sK3,sK4))
    | r1_tarski(sK3,k2_xboole_0(sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4914,c_1338])).

cnf(c_4955,plain,
    ( k2_xboole_0(k1_tops_1(sK1,sK3),k1_tops_1(sK1,k2_xboole_0(sK3,sK4))) = k1_tops_1(sK1,k2_xboole_0(sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_807,c_4921])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_810,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k2_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_5286,plain,
    ( r2_hidden(X0,k1_tops_1(sK1,k2_xboole_0(sK3,sK4))) = iProver_top
    | r2_hidden(X0,k1_tops_1(sK1,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4955,c_810])).

cnf(c_14,negated_conjecture,
    ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK1),sK3,sK4),sK1,sK2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_12,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_21,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_262,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_21])).

cnf(c_263,plain,
    ( m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X1,k1_tops_1(sK1,X0))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_262])).

cnf(c_22,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_267,plain,
    ( m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X1,k1_tops_1(sK1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_263,c_22,c_20])).

cnf(c_340,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X0,k1_tops_1(sK1,X1))
    | k4_subset_1(u1_struct_0(sK1),sK3,sK4) != X1
    | sK2 != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_267])).

cnf(c_341,plain,
    ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) ),
    inference(unflattening,[status(thm)],[c_340])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_343,plain,
    ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_341,c_19])).

cnf(c_800,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_343])).

cnf(c_26,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_342,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_341])).

cnf(c_839,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_840,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_839])).

cnf(c_1043,plain,
    ( r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_800,c_26,c_27,c_28,c_342,c_840])).

cnf(c_4076,plain,
    ( r2_hidden(sK2,k1_tops_1(sK1,k2_xboole_0(sK3,sK4))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4029,c_1043])).

cnf(c_13190,plain,
    ( r2_hidden(sK2,k1_tops_1(sK1,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5286,c_4076])).

cnf(c_16,negated_conjecture,
    ( m1_connsp_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_13,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_238,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_21])).

cnf(c_239,plain,
    ( ~ m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(X1,k1_tops_1(sK1,X0))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_238])).

cnf(c_243,plain,
    ( ~ m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(X1,k1_tops_1(sK1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_239,c_22,c_20])).

cnf(c_365,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(X0,k1_tops_1(sK1,X1))
    | sK2 != X0
    | sK3 != X1
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_243])).

cnf(c_366,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
    inference(unflattening,[status(thm)],[c_365])).

cnf(c_367,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_366])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13190,c_367,c_27,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:12:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 4.07/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.07/0.98  
% 4.07/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.07/0.98  
% 4.07/0.98  ------  iProver source info
% 4.07/0.98  
% 4.07/0.98  git: date: 2020-06-30 10:37:57 +0100
% 4.07/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.07/0.98  git: non_committed_changes: false
% 4.07/0.98  git: last_make_outside_of_git: false
% 4.07/0.98  
% 4.07/0.98  ------ 
% 4.07/0.98  
% 4.07/0.98  ------ Input Options
% 4.07/0.98  
% 4.07/0.98  --out_options                           all
% 4.07/0.98  --tptp_safe_out                         true
% 4.07/0.98  --problem_path                          ""
% 4.07/0.98  --include_path                          ""
% 4.07/0.98  --clausifier                            res/vclausify_rel
% 4.07/0.98  --clausifier_options                    ""
% 4.07/0.98  --stdin                                 false
% 4.07/0.98  --stats_out                             all
% 4.07/0.98  
% 4.07/0.98  ------ General Options
% 4.07/0.98  
% 4.07/0.98  --fof                                   false
% 4.07/0.98  --time_out_real                         305.
% 4.07/0.98  --time_out_virtual                      -1.
% 4.07/0.98  --symbol_type_check                     false
% 4.07/0.98  --clausify_out                          false
% 4.07/0.98  --sig_cnt_out                           false
% 4.07/0.98  --trig_cnt_out                          false
% 4.07/0.98  --trig_cnt_out_tolerance                1.
% 4.07/0.98  --trig_cnt_out_sk_spl                   false
% 4.07/0.98  --abstr_cl_out                          false
% 4.07/0.98  
% 4.07/0.98  ------ Global Options
% 4.07/0.98  
% 4.07/0.98  --schedule                              default
% 4.07/0.98  --add_important_lit                     false
% 4.07/0.98  --prop_solver_per_cl                    1000
% 4.07/0.98  --min_unsat_core                        false
% 4.07/0.98  --soft_assumptions                      false
% 4.07/0.98  --soft_lemma_size                       3
% 4.07/0.98  --prop_impl_unit_size                   0
% 4.07/0.98  --prop_impl_unit                        []
% 4.07/0.98  --share_sel_clauses                     true
% 4.07/0.98  --reset_solvers                         false
% 4.07/0.98  --bc_imp_inh                            [conj_cone]
% 4.07/0.98  --conj_cone_tolerance                   3.
% 4.07/0.98  --extra_neg_conj                        none
% 4.07/0.98  --large_theory_mode                     true
% 4.07/0.98  --prolific_symb_bound                   200
% 4.07/0.98  --lt_threshold                          2000
% 4.07/0.98  --clause_weak_htbl                      true
% 4.07/0.98  --gc_record_bc_elim                     false
% 4.07/0.98  
% 4.07/0.98  ------ Preprocessing Options
% 4.07/0.98  
% 4.07/0.98  --preprocessing_flag                    true
% 4.07/0.98  --time_out_prep_mult                    0.1
% 4.07/0.98  --splitting_mode                        input
% 4.07/0.98  --splitting_grd                         true
% 4.07/0.98  --splitting_cvd                         false
% 4.07/0.98  --splitting_cvd_svl                     false
% 4.07/0.98  --splitting_nvd                         32
% 4.07/0.98  --sub_typing                            true
% 4.07/0.98  --prep_gs_sim                           true
% 4.07/0.98  --prep_unflatten                        true
% 4.07/0.98  --prep_res_sim                          true
% 4.07/0.98  --prep_upred                            true
% 4.07/0.98  --prep_sem_filter                       exhaustive
% 4.07/0.98  --prep_sem_filter_out                   false
% 4.07/0.98  --pred_elim                             true
% 4.07/0.98  --res_sim_input                         true
% 4.07/0.98  --eq_ax_congr_red                       true
% 4.07/0.98  --pure_diseq_elim                       true
% 4.07/0.98  --brand_transform                       false
% 4.07/0.98  --non_eq_to_eq                          false
% 4.07/0.98  --prep_def_merge                        true
% 4.07/0.98  --prep_def_merge_prop_impl              false
% 4.07/0.98  --prep_def_merge_mbd                    true
% 4.07/0.98  --prep_def_merge_tr_red                 false
% 4.07/0.98  --prep_def_merge_tr_cl                  false
% 4.07/0.98  --smt_preprocessing                     true
% 4.07/0.98  --smt_ac_axioms                         fast
% 4.07/0.98  --preprocessed_out                      false
% 4.07/0.98  --preprocessed_stats                    false
% 4.07/0.98  
% 4.07/0.98  ------ Abstraction refinement Options
% 4.07/0.98  
% 4.07/0.98  --abstr_ref                             []
% 4.07/0.98  --abstr_ref_prep                        false
% 4.07/0.98  --abstr_ref_until_sat                   false
% 4.07/0.98  --abstr_ref_sig_restrict                funpre
% 4.07/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 4.07/0.98  --abstr_ref_under                       []
% 4.07/0.98  
% 4.07/0.98  ------ SAT Options
% 4.07/0.98  
% 4.07/0.98  --sat_mode                              false
% 4.07/0.98  --sat_fm_restart_options                ""
% 4.07/0.98  --sat_gr_def                            false
% 4.07/0.98  --sat_epr_types                         true
% 4.07/0.98  --sat_non_cyclic_types                  false
% 4.07/0.98  --sat_finite_models                     false
% 4.07/0.98  --sat_fm_lemmas                         false
% 4.07/0.98  --sat_fm_prep                           false
% 4.07/0.98  --sat_fm_uc_incr                        true
% 4.07/0.98  --sat_out_model                         small
% 4.07/0.98  --sat_out_clauses                       false
% 4.07/0.98  
% 4.07/0.98  ------ QBF Options
% 4.07/0.98  
% 4.07/0.98  --qbf_mode                              false
% 4.07/0.98  --qbf_elim_univ                         false
% 4.07/0.98  --qbf_dom_inst                          none
% 4.07/0.98  --qbf_dom_pre_inst                      false
% 4.07/0.98  --qbf_sk_in                             false
% 4.07/0.98  --qbf_pred_elim                         true
% 4.07/0.98  --qbf_split                             512
% 4.07/0.98  
% 4.07/0.98  ------ BMC1 Options
% 4.07/0.98  
% 4.07/0.98  --bmc1_incremental                      false
% 4.07/0.98  --bmc1_axioms                           reachable_all
% 4.07/0.98  --bmc1_min_bound                        0
% 4.07/0.98  --bmc1_max_bound                        -1
% 4.07/0.98  --bmc1_max_bound_default                -1
% 4.07/0.98  --bmc1_symbol_reachability              true
% 4.07/0.98  --bmc1_property_lemmas                  false
% 4.07/0.98  --bmc1_k_induction                      false
% 4.07/0.98  --bmc1_non_equiv_states                 false
% 4.07/0.98  --bmc1_deadlock                         false
% 4.07/0.98  --bmc1_ucm                              false
% 4.07/0.98  --bmc1_add_unsat_core                   none
% 4.07/0.98  --bmc1_unsat_core_children              false
% 4.07/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 4.07/0.98  --bmc1_out_stat                         full
% 4.07/0.98  --bmc1_ground_init                      false
% 4.07/0.98  --bmc1_pre_inst_next_state              false
% 4.07/0.98  --bmc1_pre_inst_state                   false
% 4.07/0.98  --bmc1_pre_inst_reach_state             false
% 4.07/0.98  --bmc1_out_unsat_core                   false
% 4.07/0.98  --bmc1_aig_witness_out                  false
% 4.07/0.98  --bmc1_verbose                          false
% 4.07/0.98  --bmc1_dump_clauses_tptp                false
% 4.07/0.98  --bmc1_dump_unsat_core_tptp             false
% 4.07/0.98  --bmc1_dump_file                        -
% 4.07/0.98  --bmc1_ucm_expand_uc_limit              128
% 4.07/0.98  --bmc1_ucm_n_expand_iterations          6
% 4.07/0.98  --bmc1_ucm_extend_mode                  1
% 4.07/0.98  --bmc1_ucm_init_mode                    2
% 4.07/0.98  --bmc1_ucm_cone_mode                    none
% 4.07/0.98  --bmc1_ucm_reduced_relation_type        0
% 4.07/0.98  --bmc1_ucm_relax_model                  4
% 4.07/0.98  --bmc1_ucm_full_tr_after_sat            true
% 4.07/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 4.07/0.98  --bmc1_ucm_layered_model                none
% 4.07/0.98  --bmc1_ucm_max_lemma_size               10
% 4.07/0.98  
% 4.07/0.98  ------ AIG Options
% 4.07/0.98  
% 4.07/0.98  --aig_mode                              false
% 4.07/0.98  
% 4.07/0.98  ------ Instantiation Options
% 4.07/0.98  
% 4.07/0.98  --instantiation_flag                    true
% 4.07/0.98  --inst_sos_flag                         true
% 4.07/0.98  --inst_sos_phase                        true
% 4.07/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.07/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.07/0.98  --inst_lit_sel_side                     num_symb
% 4.07/0.98  --inst_solver_per_active                1400
% 4.07/0.98  --inst_solver_calls_frac                1.
% 4.07/0.98  --inst_passive_queue_type               priority_queues
% 4.07/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.07/0.98  --inst_passive_queues_freq              [25;2]
% 4.07/0.98  --inst_dismatching                      true
% 4.07/0.98  --inst_eager_unprocessed_to_passive     true
% 4.07/0.98  --inst_prop_sim_given                   true
% 4.07/0.98  --inst_prop_sim_new                     false
% 4.07/0.98  --inst_subs_new                         false
% 4.07/0.98  --inst_eq_res_simp                      false
% 4.07/0.98  --inst_subs_given                       false
% 4.07/0.98  --inst_orphan_elimination               true
% 4.07/0.98  --inst_learning_loop_flag               true
% 4.07/0.98  --inst_learning_start                   3000
% 4.07/0.98  --inst_learning_factor                  2
% 4.07/0.98  --inst_start_prop_sim_after_learn       3
% 4.07/0.98  --inst_sel_renew                        solver
% 4.07/0.98  --inst_lit_activity_flag                true
% 4.07/0.98  --inst_restr_to_given                   false
% 4.07/0.98  --inst_activity_threshold               500
% 4.07/0.98  --inst_out_proof                        true
% 4.07/0.98  
% 4.07/0.98  ------ Resolution Options
% 4.07/0.98  
% 4.07/0.98  --resolution_flag                       true
% 4.07/0.98  --res_lit_sel                           adaptive
% 4.07/0.98  --res_lit_sel_side                      none
% 4.07/0.98  --res_ordering                          kbo
% 4.07/0.98  --res_to_prop_solver                    active
% 4.07/0.98  --res_prop_simpl_new                    false
% 4.07/0.98  --res_prop_simpl_given                  true
% 4.07/0.98  --res_passive_queue_type                priority_queues
% 4.07/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.07/0.98  --res_passive_queues_freq               [15;5]
% 4.07/0.98  --res_forward_subs                      full
% 4.07/0.98  --res_backward_subs                     full
% 4.07/0.98  --res_forward_subs_resolution           true
% 4.07/0.98  --res_backward_subs_resolution          true
% 4.07/0.98  --res_orphan_elimination                true
% 4.07/0.98  --res_time_limit                        2.
% 4.07/0.98  --res_out_proof                         true
% 4.07/0.98  
% 4.07/0.98  ------ Superposition Options
% 4.07/0.98  
% 4.07/0.98  --superposition_flag                    true
% 4.07/0.98  --sup_passive_queue_type                priority_queues
% 4.07/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.07/0.98  --sup_passive_queues_freq               [8;1;4]
% 4.07/0.98  --demod_completeness_check              fast
% 4.07/0.98  --demod_use_ground                      true
% 4.07/0.98  --sup_to_prop_solver                    passive
% 4.07/0.98  --sup_prop_simpl_new                    true
% 4.07/0.98  --sup_prop_simpl_given                  true
% 4.07/0.98  --sup_fun_splitting                     true
% 4.07/0.98  --sup_smt_interval                      50000
% 4.07/0.98  
% 4.07/0.98  ------ Superposition Simplification Setup
% 4.07/0.98  
% 4.07/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.07/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.07/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.07/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.07/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 4.07/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.07/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.07/0.98  --sup_immed_triv                        [TrivRules]
% 4.07/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.07/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.07/0.98  --sup_immed_bw_main                     []
% 4.07/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.07/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 4.07/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.07/0.98  --sup_input_bw                          []
% 4.07/0.98  
% 4.07/0.98  ------ Combination Options
% 4.07/0.98  
% 4.07/0.98  --comb_res_mult                         3
% 4.07/0.98  --comb_sup_mult                         2
% 4.07/0.98  --comb_inst_mult                        10
% 4.07/0.98  
% 4.07/0.98  ------ Debug Options
% 4.07/0.98  
% 4.07/0.98  --dbg_backtrace                         false
% 4.07/0.98  --dbg_dump_prop_clauses                 false
% 4.07/0.98  --dbg_dump_prop_clauses_file            -
% 4.07/0.98  --dbg_out_stat                          false
% 4.07/0.98  ------ Parsing...
% 4.07/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.07/0.98  
% 4.07/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 4.07/0.98  
% 4.07/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.07/0.98  
% 4.07/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.07/0.98  ------ Proving...
% 4.07/0.98  ------ Problem Properties 
% 4.07/0.98  
% 4.07/0.98  
% 4.07/0.98  clauses                                 20
% 4.07/0.98  conjectures                             3
% 4.07/0.98  EPR                                     0
% 4.07/0.98  Horn                                    18
% 4.07/0.98  unary                                   9
% 4.07/0.98  binary                                  4
% 4.07/0.98  lits                                    40
% 4.07/0.98  lits eq                                 8
% 4.07/0.98  fd_pure                                 0
% 4.07/0.98  fd_pseudo                               0
% 4.07/0.98  fd_cond                                 0
% 4.07/0.98  fd_pseudo_cond                          3
% 4.07/0.98  AC symbols                              0
% 4.07/0.98  
% 4.07/0.98  ------ Schedule dynamic 5 is on 
% 4.07/0.98  
% 4.07/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 4.07/0.98  
% 4.07/0.98  
% 4.07/0.98  ------ 
% 4.07/0.98  Current options:
% 4.07/0.98  ------ 
% 4.07/0.98  
% 4.07/0.98  ------ Input Options
% 4.07/0.98  
% 4.07/0.98  --out_options                           all
% 4.07/0.98  --tptp_safe_out                         true
% 4.07/0.98  --problem_path                          ""
% 4.07/0.98  --include_path                          ""
% 4.07/0.98  --clausifier                            res/vclausify_rel
% 4.07/0.98  --clausifier_options                    ""
% 4.07/0.98  --stdin                                 false
% 4.07/0.98  --stats_out                             all
% 4.07/0.98  
% 4.07/0.98  ------ General Options
% 4.07/0.98  
% 4.07/0.98  --fof                                   false
% 4.07/0.98  --time_out_real                         305.
% 4.07/0.98  --time_out_virtual                      -1.
% 4.07/0.98  --symbol_type_check                     false
% 4.07/0.98  --clausify_out                          false
% 4.07/0.98  --sig_cnt_out                           false
% 4.07/0.98  --trig_cnt_out                          false
% 4.07/0.98  --trig_cnt_out_tolerance                1.
% 4.07/0.98  --trig_cnt_out_sk_spl                   false
% 4.07/0.98  --abstr_cl_out                          false
% 4.07/0.98  
% 4.07/0.98  ------ Global Options
% 4.07/0.98  
% 4.07/0.98  --schedule                              default
% 4.07/0.98  --add_important_lit                     false
% 4.07/0.98  --prop_solver_per_cl                    1000
% 4.07/0.98  --min_unsat_core                        false
% 4.07/0.98  --soft_assumptions                      false
% 4.07/0.98  --soft_lemma_size                       3
% 4.07/0.98  --prop_impl_unit_size                   0
% 4.07/0.98  --prop_impl_unit                        []
% 4.07/0.98  --share_sel_clauses                     true
% 4.07/0.98  --reset_solvers                         false
% 4.07/0.98  --bc_imp_inh                            [conj_cone]
% 4.07/0.98  --conj_cone_tolerance                   3.
% 4.07/0.98  --extra_neg_conj                        none
% 4.07/0.98  --large_theory_mode                     true
% 4.07/0.98  --prolific_symb_bound                   200
% 4.07/0.98  --lt_threshold                          2000
% 4.07/0.98  --clause_weak_htbl                      true
% 4.07/0.98  --gc_record_bc_elim                     false
% 4.07/0.98  
% 4.07/0.98  ------ Preprocessing Options
% 4.07/0.98  
% 4.07/0.98  --preprocessing_flag                    true
% 4.07/0.98  --time_out_prep_mult                    0.1
% 4.07/0.98  --splitting_mode                        input
% 4.07/0.98  --splitting_grd                         true
% 4.07/0.98  --splitting_cvd                         false
% 4.07/0.98  --splitting_cvd_svl                     false
% 4.07/0.98  --splitting_nvd                         32
% 4.07/0.98  --sub_typing                            true
% 4.07/0.98  --prep_gs_sim                           true
% 4.07/0.98  --prep_unflatten                        true
% 4.07/0.98  --prep_res_sim                          true
% 4.07/0.98  --prep_upred                            true
% 4.07/0.98  --prep_sem_filter                       exhaustive
% 4.07/0.98  --prep_sem_filter_out                   false
% 4.07/0.98  --pred_elim                             true
% 4.07/0.98  --res_sim_input                         true
% 4.07/0.98  --eq_ax_congr_red                       true
% 4.07/0.98  --pure_diseq_elim                       true
% 4.07/0.98  --brand_transform                       false
% 4.07/0.98  --non_eq_to_eq                          false
% 4.07/0.98  --prep_def_merge                        true
% 4.07/0.98  --prep_def_merge_prop_impl              false
% 4.07/0.98  --prep_def_merge_mbd                    true
% 4.07/0.98  --prep_def_merge_tr_red                 false
% 4.07/0.98  --prep_def_merge_tr_cl                  false
% 4.07/0.98  --smt_preprocessing                     true
% 4.07/0.98  --smt_ac_axioms                         fast
% 4.07/0.98  --preprocessed_out                      false
% 4.07/0.98  --preprocessed_stats                    false
% 4.07/0.98  
% 4.07/0.98  ------ Abstraction refinement Options
% 4.07/0.98  
% 4.07/0.98  --abstr_ref                             []
% 4.07/0.98  --abstr_ref_prep                        false
% 4.07/0.98  --abstr_ref_until_sat                   false
% 4.07/0.98  --abstr_ref_sig_restrict                funpre
% 4.07/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 4.07/0.98  --abstr_ref_under                       []
% 4.07/0.98  
% 4.07/0.98  ------ SAT Options
% 4.07/0.98  
% 4.07/0.98  --sat_mode                              false
% 4.07/0.98  --sat_fm_restart_options                ""
% 4.07/0.98  --sat_gr_def                            false
% 4.07/0.98  --sat_epr_types                         true
% 4.07/0.98  --sat_non_cyclic_types                  false
% 4.07/0.98  --sat_finite_models                     false
% 4.07/0.98  --sat_fm_lemmas                         false
% 4.07/0.98  --sat_fm_prep                           false
% 4.07/0.98  --sat_fm_uc_incr                        true
% 4.07/0.98  --sat_out_model                         small
% 4.07/0.98  --sat_out_clauses                       false
% 4.07/0.98  
% 4.07/0.98  ------ QBF Options
% 4.07/0.98  
% 4.07/0.98  --qbf_mode                              false
% 4.07/0.98  --qbf_elim_univ                         false
% 4.07/0.98  --qbf_dom_inst                          none
% 4.07/0.98  --qbf_dom_pre_inst                      false
% 4.07/0.98  --qbf_sk_in                             false
% 4.07/0.98  --qbf_pred_elim                         true
% 4.07/0.98  --qbf_split                             512
% 4.07/0.98  
% 4.07/0.98  ------ BMC1 Options
% 4.07/0.98  
% 4.07/0.98  --bmc1_incremental                      false
% 4.07/0.98  --bmc1_axioms                           reachable_all
% 4.07/0.98  --bmc1_min_bound                        0
% 4.07/0.98  --bmc1_max_bound                        -1
% 4.07/0.98  --bmc1_max_bound_default                -1
% 4.07/0.98  --bmc1_symbol_reachability              true
% 4.07/0.98  --bmc1_property_lemmas                  false
% 4.07/0.98  --bmc1_k_induction                      false
% 4.07/0.98  --bmc1_non_equiv_states                 false
% 4.07/0.98  --bmc1_deadlock                         false
% 4.07/0.98  --bmc1_ucm                              false
% 4.07/0.98  --bmc1_add_unsat_core                   none
% 4.07/0.98  --bmc1_unsat_core_children              false
% 4.07/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 4.07/0.98  --bmc1_out_stat                         full
% 4.07/0.98  --bmc1_ground_init                      false
% 4.07/0.98  --bmc1_pre_inst_next_state              false
% 4.07/0.98  --bmc1_pre_inst_state                   false
% 4.07/0.98  --bmc1_pre_inst_reach_state             false
% 4.07/0.98  --bmc1_out_unsat_core                   false
% 4.07/0.98  --bmc1_aig_witness_out                  false
% 4.07/0.98  --bmc1_verbose                          false
% 4.07/0.98  --bmc1_dump_clauses_tptp                false
% 4.07/0.98  --bmc1_dump_unsat_core_tptp             false
% 4.07/0.98  --bmc1_dump_file                        -
% 4.07/0.98  --bmc1_ucm_expand_uc_limit              128
% 4.07/0.98  --bmc1_ucm_n_expand_iterations          6
% 4.07/0.98  --bmc1_ucm_extend_mode                  1
% 4.07/0.98  --bmc1_ucm_init_mode                    2
% 4.07/0.98  --bmc1_ucm_cone_mode                    none
% 4.07/0.98  --bmc1_ucm_reduced_relation_type        0
% 4.07/0.98  --bmc1_ucm_relax_model                  4
% 4.07/0.98  --bmc1_ucm_full_tr_after_sat            true
% 4.07/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 4.07/0.98  --bmc1_ucm_layered_model                none
% 4.07/0.98  --bmc1_ucm_max_lemma_size               10
% 4.07/0.98  
% 4.07/0.98  ------ AIG Options
% 4.07/0.98  
% 4.07/0.98  --aig_mode                              false
% 4.07/0.98  
% 4.07/0.98  ------ Instantiation Options
% 4.07/0.98  
% 4.07/0.98  --instantiation_flag                    true
% 4.07/0.98  --inst_sos_flag                         true
% 4.07/0.98  --inst_sos_phase                        true
% 4.07/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.07/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.07/0.98  --inst_lit_sel_side                     none
% 4.07/0.98  --inst_solver_per_active                1400
% 4.07/0.98  --inst_solver_calls_frac                1.
% 4.07/0.98  --inst_passive_queue_type               priority_queues
% 4.07/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.07/0.98  --inst_passive_queues_freq              [25;2]
% 4.07/0.98  --inst_dismatching                      true
% 4.07/0.98  --inst_eager_unprocessed_to_passive     true
% 4.07/0.98  --inst_prop_sim_given                   true
% 4.07/0.98  --inst_prop_sim_new                     false
% 4.07/0.98  --inst_subs_new                         false
% 4.07/0.98  --inst_eq_res_simp                      false
% 4.07/0.98  --inst_subs_given                       false
% 4.07/0.98  --inst_orphan_elimination               true
% 4.07/0.98  --inst_learning_loop_flag               true
% 4.07/0.98  --inst_learning_start                   3000
% 4.07/0.98  --inst_learning_factor                  2
% 4.07/0.98  --inst_start_prop_sim_after_learn       3
% 4.07/0.98  --inst_sel_renew                        solver
% 4.07/0.98  --inst_lit_activity_flag                true
% 4.07/0.98  --inst_restr_to_given                   false
% 4.07/0.98  --inst_activity_threshold               500
% 4.07/0.98  --inst_out_proof                        true
% 4.07/0.98  
% 4.07/0.98  ------ Resolution Options
% 4.07/0.98  
% 4.07/0.98  --resolution_flag                       false
% 4.07/0.98  --res_lit_sel                           adaptive
% 4.07/0.98  --res_lit_sel_side                      none
% 4.07/0.98  --res_ordering                          kbo
% 4.07/0.98  --res_to_prop_solver                    active
% 4.07/0.98  --res_prop_simpl_new                    false
% 4.07/0.98  --res_prop_simpl_given                  true
% 4.07/0.98  --res_passive_queue_type                priority_queues
% 4.07/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.07/0.98  --res_passive_queues_freq               [15;5]
% 4.07/0.98  --res_forward_subs                      full
% 4.07/0.98  --res_backward_subs                     full
% 4.07/0.98  --res_forward_subs_resolution           true
% 4.07/0.98  --res_backward_subs_resolution          true
% 4.07/0.98  --res_orphan_elimination                true
% 4.07/0.98  --res_time_limit                        2.
% 4.07/0.98  --res_out_proof                         true
% 4.07/0.98  
% 4.07/0.98  ------ Superposition Options
% 4.07/0.98  
% 4.07/0.98  --superposition_flag                    true
% 4.07/0.98  --sup_passive_queue_type                priority_queues
% 4.07/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.07/0.98  --sup_passive_queues_freq               [8;1;4]
% 4.07/0.98  --demod_completeness_check              fast
% 4.07/0.98  --demod_use_ground                      true
% 4.07/0.98  --sup_to_prop_solver                    passive
% 4.07/0.98  --sup_prop_simpl_new                    true
% 4.07/0.98  --sup_prop_simpl_given                  true
% 4.07/0.98  --sup_fun_splitting                     true
% 4.07/0.98  --sup_smt_interval                      50000
% 4.07/0.98  
% 4.07/0.98  ------ Superposition Simplification Setup
% 4.07/0.98  
% 4.07/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.07/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.07/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.07/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.07/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 4.07/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.07/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.07/0.98  --sup_immed_triv                        [TrivRules]
% 4.07/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.07/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.07/0.98  --sup_immed_bw_main                     []
% 4.07/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.07/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 4.07/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.07/0.98  --sup_input_bw                          []
% 4.07/0.98  
% 4.07/0.98  ------ Combination Options
% 4.07/0.98  
% 4.07/0.98  --comb_res_mult                         3
% 4.07/0.98  --comb_sup_mult                         2
% 4.07/0.98  --comb_inst_mult                        10
% 4.07/0.98  
% 4.07/0.98  ------ Debug Options
% 4.07/0.98  
% 4.07/0.98  --dbg_backtrace                         false
% 4.07/0.98  --dbg_dump_prop_clauses                 false
% 4.07/0.98  --dbg_dump_prop_clauses_file            -
% 4.07/0.98  --dbg_out_stat                          false
% 4.07/0.98  
% 4.07/0.98  
% 4.07/0.98  
% 4.07/0.98  
% 4.07/0.98  ------ Proving...
% 4.07/0.98  
% 4.07/0.98  
% 4.07/0.98  % SZS status Theorem for theBenchmark.p
% 4.07/0.98  
% 4.07/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 4.07/0.98  
% 4.07/0.98  fof(f4,axiom,(
% 4.07/0.98    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 4.07/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/0.98  
% 4.07/0.98  fof(f41,plain,(
% 4.07/0.98    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 4.07/0.98    inference(cnf_transformation,[],[f4])).
% 4.07/0.98  
% 4.07/0.98  fof(f9,conjecture,(
% 4.07/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1)) => m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1))))))),
% 4.07/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/0.98  
% 4.07/0.98  fof(f10,negated_conjecture,(
% 4.07/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1)) => m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1))))))),
% 4.07/0.98    inference(negated_conjecture,[],[f9])).
% 4.07/0.98  
% 4.07/0.98  fof(f20,plain,(
% 4.07/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & (m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 4.07/0.98    inference(ennf_transformation,[],[f10])).
% 4.07/0.98  
% 4.07/0.98  fof(f21,plain,(
% 4.07/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 4.07/0.98    inference(flattening,[],[f20])).
% 4.07/0.98  
% 4.07/0.98  fof(f31,plain,(
% 4.07/0.98    ( ! [X2,X0,X1] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,sK4),X0,X1) & m1_connsp_2(sK4,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 4.07/0.98    introduced(choice_axiom,[])).
% 4.07/0.98  
% 4.07/0.98  fof(f30,plain,(
% 4.07/0.98    ( ! [X0,X1] : (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),sK3,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(sK3,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 4.07/0.98    introduced(choice_axiom,[])).
% 4.07/0.98  
% 4.07/0.98  fof(f29,plain,(
% 4.07/0.98    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,sK2) & m1_connsp_2(X3,X0,sK2) & m1_connsp_2(X2,X0,sK2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK2,u1_struct_0(X0)))) )),
% 4.07/0.98    introduced(choice_axiom,[])).
% 4.07/0.98  
% 4.07/0.98  fof(f28,plain,(
% 4.07/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(sK1),X2,X3),sK1,X1) & m1_connsp_2(X3,sK1,X1) & m1_connsp_2(X2,sK1,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X1,u1_struct_0(sK1))) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 4.07/0.98    introduced(choice_axiom,[])).
% 4.07/0.98  
% 4.07/0.98  fof(f32,plain,(
% 4.07/0.98    (((~m1_connsp_2(k4_subset_1(u1_struct_0(sK1),sK3,sK4),sK1,sK2) & m1_connsp_2(sK4,sK1,sK2) & m1_connsp_2(sK3,sK1,sK2) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK2,u1_struct_0(sK1))) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 4.07/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f21,f31,f30,f29,f28])).
% 4.07/0.98  
% 4.07/0.98  fof(f51,plain,(
% 4.07/0.98    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 4.07/0.98    inference(cnf_transformation,[],[f32])).
% 4.07/0.98  
% 4.07/0.98  fof(f52,plain,(
% 4.07/0.98    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))),
% 4.07/0.98    inference(cnf_transformation,[],[f32])).
% 4.07/0.98  
% 4.07/0.98  fof(f6,axiom,(
% 4.07/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 4.07/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/0.98  
% 4.07/0.98  fof(f14,plain,(
% 4.07/0.98    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 4.07/0.98    inference(ennf_transformation,[],[f6])).
% 4.07/0.98  
% 4.07/0.98  fof(f15,plain,(
% 4.07/0.98    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.07/0.98    inference(flattening,[],[f14])).
% 4.07/0.98  
% 4.07/0.98  fof(f43,plain,(
% 4.07/0.98    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.07/0.98    inference(cnf_transformation,[],[f15])).
% 4.07/0.98  
% 4.07/0.98  fof(f5,axiom,(
% 4.07/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 4.07/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/0.98  
% 4.07/0.98  fof(f12,plain,(
% 4.07/0.98    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 4.07/0.98    inference(ennf_transformation,[],[f5])).
% 4.07/0.98  
% 4.07/0.98  fof(f13,plain,(
% 4.07/0.98    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.07/0.98    inference(flattening,[],[f12])).
% 4.07/0.98  
% 4.07/0.98  fof(f42,plain,(
% 4.07/0.98    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.07/0.98    inference(cnf_transformation,[],[f13])).
% 4.07/0.98  
% 4.07/0.98  fof(f7,axiom,(
% 4.07/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 4.07/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/0.98  
% 4.07/0.98  fof(f16,plain,(
% 4.07/0.98    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.07/0.98    inference(ennf_transformation,[],[f7])).
% 4.07/0.98  
% 4.07/0.98  fof(f17,plain,(
% 4.07/0.98    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.07/0.98    inference(flattening,[],[f16])).
% 4.07/0.98  
% 4.07/0.98  fof(f44,plain,(
% 4.07/0.98    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.07/0.98    inference(cnf_transformation,[],[f17])).
% 4.07/0.98  
% 4.07/0.98  fof(f49,plain,(
% 4.07/0.98    l1_pre_topc(sK1)),
% 4.07/0.98    inference(cnf_transformation,[],[f32])).
% 4.07/0.98  
% 4.07/0.98  fof(f3,axiom,(
% 4.07/0.98    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 4.07/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/0.98  
% 4.07/0.98  fof(f11,plain,(
% 4.07/0.98    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 4.07/0.98    inference(ennf_transformation,[],[f3])).
% 4.07/0.98  
% 4.07/0.98  fof(f40,plain,(
% 4.07/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 4.07/0.98    inference(cnf_transformation,[],[f11])).
% 4.07/0.98  
% 4.07/0.98  fof(f2,axiom,(
% 4.07/0.98    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 4.07/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/0.98  
% 4.07/0.98  fof(f22,plain,(
% 4.07/0.98    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 4.07/0.98    inference(nnf_transformation,[],[f2])).
% 4.07/0.98  
% 4.07/0.98  fof(f23,plain,(
% 4.07/0.98    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 4.07/0.98    inference(flattening,[],[f22])).
% 4.07/0.98  
% 4.07/0.98  fof(f24,plain,(
% 4.07/0.98    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 4.07/0.98    inference(rectify,[],[f23])).
% 4.07/0.98  
% 4.07/0.98  fof(f25,plain,(
% 4.07/0.98    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 4.07/0.98    introduced(choice_axiom,[])).
% 4.07/0.98  
% 4.07/0.98  fof(f26,plain,(
% 4.07/0.98    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 4.07/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).
% 4.07/0.98  
% 4.07/0.98  fof(f35,plain,(
% 4.07/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 4.07/0.98    inference(cnf_transformation,[],[f26])).
% 4.07/0.98  
% 4.07/0.98  fof(f57,plain,(
% 4.07/0.98    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X0)) )),
% 4.07/0.98    inference(equality_resolution,[],[f35])).
% 4.07/0.98  
% 4.07/0.98  fof(f55,plain,(
% 4.07/0.98    ~m1_connsp_2(k4_subset_1(u1_struct_0(sK1),sK3,sK4),sK1,sK2)),
% 4.07/0.98    inference(cnf_transformation,[],[f32])).
% 4.07/0.98  
% 4.07/0.98  fof(f8,axiom,(
% 4.07/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 4.07/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/0.98  
% 4.07/0.98  fof(f18,plain,(
% 4.07/0.98    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 4.07/0.98    inference(ennf_transformation,[],[f8])).
% 4.07/0.98  
% 4.07/0.98  fof(f19,plain,(
% 4.07/0.98    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.07/0.98    inference(flattening,[],[f18])).
% 4.07/0.98  
% 4.07/0.98  fof(f27,plain,(
% 4.07/0.98    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.07/0.98    inference(nnf_transformation,[],[f19])).
% 4.07/0.98  
% 4.07/0.98  fof(f46,plain,(
% 4.07/0.98    ( ! [X2,X0,X1] : (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.07/0.98    inference(cnf_transformation,[],[f27])).
% 4.07/0.98  
% 4.07/0.98  fof(f48,plain,(
% 4.07/0.98    v2_pre_topc(sK1)),
% 4.07/0.98    inference(cnf_transformation,[],[f32])).
% 4.07/0.98  
% 4.07/0.98  fof(f47,plain,(
% 4.07/0.98    ~v2_struct_0(sK1)),
% 4.07/0.98    inference(cnf_transformation,[],[f32])).
% 4.07/0.98  
% 4.07/0.98  fof(f50,plain,(
% 4.07/0.98    m1_subset_1(sK2,u1_struct_0(sK1))),
% 4.07/0.98    inference(cnf_transformation,[],[f32])).
% 4.07/0.98  
% 4.07/0.98  fof(f53,plain,(
% 4.07/0.98    m1_connsp_2(sK3,sK1,sK2)),
% 4.07/0.98    inference(cnf_transformation,[],[f32])).
% 4.07/0.98  
% 4.07/0.98  fof(f45,plain,(
% 4.07/0.98    ( ! [X2,X0,X1] : (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.07/0.98    inference(cnf_transformation,[],[f27])).
% 4.07/0.98  
% 4.07/0.98  cnf(c_8,plain,
% 4.07/0.98      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 4.07/0.98      inference(cnf_transformation,[],[f41]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_807,plain,
% 4.07/0.98      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 4.07/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_18,negated_conjecture,
% 4.07/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 4.07/0.98      inference(cnf_transformation,[],[f51]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_803,plain,
% 4.07/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 4.07/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_17,negated_conjecture,
% 4.07/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 4.07/0.98      inference(cnf_transformation,[],[f52]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_804,plain,
% 4.07/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 4.07/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_10,plain,
% 4.07/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 4.07/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 4.07/0.98      | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
% 4.07/0.98      inference(cnf_transformation,[],[f43]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_805,plain,
% 4.07/0.98      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
% 4.07/0.98      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 4.07/0.98      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 4.07/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_3960,plain,
% 4.07/0.98      ( k4_subset_1(u1_struct_0(sK1),X0,sK4) = k2_xboole_0(X0,sK4)
% 4.07/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 4.07/0.98      inference(superposition,[status(thm)],[c_804,c_805]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_4029,plain,
% 4.07/0.98      ( k4_subset_1(u1_struct_0(sK1),sK3,sK4) = k2_xboole_0(sK3,sK4) ),
% 4.07/0.98      inference(superposition,[status(thm)],[c_803,c_3960]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_9,plain,
% 4.07/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 4.07/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 4.07/0.98      | m1_subset_1(k4_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 4.07/0.98      inference(cnf_transformation,[],[f42]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_806,plain,
% 4.07/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 4.07/0.98      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 4.07/0.98      | m1_subset_1(k4_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 4.07/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_4080,plain,
% 4.07/0.98      ( m1_subset_1(k2_xboole_0(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 4.07/0.98      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 4.07/0.98      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 4.07/0.98      inference(superposition,[status(thm)],[c_4029,c_806]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_27,plain,
% 4.07/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 4.07/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_28,plain,
% 4.07/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 4.07/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_4914,plain,
% 4.07/0.98      ( m1_subset_1(k2_xboole_0(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 4.07/0.98      inference(global_propositional_subsumption,
% 4.07/0.98                [status(thm)],
% 4.07/0.98                [c_4080,c_27,c_28]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_11,plain,
% 4.07/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.07/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 4.07/0.98      | ~ r1_tarski(X2,X0)
% 4.07/0.98      | r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X0))
% 4.07/0.98      | ~ l1_pre_topc(X1) ),
% 4.07/0.98      inference(cnf_transformation,[],[f44]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_20,negated_conjecture,
% 4.07/0.98      ( l1_pre_topc(sK1) ),
% 4.07/0.98      inference(cnf_transformation,[],[f49]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_296,plain,
% 4.07/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.07/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 4.07/0.98      | ~ r1_tarski(X2,X0)
% 4.07/0.98      | r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X0))
% 4.07/0.98      | sK1 != X1 ),
% 4.07/0.98      inference(resolution_lifted,[status(thm)],[c_11,c_20]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_297,plain,
% 4.07/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 4.07/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 4.07/0.98      | ~ r1_tarski(X1,X0)
% 4.07/0.98      | r1_tarski(k1_tops_1(sK1,X1),k1_tops_1(sK1,X0)) ),
% 4.07/0.98      inference(unflattening,[status(thm)],[c_296]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_801,plain,
% 4.07/0.98      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 4.07/0.98      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 4.07/0.98      | r1_tarski(X1,X0) != iProver_top
% 4.07/0.98      | r1_tarski(k1_tops_1(sK1,X1),k1_tops_1(sK1,X0)) = iProver_top ),
% 4.07/0.98      inference(predicate_to_equality,[status(thm)],[c_297]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_7,plain,
% 4.07/0.98      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 4.07/0.98      inference(cnf_transformation,[],[f40]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_808,plain,
% 4.07/0.98      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 4.07/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_1330,plain,
% 4.07/0.98      ( k2_xboole_0(k1_tops_1(sK1,X0),k1_tops_1(sK1,X1)) = k1_tops_1(sK1,X1)
% 4.07/0.98      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 4.07/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 4.07/0.98      | r1_tarski(X0,X1) != iProver_top ),
% 4.07/0.98      inference(superposition,[status(thm)],[c_801,c_808]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_1338,plain,
% 4.07/0.98      ( k2_xboole_0(k1_tops_1(sK1,sK3),k1_tops_1(sK1,X0)) = k1_tops_1(sK1,X0)
% 4.07/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 4.07/0.98      | r1_tarski(sK3,X0) != iProver_top ),
% 4.07/0.98      inference(superposition,[status(thm)],[c_803,c_1330]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_4921,plain,
% 4.07/0.98      ( k2_xboole_0(k1_tops_1(sK1,sK3),k1_tops_1(sK1,k2_xboole_0(sK3,sK4))) = k1_tops_1(sK1,k2_xboole_0(sK3,sK4))
% 4.07/0.98      | r1_tarski(sK3,k2_xboole_0(sK3,sK4)) != iProver_top ),
% 4.07/0.98      inference(superposition,[status(thm)],[c_4914,c_1338]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_4955,plain,
% 4.07/0.98      ( k2_xboole_0(k1_tops_1(sK1,sK3),k1_tops_1(sK1,k2_xboole_0(sK3,sK4))) = k1_tops_1(sK1,k2_xboole_0(sK3,sK4)) ),
% 4.07/0.98      inference(superposition,[status(thm)],[c_807,c_4921]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_5,plain,
% 4.07/0.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
% 4.07/0.98      inference(cnf_transformation,[],[f57]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_810,plain,
% 4.07/0.98      ( r2_hidden(X0,X1) != iProver_top
% 4.07/0.98      | r2_hidden(X0,k2_xboole_0(X1,X2)) = iProver_top ),
% 4.07/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_5286,plain,
% 4.07/0.98      ( r2_hidden(X0,k1_tops_1(sK1,k2_xboole_0(sK3,sK4))) = iProver_top
% 4.07/0.98      | r2_hidden(X0,k1_tops_1(sK1,sK3)) != iProver_top ),
% 4.07/0.98      inference(superposition,[status(thm)],[c_4955,c_810]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_14,negated_conjecture,
% 4.07/0.98      ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK1),sK3,sK4),sK1,sK2) ),
% 4.07/0.98      inference(cnf_transformation,[],[f55]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_12,plain,
% 4.07/0.98      ( m1_connsp_2(X0,X1,X2)
% 4.07/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 4.07/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.07/0.98      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 4.07/0.98      | v2_struct_0(X1)
% 4.07/0.98      | ~ v2_pre_topc(X1)
% 4.07/0.98      | ~ l1_pre_topc(X1) ),
% 4.07/0.98      inference(cnf_transformation,[],[f46]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_21,negated_conjecture,
% 4.07/0.98      ( v2_pre_topc(sK1) ),
% 4.07/0.98      inference(cnf_transformation,[],[f48]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_262,plain,
% 4.07/0.98      ( m1_connsp_2(X0,X1,X2)
% 4.07/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 4.07/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.07/0.98      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 4.07/0.98      | v2_struct_0(X1)
% 4.07/0.98      | ~ l1_pre_topc(X1)
% 4.07/0.98      | sK1 != X1 ),
% 4.07/0.98      inference(resolution_lifted,[status(thm)],[c_12,c_21]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_263,plain,
% 4.07/0.98      ( m1_connsp_2(X0,sK1,X1)
% 4.07/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 4.07/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 4.07/0.98      | ~ r2_hidden(X1,k1_tops_1(sK1,X0))
% 4.07/0.98      | v2_struct_0(sK1)
% 4.07/0.98      | ~ l1_pre_topc(sK1) ),
% 4.07/0.98      inference(unflattening,[status(thm)],[c_262]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_22,negated_conjecture,
% 4.07/0.98      ( ~ v2_struct_0(sK1) ),
% 4.07/0.98      inference(cnf_transformation,[],[f47]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_267,plain,
% 4.07/0.98      ( m1_connsp_2(X0,sK1,X1)
% 4.07/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 4.07/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 4.07/0.98      | ~ r2_hidden(X1,k1_tops_1(sK1,X0)) ),
% 4.07/0.98      inference(global_propositional_subsumption,
% 4.07/0.98                [status(thm)],
% 4.07/0.98                [c_263,c_22,c_20]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_340,plain,
% 4.07/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 4.07/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 4.07/0.98      | ~ r2_hidden(X0,k1_tops_1(sK1,X1))
% 4.07/0.98      | k4_subset_1(u1_struct_0(sK1),sK3,sK4) != X1
% 4.07/0.98      | sK2 != X0
% 4.07/0.98      | sK1 != sK1 ),
% 4.07/0.98      inference(resolution_lifted,[status(thm)],[c_14,c_267]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_341,plain,
% 4.07/0.98      ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
% 4.07/0.98      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 4.07/0.98      | ~ r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) ),
% 4.07/0.98      inference(unflattening,[status(thm)],[c_340]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_19,negated_conjecture,
% 4.07/0.98      ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 4.07/0.98      inference(cnf_transformation,[],[f50]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_343,plain,
% 4.07/0.98      ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
% 4.07/0.98      | ~ r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) ),
% 4.07/0.98      inference(global_propositional_subsumption,
% 4.07/0.98                [status(thm)],
% 4.07/0.98                [c_341,c_19]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_800,plain,
% 4.07/0.98      ( m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 4.07/0.98      | r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) != iProver_top ),
% 4.07/0.98      inference(predicate_to_equality,[status(thm)],[c_343]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_26,plain,
% 4.07/0.98      ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
% 4.07/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_342,plain,
% 4.07/0.98      ( m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 4.07/0.98      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 4.07/0.98      | r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) != iProver_top ),
% 4.07/0.98      inference(predicate_to_equality,[status(thm)],[c_341]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_839,plain,
% 4.07/0.98      ( m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
% 4.07/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 4.07/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 4.07/0.98      inference(instantiation,[status(thm)],[c_9]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_840,plain,
% 4.07/0.98      ( m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 4.07/0.98      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 4.07/0.98      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 4.07/0.98      inference(predicate_to_equality,[status(thm)],[c_839]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_1043,plain,
% 4.07/0.98      ( r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) != iProver_top ),
% 4.07/0.98      inference(global_propositional_subsumption,
% 4.07/0.98                [status(thm)],
% 4.07/0.98                [c_800,c_26,c_27,c_28,c_342,c_840]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_4076,plain,
% 4.07/0.98      ( r2_hidden(sK2,k1_tops_1(sK1,k2_xboole_0(sK3,sK4))) != iProver_top ),
% 4.07/0.98      inference(demodulation,[status(thm)],[c_4029,c_1043]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_13190,plain,
% 4.07/0.98      ( r2_hidden(sK2,k1_tops_1(sK1,sK3)) != iProver_top ),
% 4.07/0.98      inference(superposition,[status(thm)],[c_5286,c_4076]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_16,negated_conjecture,
% 4.07/0.98      ( m1_connsp_2(sK3,sK1,sK2) ),
% 4.07/0.98      inference(cnf_transformation,[],[f53]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_13,plain,
% 4.07/0.98      ( ~ m1_connsp_2(X0,X1,X2)
% 4.07/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 4.07/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.07/0.98      | r2_hidden(X2,k1_tops_1(X1,X0))
% 4.07/0.98      | v2_struct_0(X1)
% 4.07/0.98      | ~ v2_pre_topc(X1)
% 4.07/0.98      | ~ l1_pre_topc(X1) ),
% 4.07/0.98      inference(cnf_transformation,[],[f45]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_238,plain,
% 4.07/0.98      ( ~ m1_connsp_2(X0,X1,X2)
% 4.07/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 4.07/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.07/0.98      | r2_hidden(X2,k1_tops_1(X1,X0))
% 4.07/0.98      | v2_struct_0(X1)
% 4.07/0.98      | ~ l1_pre_topc(X1)
% 4.07/0.98      | sK1 != X1 ),
% 4.07/0.98      inference(resolution_lifted,[status(thm)],[c_13,c_21]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_239,plain,
% 4.07/0.98      ( ~ m1_connsp_2(X0,sK1,X1)
% 4.07/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 4.07/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 4.07/0.98      | r2_hidden(X1,k1_tops_1(sK1,X0))
% 4.07/0.98      | v2_struct_0(sK1)
% 4.07/0.98      | ~ l1_pre_topc(sK1) ),
% 4.07/0.98      inference(unflattening,[status(thm)],[c_238]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_243,plain,
% 4.07/0.98      ( ~ m1_connsp_2(X0,sK1,X1)
% 4.07/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 4.07/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 4.07/0.98      | r2_hidden(X1,k1_tops_1(sK1,X0)) ),
% 4.07/0.98      inference(global_propositional_subsumption,
% 4.07/0.98                [status(thm)],
% 4.07/0.98                [c_239,c_22,c_20]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_365,plain,
% 4.07/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 4.07/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 4.07/0.98      | r2_hidden(X0,k1_tops_1(sK1,X1))
% 4.07/0.98      | sK2 != X0
% 4.07/0.98      | sK3 != X1
% 4.07/0.98      | sK1 != sK1 ),
% 4.07/0.98      inference(resolution_lifted,[status(thm)],[c_16,c_243]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_366,plain,
% 4.07/0.98      ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 4.07/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 4.07/0.98      | r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
% 4.07/0.98      inference(unflattening,[status(thm)],[c_365]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_367,plain,
% 4.07/0.98      ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 4.07/0.98      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 4.07/0.98      | r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top ),
% 4.07/0.98      inference(predicate_to_equality,[status(thm)],[c_366]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(contradiction,plain,
% 4.07/0.98      ( $false ),
% 4.07/0.98      inference(minisat,[status(thm)],[c_13190,c_367,c_27,c_26]) ).
% 4.07/0.98  
% 4.07/0.98  
% 4.07/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 4.07/0.98  
% 4.07/0.98  ------                               Statistics
% 4.07/0.98  
% 4.07/0.98  ------ General
% 4.07/0.98  
% 4.07/0.98  abstr_ref_over_cycles:                  0
% 4.07/0.98  abstr_ref_under_cycles:                 0
% 4.07/0.98  gc_basic_clause_elim:                   0
% 4.07/0.98  forced_gc_time:                         0
% 4.07/0.98  parsing_time:                           0.008
% 4.07/0.98  unif_index_cands_time:                  0.
% 4.07/0.98  unif_index_add_time:                    0.
% 4.07/0.98  orderings_time:                         0.
% 4.07/0.98  out_proof_time:                         0.022
% 4.07/0.98  total_time:                             0.459
% 4.07/0.98  num_of_symbols:                         48
% 4.07/0.98  num_of_terms:                           19519
% 4.07/0.98  
% 4.07/0.98  ------ Preprocessing
% 4.07/0.98  
% 4.07/0.98  num_of_splits:                          0
% 4.07/0.98  num_of_split_atoms:                     0
% 4.07/0.98  num_of_reused_defs:                     0
% 4.07/0.98  num_eq_ax_congr_red:                    17
% 4.07/0.98  num_of_sem_filtered_clauses:            1
% 4.07/0.98  num_of_subtypes:                        0
% 4.07/0.98  monotx_restored_types:                  0
% 4.07/0.98  sat_num_of_epr_types:                   0
% 4.07/0.98  sat_num_of_non_cyclic_types:            0
% 4.07/0.98  sat_guarded_non_collapsed_types:        0
% 4.07/0.98  num_pure_diseq_elim:                    0
% 4.07/0.98  simp_replaced_by:                       0
% 4.07/0.98  res_preprocessed:                       102
% 4.07/0.98  prep_upred:                             0
% 4.07/0.98  prep_unflattend:                        9
% 4.07/0.98  smt_new_axioms:                         0
% 4.07/0.98  pred_elim_cands:                        3
% 4.07/0.98  pred_elim:                              4
% 4.07/0.98  pred_elim_cl:                           3
% 4.07/0.98  pred_elim_cycles:                       6
% 4.07/0.98  merged_defs:                            0
% 4.07/0.98  merged_defs_ncl:                        0
% 4.07/0.98  bin_hyper_res:                          0
% 4.07/0.98  prep_cycles:                            4
% 4.07/0.98  pred_elim_time:                         0.003
% 4.07/0.98  splitting_time:                         0.
% 4.07/0.98  sem_filter_time:                        0.
% 4.07/0.98  monotx_time:                            0.
% 4.07/0.98  subtype_inf_time:                       0.
% 4.07/0.98  
% 4.07/0.98  ------ Problem properties
% 4.07/0.98  
% 4.07/0.98  clauses:                                20
% 4.07/0.98  conjectures:                            3
% 4.07/0.98  epr:                                    0
% 4.07/0.98  horn:                                   18
% 4.07/0.98  ground:                                 8
% 4.07/0.98  unary:                                  9
% 4.07/0.98  binary:                                 4
% 4.07/0.98  lits:                                   40
% 4.07/0.98  lits_eq:                                8
% 4.07/0.98  fd_pure:                                0
% 4.07/0.98  fd_pseudo:                              0
% 4.07/0.98  fd_cond:                                0
% 4.07/0.98  fd_pseudo_cond:                         3
% 4.07/0.98  ac_symbols:                             0
% 4.07/0.98  
% 4.07/0.98  ------ Propositional Solver
% 4.07/0.98  
% 4.07/0.98  prop_solver_calls:                      33
% 4.07/0.98  prop_fast_solver_calls:                 893
% 4.07/0.98  smt_solver_calls:                       0
% 4.07/0.98  smt_fast_solver_calls:                  0
% 4.07/0.98  prop_num_of_clauses:                    5634
% 4.07/0.98  prop_preprocess_simplified:             8789
% 4.07/0.98  prop_fo_subsumed:                       28
% 4.07/0.98  prop_solver_time:                       0.
% 4.07/0.98  smt_solver_time:                        0.
% 4.07/0.98  smt_fast_solver_time:                   0.
% 4.07/0.98  prop_fast_solver_time:                  0.
% 4.07/0.98  prop_unsat_core_time:                   0.
% 4.07/0.98  
% 4.07/0.98  ------ QBF
% 4.07/0.98  
% 4.07/0.98  qbf_q_res:                              0
% 4.07/0.98  qbf_num_tautologies:                    0
% 4.07/0.98  qbf_prep_cycles:                        0
% 4.07/0.98  
% 4.07/0.98  ------ BMC1
% 4.07/0.98  
% 4.07/0.98  bmc1_current_bound:                     -1
% 4.07/0.98  bmc1_last_solved_bound:                 -1
% 4.07/0.98  bmc1_unsat_core_size:                   -1
% 4.07/0.98  bmc1_unsat_core_parents_size:           -1
% 4.07/0.98  bmc1_merge_next_fun:                    0
% 4.07/0.98  bmc1_unsat_core_clauses_time:           0.
% 4.07/0.98  
% 4.07/0.98  ------ Instantiation
% 4.07/0.98  
% 4.07/0.98  inst_num_of_clauses:                    1349
% 4.07/0.98  inst_num_in_passive:                    90
% 4.07/0.98  inst_num_in_active:                     741
% 4.07/0.98  inst_num_in_unprocessed:                518
% 4.07/0.98  inst_num_of_loops:                      810
% 4.07/0.98  inst_num_of_learning_restarts:          0
% 4.07/0.98  inst_num_moves_active_passive:          65
% 4.07/0.98  inst_lit_activity:                      0
% 4.07/0.98  inst_lit_activity_moves:                1
% 4.07/0.98  inst_num_tautologies:                   0
% 4.07/0.98  inst_num_prop_implied:                  0
% 4.07/0.98  inst_num_existing_simplified:           0
% 4.07/0.98  inst_num_eq_res_simplified:             0
% 4.07/0.98  inst_num_child_elim:                    0
% 4.07/0.98  inst_num_of_dismatching_blockings:      2734
% 4.07/0.98  inst_num_of_non_proper_insts:           1549
% 4.07/0.98  inst_num_of_duplicates:                 0
% 4.07/0.98  inst_inst_num_from_inst_to_res:         0
% 4.07/0.98  inst_dismatching_checking_time:         0.
% 4.07/0.98  
% 4.07/0.98  ------ Resolution
% 4.07/0.98  
% 4.07/0.98  res_num_of_clauses:                     0
% 4.07/0.98  res_num_in_passive:                     0
% 4.07/0.98  res_num_in_active:                      0
% 4.07/0.98  res_num_of_loops:                       106
% 4.07/0.98  res_forward_subset_subsumed:            82
% 4.07/0.98  res_backward_subset_subsumed:           0
% 4.07/0.98  res_forward_subsumed:                   0
% 4.07/0.98  res_backward_subsumed:                  0
% 4.07/0.98  res_forward_subsumption_resolution:     0
% 4.07/0.98  res_backward_subsumption_resolution:    0
% 4.07/0.98  res_clause_to_clause_subsumption:       2972
% 4.07/0.98  res_orphan_elimination:                 0
% 4.07/0.98  res_tautology_del:                      64
% 4.07/0.98  res_num_eq_res_simplified:              2
% 4.07/0.98  res_num_sel_changes:                    0
% 4.07/0.98  res_moves_from_active_to_pass:          0
% 4.07/0.98  
% 4.07/0.98  ------ Superposition
% 4.07/0.98  
% 4.07/0.98  sup_time_total:                         0.
% 4.07/0.98  sup_time_generating:                    0.
% 4.07/0.98  sup_time_sim_full:                      0.
% 4.07/0.98  sup_time_sim_immed:                     0.
% 4.07/0.98  
% 4.07/0.98  sup_num_of_clauses:                     500
% 4.07/0.98  sup_num_in_active:                      145
% 4.07/0.98  sup_num_in_passive:                     355
% 4.07/0.98  sup_num_of_loops:                       161
% 4.07/0.98  sup_fw_superposition:                   504
% 4.07/0.98  sup_bw_superposition:                   638
% 4.07/0.98  sup_immediate_simplified:               760
% 4.07/0.98  sup_given_eliminated:                   5
% 4.07/0.98  comparisons_done:                       0
% 4.07/0.98  comparisons_avoided:                    0
% 4.07/0.98  
% 4.07/0.98  ------ Simplifications
% 4.07/0.98  
% 4.07/0.98  
% 4.07/0.98  sim_fw_subset_subsumed:                 8
% 4.07/0.98  sim_bw_subset_subsumed:                 34
% 4.07/0.98  sim_fw_subsumed:                        125
% 4.07/0.98  sim_bw_subsumed:                        0
% 4.07/0.98  sim_fw_subsumption_res:                 0
% 4.07/0.98  sim_bw_subsumption_res:                 0
% 4.07/0.98  sim_tautology_del:                      52
% 4.07/0.98  sim_eq_tautology_del:                   110
% 4.07/0.98  sim_eq_res_simp:                        6
% 4.07/0.98  sim_fw_demodulated:                     367
% 4.07/0.98  sim_bw_demodulated:                     51
% 4.07/0.98  sim_light_normalised:                   479
% 4.07/0.98  sim_joinable_taut:                      0
% 4.07/0.98  sim_joinable_simp:                      0
% 4.07/0.98  sim_ac_normalised:                      0
% 4.07/0.98  sim_smt_subsumption:                    0
% 4.07/0.98  
%------------------------------------------------------------------------------
