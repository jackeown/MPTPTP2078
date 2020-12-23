%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:18:15 EST 2020

% Result     : Theorem 2.31s
% Output     : CNFRefutation 2.31s
% Verified   : 
% Statistics : Number of formulae       :  172 ( 687 expanded)
%              Number of clauses        :  114 ( 202 expanded)
%              Number of leaves         :   16 ( 193 expanded)
%              Depth                    :   20
%              Number of atoms          :  689 (5405 expanded)
%              Number of equality atoms :  146 ( 233 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
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

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f35,plain,(
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
            ( ~ r1_tarski(X3,sK3)
            | ~ v3_pre_topc(X3,X0)
            | ~ m1_connsp_2(X3,X0,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
            | v1_xboole_0(X3) )
        & m1_connsp_2(sK3,X0,X1)
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
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
                | ~ m1_connsp_2(X3,X0,sK2)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                | v1_xboole_0(X3) )
            & m1_connsp_2(X2,X0,sK2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
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
                  | ~ v3_pre_topc(X3,sK1)
                  | ~ m1_connsp_2(X3,sK1,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))
                  | v1_xboole_0(X3) )
              & m1_connsp_2(X2,sK1,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) )
          & m1_subset_1(X1,u1_struct_0(sK1)) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ! [X3] :
        ( ~ r1_tarski(X3,sK3)
        | ~ v3_pre_topc(X3,sK1)
        | ~ m1_connsp_2(X3,sK1,sK2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))
        | v1_xboole_0(X3) )
    & m1_connsp_2(sK3,sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f24,f35,f34,f33])).

fof(f57,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f36])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f55,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
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
    inference(nnf_transformation,[],[f12])).

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

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f37,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f60,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f41])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f7,axiom,(
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

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f54,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X2,X0)
      | k1_tops_1(X0,X2) != X2
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f58,plain,(
    m1_connsp_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f36])).

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
    inference(ennf_transformation,[],[f8])).

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

fof(f32,plain,(
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

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

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

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f53,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f56,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f36])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f59,plain,(
    ! [X3] :
      ( ~ r1_tarski(X3,sK3)
      | ~ v3_pre_topc(X3,sK1)
      | ~ m1_connsp_2(X3,sK1,sK2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))
      | v1_xboole_0(X3) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f15,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1691,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1692,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2221,plain,
    ( r1_tarski(sK3,u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1691,c_1692])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_20,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_518,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_20])).

cnf(c_519,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(k1_tops_1(sK1,X0),X0) ),
    inference(unflattening,[status(thm)],[c_518])).

cnf(c_1684,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(k1_tops_1(sK1,X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_519])).

cnf(c_1895,plain,
    ( r1_tarski(k1_tops_1(sK1,sK3),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1691,c_1684])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1697,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1696,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2987,plain,
    ( r2_hidden(sK0(X0,X1),X2) = iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1697,c_1696])).

cnf(c_4393,plain,
    ( r2_hidden(sK0(X0,X1),X2) = iProver_top
    | r1_tarski(X0,X3) != iProver_top
    | r1_tarski(X3,X2) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2987,c_1696])).

cnf(c_4624,plain,
    ( r2_hidden(sK0(k1_tops_1(sK1,sK3),X0),X1) = iProver_top
    | r1_tarski(k1_tops_1(sK1,sK3),X0) = iProver_top
    | r1_tarski(sK3,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1895,c_4393])).

cnf(c_4775,plain,
    ( r2_hidden(sK0(k1_tops_1(sK1,sK3),X0),X1) = iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(k1_tops_1(sK1,sK3),X0) = iProver_top
    | r1_tarski(sK3,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4624,c_1696])).

cnf(c_5583,plain,
    ( r2_hidden(sK0(k1_tops_1(sK1,sK3),X0),u1_struct_0(sK1)) = iProver_top
    | r1_tarski(k1_tops_1(sK1,sK3),X0) = iProver_top
    | r1_tarski(sK3,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2221,c_4775])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2823,plain,
    ( r1_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2826,plain,
    ( r1_tarski(sK3,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2823])).

cnf(c_5732,plain,
    ( r1_tarski(k1_tops_1(sK1,sK3),X0) = iProver_top
    | r2_hidden(sK0(k1_tops_1(sK1,sK3),X0),u1_struct_0(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5583,c_2826])).

cnf(c_5733,plain,
    ( r2_hidden(sK0(k1_tops_1(sK1,sK3),X0),u1_struct_0(sK1)) = iProver_top
    | r1_tarski(k1_tops_1(sK1,sK3),X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_5732])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1698,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_5740,plain,
    ( r1_tarski(k1_tops_1(sK1,sK3),u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5733,c_1698])).

cnf(c_4773,plain,
    ( r1_tarski(k1_tops_1(sK1,sK3),X0) = iProver_top
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4624,c_1698])).

cnf(c_6,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1693,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_12,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_21,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_460,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X1,X0) = X0
    | sK1 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_21])).

cnf(c_461,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK1)
    | k1_tops_1(X1,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_460])).

cnf(c_465,plain,
    ( ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X0,X1)
    | k1_tops_1(X1,X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_461,c_20])).

cnf(c_466,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = X0 ),
    inference(renaming,[status(thm)],[c_465])).

cnf(c_500,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(X1,X0) = X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_466,c_20])).

cnf(c_501,plain,
    ( ~ v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_500])).

cnf(c_1193,plain,
    ( ~ v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,X0) = X0
    | ~ sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP2_iProver_split])],[c_501])).

cnf(c_1686,plain,
    ( k1_tops_1(sK1,X0) = X0
    | v3_pre_topc(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1193])).

cnf(c_1194,plain,
    ( sP2_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_501])).

cnf(c_1225,plain,
    ( sP2_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1194])).

cnf(c_1226,plain,
    ( k1_tops_1(sK1,X0) = X0
    | v3_pre_topc(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1193])).

cnf(c_11,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_435,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X1,X0) != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_21])).

cnf(c_436,plain,
    ( v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(sK1)
    | k1_tops_1(sK1,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_435])).

cnf(c_440,plain,
    ( ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | v3_pre_topc(X0,sK1)
    | k1_tops_1(sK1,X0) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_436,c_20])).

cnf(c_441,plain,
    ( v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(X2)
    | k1_tops_1(sK1,X0) != X0 ),
    inference(renaming,[status(thm)],[c_440])).

cnf(c_530,plain,
    ( v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,X0) != X0
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_441])).

cnf(c_531,plain,
    ( v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_530])).

cnf(c_1190,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_531])).

cnf(c_1683,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1190])).

cnf(c_1861,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_1691,c_1683])).

cnf(c_2552,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v3_pre_topc(X0,sK1) != iProver_top
    | k1_tops_1(sK1,X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1686,c_1225,c_1226,c_1861])).

cnf(c_2553,plain,
    ( k1_tops_1(sK1,X0) = X0
    | v3_pre_topc(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2552])).

cnf(c_2559,plain,
    ( k1_tops_1(sK1,X0) = X0
    | v3_pre_topc(X0,sK1) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1693,c_2553])).

cnf(c_4940,plain,
    ( k1_tops_1(sK1,k1_tops_1(sK1,sK3)) = k1_tops_1(sK1,sK3)
    | v3_pre_topc(k1_tops_1(sK1,sK3),sK1) != iProver_top
    | r1_tarski(sK3,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4773,c_2559])).

cnf(c_1694,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_17,negated_conjecture,
    ( m1_connsp_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_14,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_15,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_127,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X0,X1,X2)
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14,c_15])).

cnf(c_128,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_127])).

cnf(c_22,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_338,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_128,c_22])).

cnf(c_339,plain,
    ( ~ m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | r2_hidden(X1,k1_tops_1(sK1,X0))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_338])).

cnf(c_343,plain,
    ( ~ m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | r2_hidden(X1,k1_tops_1(sK1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_339,c_21,c_20])).

cnf(c_687,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | r2_hidden(X0,k1_tops_1(sK1,X1))
    | sK2 != X0
    | sK1 != sK1
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_343])).

cnf(c_688,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
    inference(unflattening,[status(thm)],[c_687])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_690,plain,
    ( r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_688,c_19])).

cnf(c_1678,plain,
    ( r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_690])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_175,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_6])).

cnf(c_176,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_175])).

cnf(c_226,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(bin_hyper_res,[status(thm)],[c_8,c_176])).

cnf(c_1689,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_226])).

cnf(c_3455,plain,
    ( r1_tarski(k1_tops_1(sK1,sK3),X0) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1678,c_1689])).

cnf(c_4001,plain,
    ( v1_xboole_0(k1_tops_1(sK1,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1694,c_3455])).

cnf(c_1199,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1874,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | X1 != k1_tops_1(sK1,sK3)
    | X0 != sK2 ),
    inference(instantiation,[status(thm)],[c_1199])).

cnf(c_2020,plain,
    ( r2_hidden(sK2,X0)
    | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | X0 != k1_tops_1(sK1,sK3)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1874])).

cnf(c_3217,plain,
    ( r2_hidden(sK2,k1_tops_1(sK1,k1_tops_1(sK1,sK3)))
    | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | k1_tops_1(sK1,k1_tops_1(sK1,sK3)) != k1_tops_1(sK1,sK3)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_2020])).

cnf(c_3221,plain,
    ( k1_tops_1(sK1,k1_tops_1(sK1,sK3)) != k1_tops_1(sK1,sK3)
    | sK2 != sK2
    | r2_hidden(sK2,k1_tops_1(sK1,k1_tops_1(sK1,sK3))) = iProver_top
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3217])).

cnf(c_1846,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X0,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2155,plain,
    ( m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(k1_tops_1(sK1,sK3),u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1846])).

cnf(c_2156,plain,
    ( m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | r1_tarski(k1_tops_1(sK1,sK3),u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2155])).

cnf(c_1196,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1908,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1196])).

cnf(c_16,negated_conjecture,
    ( ~ m1_connsp_2(X0,sK1,sK2)
    | ~ v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X0,sK3)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_13,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_380,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_22])).

cnf(c_381,plain,
    ( m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X1,k1_tops_1(sK1,X0))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_380])).

cnf(c_385,plain,
    ( m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X1,k1_tops_1(sK1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_381,c_21,c_20])).

cnf(c_658,plain,
    ( ~ v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X1,k1_tops_1(sK1,X2))
    | ~ r1_tarski(X0,sK3)
    | v1_xboole_0(X0)
    | X2 != X0
    | sK2 != X1
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_385])).

cnf(c_659,plain,
    ( ~ v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ r2_hidden(sK2,k1_tops_1(sK1,X0))
    | ~ r1_tarski(X0,sK3)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_658])).

cnf(c_663,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v3_pre_topc(X0,sK1)
    | ~ r2_hidden(sK2,k1_tops_1(sK1,X0))
    | ~ r1_tarski(X0,sK3)
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_659,c_19])).

cnf(c_664,plain,
    ( ~ v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK2,k1_tops_1(sK1,X0))
    | ~ r1_tarski(X0,sK3)
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_663])).

cnf(c_1884,plain,
    ( ~ v3_pre_topc(k1_tops_1(sK1,sK3),sK1)
    | ~ m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK2,k1_tops_1(sK1,k1_tops_1(sK1,sK3)))
    | ~ r1_tarski(k1_tops_1(sK1,sK3),sK3)
    | v1_xboole_0(k1_tops_1(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_664])).

cnf(c_1888,plain,
    ( v3_pre_topc(k1_tops_1(sK1,sK3),sK1) != iProver_top
    | m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(sK2,k1_tops_1(sK1,k1_tops_1(sK1,sK3))) != iProver_top
    | r1_tarski(k1_tops_1(sK1,sK3),sK3) != iProver_top
    | v1_xboole_0(k1_tops_1(sK1,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1884])).

cnf(c_1836,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(k1_tops_1(sK1,sK3),sK3) ),
    inference(instantiation,[status(thm)],[c_519])).

cnf(c_1837,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(k1_tops_1(sK1,sK3),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1836])).

cnf(c_9,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_417,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_21])).

cnf(c_418,plain,
    ( v3_pre_topc(k1_tops_1(sK1,X0),sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_417])).

cnf(c_422,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v3_pre_topc(k1_tops_1(sK1,X0),sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_418,c_20])).

cnf(c_423,plain,
    ( v3_pre_topc(k1_tops_1(sK1,X0),sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(renaming,[status(thm)],[c_422])).

cnf(c_1833,plain,
    ( v3_pre_topc(k1_tops_1(sK1,sK3),sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_423])).

cnf(c_1834,plain,
    ( v3_pre_topc(k1_tops_1(sK1,sK3),sK1) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1833])).

cnf(c_689,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_688])).

cnf(c_27,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_26,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5740,c_4940,c_4001,c_3221,c_2221,c_2156,c_1908,c_1888,c_1837,c_1834,c_689,c_27,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n017.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 20:29:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.31/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/0.98  
% 2.31/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.31/0.98  
% 2.31/0.98  ------  iProver source info
% 2.31/0.98  
% 2.31/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.31/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.31/0.98  git: non_committed_changes: false
% 2.31/0.98  git: last_make_outside_of_git: false
% 2.31/0.98  
% 2.31/0.98  ------ 
% 2.31/0.98  
% 2.31/0.98  ------ Input Options
% 2.31/0.98  
% 2.31/0.98  --out_options                           all
% 2.31/0.98  --tptp_safe_out                         true
% 2.31/0.98  --problem_path                          ""
% 2.31/0.98  --include_path                          ""
% 2.31/0.98  --clausifier                            res/vclausify_rel
% 2.31/0.98  --clausifier_options                    --mode clausify
% 2.31/0.98  --stdin                                 false
% 2.31/0.98  --stats_out                             all
% 2.31/0.98  
% 2.31/0.98  ------ General Options
% 2.31/0.98  
% 2.31/0.98  --fof                                   false
% 2.31/0.98  --time_out_real                         305.
% 2.31/0.98  --time_out_virtual                      -1.
% 2.31/0.98  --symbol_type_check                     false
% 2.31/0.98  --clausify_out                          false
% 2.31/0.98  --sig_cnt_out                           false
% 2.31/0.98  --trig_cnt_out                          false
% 2.31/0.98  --trig_cnt_out_tolerance                1.
% 2.31/0.98  --trig_cnt_out_sk_spl                   false
% 2.31/0.98  --abstr_cl_out                          false
% 2.31/0.98  
% 2.31/0.98  ------ Global Options
% 2.31/0.98  
% 2.31/0.98  --schedule                              default
% 2.31/0.98  --add_important_lit                     false
% 2.31/0.98  --prop_solver_per_cl                    1000
% 2.31/0.98  --min_unsat_core                        false
% 2.31/0.98  --soft_assumptions                      false
% 2.31/0.98  --soft_lemma_size                       3
% 2.31/0.98  --prop_impl_unit_size                   0
% 2.31/0.98  --prop_impl_unit                        []
% 2.31/0.98  --share_sel_clauses                     true
% 2.31/0.98  --reset_solvers                         false
% 2.31/0.98  --bc_imp_inh                            [conj_cone]
% 2.31/0.98  --conj_cone_tolerance                   3.
% 2.31/0.98  --extra_neg_conj                        none
% 2.31/0.98  --large_theory_mode                     true
% 2.31/0.98  --prolific_symb_bound                   200
% 2.31/0.98  --lt_threshold                          2000
% 2.31/0.98  --clause_weak_htbl                      true
% 2.31/0.98  --gc_record_bc_elim                     false
% 2.31/0.98  
% 2.31/0.98  ------ Preprocessing Options
% 2.31/0.98  
% 2.31/0.98  --preprocessing_flag                    true
% 2.31/0.98  --time_out_prep_mult                    0.1
% 2.31/0.98  --splitting_mode                        input
% 2.31/0.98  --splitting_grd                         true
% 2.31/0.98  --splitting_cvd                         false
% 2.31/0.98  --splitting_cvd_svl                     false
% 2.31/0.98  --splitting_nvd                         32
% 2.31/0.98  --sub_typing                            true
% 2.31/0.98  --prep_gs_sim                           true
% 2.31/0.98  --prep_unflatten                        true
% 2.31/0.98  --prep_res_sim                          true
% 2.31/0.98  --prep_upred                            true
% 2.31/0.98  --prep_sem_filter                       exhaustive
% 2.31/0.98  --prep_sem_filter_out                   false
% 2.31/0.98  --pred_elim                             true
% 2.31/0.98  --res_sim_input                         true
% 2.31/0.98  --eq_ax_congr_red                       true
% 2.31/0.98  --pure_diseq_elim                       true
% 2.31/0.98  --brand_transform                       false
% 2.31/0.98  --non_eq_to_eq                          false
% 2.31/0.98  --prep_def_merge                        true
% 2.31/0.98  --prep_def_merge_prop_impl              false
% 2.31/0.98  --prep_def_merge_mbd                    true
% 2.31/0.98  --prep_def_merge_tr_red                 false
% 2.31/0.98  --prep_def_merge_tr_cl                  false
% 2.31/0.98  --smt_preprocessing                     true
% 2.31/0.98  --smt_ac_axioms                         fast
% 2.31/0.98  --preprocessed_out                      false
% 2.31/0.98  --preprocessed_stats                    false
% 2.31/0.98  
% 2.31/0.98  ------ Abstraction refinement Options
% 2.31/0.98  
% 2.31/0.98  --abstr_ref                             []
% 2.31/0.98  --abstr_ref_prep                        false
% 2.31/0.98  --abstr_ref_until_sat                   false
% 2.31/0.98  --abstr_ref_sig_restrict                funpre
% 2.31/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.31/0.98  --abstr_ref_under                       []
% 2.31/0.98  
% 2.31/0.98  ------ SAT Options
% 2.31/0.98  
% 2.31/0.98  --sat_mode                              false
% 2.31/0.98  --sat_fm_restart_options                ""
% 2.31/0.98  --sat_gr_def                            false
% 2.31/0.98  --sat_epr_types                         true
% 2.31/0.98  --sat_non_cyclic_types                  false
% 2.31/0.98  --sat_finite_models                     false
% 2.31/0.98  --sat_fm_lemmas                         false
% 2.31/0.98  --sat_fm_prep                           false
% 2.31/0.98  --sat_fm_uc_incr                        true
% 2.31/0.98  --sat_out_model                         small
% 2.31/0.98  --sat_out_clauses                       false
% 2.31/0.98  
% 2.31/0.98  ------ QBF Options
% 2.31/0.98  
% 2.31/0.98  --qbf_mode                              false
% 2.31/0.98  --qbf_elim_univ                         false
% 2.31/0.98  --qbf_dom_inst                          none
% 2.31/0.98  --qbf_dom_pre_inst                      false
% 2.31/0.98  --qbf_sk_in                             false
% 2.31/0.98  --qbf_pred_elim                         true
% 2.31/0.98  --qbf_split                             512
% 2.31/0.98  
% 2.31/0.98  ------ BMC1 Options
% 2.31/0.98  
% 2.31/0.98  --bmc1_incremental                      false
% 2.31/0.98  --bmc1_axioms                           reachable_all
% 2.31/0.98  --bmc1_min_bound                        0
% 2.31/0.98  --bmc1_max_bound                        -1
% 2.31/0.98  --bmc1_max_bound_default                -1
% 2.31/0.98  --bmc1_symbol_reachability              true
% 2.31/0.98  --bmc1_property_lemmas                  false
% 2.31/0.98  --bmc1_k_induction                      false
% 2.31/0.98  --bmc1_non_equiv_states                 false
% 2.31/0.98  --bmc1_deadlock                         false
% 2.31/0.98  --bmc1_ucm                              false
% 2.31/0.98  --bmc1_add_unsat_core                   none
% 2.31/0.98  --bmc1_unsat_core_children              false
% 2.31/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.31/0.98  --bmc1_out_stat                         full
% 2.31/0.98  --bmc1_ground_init                      false
% 2.31/0.98  --bmc1_pre_inst_next_state              false
% 2.31/0.98  --bmc1_pre_inst_state                   false
% 2.31/0.98  --bmc1_pre_inst_reach_state             false
% 2.31/0.98  --bmc1_out_unsat_core                   false
% 2.31/0.98  --bmc1_aig_witness_out                  false
% 2.31/0.98  --bmc1_verbose                          false
% 2.31/0.98  --bmc1_dump_clauses_tptp                false
% 2.31/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.31/0.98  --bmc1_dump_file                        -
% 2.31/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.31/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.31/0.98  --bmc1_ucm_extend_mode                  1
% 2.31/0.98  --bmc1_ucm_init_mode                    2
% 2.31/0.98  --bmc1_ucm_cone_mode                    none
% 2.31/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.31/0.98  --bmc1_ucm_relax_model                  4
% 2.31/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.31/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.31/0.98  --bmc1_ucm_layered_model                none
% 2.31/0.98  --bmc1_ucm_max_lemma_size               10
% 2.31/0.98  
% 2.31/0.98  ------ AIG Options
% 2.31/0.98  
% 2.31/0.98  --aig_mode                              false
% 2.31/0.98  
% 2.31/0.98  ------ Instantiation Options
% 2.31/0.98  
% 2.31/0.98  --instantiation_flag                    true
% 2.31/0.98  --inst_sos_flag                         false
% 2.31/0.98  --inst_sos_phase                        true
% 2.31/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.31/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.31/0.98  --inst_lit_sel_side                     num_symb
% 2.31/0.98  --inst_solver_per_active                1400
% 2.31/0.98  --inst_solver_calls_frac                1.
% 2.31/0.98  --inst_passive_queue_type               priority_queues
% 2.31/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.31/0.98  --inst_passive_queues_freq              [25;2]
% 2.31/0.98  --inst_dismatching                      true
% 2.31/0.98  --inst_eager_unprocessed_to_passive     true
% 2.31/0.98  --inst_prop_sim_given                   true
% 2.31/0.98  --inst_prop_sim_new                     false
% 2.31/0.98  --inst_subs_new                         false
% 2.31/0.98  --inst_eq_res_simp                      false
% 2.31/0.98  --inst_subs_given                       false
% 2.31/0.98  --inst_orphan_elimination               true
% 2.31/0.98  --inst_learning_loop_flag               true
% 2.31/0.98  --inst_learning_start                   3000
% 2.31/0.98  --inst_learning_factor                  2
% 2.31/0.98  --inst_start_prop_sim_after_learn       3
% 2.31/0.98  --inst_sel_renew                        solver
% 2.31/0.98  --inst_lit_activity_flag                true
% 2.31/0.98  --inst_restr_to_given                   false
% 2.31/0.98  --inst_activity_threshold               500
% 2.31/0.98  --inst_out_proof                        true
% 2.31/0.98  
% 2.31/0.98  ------ Resolution Options
% 2.31/0.98  
% 2.31/0.98  --resolution_flag                       true
% 2.31/0.98  --res_lit_sel                           adaptive
% 2.31/0.98  --res_lit_sel_side                      none
% 2.31/0.98  --res_ordering                          kbo
% 2.31/0.98  --res_to_prop_solver                    active
% 2.31/0.98  --res_prop_simpl_new                    false
% 2.31/0.98  --res_prop_simpl_given                  true
% 2.31/0.98  --res_passive_queue_type                priority_queues
% 2.31/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.31/0.98  --res_passive_queues_freq               [15;5]
% 2.31/0.98  --res_forward_subs                      full
% 2.31/0.98  --res_backward_subs                     full
% 2.31/0.98  --res_forward_subs_resolution           true
% 2.31/0.98  --res_backward_subs_resolution          true
% 2.31/0.98  --res_orphan_elimination                true
% 2.31/0.98  --res_time_limit                        2.
% 2.31/0.98  --res_out_proof                         true
% 2.31/0.98  
% 2.31/0.98  ------ Superposition Options
% 2.31/0.98  
% 2.31/0.98  --superposition_flag                    true
% 2.31/0.98  --sup_passive_queue_type                priority_queues
% 2.31/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.31/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.31/0.98  --demod_completeness_check              fast
% 2.31/0.98  --demod_use_ground                      true
% 2.31/0.98  --sup_to_prop_solver                    passive
% 2.31/0.98  --sup_prop_simpl_new                    true
% 2.31/0.98  --sup_prop_simpl_given                  true
% 2.31/0.98  --sup_fun_splitting                     false
% 2.31/0.98  --sup_smt_interval                      50000
% 2.31/0.98  
% 2.31/0.98  ------ Superposition Simplification Setup
% 2.31/0.98  
% 2.31/0.98  --sup_indices_passive                   []
% 2.31/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.31/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.31/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.31/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.31/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.31/0.98  --sup_full_bw                           [BwDemod]
% 2.31/0.98  --sup_immed_triv                        [TrivRules]
% 2.31/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.31/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.31/0.98  --sup_immed_bw_main                     []
% 2.31/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.31/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.31/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.31/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.31/0.98  
% 2.31/0.98  ------ Combination Options
% 2.31/0.98  
% 2.31/0.98  --comb_res_mult                         3
% 2.31/0.98  --comb_sup_mult                         2
% 2.31/0.98  --comb_inst_mult                        10
% 2.31/0.98  
% 2.31/0.98  ------ Debug Options
% 2.31/0.98  
% 2.31/0.98  --dbg_backtrace                         false
% 2.31/0.98  --dbg_dump_prop_clauses                 false
% 2.31/0.98  --dbg_dump_prop_clauses_file            -
% 2.31/0.98  --dbg_out_stat                          false
% 2.31/0.98  ------ Parsing...
% 2.31/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.31/0.98  
% 2.31/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 2.31/0.98  
% 2.31/0.98  ------ Preprocessing... gs_s  sp: 4 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.31/0.98  
% 2.31/0.98  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.31/0.98  ------ Proving...
% 2.31/0.98  ------ Problem Properties 
% 2.31/0.98  
% 2.31/0.98  
% 2.31/0.98  clauses                                 21
% 2.31/0.98  conjectures                             2
% 2.31/0.98  EPR                                     7
% 2.31/0.98  Horn                                    18
% 2.31/0.98  unary                                   4
% 2.31/0.98  binary                                  11
% 2.31/0.98  lits                                    48
% 2.31/0.98  lits eq                                 3
% 2.31/0.98  fd_pure                                 0
% 2.31/0.98  fd_pseudo                               0
% 2.31/0.98  fd_cond                                 0
% 2.31/0.98  fd_pseudo_cond                          1
% 2.31/0.98  AC symbols                              0
% 2.31/0.98  
% 2.31/0.98  ------ Schedule dynamic 5 is on 
% 2.31/0.98  
% 2.31/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.31/0.98  
% 2.31/0.98  
% 2.31/0.98  ------ 
% 2.31/0.98  Current options:
% 2.31/0.98  ------ 
% 2.31/0.98  
% 2.31/0.98  ------ Input Options
% 2.31/0.98  
% 2.31/0.98  --out_options                           all
% 2.31/0.98  --tptp_safe_out                         true
% 2.31/0.98  --problem_path                          ""
% 2.31/0.98  --include_path                          ""
% 2.31/0.98  --clausifier                            res/vclausify_rel
% 2.31/0.98  --clausifier_options                    --mode clausify
% 2.31/0.98  --stdin                                 false
% 2.31/0.98  --stats_out                             all
% 2.31/0.98  
% 2.31/0.98  ------ General Options
% 2.31/0.98  
% 2.31/0.98  --fof                                   false
% 2.31/0.98  --time_out_real                         305.
% 2.31/0.98  --time_out_virtual                      -1.
% 2.31/0.98  --symbol_type_check                     false
% 2.31/0.98  --clausify_out                          false
% 2.31/0.98  --sig_cnt_out                           false
% 2.31/0.98  --trig_cnt_out                          false
% 2.31/0.98  --trig_cnt_out_tolerance                1.
% 2.31/0.98  --trig_cnt_out_sk_spl                   false
% 2.31/0.98  --abstr_cl_out                          false
% 2.31/0.98  
% 2.31/0.98  ------ Global Options
% 2.31/0.98  
% 2.31/0.98  --schedule                              default
% 2.31/0.98  --add_important_lit                     false
% 2.31/0.98  --prop_solver_per_cl                    1000
% 2.31/0.98  --min_unsat_core                        false
% 2.31/0.98  --soft_assumptions                      false
% 2.31/0.98  --soft_lemma_size                       3
% 2.31/0.98  --prop_impl_unit_size                   0
% 2.31/0.98  --prop_impl_unit                        []
% 2.31/0.98  --share_sel_clauses                     true
% 2.31/0.98  --reset_solvers                         false
% 2.31/0.98  --bc_imp_inh                            [conj_cone]
% 2.31/0.98  --conj_cone_tolerance                   3.
% 2.31/0.98  --extra_neg_conj                        none
% 2.31/0.98  --large_theory_mode                     true
% 2.31/0.98  --prolific_symb_bound                   200
% 2.31/0.98  --lt_threshold                          2000
% 2.31/0.98  --clause_weak_htbl                      true
% 2.31/0.98  --gc_record_bc_elim                     false
% 2.31/0.98  
% 2.31/0.98  ------ Preprocessing Options
% 2.31/0.98  
% 2.31/0.98  --preprocessing_flag                    true
% 2.31/0.98  --time_out_prep_mult                    0.1
% 2.31/0.98  --splitting_mode                        input
% 2.31/0.98  --splitting_grd                         true
% 2.31/0.98  --splitting_cvd                         false
% 2.31/0.98  --splitting_cvd_svl                     false
% 2.31/0.98  --splitting_nvd                         32
% 2.31/0.98  --sub_typing                            true
% 2.31/0.98  --prep_gs_sim                           true
% 2.31/0.98  --prep_unflatten                        true
% 2.31/0.98  --prep_res_sim                          true
% 2.31/0.98  --prep_upred                            true
% 2.31/0.98  --prep_sem_filter                       exhaustive
% 2.31/0.98  --prep_sem_filter_out                   false
% 2.31/0.98  --pred_elim                             true
% 2.31/0.98  --res_sim_input                         true
% 2.31/0.98  --eq_ax_congr_red                       true
% 2.31/0.98  --pure_diseq_elim                       true
% 2.31/0.98  --brand_transform                       false
% 2.31/0.98  --non_eq_to_eq                          false
% 2.31/0.98  --prep_def_merge                        true
% 2.31/0.98  --prep_def_merge_prop_impl              false
% 2.31/0.98  --prep_def_merge_mbd                    true
% 2.31/0.98  --prep_def_merge_tr_red                 false
% 2.31/0.98  --prep_def_merge_tr_cl                  false
% 2.31/0.98  --smt_preprocessing                     true
% 2.31/0.98  --smt_ac_axioms                         fast
% 2.31/0.98  --preprocessed_out                      false
% 2.31/0.98  --preprocessed_stats                    false
% 2.31/0.98  
% 2.31/0.98  ------ Abstraction refinement Options
% 2.31/0.98  
% 2.31/0.98  --abstr_ref                             []
% 2.31/0.98  --abstr_ref_prep                        false
% 2.31/0.98  --abstr_ref_until_sat                   false
% 2.31/0.98  --abstr_ref_sig_restrict                funpre
% 2.31/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.31/0.98  --abstr_ref_under                       []
% 2.31/0.98  
% 2.31/0.98  ------ SAT Options
% 2.31/0.98  
% 2.31/0.98  --sat_mode                              false
% 2.31/0.98  --sat_fm_restart_options                ""
% 2.31/0.98  --sat_gr_def                            false
% 2.31/0.98  --sat_epr_types                         true
% 2.31/0.98  --sat_non_cyclic_types                  false
% 2.31/0.98  --sat_finite_models                     false
% 2.31/0.98  --sat_fm_lemmas                         false
% 2.31/0.98  --sat_fm_prep                           false
% 2.31/0.98  --sat_fm_uc_incr                        true
% 2.31/0.98  --sat_out_model                         small
% 2.31/0.98  --sat_out_clauses                       false
% 2.31/0.98  
% 2.31/0.98  ------ QBF Options
% 2.31/0.98  
% 2.31/0.98  --qbf_mode                              false
% 2.31/0.98  --qbf_elim_univ                         false
% 2.31/0.98  --qbf_dom_inst                          none
% 2.31/0.98  --qbf_dom_pre_inst                      false
% 2.31/0.98  --qbf_sk_in                             false
% 2.31/0.98  --qbf_pred_elim                         true
% 2.31/0.98  --qbf_split                             512
% 2.31/0.98  
% 2.31/0.98  ------ BMC1 Options
% 2.31/0.98  
% 2.31/0.98  --bmc1_incremental                      false
% 2.31/0.98  --bmc1_axioms                           reachable_all
% 2.31/0.98  --bmc1_min_bound                        0
% 2.31/0.98  --bmc1_max_bound                        -1
% 2.31/0.98  --bmc1_max_bound_default                -1
% 2.31/0.98  --bmc1_symbol_reachability              true
% 2.31/0.98  --bmc1_property_lemmas                  false
% 2.31/0.98  --bmc1_k_induction                      false
% 2.31/0.98  --bmc1_non_equiv_states                 false
% 2.31/0.98  --bmc1_deadlock                         false
% 2.31/0.98  --bmc1_ucm                              false
% 2.31/0.98  --bmc1_add_unsat_core                   none
% 2.31/0.98  --bmc1_unsat_core_children              false
% 2.31/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.31/0.98  --bmc1_out_stat                         full
% 2.31/0.98  --bmc1_ground_init                      false
% 2.31/0.98  --bmc1_pre_inst_next_state              false
% 2.31/0.98  --bmc1_pre_inst_state                   false
% 2.31/0.98  --bmc1_pre_inst_reach_state             false
% 2.31/0.98  --bmc1_out_unsat_core                   false
% 2.31/0.98  --bmc1_aig_witness_out                  false
% 2.31/0.98  --bmc1_verbose                          false
% 2.31/0.98  --bmc1_dump_clauses_tptp                false
% 2.31/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.31/0.98  --bmc1_dump_file                        -
% 2.31/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.31/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.31/0.98  --bmc1_ucm_extend_mode                  1
% 2.31/0.98  --bmc1_ucm_init_mode                    2
% 2.31/0.98  --bmc1_ucm_cone_mode                    none
% 2.31/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.31/0.98  --bmc1_ucm_relax_model                  4
% 2.31/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.31/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.31/0.98  --bmc1_ucm_layered_model                none
% 2.31/0.98  --bmc1_ucm_max_lemma_size               10
% 2.31/0.98  
% 2.31/0.98  ------ AIG Options
% 2.31/0.98  
% 2.31/0.98  --aig_mode                              false
% 2.31/0.98  
% 2.31/0.98  ------ Instantiation Options
% 2.31/0.98  
% 2.31/0.98  --instantiation_flag                    true
% 2.31/0.98  --inst_sos_flag                         false
% 2.31/0.98  --inst_sos_phase                        true
% 2.31/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.31/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.31/0.98  --inst_lit_sel_side                     none
% 2.31/0.98  --inst_solver_per_active                1400
% 2.31/0.98  --inst_solver_calls_frac                1.
% 2.31/0.98  --inst_passive_queue_type               priority_queues
% 2.31/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.31/0.98  --inst_passive_queues_freq              [25;2]
% 2.31/0.98  --inst_dismatching                      true
% 2.31/0.98  --inst_eager_unprocessed_to_passive     true
% 2.31/0.98  --inst_prop_sim_given                   true
% 2.31/0.98  --inst_prop_sim_new                     false
% 2.31/0.98  --inst_subs_new                         false
% 2.31/0.98  --inst_eq_res_simp                      false
% 2.31/0.98  --inst_subs_given                       false
% 2.31/0.98  --inst_orphan_elimination               true
% 2.31/0.98  --inst_learning_loop_flag               true
% 2.31/0.98  --inst_learning_start                   3000
% 2.31/0.98  --inst_learning_factor                  2
% 2.31/0.98  --inst_start_prop_sim_after_learn       3
% 2.31/0.98  --inst_sel_renew                        solver
% 2.31/0.98  --inst_lit_activity_flag                true
% 2.31/0.98  --inst_restr_to_given                   false
% 2.31/0.98  --inst_activity_threshold               500
% 2.31/0.98  --inst_out_proof                        true
% 2.31/0.98  
% 2.31/0.98  ------ Resolution Options
% 2.31/0.98  
% 2.31/0.98  --resolution_flag                       false
% 2.31/0.98  --res_lit_sel                           adaptive
% 2.31/0.98  --res_lit_sel_side                      none
% 2.31/0.98  --res_ordering                          kbo
% 2.31/0.98  --res_to_prop_solver                    active
% 2.31/0.98  --res_prop_simpl_new                    false
% 2.31/0.98  --res_prop_simpl_given                  true
% 2.31/0.98  --res_passive_queue_type                priority_queues
% 2.31/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.31/0.98  --res_passive_queues_freq               [15;5]
% 2.31/0.98  --res_forward_subs                      full
% 2.31/0.98  --res_backward_subs                     full
% 2.31/0.98  --res_forward_subs_resolution           true
% 2.31/0.98  --res_backward_subs_resolution          true
% 2.31/0.98  --res_orphan_elimination                true
% 2.31/0.98  --res_time_limit                        2.
% 2.31/0.98  --res_out_proof                         true
% 2.31/0.98  
% 2.31/0.98  ------ Superposition Options
% 2.31/0.98  
% 2.31/0.98  --superposition_flag                    true
% 2.31/0.98  --sup_passive_queue_type                priority_queues
% 2.31/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.31/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.31/0.98  --demod_completeness_check              fast
% 2.31/0.98  --demod_use_ground                      true
% 2.31/0.98  --sup_to_prop_solver                    passive
% 2.31/0.98  --sup_prop_simpl_new                    true
% 2.31/0.98  --sup_prop_simpl_given                  true
% 2.31/0.98  --sup_fun_splitting                     false
% 2.31/0.98  --sup_smt_interval                      50000
% 2.31/0.98  
% 2.31/0.98  ------ Superposition Simplification Setup
% 2.31/0.98  
% 2.31/0.98  --sup_indices_passive                   []
% 2.31/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.31/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.31/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.31/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.31/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.31/0.98  --sup_full_bw                           [BwDemod]
% 2.31/0.98  --sup_immed_triv                        [TrivRules]
% 2.31/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.31/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.31/0.98  --sup_immed_bw_main                     []
% 2.31/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.31/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.31/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.31/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.31/0.98  
% 2.31/0.98  ------ Combination Options
% 2.31/0.98  
% 2.31/0.98  --comb_res_mult                         3
% 2.31/0.98  --comb_sup_mult                         2
% 2.31/0.98  --comb_inst_mult                        10
% 2.31/0.98  
% 2.31/0.98  ------ Debug Options
% 2.31/0.98  
% 2.31/0.98  --dbg_backtrace                         false
% 2.31/0.98  --dbg_dump_prop_clauses                 false
% 2.31/0.98  --dbg_dump_prop_clauses_file            -
% 2.31/0.98  --dbg_out_stat                          false
% 2.31/0.98  
% 2.31/0.98  
% 2.31/0.98  
% 2.31/0.98  
% 2.31/0.98  ------ Proving...
% 2.31/0.98  
% 2.31/0.98  
% 2.31/0.98  % SZS status Theorem for theBenchmark.p
% 2.31/0.98  
% 2.31/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.31/0.98  
% 2.31/0.98  fof(f10,conjecture,(
% 2.31/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X3)) => ~(r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1))) & m1_connsp_2(X2,X0,X1)))))),
% 2.31/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.31/0.98  
% 2.31/0.98  fof(f11,negated_conjecture,(
% 2.31/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X3)) => ~(r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1))) & m1_connsp_2(X2,X0,X1)))))),
% 2.31/0.98    inference(negated_conjecture,[],[f10])).
% 2.31/0.98  
% 2.31/0.98  fof(f23,plain,(
% 2.31/0.98    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : ((~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_connsp_2(X3,X0,X1)) | (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X3))) & m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.31/0.98    inference(ennf_transformation,[],[f11])).
% 2.31/0.98  
% 2.31/0.98  fof(f24,plain,(
% 2.31/0.98    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_connsp_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X3)) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.31/0.98    inference(flattening,[],[f23])).
% 2.31/0.98  
% 2.31/0.98  fof(f35,plain,(
% 2.31/0.98    ( ! [X0,X1] : (? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_connsp_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X3)) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (! [X3] : (~r1_tarski(X3,sK3) | ~v3_pre_topc(X3,X0) | ~m1_connsp_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X3)) & m1_connsp_2(sK3,X0,X1) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.31/0.98    introduced(choice_axiom,[])).
% 2.31/0.98  
% 2.31/0.98  fof(f34,plain,(
% 2.31/0.98    ( ! [X0] : (? [X1] : (? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_connsp_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X3)) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_connsp_2(X3,X0,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X3)) & m1_connsp_2(X2,X0,sK2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK2,u1_struct_0(X0)))) )),
% 2.31/0.98    introduced(choice_axiom,[])).
% 2.31/0.98  
% 2.31/0.98  fof(f33,plain,(
% 2.31/0.98    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_connsp_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X3)) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~v3_pre_topc(X3,sK1) | ~m1_connsp_2(X3,sK1,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) | v1_xboole_0(X3)) & m1_connsp_2(X2,sK1,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X1,u1_struct_0(sK1))) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 2.31/0.98    introduced(choice_axiom,[])).
% 2.31/0.98  
% 2.31/0.98  fof(f36,plain,(
% 2.31/0.98    ((! [X3] : (~r1_tarski(X3,sK3) | ~v3_pre_topc(X3,sK1) | ~m1_connsp_2(X3,sK1,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) | v1_xboole_0(X3)) & m1_connsp_2(sK3,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK2,u1_struct_0(sK1))) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 2.31/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f24,f35,f34,f33])).
% 2.31/0.98  
% 2.31/0.98  fof(f57,plain,(
% 2.31/0.98    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 2.31/0.98    inference(cnf_transformation,[],[f36])).
% 2.31/0.98  
% 2.31/0.98  fof(f3,axiom,(
% 2.31/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.31/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.31/0.98  
% 2.31/0.98  fof(f31,plain,(
% 2.31/0.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.31/0.98    inference(nnf_transformation,[],[f3])).
% 2.31/0.98  
% 2.31/0.98  fof(f43,plain,(
% 2.31/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.31/0.98    inference(cnf_transformation,[],[f31])).
% 2.31/0.98  
% 2.31/0.98  fof(f6,axiom,(
% 2.31/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 2.31/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.31/0.98  
% 2.31/0.98  fof(f16,plain,(
% 2.31/0.98    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.31/0.98    inference(ennf_transformation,[],[f6])).
% 2.31/0.98  
% 2.31/0.98  fof(f47,plain,(
% 2.31/0.98    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.31/0.98    inference(cnf_transformation,[],[f16])).
% 2.31/0.98  
% 2.31/0.98  fof(f55,plain,(
% 2.31/0.98    l1_pre_topc(sK1)),
% 2.31/0.98    inference(cnf_transformation,[],[f36])).
% 2.31/0.98  
% 2.31/0.98  fof(f1,axiom,(
% 2.31/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.31/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.31/0.98  
% 2.31/0.98  fof(f12,plain,(
% 2.31/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.31/0.98    inference(ennf_transformation,[],[f1])).
% 2.31/0.98  
% 2.31/0.98  fof(f25,plain,(
% 2.31/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.31/0.98    inference(nnf_transformation,[],[f12])).
% 2.31/0.98  
% 2.31/0.98  fof(f26,plain,(
% 2.31/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.31/0.98    inference(rectify,[],[f25])).
% 2.31/0.98  
% 2.31/0.98  fof(f27,plain,(
% 2.31/0.98    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.31/0.98    introduced(choice_axiom,[])).
% 2.31/0.98  
% 2.31/0.98  fof(f28,plain,(
% 2.31/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.31/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).
% 2.31/0.98  
% 2.31/0.98  fof(f38,plain,(
% 2.31/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.31/0.98    inference(cnf_transformation,[],[f28])).
% 2.31/0.98  
% 2.31/0.98  fof(f37,plain,(
% 2.31/0.98    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.31/0.98    inference(cnf_transformation,[],[f28])).
% 2.31/0.98  
% 2.31/0.98  fof(f2,axiom,(
% 2.31/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.31/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.31/0.98  
% 2.31/0.98  fof(f29,plain,(
% 2.31/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.31/0.98    inference(nnf_transformation,[],[f2])).
% 2.31/0.98  
% 2.31/0.98  fof(f30,plain,(
% 2.31/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.31/0.98    inference(flattening,[],[f29])).
% 2.31/0.98  
% 2.31/0.98  fof(f41,plain,(
% 2.31/0.98    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.31/0.98    inference(cnf_transformation,[],[f30])).
% 2.31/0.98  
% 2.31/0.98  fof(f60,plain,(
% 2.31/0.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.31/0.98    inference(equality_resolution,[],[f41])).
% 2.31/0.98  
% 2.31/0.98  fof(f39,plain,(
% 2.31/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 2.31/0.98    inference(cnf_transformation,[],[f28])).
% 2.31/0.98  
% 2.31/0.98  fof(f44,plain,(
% 2.31/0.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.31/0.98    inference(cnf_transformation,[],[f31])).
% 2.31/0.98  
% 2.31/0.98  fof(f7,axiom,(
% 2.31/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 2.31/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.31/0.98  
% 2.31/0.98  fof(f17,plain,(
% 2.31/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.31/0.98    inference(ennf_transformation,[],[f7])).
% 2.31/0.98  
% 2.31/0.98  fof(f18,plain,(
% 2.31/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.31/0.98    inference(flattening,[],[f17])).
% 2.31/0.98  
% 2.31/0.98  fof(f48,plain,(
% 2.31/0.98    ( ! [X2,X0,X3,X1] : (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.31/0.98    inference(cnf_transformation,[],[f18])).
% 2.31/0.98  
% 2.31/0.98  fof(f54,plain,(
% 2.31/0.98    v2_pre_topc(sK1)),
% 2.31/0.98    inference(cnf_transformation,[],[f36])).
% 2.31/0.98  
% 2.31/0.98  fof(f49,plain,(
% 2.31/0.98    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.31/0.98    inference(cnf_transformation,[],[f18])).
% 2.31/0.98  
% 2.31/0.98  fof(f58,plain,(
% 2.31/0.98    m1_connsp_2(sK3,sK1,sK2)),
% 2.31/0.98    inference(cnf_transformation,[],[f36])).
% 2.31/0.98  
% 2.31/0.98  fof(f8,axiom,(
% 2.31/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 2.31/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.31/0.98  
% 2.31/0.98  fof(f19,plain,(
% 2.31/0.98    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.31/0.98    inference(ennf_transformation,[],[f8])).
% 2.31/0.98  
% 2.31/0.98  fof(f20,plain,(
% 2.31/0.98    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.31/0.98    inference(flattening,[],[f19])).
% 2.31/0.98  
% 2.31/0.98  fof(f32,plain,(
% 2.31/0.98    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.31/0.98    inference(nnf_transformation,[],[f20])).
% 2.31/0.98  
% 2.31/0.98  fof(f50,plain,(
% 2.31/0.98    ( ! [X2,X0,X1] : (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.31/0.98    inference(cnf_transformation,[],[f32])).
% 2.31/0.98  
% 2.31/0.98  fof(f9,axiom,(
% 2.31/0.98    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.31/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.31/0.98  
% 2.31/0.98  fof(f21,plain,(
% 2.31/0.98    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.31/0.98    inference(ennf_transformation,[],[f9])).
% 2.31/0.98  
% 2.31/0.98  fof(f22,plain,(
% 2.31/0.98    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.31/0.98    inference(flattening,[],[f21])).
% 2.31/0.98  
% 2.31/0.98  fof(f52,plain,(
% 2.31/0.98    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.31/0.98    inference(cnf_transformation,[],[f22])).
% 2.31/0.98  
% 2.31/0.98  fof(f53,plain,(
% 2.31/0.98    ~v2_struct_0(sK1)),
% 2.31/0.98    inference(cnf_transformation,[],[f36])).
% 2.31/0.98  
% 2.31/0.98  fof(f56,plain,(
% 2.31/0.98    m1_subset_1(sK2,u1_struct_0(sK1))),
% 2.31/0.98    inference(cnf_transformation,[],[f36])).
% 2.31/0.98  
% 2.31/0.98  fof(f4,axiom,(
% 2.31/0.98    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.31/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.31/0.98  
% 2.31/0.98  fof(f13,plain,(
% 2.31/0.98    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.31/0.98    inference(ennf_transformation,[],[f4])).
% 2.31/0.98  
% 2.31/0.98  fof(f45,plain,(
% 2.31/0.98    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.31/0.98    inference(cnf_transformation,[],[f13])).
% 2.31/0.98  
% 2.31/0.98  fof(f59,plain,(
% 2.31/0.98    ( ! [X3] : (~r1_tarski(X3,sK3) | ~v3_pre_topc(X3,sK1) | ~m1_connsp_2(X3,sK1,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) | v1_xboole_0(X3)) )),
% 2.31/0.98    inference(cnf_transformation,[],[f36])).
% 2.31/0.98  
% 2.31/0.98  fof(f51,plain,(
% 2.31/0.98    ( ! [X2,X0,X1] : (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.31/0.98    inference(cnf_transformation,[],[f32])).
% 2.31/0.98  
% 2.31/0.98  fof(f5,axiom,(
% 2.31/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 2.31/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.31/0.98  
% 2.31/0.98  fof(f14,plain,(
% 2.31/0.98    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.31/0.98    inference(ennf_transformation,[],[f5])).
% 2.31/0.98  
% 2.31/0.98  fof(f15,plain,(
% 2.31/0.98    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.31/0.98    inference(flattening,[],[f14])).
% 2.31/0.98  
% 2.31/0.98  fof(f46,plain,(
% 2.31/0.98    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.31/0.98    inference(cnf_transformation,[],[f15])).
% 2.31/0.98  
% 2.31/0.98  cnf(c_18,negated_conjecture,
% 2.31/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.31/0.98      inference(cnf_transformation,[],[f57]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_1691,plain,
% 2.31/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.31/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_7,plain,
% 2.31/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.31/0.98      inference(cnf_transformation,[],[f43]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_1692,plain,
% 2.31/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.31/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 2.31/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_2221,plain,
% 2.31/0.98      ( r1_tarski(sK3,u1_struct_0(sK1)) = iProver_top ),
% 2.31/0.98      inference(superposition,[status(thm)],[c_1691,c_1692]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_10,plain,
% 2.31/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.31/0.98      | r1_tarski(k1_tops_1(X1,X0),X0)
% 2.31/0.98      | ~ l1_pre_topc(X1) ),
% 2.31/0.98      inference(cnf_transformation,[],[f47]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_20,negated_conjecture,
% 2.31/0.98      ( l1_pre_topc(sK1) ),
% 2.31/0.98      inference(cnf_transformation,[],[f55]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_518,plain,
% 2.31/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.31/0.98      | r1_tarski(k1_tops_1(X1,X0),X0)
% 2.31/0.98      | sK1 != X1 ),
% 2.31/0.98      inference(resolution_lifted,[status(thm)],[c_10,c_20]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_519,plain,
% 2.31/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.31/0.98      | r1_tarski(k1_tops_1(sK1,X0),X0) ),
% 2.31/0.98      inference(unflattening,[status(thm)],[c_518]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_1684,plain,
% 2.31/0.98      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.31/0.98      | r1_tarski(k1_tops_1(sK1,X0),X0) = iProver_top ),
% 2.31/0.98      inference(predicate_to_equality,[status(thm)],[c_519]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_1895,plain,
% 2.31/0.98      ( r1_tarski(k1_tops_1(sK1,sK3),sK3) = iProver_top ),
% 2.31/0.98      inference(superposition,[status(thm)],[c_1691,c_1684]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_1,plain,
% 2.31/0.98      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 2.31/0.98      inference(cnf_transformation,[],[f38]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_1697,plain,
% 2.31/0.98      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 2.31/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 2.31/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_2,plain,
% 2.31/0.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 2.31/0.98      inference(cnf_transformation,[],[f37]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_1696,plain,
% 2.31/0.98      ( r2_hidden(X0,X1) != iProver_top
% 2.31/0.98      | r2_hidden(X0,X2) = iProver_top
% 2.31/0.98      | r1_tarski(X1,X2) != iProver_top ),
% 2.31/0.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_2987,plain,
% 2.31/0.98      ( r2_hidden(sK0(X0,X1),X2) = iProver_top
% 2.31/0.98      | r1_tarski(X0,X2) != iProver_top
% 2.31/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 2.31/0.98      inference(superposition,[status(thm)],[c_1697,c_1696]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_4393,plain,
% 2.31/0.98      ( r2_hidden(sK0(X0,X1),X2) = iProver_top
% 2.31/0.98      | r1_tarski(X0,X3) != iProver_top
% 2.31/0.98      | r1_tarski(X3,X2) != iProver_top
% 2.31/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 2.31/0.98      inference(superposition,[status(thm)],[c_2987,c_1696]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_4624,plain,
% 2.31/0.98      ( r2_hidden(sK0(k1_tops_1(sK1,sK3),X0),X1) = iProver_top
% 2.31/0.98      | r1_tarski(k1_tops_1(sK1,sK3),X0) = iProver_top
% 2.31/0.98      | r1_tarski(sK3,X1) != iProver_top ),
% 2.31/0.98      inference(superposition,[status(thm)],[c_1895,c_4393]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_4775,plain,
% 2.31/0.98      ( r2_hidden(sK0(k1_tops_1(sK1,sK3),X0),X1) = iProver_top
% 2.31/0.98      | r1_tarski(X2,X1) != iProver_top
% 2.31/0.98      | r1_tarski(k1_tops_1(sK1,sK3),X0) = iProver_top
% 2.31/0.98      | r1_tarski(sK3,X2) != iProver_top ),
% 2.31/0.98      inference(superposition,[status(thm)],[c_4624,c_1696]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_5583,plain,
% 2.31/0.98      ( r2_hidden(sK0(k1_tops_1(sK1,sK3),X0),u1_struct_0(sK1)) = iProver_top
% 2.31/0.98      | r1_tarski(k1_tops_1(sK1,sK3),X0) = iProver_top
% 2.31/0.98      | r1_tarski(sK3,sK3) != iProver_top ),
% 2.31/0.98      inference(superposition,[status(thm)],[c_2221,c_4775]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_4,plain,
% 2.31/0.98      ( r1_tarski(X0,X0) ),
% 2.31/0.98      inference(cnf_transformation,[],[f60]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_2823,plain,
% 2.31/0.98      ( r1_tarski(sK3,sK3) ),
% 2.31/0.98      inference(instantiation,[status(thm)],[c_4]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_2826,plain,
% 2.31/0.98      ( r1_tarski(sK3,sK3) = iProver_top ),
% 2.31/0.98      inference(predicate_to_equality,[status(thm)],[c_2823]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_5732,plain,
% 2.31/0.98      ( r1_tarski(k1_tops_1(sK1,sK3),X0) = iProver_top
% 2.31/0.98      | r2_hidden(sK0(k1_tops_1(sK1,sK3),X0),u1_struct_0(sK1)) = iProver_top ),
% 2.31/0.98      inference(global_propositional_subsumption,
% 2.31/0.98                [status(thm)],
% 2.31/0.98                [c_5583,c_2826]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_5733,plain,
% 2.31/0.98      ( r2_hidden(sK0(k1_tops_1(sK1,sK3),X0),u1_struct_0(sK1)) = iProver_top
% 2.31/0.98      | r1_tarski(k1_tops_1(sK1,sK3),X0) = iProver_top ),
% 2.31/0.98      inference(renaming,[status(thm)],[c_5732]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_0,plain,
% 2.31/0.98      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 2.31/0.98      inference(cnf_transformation,[],[f39]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_1698,plain,
% 2.31/0.98      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 2.31/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 2.31/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_5740,plain,
% 2.31/0.98      ( r1_tarski(k1_tops_1(sK1,sK3),u1_struct_0(sK1)) = iProver_top ),
% 2.31/0.98      inference(superposition,[status(thm)],[c_5733,c_1698]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_4773,plain,
% 2.31/0.98      ( r1_tarski(k1_tops_1(sK1,sK3),X0) = iProver_top
% 2.31/0.98      | r1_tarski(sK3,X0) != iProver_top ),
% 2.31/0.98      inference(superposition,[status(thm)],[c_4624,c_1698]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_6,plain,
% 2.31/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.31/0.98      inference(cnf_transformation,[],[f44]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_1693,plain,
% 2.31/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 2.31/0.98      | r1_tarski(X0,X1) != iProver_top ),
% 2.31/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_12,plain,
% 2.31/0.98      ( ~ v3_pre_topc(X0,X1)
% 2.31/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.31/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 2.31/0.98      | ~ v2_pre_topc(X3)
% 2.31/0.98      | ~ l1_pre_topc(X3)
% 2.31/0.98      | ~ l1_pre_topc(X1)
% 2.31/0.98      | k1_tops_1(X1,X0) = X0 ),
% 2.31/0.98      inference(cnf_transformation,[],[f48]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_21,negated_conjecture,
% 2.31/0.98      ( v2_pre_topc(sK1) ),
% 2.31/0.98      inference(cnf_transformation,[],[f54]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_460,plain,
% 2.31/0.98      ( ~ v3_pre_topc(X0,X1)
% 2.31/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.31/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 2.31/0.98      | ~ l1_pre_topc(X1)
% 2.31/0.98      | ~ l1_pre_topc(X3)
% 2.31/0.98      | k1_tops_1(X1,X0) = X0
% 2.31/0.98      | sK1 != X3 ),
% 2.31/0.98      inference(resolution_lifted,[status(thm)],[c_12,c_21]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_461,plain,
% 2.31/0.98      ( ~ v3_pre_topc(X0,X1)
% 2.31/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.31/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.31/0.98      | ~ l1_pre_topc(X1)
% 2.31/0.98      | ~ l1_pre_topc(sK1)
% 2.31/0.98      | k1_tops_1(X1,X0) = X0 ),
% 2.31/0.98      inference(unflattening,[status(thm)],[c_460]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_465,plain,
% 2.31/0.98      ( ~ l1_pre_topc(X1)
% 2.31/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.31/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.31/0.98      | ~ v3_pre_topc(X0,X1)
% 2.31/0.98      | k1_tops_1(X1,X0) = X0 ),
% 2.31/0.98      inference(global_propositional_subsumption,
% 2.31/0.98                [status(thm)],
% 2.31/0.98                [c_461,c_20]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_466,plain,
% 2.31/0.98      ( ~ v3_pre_topc(X0,X1)
% 2.31/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.31/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.31/0.98      | ~ l1_pre_topc(X1)
% 2.31/0.98      | k1_tops_1(X1,X0) = X0 ),
% 2.31/0.98      inference(renaming,[status(thm)],[c_465]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_500,plain,
% 2.31/0.98      ( ~ v3_pre_topc(X0,X1)
% 2.31/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.31/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.31/0.98      | k1_tops_1(X1,X0) = X0
% 2.31/0.98      | sK1 != X1 ),
% 2.31/0.98      inference(resolution_lifted,[status(thm)],[c_466,c_20]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_501,plain,
% 2.31/0.98      ( ~ v3_pre_topc(X0,sK1)
% 2.31/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.31/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.31/0.98      | k1_tops_1(sK1,X0) = X0 ),
% 2.31/0.98      inference(unflattening,[status(thm)],[c_500]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_1193,plain,
% 2.31/0.98      ( ~ v3_pre_topc(X0,sK1)
% 2.31/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.31/0.98      | k1_tops_1(sK1,X0) = X0
% 2.31/0.98      | ~ sP2_iProver_split ),
% 2.31/0.98      inference(splitting,
% 2.31/0.98                [splitting(split),new_symbols(definition,[sP2_iProver_split])],
% 2.31/0.98                [c_501]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_1686,plain,
% 2.31/0.98      ( k1_tops_1(sK1,X0) = X0
% 2.31/0.98      | v3_pre_topc(X0,sK1) != iProver_top
% 2.31/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.31/0.98      | sP2_iProver_split != iProver_top ),
% 2.31/0.98      inference(predicate_to_equality,[status(thm)],[c_1193]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_1194,plain,
% 2.31/0.98      ( sP2_iProver_split | sP0_iProver_split ),
% 2.31/0.98      inference(splitting,
% 2.31/0.98                [splitting(split),new_symbols(definition,[])],
% 2.31/0.98                [c_501]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_1225,plain,
% 2.31/0.98      ( sP2_iProver_split = iProver_top
% 2.31/0.98      | sP0_iProver_split = iProver_top ),
% 2.31/0.98      inference(predicate_to_equality,[status(thm)],[c_1194]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_1226,plain,
% 2.31/0.98      ( k1_tops_1(sK1,X0) = X0
% 2.31/0.98      | v3_pre_topc(X0,sK1) != iProver_top
% 2.31/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.31/0.98      | sP2_iProver_split != iProver_top ),
% 2.31/0.98      inference(predicate_to_equality,[status(thm)],[c_1193]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_11,plain,
% 2.31/0.98      ( v3_pre_topc(X0,X1)
% 2.31/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 2.31/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.31/0.98      | ~ v2_pre_topc(X1)
% 2.31/0.98      | ~ l1_pre_topc(X1)
% 2.31/0.98      | ~ l1_pre_topc(X3)
% 2.31/0.98      | k1_tops_1(X1,X0) != X0 ),
% 2.31/0.98      inference(cnf_transformation,[],[f49]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_435,plain,
% 2.31/0.98      ( v3_pre_topc(X0,X1)
% 2.31/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.31/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 2.31/0.98      | ~ l1_pre_topc(X1)
% 2.31/0.98      | ~ l1_pre_topc(X3)
% 2.31/0.98      | k1_tops_1(X1,X0) != X0
% 2.31/0.98      | sK1 != X1 ),
% 2.31/0.98      inference(resolution_lifted,[status(thm)],[c_11,c_21]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_436,plain,
% 2.31/0.98      ( v3_pre_topc(X0,sK1)
% 2.31/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.31/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.31/0.98      | ~ l1_pre_topc(X2)
% 2.31/0.98      | ~ l1_pre_topc(sK1)
% 2.31/0.98      | k1_tops_1(sK1,X0) != X0 ),
% 2.31/0.98      inference(unflattening,[status(thm)],[c_435]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_440,plain,
% 2.31/0.98      ( ~ l1_pre_topc(X2)
% 2.31/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.31/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.31/0.98      | v3_pre_topc(X0,sK1)
% 2.31/0.98      | k1_tops_1(sK1,X0) != X0 ),
% 2.31/0.98      inference(global_propositional_subsumption,
% 2.31/0.98                [status(thm)],
% 2.31/0.98                [c_436,c_20]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_441,plain,
% 2.31/0.98      ( v3_pre_topc(X0,sK1)
% 2.31/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.31/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.31/0.98      | ~ l1_pre_topc(X2)
% 2.31/0.98      | k1_tops_1(sK1,X0) != X0 ),
% 2.31/0.98      inference(renaming,[status(thm)],[c_440]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_530,plain,
% 2.31/0.98      ( v3_pre_topc(X0,sK1)
% 2.31/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.31/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.31/0.98      | k1_tops_1(sK1,X0) != X0
% 2.31/0.98      | sK1 != X2 ),
% 2.31/0.98      inference(resolution_lifted,[status(thm)],[c_20,c_441]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_531,plain,
% 2.31/0.98      ( v3_pre_topc(X0,sK1)
% 2.31/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.31/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.31/0.98      | k1_tops_1(sK1,X0) != X0 ),
% 2.31/0.98      inference(unflattening,[status(thm)],[c_530]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_1190,plain,
% 2.31/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.31/0.98      | ~ sP0_iProver_split ),
% 2.31/0.98      inference(splitting,
% 2.31/0.98                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.31/0.98                [c_531]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_1683,plain,
% 2.31/0.98      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.31/0.98      | sP0_iProver_split != iProver_top ),
% 2.31/0.98      inference(predicate_to_equality,[status(thm)],[c_1190]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_1861,plain,
% 2.31/0.98      ( sP0_iProver_split != iProver_top ),
% 2.31/0.98      inference(superposition,[status(thm)],[c_1691,c_1683]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_2552,plain,
% 2.31/0.98      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.31/0.98      | v3_pre_topc(X0,sK1) != iProver_top
% 2.31/0.98      | k1_tops_1(sK1,X0) = X0 ),
% 2.31/0.98      inference(global_propositional_subsumption,
% 2.31/0.98                [status(thm)],
% 2.31/0.98                [c_1686,c_1225,c_1226,c_1861]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_2553,plain,
% 2.31/0.98      ( k1_tops_1(sK1,X0) = X0
% 2.31/0.98      | v3_pre_topc(X0,sK1) != iProver_top
% 2.31/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.31/0.98      inference(renaming,[status(thm)],[c_2552]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_2559,plain,
% 2.31/0.98      ( k1_tops_1(sK1,X0) = X0
% 2.31/0.98      | v3_pre_topc(X0,sK1) != iProver_top
% 2.31/0.98      | r1_tarski(X0,u1_struct_0(sK1)) != iProver_top ),
% 2.31/0.98      inference(superposition,[status(thm)],[c_1693,c_2553]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_4940,plain,
% 2.31/0.98      ( k1_tops_1(sK1,k1_tops_1(sK1,sK3)) = k1_tops_1(sK1,sK3)
% 2.31/0.98      | v3_pre_topc(k1_tops_1(sK1,sK3),sK1) != iProver_top
% 2.31/0.98      | r1_tarski(sK3,u1_struct_0(sK1)) != iProver_top ),
% 2.31/0.98      inference(superposition,[status(thm)],[c_4773,c_2559]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_1694,plain,
% 2.31/0.98      ( r1_tarski(X0,X0) = iProver_top ),
% 2.31/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_17,negated_conjecture,
% 2.31/0.98      ( m1_connsp_2(sK3,sK1,sK2) ),
% 2.31/0.98      inference(cnf_transformation,[],[f58]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_14,plain,
% 2.31/0.98      ( ~ m1_connsp_2(X0,X1,X2)
% 2.31/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.31/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.31/0.98      | r2_hidden(X2,k1_tops_1(X1,X0))
% 2.31/0.98      | v2_struct_0(X1)
% 2.31/0.98      | ~ v2_pre_topc(X1)
% 2.31/0.98      | ~ l1_pre_topc(X1) ),
% 2.31/0.98      inference(cnf_transformation,[],[f50]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_15,plain,
% 2.31/0.98      ( ~ m1_connsp_2(X0,X1,X2)
% 2.31/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.31/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.31/0.98      | v2_struct_0(X1)
% 2.31/0.98      | ~ v2_pre_topc(X1)
% 2.31/0.98      | ~ l1_pre_topc(X1) ),
% 2.31/0.98      inference(cnf_transformation,[],[f52]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_127,plain,
% 2.31/0.98      ( ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.31/0.98      | ~ m1_connsp_2(X0,X1,X2)
% 2.31/0.98      | r2_hidden(X2,k1_tops_1(X1,X0))
% 2.31/0.98      | v2_struct_0(X1)
% 2.31/0.98      | ~ v2_pre_topc(X1)
% 2.31/0.98      | ~ l1_pre_topc(X1) ),
% 2.31/0.98      inference(global_propositional_subsumption,
% 2.31/0.98                [status(thm)],
% 2.31/0.98                [c_14,c_15]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_128,plain,
% 2.31/0.98      ( ~ m1_connsp_2(X0,X1,X2)
% 2.31/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.31/0.98      | r2_hidden(X2,k1_tops_1(X1,X0))
% 2.31/0.98      | v2_struct_0(X1)
% 2.31/0.98      | ~ v2_pre_topc(X1)
% 2.31/0.98      | ~ l1_pre_topc(X1) ),
% 2.31/0.98      inference(renaming,[status(thm)],[c_127]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_22,negated_conjecture,
% 2.31/0.98      ( ~ v2_struct_0(sK1) ),
% 2.31/0.98      inference(cnf_transformation,[],[f53]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_338,plain,
% 2.31/0.98      ( ~ m1_connsp_2(X0,X1,X2)
% 2.31/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.31/0.98      | r2_hidden(X2,k1_tops_1(X1,X0))
% 2.31/0.98      | ~ v2_pre_topc(X1)
% 2.31/0.98      | ~ l1_pre_topc(X1)
% 2.31/0.98      | sK1 != X1 ),
% 2.31/0.98      inference(resolution_lifted,[status(thm)],[c_128,c_22]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_339,plain,
% 2.31/0.98      ( ~ m1_connsp_2(X0,sK1,X1)
% 2.31/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.31/0.98      | r2_hidden(X1,k1_tops_1(sK1,X0))
% 2.31/0.98      | ~ v2_pre_topc(sK1)
% 2.31/0.98      | ~ l1_pre_topc(sK1) ),
% 2.31/0.98      inference(unflattening,[status(thm)],[c_338]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_343,plain,
% 2.31/0.98      ( ~ m1_connsp_2(X0,sK1,X1)
% 2.31/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.31/0.98      | r2_hidden(X1,k1_tops_1(sK1,X0)) ),
% 2.31/0.98      inference(global_propositional_subsumption,
% 2.31/0.98                [status(thm)],
% 2.31/0.98                [c_339,c_21,c_20]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_687,plain,
% 2.31/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.31/0.98      | r2_hidden(X0,k1_tops_1(sK1,X1))
% 2.31/0.98      | sK2 != X0
% 2.31/0.98      | sK1 != sK1
% 2.31/0.98      | sK3 != X1 ),
% 2.31/0.98      inference(resolution_lifted,[status(thm)],[c_17,c_343]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_688,plain,
% 2.31/0.98      ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 2.31/0.98      | r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
% 2.31/0.98      inference(unflattening,[status(thm)],[c_687]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_19,negated_conjecture,
% 2.31/0.98      ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 2.31/0.98      inference(cnf_transformation,[],[f56]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_690,plain,
% 2.31/0.98      ( r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
% 2.31/0.98      inference(global_propositional_subsumption,
% 2.31/0.98                [status(thm)],
% 2.31/0.98                [c_688,c_19]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_1678,plain,
% 2.31/0.98      ( r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top ),
% 2.31/0.98      inference(predicate_to_equality,[status(thm)],[c_690]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_8,plain,
% 2.31/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.31/0.98      | ~ r2_hidden(X2,X0)
% 2.31/0.98      | ~ v1_xboole_0(X1) ),
% 2.31/0.98      inference(cnf_transformation,[],[f45]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_175,plain,
% 2.31/0.98      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.31/0.98      inference(prop_impl,[status(thm)],[c_6]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_176,plain,
% 2.31/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.31/0.98      inference(renaming,[status(thm)],[c_175]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_226,plain,
% 2.31/0.98      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X2) | ~ v1_xboole_0(X2) ),
% 2.31/0.98      inference(bin_hyper_res,[status(thm)],[c_8,c_176]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_1689,plain,
% 2.31/0.98      ( r2_hidden(X0,X1) != iProver_top
% 2.31/0.98      | r1_tarski(X1,X2) != iProver_top
% 2.31/0.98      | v1_xboole_0(X2) != iProver_top ),
% 2.31/0.98      inference(predicate_to_equality,[status(thm)],[c_226]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_3455,plain,
% 2.31/0.98      ( r1_tarski(k1_tops_1(sK1,sK3),X0) != iProver_top
% 2.31/0.98      | v1_xboole_0(X0) != iProver_top ),
% 2.31/0.98      inference(superposition,[status(thm)],[c_1678,c_1689]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_4001,plain,
% 2.31/0.98      ( v1_xboole_0(k1_tops_1(sK1,sK3)) != iProver_top ),
% 2.31/0.98      inference(superposition,[status(thm)],[c_1694,c_3455]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_1199,plain,
% 2.31/0.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.31/0.98      theory(equality) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_1874,plain,
% 2.31/0.98      ( r2_hidden(X0,X1)
% 2.31/0.98      | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3))
% 2.31/0.98      | X1 != k1_tops_1(sK1,sK3)
% 2.31/0.98      | X0 != sK2 ),
% 2.31/0.98      inference(instantiation,[status(thm)],[c_1199]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_2020,plain,
% 2.31/0.98      ( r2_hidden(sK2,X0)
% 2.31/0.98      | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3))
% 2.31/0.98      | X0 != k1_tops_1(sK1,sK3)
% 2.31/0.98      | sK2 != sK2 ),
% 2.31/0.98      inference(instantiation,[status(thm)],[c_1874]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_3217,plain,
% 2.31/0.98      ( r2_hidden(sK2,k1_tops_1(sK1,k1_tops_1(sK1,sK3)))
% 2.31/0.98      | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3))
% 2.31/0.98      | k1_tops_1(sK1,k1_tops_1(sK1,sK3)) != k1_tops_1(sK1,sK3)
% 2.31/0.98      | sK2 != sK2 ),
% 2.31/0.98      inference(instantiation,[status(thm)],[c_2020]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_3221,plain,
% 2.31/0.98      ( k1_tops_1(sK1,k1_tops_1(sK1,sK3)) != k1_tops_1(sK1,sK3)
% 2.31/0.98      | sK2 != sK2
% 2.31/0.98      | r2_hidden(sK2,k1_tops_1(sK1,k1_tops_1(sK1,sK3))) = iProver_top
% 2.31/0.98      | r2_hidden(sK2,k1_tops_1(sK1,sK3)) != iProver_top ),
% 2.31/0.98      inference(predicate_to_equality,[status(thm)],[c_3217]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_1846,plain,
% 2.31/0.98      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.31/0.98      | ~ r1_tarski(X0,u1_struct_0(sK1)) ),
% 2.31/0.98      inference(instantiation,[status(thm)],[c_6]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_2155,plain,
% 2.31/0.98      ( m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.31/0.98      | ~ r1_tarski(k1_tops_1(sK1,sK3),u1_struct_0(sK1)) ),
% 2.31/0.98      inference(instantiation,[status(thm)],[c_1846]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_2156,plain,
% 2.31/0.98      ( m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 2.31/0.98      | r1_tarski(k1_tops_1(sK1,sK3),u1_struct_0(sK1)) != iProver_top ),
% 2.31/0.98      inference(predicate_to_equality,[status(thm)],[c_2155]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_1196,plain,( X0 = X0 ),theory(equality) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_1908,plain,
% 2.31/0.98      ( sK2 = sK2 ),
% 2.31/0.98      inference(instantiation,[status(thm)],[c_1196]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_16,negated_conjecture,
% 2.31/0.98      ( ~ m1_connsp_2(X0,sK1,sK2)
% 2.31/0.98      | ~ v3_pre_topc(X0,sK1)
% 2.31/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.31/0.98      | ~ r1_tarski(X0,sK3)
% 2.31/0.98      | v1_xboole_0(X0) ),
% 2.31/0.98      inference(cnf_transformation,[],[f59]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_13,plain,
% 2.31/0.98      ( m1_connsp_2(X0,X1,X2)
% 2.31/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.31/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.31/0.98      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 2.31/0.98      | v2_struct_0(X1)
% 2.31/0.98      | ~ v2_pre_topc(X1)
% 2.31/0.98      | ~ l1_pre_topc(X1) ),
% 2.31/0.98      inference(cnf_transformation,[],[f51]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_380,plain,
% 2.31/0.98      ( m1_connsp_2(X0,X1,X2)
% 2.31/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.31/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.31/0.98      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 2.31/0.98      | ~ v2_pre_topc(X1)
% 2.31/0.98      | ~ l1_pre_topc(X1)
% 2.31/0.98      | sK1 != X1 ),
% 2.31/0.98      inference(resolution_lifted,[status(thm)],[c_13,c_22]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_381,plain,
% 2.31/0.98      ( m1_connsp_2(X0,sK1,X1)
% 2.31/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.31/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.31/0.98      | ~ r2_hidden(X1,k1_tops_1(sK1,X0))
% 2.31/0.98      | ~ v2_pre_topc(sK1)
% 2.31/0.98      | ~ l1_pre_topc(sK1) ),
% 2.31/0.98      inference(unflattening,[status(thm)],[c_380]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_385,plain,
% 2.31/0.98      ( m1_connsp_2(X0,sK1,X1)
% 2.31/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.31/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.31/0.98      | ~ r2_hidden(X1,k1_tops_1(sK1,X0)) ),
% 2.31/0.98      inference(global_propositional_subsumption,
% 2.31/0.98                [status(thm)],
% 2.31/0.98                [c_381,c_21,c_20]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_658,plain,
% 2.31/0.98      ( ~ v3_pre_topc(X0,sK1)
% 2.31/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.31/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.31/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.31/0.98      | ~ r2_hidden(X1,k1_tops_1(sK1,X2))
% 2.31/0.98      | ~ r1_tarski(X0,sK3)
% 2.31/0.98      | v1_xboole_0(X0)
% 2.31/0.98      | X2 != X0
% 2.31/0.98      | sK2 != X1
% 2.31/0.98      | sK1 != sK1 ),
% 2.31/0.98      inference(resolution_lifted,[status(thm)],[c_16,c_385]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_659,plain,
% 2.31/0.98      ( ~ v3_pre_topc(X0,sK1)
% 2.31/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.31/0.98      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 2.31/0.98      | ~ r2_hidden(sK2,k1_tops_1(sK1,X0))
% 2.31/0.98      | ~ r1_tarski(X0,sK3)
% 2.31/0.98      | v1_xboole_0(X0) ),
% 2.31/0.98      inference(unflattening,[status(thm)],[c_658]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_663,plain,
% 2.31/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.31/0.98      | ~ v3_pre_topc(X0,sK1)
% 2.31/0.98      | ~ r2_hidden(sK2,k1_tops_1(sK1,X0))
% 2.31/0.98      | ~ r1_tarski(X0,sK3)
% 2.31/0.98      | v1_xboole_0(X0) ),
% 2.31/0.98      inference(global_propositional_subsumption,
% 2.31/0.98                [status(thm)],
% 2.31/0.98                [c_659,c_19]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_664,plain,
% 2.31/0.98      ( ~ v3_pre_topc(X0,sK1)
% 2.31/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.31/0.98      | ~ r2_hidden(sK2,k1_tops_1(sK1,X0))
% 2.31/0.98      | ~ r1_tarski(X0,sK3)
% 2.31/0.98      | v1_xboole_0(X0) ),
% 2.31/0.98      inference(renaming,[status(thm)],[c_663]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_1884,plain,
% 2.31/0.98      ( ~ v3_pre_topc(k1_tops_1(sK1,sK3),sK1)
% 2.31/0.98      | ~ m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.31/0.98      | ~ r2_hidden(sK2,k1_tops_1(sK1,k1_tops_1(sK1,sK3)))
% 2.31/0.98      | ~ r1_tarski(k1_tops_1(sK1,sK3),sK3)
% 2.31/0.98      | v1_xboole_0(k1_tops_1(sK1,sK3)) ),
% 2.31/0.98      inference(instantiation,[status(thm)],[c_664]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_1888,plain,
% 2.31/0.98      ( v3_pre_topc(k1_tops_1(sK1,sK3),sK1) != iProver_top
% 2.31/0.98      | m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.31/0.98      | r2_hidden(sK2,k1_tops_1(sK1,k1_tops_1(sK1,sK3))) != iProver_top
% 2.31/0.98      | r1_tarski(k1_tops_1(sK1,sK3),sK3) != iProver_top
% 2.31/0.98      | v1_xboole_0(k1_tops_1(sK1,sK3)) = iProver_top ),
% 2.31/0.98      inference(predicate_to_equality,[status(thm)],[c_1884]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_1836,plain,
% 2.31/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.31/0.98      | r1_tarski(k1_tops_1(sK1,sK3),sK3) ),
% 2.31/0.98      inference(instantiation,[status(thm)],[c_519]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_1837,plain,
% 2.31/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.31/0.98      | r1_tarski(k1_tops_1(sK1,sK3),sK3) = iProver_top ),
% 2.31/0.98      inference(predicate_to_equality,[status(thm)],[c_1836]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_9,plain,
% 2.31/0.98      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 2.31/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.31/0.98      | ~ v2_pre_topc(X0)
% 2.31/0.98      | ~ l1_pre_topc(X0) ),
% 2.31/0.98      inference(cnf_transformation,[],[f46]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_417,plain,
% 2.31/0.98      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 2.31/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.31/0.98      | ~ l1_pre_topc(X0)
% 2.31/0.98      | sK1 != X0 ),
% 2.31/0.98      inference(resolution_lifted,[status(thm)],[c_9,c_21]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_418,plain,
% 2.31/0.98      ( v3_pre_topc(k1_tops_1(sK1,X0),sK1)
% 2.31/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.31/0.98      | ~ l1_pre_topc(sK1) ),
% 2.31/0.98      inference(unflattening,[status(thm)],[c_417]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_422,plain,
% 2.31/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.31/0.98      | v3_pre_topc(k1_tops_1(sK1,X0),sK1) ),
% 2.31/0.98      inference(global_propositional_subsumption,
% 2.31/0.98                [status(thm)],
% 2.31/0.98                [c_418,c_20]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_423,plain,
% 2.31/0.98      ( v3_pre_topc(k1_tops_1(sK1,X0),sK1)
% 2.31/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.31/0.98      inference(renaming,[status(thm)],[c_422]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_1833,plain,
% 2.31/0.98      ( v3_pre_topc(k1_tops_1(sK1,sK3),sK1)
% 2.31/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.31/0.98      inference(instantiation,[status(thm)],[c_423]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_1834,plain,
% 2.31/0.98      ( v3_pre_topc(k1_tops_1(sK1,sK3),sK1) = iProver_top
% 2.31/0.98      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.31/0.98      inference(predicate_to_equality,[status(thm)],[c_1833]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_689,plain,
% 2.31/0.98      ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 2.31/0.98      | r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top ),
% 2.31/0.98      inference(predicate_to_equality,[status(thm)],[c_688]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_27,plain,
% 2.31/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.31/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(c_26,plain,
% 2.31/0.98      ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
% 2.31/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.31/0.98  
% 2.31/0.98  cnf(contradiction,plain,
% 2.31/0.98      ( $false ),
% 2.31/0.98      inference(minisat,
% 2.31/0.98                [status(thm)],
% 2.31/0.98                [c_5740,c_4940,c_4001,c_3221,c_2221,c_2156,c_1908,c_1888,
% 2.31/0.98                 c_1837,c_1834,c_689,c_27,c_26]) ).
% 2.31/0.98  
% 2.31/0.98  
% 2.31/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.31/0.98  
% 2.31/0.98  ------                               Statistics
% 2.31/0.98  
% 2.31/0.98  ------ General
% 2.31/0.98  
% 2.31/0.98  abstr_ref_over_cycles:                  0
% 2.31/0.98  abstr_ref_under_cycles:                 0
% 2.31/0.98  gc_basic_clause_elim:                   0
% 2.31/0.98  forced_gc_time:                         0
% 2.31/0.98  parsing_time:                           0.009
% 2.31/0.98  unif_index_cands_time:                  0.
% 2.31/0.98  unif_index_add_time:                    0.
% 2.31/0.98  orderings_time:                         0.
% 2.31/0.98  out_proof_time:                         0.009
% 2.31/0.98  total_time:                             0.163
% 2.31/0.98  num_of_symbols:                         50
% 2.31/0.98  num_of_terms:                           3318
% 2.31/0.98  
% 2.31/0.98  ------ Preprocessing
% 2.31/0.98  
% 2.31/0.98  num_of_splits:                          4
% 2.31/0.98  num_of_split_atoms:                     3
% 2.31/0.98  num_of_reused_defs:                     1
% 2.31/0.98  num_eq_ax_congr_red:                    9
% 2.31/0.98  num_of_sem_filtered_clauses:            4
% 2.31/0.98  num_of_subtypes:                        0
% 2.31/0.98  monotx_restored_types:                  0
% 2.31/0.98  sat_num_of_epr_types:                   0
% 2.31/0.98  sat_num_of_non_cyclic_types:            0
% 2.31/0.98  sat_guarded_non_collapsed_types:        0
% 2.31/0.98  num_pure_diseq_elim:                    0
% 2.31/0.98  simp_replaced_by:                       0
% 2.31/0.98  res_preprocessed:                       97
% 2.31/0.98  prep_upred:                             0
% 2.31/0.98  prep_unflattend:                        29
% 2.31/0.98  smt_new_axioms:                         0
% 2.31/0.98  pred_elim_cands:                        5
% 2.31/0.98  pred_elim:                              4
% 2.31/0.98  pred_elim_cl:                           5
% 2.31/0.98  pred_elim_cycles:                       10
% 2.31/0.98  merged_defs:                            8
% 2.31/0.98  merged_defs_ncl:                        0
% 2.31/0.98  bin_hyper_res:                          9
% 2.31/0.98  prep_cycles:                            4
% 2.31/0.98  pred_elim_time:                         0.013
% 2.31/0.98  splitting_time:                         0.
% 2.31/0.98  sem_filter_time:                        0.
% 2.31/0.98  monotx_time:                            0.
% 2.31/0.98  subtype_inf_time:                       0.
% 2.31/0.98  
% 2.31/0.98  ------ Problem properties
% 2.31/0.98  
% 2.31/0.98  clauses:                                21
% 2.31/0.98  conjectures:                            2
% 2.31/0.98  epr:                                    7
% 2.31/0.98  horn:                                   18
% 2.31/0.98  ground:                                 6
% 2.31/0.98  unary:                                  4
% 2.31/0.98  binary:                                 11
% 2.31/0.98  lits:                                   48
% 2.31/0.98  lits_eq:                                3
% 2.31/0.98  fd_pure:                                0
% 2.31/0.98  fd_pseudo:                              0
% 2.31/0.98  fd_cond:                                0
% 2.31/0.98  fd_pseudo_cond:                         1
% 2.31/0.98  ac_symbols:                             0
% 2.31/0.99  
% 2.31/0.99  ------ Propositional Solver
% 2.31/0.99  
% 2.31/0.99  prop_solver_calls:                      27
% 2.31/0.99  prop_fast_solver_calls:                 876
% 2.31/0.99  smt_solver_calls:                       0
% 2.31/0.99  smt_fast_solver_calls:                  0
% 2.31/0.99  prop_num_of_clauses:                    1780
% 2.31/0.99  prop_preprocess_simplified:             6007
% 2.31/0.99  prop_fo_subsumed:                       32
% 2.31/0.99  prop_solver_time:                       0.
% 2.31/0.99  smt_solver_time:                        0.
% 2.31/0.99  smt_fast_solver_time:                   0.
% 2.31/0.99  prop_fast_solver_time:                  0.
% 2.31/0.99  prop_unsat_core_time:                   0.
% 2.31/0.99  
% 2.31/0.99  ------ QBF
% 2.31/0.99  
% 2.31/0.99  qbf_q_res:                              0
% 2.31/0.99  qbf_num_tautologies:                    0
% 2.31/0.99  qbf_prep_cycles:                        0
% 2.31/0.99  
% 2.31/0.99  ------ BMC1
% 2.31/0.99  
% 2.31/0.99  bmc1_current_bound:                     -1
% 2.31/0.99  bmc1_last_solved_bound:                 -1
% 2.31/0.99  bmc1_unsat_core_size:                   -1
% 2.31/0.99  bmc1_unsat_core_parents_size:           -1
% 2.31/0.99  bmc1_merge_next_fun:                    0
% 2.31/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.31/0.99  
% 2.31/0.99  ------ Instantiation
% 2.31/0.99  
% 2.31/0.99  inst_num_of_clauses:                    516
% 2.31/0.99  inst_num_in_passive:                    267
% 2.31/0.99  inst_num_in_active:                     229
% 2.31/0.99  inst_num_in_unprocessed:                20
% 2.31/0.99  inst_num_of_loops:                      320
% 2.31/0.99  inst_num_of_learning_restarts:          0
% 2.31/0.99  inst_num_moves_active_passive:          89
% 2.31/0.99  inst_lit_activity:                      0
% 2.31/0.99  inst_lit_activity_moves:                0
% 2.31/0.99  inst_num_tautologies:                   0
% 2.31/0.99  inst_num_prop_implied:                  0
% 2.31/0.99  inst_num_existing_simplified:           0
% 2.31/0.99  inst_num_eq_res_simplified:             0
% 2.31/0.99  inst_num_child_elim:                    0
% 2.31/0.99  inst_num_of_dismatching_blockings:      184
% 2.31/0.99  inst_num_of_non_proper_insts:           560
% 2.31/0.99  inst_num_of_duplicates:                 0
% 2.31/0.99  inst_inst_num_from_inst_to_res:         0
% 2.31/0.99  inst_dismatching_checking_time:         0.
% 2.31/0.99  
% 2.31/0.99  ------ Resolution
% 2.31/0.99  
% 2.31/0.99  res_num_of_clauses:                     0
% 2.31/0.99  res_num_in_passive:                     0
% 2.31/0.99  res_num_in_active:                      0
% 2.31/0.99  res_num_of_loops:                       101
% 2.31/0.99  res_forward_subset_subsumed:            47
% 2.31/0.99  res_backward_subset_subsumed:           0
% 2.31/0.99  res_forward_subsumed:                   0
% 2.31/0.99  res_backward_subsumed:                  0
% 2.31/0.99  res_forward_subsumption_resolution:     1
% 2.31/0.99  res_backward_subsumption_resolution:    0
% 2.31/0.99  res_clause_to_clause_subsumption:       468
% 2.31/0.99  res_orphan_elimination:                 0
% 2.31/0.99  res_tautology_del:                      54
% 2.31/0.99  res_num_eq_res_simplified:              0
% 2.31/0.99  res_num_sel_changes:                    0
% 2.31/0.99  res_moves_from_active_to_pass:          0
% 2.31/0.99  
% 2.31/0.99  ------ Superposition
% 2.31/0.99  
% 2.31/0.99  sup_time_total:                         0.
% 2.31/0.99  sup_time_generating:                    0.
% 2.31/0.99  sup_time_sim_full:                      0.
% 2.31/0.99  sup_time_sim_immed:                     0.
% 2.31/0.99  
% 2.31/0.99  sup_num_of_clauses:                     78
% 2.31/0.99  sup_num_in_active:                      64
% 2.31/0.99  sup_num_in_passive:                     14
% 2.31/0.99  sup_num_of_loops:                       63
% 2.31/0.99  sup_fw_superposition:                   67
% 2.31/0.99  sup_bw_superposition:                   43
% 2.31/0.99  sup_immediate_simplified:               23
% 2.31/0.99  sup_given_eliminated:                   0
% 2.31/0.99  comparisons_done:                       0
% 2.31/0.99  comparisons_avoided:                    0
% 2.31/0.99  
% 2.31/0.99  ------ Simplifications
% 2.31/0.99  
% 2.31/0.99  
% 2.31/0.99  sim_fw_subset_subsumed:                 16
% 2.31/0.99  sim_bw_subset_subsumed:                 1
% 2.31/0.99  sim_fw_subsumed:                        5
% 2.31/0.99  sim_bw_subsumed:                        1
% 2.31/0.99  sim_fw_subsumption_res:                 2
% 2.31/0.99  sim_bw_subsumption_res:                 1
% 2.31/0.99  sim_tautology_del:                      2
% 2.31/0.99  sim_eq_tautology_del:                   2
% 2.31/0.99  sim_eq_res_simp:                        0
% 2.31/0.99  sim_fw_demodulated:                     0
% 2.31/0.99  sim_bw_demodulated:                     0
% 2.31/0.99  sim_light_normalised:                   0
% 2.31/0.99  sim_joinable_taut:                      0
% 2.31/0.99  sim_joinable_simp:                      0
% 2.31/0.99  sim_ac_normalised:                      0
% 2.31/0.99  sim_smt_subsumption:                    0
% 2.31/0.99  
%------------------------------------------------------------------------------
