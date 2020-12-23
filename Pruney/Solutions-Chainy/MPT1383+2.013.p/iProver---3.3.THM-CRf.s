%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:18:22 EST 2020

% Result     : Theorem 1.80s
% Output     : CNFRefutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 535 expanded)
%              Number of clauses        :   92 ( 127 expanded)
%              Number of leaves         :   17 ( 153 expanded)
%              Depth                    :   21
%              Number of atoms          :  704 (5736 expanded)
%              Number of equality atoms :   46 (  80 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   30 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
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

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( m1_connsp_2(X2,X0,X1)
                <=> ? [X3] :
                      ( r2_hidden(X1,X3)
                      & r1_tarski(X3,X2)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <~> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <~> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( ~ r2_hidden(X1,X3)
                    | ~ r1_tarski(X3,X2)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ m1_connsp_2(X2,X0,X1) )
              & ( ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | m1_connsp_2(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( ~ r2_hidden(X1,X3)
                    | ~ r1_tarski(X3,X2)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ m1_connsp_2(X2,X0,X1) )
              & ( ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | m1_connsp_2(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( ~ r2_hidden(X1,X3)
                    | ~ r1_tarski(X3,X2)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ m1_connsp_2(X2,X0,X1) )
              & ( ? [X4] :
                    ( r2_hidden(X1,X4)
                    & r1_tarski(X4,X2)
                    & v3_pre_topc(X4,X0)
                    & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                | m1_connsp_2(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f31])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ? [X4] :
          ( r2_hidden(X1,X4)
          & r1_tarski(X4,X2)
          & v3_pre_topc(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r2_hidden(X1,sK3)
        & r1_tarski(sK3,X2)
        & v3_pre_topc(sK3,X0)
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X1,X3)
                | ~ r1_tarski(X3,X2)
                | ~ v3_pre_topc(X3,X0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ m1_connsp_2(X2,X0,X1) )
          & ( ? [X4] :
                ( r2_hidden(X1,X4)
                & r1_tarski(X4,X2)
                & v3_pre_topc(X4,X0)
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            | m1_connsp_2(X2,X0,X1) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ! [X3] :
              ( ~ r2_hidden(X1,X3)
              | ~ r1_tarski(X3,sK2)
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_connsp_2(sK2,X0,X1) )
        & ( ? [X4] :
              ( r2_hidden(X1,X4)
              & r1_tarski(X4,sK2)
              & v3_pre_topc(X4,X0)
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
          | m1_connsp_2(sK2,X0,X1) )
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( ~ r2_hidden(X1,X3)
                    | ~ r1_tarski(X3,X2)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ m1_connsp_2(X2,X0,X1) )
              & ( ? [X4] :
                    ( r2_hidden(X1,X4)
                    & r1_tarski(X4,X2)
                    & v3_pre_topc(X4,X0)
                    & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                | m1_connsp_2(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(sK1,X3)
                  | ~ r1_tarski(X3,X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_connsp_2(X2,X0,sK1) )
            & ( ? [X4] :
                  ( r2_hidden(sK1,X4)
                  & r1_tarski(X4,X2)
                  & v3_pre_topc(X4,X0)
                  & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | m1_connsp_2(X2,X0,sK1) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK1,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ! [X3] :
                      ( ~ r2_hidden(X1,X3)
                      | ~ r1_tarski(X3,X2)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_connsp_2(X2,X0,X1) )
                & ( ? [X4] :
                      ( r2_hidden(X1,X4)
                      & r1_tarski(X4,X2)
                      & v3_pre_topc(X4,X0)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | m1_connsp_2(X2,X0,X1) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( ~ r2_hidden(X1,X3)
                    | ~ r1_tarski(X3,X2)
                    | ~ v3_pre_topc(X3,sK0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
                | ~ m1_connsp_2(X2,sK0,X1) )
              & ( ? [X4] :
                    ( r2_hidden(X1,X4)
                    & r1_tarski(X4,X2)
                    & v3_pre_topc(X4,sK0)
                    & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
                | m1_connsp_2(X2,sK0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ( ! [X3] :
          ( ~ r2_hidden(sK1,X3)
          | ~ r1_tarski(X3,sK2)
          | ~ v3_pre_topc(X3,sK0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
      | ~ m1_connsp_2(sK2,sK0,sK1) )
    & ( ( r2_hidden(sK1,sK3)
        & r1_tarski(sK3,sK2)
        & v3_pre_topc(sK3,sK0)
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) )
      | m1_connsp_2(sK2,sK0,sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f32,f36,f35,f34,f33])).

fof(f53,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f37])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
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

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f52,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f27])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
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

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f51,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f60,plain,(
    ! [X3] :
      ( ~ r2_hidden(sK1,X3)
      | ~ r1_tarski(X3,sK2)
      | ~ v3_pre_topc(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_connsp_2(sK2,sK0,sK1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f54,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f37])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f59,plain,
    ( r2_hidden(sK1,sK3)
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f58,plain,
    ( r1_tarski(sK3,sK2)
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f57,plain,
    ( v3_pre_topc(sK3,sK0)
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f56,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f55,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1321,plain,
    ( ~ r1_tarski(X0_44,X1_44)
    | ~ r1_tarski(X2_44,X0_44)
    | r1_tarski(X2_44,X1_44) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_3149,plain,
    ( ~ r1_tarski(X0_44,k1_tops_1(sK0,sK3))
    | r1_tarski(X0_44,k1_tops_1(sK0,sK2))
    | ~ r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_1321])).

cnf(c_3982,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2))
    | ~ r1_tarski(k1_tarski(X0_44),k1_tops_1(sK0,sK3))
    | r1_tarski(k1_tarski(X0_44),k1_tops_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_3149])).

cnf(c_3984,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2))
    | ~ r1_tarski(k1_tarski(sK1),k1_tops_1(sK0,sK3))
    | r1_tarski(k1_tarski(sK1),k1_tops_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_3982])).

cnf(c_1330,plain,
    ( ~ r1_tarski(X0_44,X1_44)
    | r1_tarski(X2_44,X3_44)
    | X2_44 != X0_44
    | X3_44 != X1_44 ),
    theory(equality)).

cnf(c_2216,plain,
    ( r1_tarski(X0_44,X1_44)
    | ~ r1_tarski(k1_tarski(sK1),sK3)
    | X0_44 != k1_tarski(sK1)
    | X1_44 != sK3 ),
    inference(instantiation,[status(thm)],[c_1330])).

cnf(c_2651,plain,
    ( r1_tarski(X0_44,k1_tops_1(sK0,sK3))
    | ~ r1_tarski(k1_tarski(sK1),sK3)
    | X0_44 != k1_tarski(sK1)
    | k1_tops_1(sK0,sK3) != sK3 ),
    inference(instantiation,[status(thm)],[c_2216])).

cnf(c_2830,plain,
    ( r1_tarski(k1_tarski(sK1),k1_tops_1(sK0,sK3))
    | ~ r1_tarski(k1_tarski(sK1),sK3)
    | k1_tops_1(sK0,sK3) != sK3
    | k1_tarski(sK1) != k1_tarski(sK1) ),
    inference(instantiation,[status(thm)],[c_2651])).

cnf(c_3,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1320,plain,
    ( m1_subset_1(X0_44,k1_zfmisc_1(X1_44))
    | ~ r1_tarski(X0_44,X1_44) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_2790,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1320])).

cnf(c_2266,plain,
    ( r1_tarski(X0_44,u1_struct_0(sK0))
    | ~ r1_tarski(X0_44,sK2)
    | ~ r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1321])).

cnf(c_2617,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
    | ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_2266])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_20,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_502,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_20])).

cnf(c_503,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,X1)
    | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1)) ),
    inference(unflattening,[status(thm)],[c_502])).

cnf(c_1310,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1_44,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0_44,X1_44)
    | r1_tarski(k1_tops_1(sK0,X0_44),k1_tops_1(sK0,X1_44)) ),
    inference(subtyping,[status(esa)],[c_503])).

cnf(c_2166,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,X0_44))
    | ~ r1_tarski(sK3,X0_44) ),
    inference(instantiation,[status(thm)],[c_1310])).

cnf(c_2580,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2))
    | ~ r1_tarski(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_2166])).

cnf(c_9,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_21,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_444,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X1,X0) = X0
    | sK0 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_21])).

cnf(c_445,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK0)
    | k1_tops_1(X1,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_444])).

cnf(c_449,plain,
    ( ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X0,X1)
    | k1_tops_1(X1,X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_445,c_20])).

cnf(c_450,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = X0 ),
    inference(renaming,[status(thm)],[c_449])).

cnf(c_484,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(X1,X0) = X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_450,c_20])).

cnf(c_485,plain,
    ( ~ v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_484])).

cnf(c_1311,plain,
    ( ~ v3_pre_topc(X0_44,sK0)
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1_44,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0_44) = X0_44 ),
    inference(subtyping,[status(esa)],[c_485])).

cnf(c_1323,plain,
    ( ~ v3_pre_topc(X0_44,sK0)
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0_44) = X0_44
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_1311])).

cnf(c_1324,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_1311])).

cnf(c_1322,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_1311])).

cnf(c_1440,plain,
    ( k1_tops_1(sK0,X0_44) = X0_44
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(X0_44,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1323,c_1324,c_1322])).

cnf(c_1441,plain,
    ( ~ v3_pre_topc(X0_44,sK0)
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0_44) = X0_44 ),
    inference(renaming,[status(thm)],[c_1440])).

cnf(c_2192,plain,
    ( ~ v3_pre_topc(sK3,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,sK3) = sK3 ),
    inference(instantiation,[status(thm)],[c_1441])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1319,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X1_44))
    | r1_tarski(X0_44,X1_44) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_2106,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1319])).

cnf(c_2,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_178,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(k1_tarski(X0),X1) ),
    inference(prop_impl,[status(thm)],[c_2])).

cnf(c_10,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_22,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_364,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_22])).

cnf(c_365,plain,
    ( m1_connsp_2(X0,sK0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(X1,k1_tops_1(sK0,X0))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_364])).

cnf(c_369,plain,
    ( m1_connsp_2(X0,sK0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(X1,k1_tops_1(sK0,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_365,c_21,c_20])).

cnf(c_705,plain,
    ( m1_connsp_2(X0,sK0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k1_tarski(X2),X3)
    | X1 != X2
    | k1_tops_1(sK0,X0) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_178,c_369])).

cnf(c_706,plain,
    ( m1_connsp_2(X0,sK0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k1_tarski(X1),k1_tops_1(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_705])).

cnf(c_1305,plain,
    ( m1_connsp_2(X0_44,sK0,X1_44)
    | ~ m1_subset_1(X1_44,u1_struct_0(sK0))
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k1_tarski(X1_44),k1_tops_1(sK0,X0_44)) ),
    inference(subtyping,[status(esa)],[c_706])).

cnf(c_2101,plain,
    ( m1_connsp_2(sK2,sK0,X0_44)
    | ~ m1_subset_1(X0_44,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k1_tarski(X0_44),k1_tops_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_1305])).

cnf(c_2103,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r1_tarski(k1_tarski(sK1),k1_tops_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_2101])).

cnf(c_13,negated_conjecture,
    ( ~ m1_connsp_2(sK2,sK0,sK1)
    | ~ v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1,X0)
    | ~ r1_tarski(X0,sK2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_11,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_12,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_130,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X0,X1,X2)
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11,c_12])).

cnf(c_131,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_130])).

cnf(c_322,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_131,c_22])).

cnf(c_323,plain,
    ( ~ m1_connsp_2(X0,sK0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | r2_hidden(X1,k1_tops_1(sK0,X0))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_322])).

cnf(c_327,plain,
    ( ~ m1_connsp_2(X0,sK0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | r2_hidden(X1,k1_tops_1(sK0,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_323,c_21,c_20])).

cnf(c_740,plain,
    ( ~ m1_connsp_2(X0,sK0,X1)
    | ~ m1_connsp_2(sK2,sK0,sK1)
    | ~ v3_pre_topc(X2,sK0)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X2,sK2)
    | k1_tops_1(sK0,X0) != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_327])).

cnf(c_741,plain,
    ( ~ m1_connsp_2(X0,sK0,sK1)
    | ~ m1_connsp_2(sK2,sK0,sK1)
    | ~ v3_pre_topc(k1_tops_1(sK0,X0),sK0)
    | ~ m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r1_tarski(k1_tops_1(sK0,X0),sK2) ),
    inference(unflattening,[status(thm)],[c_740])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_745,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(k1_tops_1(sK0,X0),sK0)
    | ~ m1_connsp_2(sK2,sK0,sK1)
    | ~ m1_connsp_2(X0,sK0,sK1)
    | ~ r1_tarski(k1_tops_1(sK0,X0),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_741,c_19])).

cnf(c_746,plain,
    ( ~ m1_connsp_2(X0,sK0,sK1)
    | ~ m1_connsp_2(sK2,sK0,sK1)
    | ~ v3_pre_topc(k1_tops_1(sK0,X0),sK0)
    | ~ m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k1_tops_1(sK0,X0),sK2) ),
    inference(renaming,[status(thm)],[c_745])).

cnf(c_1303,plain,
    ( ~ m1_connsp_2(X0_44,sK0,sK1)
    | ~ m1_connsp_2(sK2,sK0,sK1)
    | ~ v3_pre_topc(k1_tops_1(sK0,X0_44),sK0)
    | ~ m1_subset_1(k1_tops_1(sK0,X0_44),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k1_tops_1(sK0,X0_44),sK2) ),
    inference(subtyping,[status(esa)],[c_746])).

cnf(c_2082,plain,
    ( ~ m1_connsp_2(sK2,sK0,sK1)
    | ~ v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
    | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    inference(instantiation,[status(thm)],[c_1303])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_520,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_20])).

cnf(c_521,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,X0),X0) ),
    inference(unflattening,[status(thm)],[c_520])).

cnf(c_1309,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,X0_44),X0_44) ),
    inference(subtyping,[status(esa)],[c_521])).

cnf(c_2079,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    inference(instantiation,[status(thm)],[c_1309])).

cnf(c_5,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_401,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_21])).

cnf(c_402,plain,
    ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_401])).

cnf(c_406,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(k1_tops_1(sK0,X0),sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_402,c_20])).

cnf(c_407,plain,
    ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(renaming,[status(thm)],[c_406])).

cnf(c_1312,plain,
    ( v3_pre_topc(k1_tops_1(sK0,X0_44),sK0)
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_407])).

cnf(c_2076,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_1312])).

cnf(c_1328,plain,
    ( X0_44 = X0_44 ),
    theory(equality)).

cnf(c_1343,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_1328])).

cnf(c_1331,plain,
    ( X0_44 != X1_44
    | k1_tarski(X0_44) = k1_tarski(X1_44) ),
    theory(equality)).

cnf(c_1337,plain,
    ( k1_tarski(sK1) = k1_tarski(sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1331])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_180,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k1_tarski(X0),X1) ),
    inference(prop_impl,[status(thm)],[c_1])).

cnf(c_14,negated_conjecture,
    ( m1_connsp_2(sK2,sK0,sK1)
    | r2_hidden(sK1,sK3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_695,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | r1_tarski(k1_tarski(X0),X1)
    | sK3 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_180,c_14])).

cnf(c_696,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | r1_tarski(k1_tarski(sK1),sK3) ),
    inference(unflattening,[status(thm)],[c_695])).

cnf(c_15,negated_conjecture,
    ( m1_connsp_2(sK2,sK0,sK1)
    | r1_tarski(sK3,sK2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_16,negated_conjecture,
    ( m1_connsp_2(sK2,sK0,sK1)
    | v3_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_17,negated_conjecture,
    ( m1_connsp_2(sK2,sK0,sK1)
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f55])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3984,c_2830,c_2790,c_2617,c_2580,c_2192,c_2106,c_2103,c_2082,c_2079,c_2076,c_1343,c_1337,c_696,c_15,c_16,c_17,c_18,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 12:31:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.80/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/0.99  
% 1.80/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.80/0.99  
% 1.80/0.99  ------  iProver source info
% 1.80/0.99  
% 1.80/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.80/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.80/0.99  git: non_committed_changes: false
% 1.80/0.99  git: last_make_outside_of_git: false
% 1.80/0.99  
% 1.80/0.99  ------ 
% 1.80/0.99  
% 1.80/0.99  ------ Input Options
% 1.80/0.99  
% 1.80/0.99  --out_options                           all
% 1.80/0.99  --tptp_safe_out                         true
% 1.80/0.99  --problem_path                          ""
% 1.80/0.99  --include_path                          ""
% 1.80/0.99  --clausifier                            res/vclausify_rel
% 1.80/0.99  --clausifier_options                    --mode clausify
% 1.80/0.99  --stdin                                 false
% 1.80/0.99  --stats_out                             all
% 1.80/0.99  
% 1.80/0.99  ------ General Options
% 1.80/0.99  
% 1.80/0.99  --fof                                   false
% 1.80/0.99  --time_out_real                         305.
% 1.80/0.99  --time_out_virtual                      -1.
% 1.80/0.99  --symbol_type_check                     false
% 1.80/0.99  --clausify_out                          false
% 1.80/0.99  --sig_cnt_out                           false
% 1.80/0.99  --trig_cnt_out                          false
% 1.80/0.99  --trig_cnt_out_tolerance                1.
% 1.80/0.99  --trig_cnt_out_sk_spl                   false
% 1.80/0.99  --abstr_cl_out                          false
% 1.80/0.99  
% 1.80/0.99  ------ Global Options
% 1.80/0.99  
% 1.80/0.99  --schedule                              default
% 1.80/0.99  --add_important_lit                     false
% 1.80/0.99  --prop_solver_per_cl                    1000
% 1.80/0.99  --min_unsat_core                        false
% 1.80/0.99  --soft_assumptions                      false
% 1.80/0.99  --soft_lemma_size                       3
% 1.80/0.99  --prop_impl_unit_size                   0
% 1.80/0.99  --prop_impl_unit                        []
% 1.80/0.99  --share_sel_clauses                     true
% 1.80/0.99  --reset_solvers                         false
% 1.80/0.99  --bc_imp_inh                            [conj_cone]
% 1.80/0.99  --conj_cone_tolerance                   3.
% 1.80/0.99  --extra_neg_conj                        none
% 1.80/0.99  --large_theory_mode                     true
% 1.80/0.99  --prolific_symb_bound                   200
% 1.80/0.99  --lt_threshold                          2000
% 1.80/0.99  --clause_weak_htbl                      true
% 1.80/0.99  --gc_record_bc_elim                     false
% 1.80/0.99  
% 1.80/0.99  ------ Preprocessing Options
% 1.80/0.99  
% 1.80/0.99  --preprocessing_flag                    true
% 1.80/0.99  --time_out_prep_mult                    0.1
% 1.80/0.99  --splitting_mode                        input
% 1.80/0.99  --splitting_grd                         true
% 1.80/0.99  --splitting_cvd                         false
% 1.80/0.99  --splitting_cvd_svl                     false
% 1.80/0.99  --splitting_nvd                         32
% 1.80/0.99  --sub_typing                            true
% 1.80/0.99  --prep_gs_sim                           true
% 1.80/0.99  --prep_unflatten                        true
% 1.80/0.99  --prep_res_sim                          true
% 1.80/0.99  --prep_upred                            true
% 1.80/0.99  --prep_sem_filter                       exhaustive
% 1.80/0.99  --prep_sem_filter_out                   false
% 1.80/0.99  --pred_elim                             true
% 1.80/0.99  --res_sim_input                         true
% 1.80/0.99  --eq_ax_congr_red                       true
% 1.80/0.99  --pure_diseq_elim                       true
% 1.80/0.99  --brand_transform                       false
% 1.80/0.99  --non_eq_to_eq                          false
% 1.80/0.99  --prep_def_merge                        true
% 1.80/0.99  --prep_def_merge_prop_impl              false
% 1.80/0.99  --prep_def_merge_mbd                    true
% 1.80/0.99  --prep_def_merge_tr_red                 false
% 1.80/0.99  --prep_def_merge_tr_cl                  false
% 1.80/0.99  --smt_preprocessing                     true
% 1.80/0.99  --smt_ac_axioms                         fast
% 1.80/0.99  --preprocessed_out                      false
% 1.80/0.99  --preprocessed_stats                    false
% 1.80/0.99  
% 1.80/0.99  ------ Abstraction refinement Options
% 1.80/0.99  
% 1.80/0.99  --abstr_ref                             []
% 1.80/0.99  --abstr_ref_prep                        false
% 1.80/0.99  --abstr_ref_until_sat                   false
% 1.80/0.99  --abstr_ref_sig_restrict                funpre
% 1.80/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.80/0.99  --abstr_ref_under                       []
% 1.80/0.99  
% 1.80/0.99  ------ SAT Options
% 1.80/0.99  
% 1.80/0.99  --sat_mode                              false
% 1.80/0.99  --sat_fm_restart_options                ""
% 1.80/0.99  --sat_gr_def                            false
% 1.80/0.99  --sat_epr_types                         true
% 1.80/0.99  --sat_non_cyclic_types                  false
% 1.80/0.99  --sat_finite_models                     false
% 1.80/0.99  --sat_fm_lemmas                         false
% 1.80/0.99  --sat_fm_prep                           false
% 1.80/0.99  --sat_fm_uc_incr                        true
% 1.80/0.99  --sat_out_model                         small
% 1.80/0.99  --sat_out_clauses                       false
% 1.80/0.99  
% 1.80/0.99  ------ QBF Options
% 1.80/0.99  
% 1.80/0.99  --qbf_mode                              false
% 1.80/0.99  --qbf_elim_univ                         false
% 1.80/0.99  --qbf_dom_inst                          none
% 1.80/0.99  --qbf_dom_pre_inst                      false
% 1.80/0.99  --qbf_sk_in                             false
% 1.80/0.99  --qbf_pred_elim                         true
% 1.80/0.99  --qbf_split                             512
% 1.80/0.99  
% 1.80/0.99  ------ BMC1 Options
% 1.80/0.99  
% 1.80/0.99  --bmc1_incremental                      false
% 1.80/0.99  --bmc1_axioms                           reachable_all
% 1.80/0.99  --bmc1_min_bound                        0
% 1.80/0.99  --bmc1_max_bound                        -1
% 1.80/0.99  --bmc1_max_bound_default                -1
% 1.80/0.99  --bmc1_symbol_reachability              true
% 1.80/0.99  --bmc1_property_lemmas                  false
% 1.80/0.99  --bmc1_k_induction                      false
% 1.80/0.99  --bmc1_non_equiv_states                 false
% 1.80/0.99  --bmc1_deadlock                         false
% 1.80/0.99  --bmc1_ucm                              false
% 1.80/0.99  --bmc1_add_unsat_core                   none
% 1.80/0.99  --bmc1_unsat_core_children              false
% 1.80/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.80/0.99  --bmc1_out_stat                         full
% 1.80/0.99  --bmc1_ground_init                      false
% 1.80/0.99  --bmc1_pre_inst_next_state              false
% 1.80/0.99  --bmc1_pre_inst_state                   false
% 1.80/0.99  --bmc1_pre_inst_reach_state             false
% 1.80/0.99  --bmc1_out_unsat_core                   false
% 1.80/0.99  --bmc1_aig_witness_out                  false
% 1.80/0.99  --bmc1_verbose                          false
% 1.80/0.99  --bmc1_dump_clauses_tptp                false
% 1.80/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.80/0.99  --bmc1_dump_file                        -
% 1.80/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.80/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.80/0.99  --bmc1_ucm_extend_mode                  1
% 1.80/0.99  --bmc1_ucm_init_mode                    2
% 1.80/0.99  --bmc1_ucm_cone_mode                    none
% 1.80/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.80/0.99  --bmc1_ucm_relax_model                  4
% 1.80/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.80/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.80/0.99  --bmc1_ucm_layered_model                none
% 1.80/0.99  --bmc1_ucm_max_lemma_size               10
% 1.80/0.99  
% 1.80/0.99  ------ AIG Options
% 1.80/0.99  
% 1.80/0.99  --aig_mode                              false
% 1.80/0.99  
% 1.80/0.99  ------ Instantiation Options
% 1.80/0.99  
% 1.80/0.99  --instantiation_flag                    true
% 1.80/0.99  --inst_sos_flag                         false
% 1.80/0.99  --inst_sos_phase                        true
% 1.80/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.80/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.80/0.99  --inst_lit_sel_side                     num_symb
% 1.80/0.99  --inst_solver_per_active                1400
% 1.80/0.99  --inst_solver_calls_frac                1.
% 1.80/0.99  --inst_passive_queue_type               priority_queues
% 1.80/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.80/0.99  --inst_passive_queues_freq              [25;2]
% 1.80/0.99  --inst_dismatching                      true
% 1.80/0.99  --inst_eager_unprocessed_to_passive     true
% 1.80/0.99  --inst_prop_sim_given                   true
% 1.80/0.99  --inst_prop_sim_new                     false
% 1.80/0.99  --inst_subs_new                         false
% 1.80/0.99  --inst_eq_res_simp                      false
% 1.80/0.99  --inst_subs_given                       false
% 1.80/0.99  --inst_orphan_elimination               true
% 1.80/0.99  --inst_learning_loop_flag               true
% 1.80/0.99  --inst_learning_start                   3000
% 1.80/0.99  --inst_learning_factor                  2
% 1.80/0.99  --inst_start_prop_sim_after_learn       3
% 1.80/0.99  --inst_sel_renew                        solver
% 1.80/0.99  --inst_lit_activity_flag                true
% 1.80/0.99  --inst_restr_to_given                   false
% 1.80/0.99  --inst_activity_threshold               500
% 1.80/0.99  --inst_out_proof                        true
% 1.80/0.99  
% 1.80/0.99  ------ Resolution Options
% 1.80/0.99  
% 1.80/0.99  --resolution_flag                       true
% 1.80/0.99  --res_lit_sel                           adaptive
% 1.80/0.99  --res_lit_sel_side                      none
% 1.80/0.99  --res_ordering                          kbo
% 1.80/0.99  --res_to_prop_solver                    active
% 1.80/0.99  --res_prop_simpl_new                    false
% 1.80/0.99  --res_prop_simpl_given                  true
% 1.80/0.99  --res_passive_queue_type                priority_queues
% 1.80/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.80/0.99  --res_passive_queues_freq               [15;5]
% 1.80/0.99  --res_forward_subs                      full
% 1.80/0.99  --res_backward_subs                     full
% 1.80/0.99  --res_forward_subs_resolution           true
% 1.80/0.99  --res_backward_subs_resolution          true
% 1.80/0.99  --res_orphan_elimination                true
% 1.80/0.99  --res_time_limit                        2.
% 1.80/0.99  --res_out_proof                         true
% 1.80/0.99  
% 1.80/0.99  ------ Superposition Options
% 1.80/0.99  
% 1.80/0.99  --superposition_flag                    true
% 1.80/0.99  --sup_passive_queue_type                priority_queues
% 1.80/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.80/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.80/0.99  --demod_completeness_check              fast
% 1.80/0.99  --demod_use_ground                      true
% 1.80/0.99  --sup_to_prop_solver                    passive
% 1.80/0.99  --sup_prop_simpl_new                    true
% 1.80/0.99  --sup_prop_simpl_given                  true
% 1.80/0.99  --sup_fun_splitting                     false
% 1.80/0.99  --sup_smt_interval                      50000
% 1.80/0.99  
% 1.80/0.99  ------ Superposition Simplification Setup
% 1.80/0.99  
% 1.80/0.99  --sup_indices_passive                   []
% 1.80/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.80/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.80/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.80/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.80/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.80/0.99  --sup_full_bw                           [BwDemod]
% 1.80/0.99  --sup_immed_triv                        [TrivRules]
% 1.80/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.80/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.80/0.99  --sup_immed_bw_main                     []
% 1.80/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.80/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.80/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.80/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.80/0.99  
% 1.80/0.99  ------ Combination Options
% 1.80/0.99  
% 1.80/0.99  --comb_res_mult                         3
% 1.80/0.99  --comb_sup_mult                         2
% 1.80/0.99  --comb_inst_mult                        10
% 1.80/0.99  
% 1.80/0.99  ------ Debug Options
% 1.80/0.99  
% 1.80/0.99  --dbg_backtrace                         false
% 1.80/0.99  --dbg_dump_prop_clauses                 false
% 1.80/0.99  --dbg_dump_prop_clauses_file            -
% 1.80/0.99  --dbg_out_stat                          false
% 1.80/0.99  ------ Parsing...
% 1.80/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.80/0.99  
% 1.80/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 1.80/0.99  
% 1.80/0.99  ------ Preprocessing... gs_s  sp: 4 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.80/0.99  
% 1.80/0.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.80/0.99  ------ Proving...
% 1.80/0.99  ------ Problem Properties 
% 1.80/0.99  
% 1.80/0.99  
% 1.80/0.99  clauses                                 24
% 1.80/0.99  conjectures                             5
% 1.80/0.99  EPR                                     5
% 1.80/0.99  Horn                                    17
% 1.80/0.99  unary                                   2
% 1.80/0.99  binary                                  12
% 1.80/0.99  lits                                    65
% 1.80/0.99  lits eq                                 3
% 1.80/0.99  fd_pure                                 0
% 1.80/0.99  fd_pseudo                               0
% 1.80/0.99  fd_cond                                 0
% 1.80/0.99  fd_pseudo_cond                          0
% 1.80/0.99  AC symbols                              0
% 1.80/0.99  
% 1.80/0.99  ------ Schedule dynamic 5 is on 
% 1.80/0.99  
% 1.80/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.80/0.99  
% 1.80/0.99  
% 1.80/0.99  ------ 
% 1.80/0.99  Current options:
% 1.80/0.99  ------ 
% 1.80/0.99  
% 1.80/0.99  ------ Input Options
% 1.80/0.99  
% 1.80/0.99  --out_options                           all
% 1.80/0.99  --tptp_safe_out                         true
% 1.80/0.99  --problem_path                          ""
% 1.80/0.99  --include_path                          ""
% 1.80/0.99  --clausifier                            res/vclausify_rel
% 1.80/0.99  --clausifier_options                    --mode clausify
% 1.80/0.99  --stdin                                 false
% 1.80/0.99  --stats_out                             all
% 1.80/0.99  
% 1.80/0.99  ------ General Options
% 1.80/0.99  
% 1.80/0.99  --fof                                   false
% 1.80/0.99  --time_out_real                         305.
% 1.80/0.99  --time_out_virtual                      -1.
% 1.80/0.99  --symbol_type_check                     false
% 1.80/0.99  --clausify_out                          false
% 1.80/0.99  --sig_cnt_out                           false
% 1.80/0.99  --trig_cnt_out                          false
% 1.80/0.99  --trig_cnt_out_tolerance                1.
% 1.80/0.99  --trig_cnt_out_sk_spl                   false
% 1.80/0.99  --abstr_cl_out                          false
% 1.80/0.99  
% 1.80/0.99  ------ Global Options
% 1.80/0.99  
% 1.80/0.99  --schedule                              default
% 1.80/0.99  --add_important_lit                     false
% 1.80/0.99  --prop_solver_per_cl                    1000
% 1.80/0.99  --min_unsat_core                        false
% 1.80/0.99  --soft_assumptions                      false
% 1.80/0.99  --soft_lemma_size                       3
% 1.80/0.99  --prop_impl_unit_size                   0
% 1.80/0.99  --prop_impl_unit                        []
% 1.80/0.99  --share_sel_clauses                     true
% 1.80/0.99  --reset_solvers                         false
% 1.80/0.99  --bc_imp_inh                            [conj_cone]
% 1.80/0.99  --conj_cone_tolerance                   3.
% 1.80/0.99  --extra_neg_conj                        none
% 1.80/0.99  --large_theory_mode                     true
% 1.80/0.99  --prolific_symb_bound                   200
% 1.80/0.99  --lt_threshold                          2000
% 1.80/0.99  --clause_weak_htbl                      true
% 1.80/0.99  --gc_record_bc_elim                     false
% 1.80/0.99  
% 1.80/0.99  ------ Preprocessing Options
% 1.80/0.99  
% 1.80/0.99  --preprocessing_flag                    true
% 1.80/0.99  --time_out_prep_mult                    0.1
% 1.80/0.99  --splitting_mode                        input
% 1.80/0.99  --splitting_grd                         true
% 1.80/0.99  --splitting_cvd                         false
% 1.80/0.99  --splitting_cvd_svl                     false
% 1.80/0.99  --splitting_nvd                         32
% 1.80/0.99  --sub_typing                            true
% 1.80/0.99  --prep_gs_sim                           true
% 1.80/0.99  --prep_unflatten                        true
% 1.80/0.99  --prep_res_sim                          true
% 1.80/0.99  --prep_upred                            true
% 1.80/0.99  --prep_sem_filter                       exhaustive
% 1.80/0.99  --prep_sem_filter_out                   false
% 1.80/0.99  --pred_elim                             true
% 1.80/0.99  --res_sim_input                         true
% 1.80/0.99  --eq_ax_congr_red                       true
% 1.80/0.99  --pure_diseq_elim                       true
% 1.80/0.99  --brand_transform                       false
% 1.80/0.99  --non_eq_to_eq                          false
% 1.80/0.99  --prep_def_merge                        true
% 1.80/0.99  --prep_def_merge_prop_impl              false
% 1.80/0.99  --prep_def_merge_mbd                    true
% 1.80/0.99  --prep_def_merge_tr_red                 false
% 1.80/0.99  --prep_def_merge_tr_cl                  false
% 1.80/0.99  --smt_preprocessing                     true
% 1.80/0.99  --smt_ac_axioms                         fast
% 1.80/0.99  --preprocessed_out                      false
% 1.80/0.99  --preprocessed_stats                    false
% 1.80/0.99  
% 1.80/0.99  ------ Abstraction refinement Options
% 1.80/0.99  
% 1.80/0.99  --abstr_ref                             []
% 1.80/0.99  --abstr_ref_prep                        false
% 1.80/0.99  --abstr_ref_until_sat                   false
% 1.80/0.99  --abstr_ref_sig_restrict                funpre
% 1.80/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.80/0.99  --abstr_ref_under                       []
% 1.80/0.99  
% 1.80/0.99  ------ SAT Options
% 1.80/0.99  
% 1.80/0.99  --sat_mode                              false
% 1.80/0.99  --sat_fm_restart_options                ""
% 1.80/0.99  --sat_gr_def                            false
% 1.80/0.99  --sat_epr_types                         true
% 1.80/0.99  --sat_non_cyclic_types                  false
% 1.80/0.99  --sat_finite_models                     false
% 1.80/0.99  --sat_fm_lemmas                         false
% 1.80/0.99  --sat_fm_prep                           false
% 1.80/0.99  --sat_fm_uc_incr                        true
% 1.80/0.99  --sat_out_model                         small
% 1.80/0.99  --sat_out_clauses                       false
% 1.80/0.99  
% 1.80/0.99  ------ QBF Options
% 1.80/0.99  
% 1.80/0.99  --qbf_mode                              false
% 1.80/0.99  --qbf_elim_univ                         false
% 1.80/0.99  --qbf_dom_inst                          none
% 1.80/0.99  --qbf_dom_pre_inst                      false
% 1.80/0.99  --qbf_sk_in                             false
% 1.80/0.99  --qbf_pred_elim                         true
% 1.80/0.99  --qbf_split                             512
% 1.80/0.99  
% 1.80/0.99  ------ BMC1 Options
% 1.80/0.99  
% 1.80/0.99  --bmc1_incremental                      false
% 1.80/0.99  --bmc1_axioms                           reachable_all
% 1.80/0.99  --bmc1_min_bound                        0
% 1.80/0.99  --bmc1_max_bound                        -1
% 1.80/0.99  --bmc1_max_bound_default                -1
% 1.80/0.99  --bmc1_symbol_reachability              true
% 1.80/0.99  --bmc1_property_lemmas                  false
% 1.80/0.99  --bmc1_k_induction                      false
% 1.80/0.99  --bmc1_non_equiv_states                 false
% 1.80/0.99  --bmc1_deadlock                         false
% 1.80/0.99  --bmc1_ucm                              false
% 1.80/0.99  --bmc1_add_unsat_core                   none
% 1.80/0.99  --bmc1_unsat_core_children              false
% 1.80/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.80/0.99  --bmc1_out_stat                         full
% 1.80/0.99  --bmc1_ground_init                      false
% 1.80/0.99  --bmc1_pre_inst_next_state              false
% 1.80/0.99  --bmc1_pre_inst_state                   false
% 1.80/0.99  --bmc1_pre_inst_reach_state             false
% 1.80/0.99  --bmc1_out_unsat_core                   false
% 1.80/0.99  --bmc1_aig_witness_out                  false
% 1.80/0.99  --bmc1_verbose                          false
% 1.80/0.99  --bmc1_dump_clauses_tptp                false
% 1.80/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.80/0.99  --bmc1_dump_file                        -
% 1.80/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.80/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.80/0.99  --bmc1_ucm_extend_mode                  1
% 1.80/0.99  --bmc1_ucm_init_mode                    2
% 1.80/0.99  --bmc1_ucm_cone_mode                    none
% 1.80/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.80/0.99  --bmc1_ucm_relax_model                  4
% 1.80/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.80/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.80/0.99  --bmc1_ucm_layered_model                none
% 1.80/0.99  --bmc1_ucm_max_lemma_size               10
% 1.80/0.99  
% 1.80/0.99  ------ AIG Options
% 1.80/0.99  
% 1.80/0.99  --aig_mode                              false
% 1.80/0.99  
% 1.80/0.99  ------ Instantiation Options
% 1.80/0.99  
% 1.80/0.99  --instantiation_flag                    true
% 1.80/0.99  --inst_sos_flag                         false
% 1.80/0.99  --inst_sos_phase                        true
% 1.80/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.80/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.80/0.99  --inst_lit_sel_side                     none
% 1.80/0.99  --inst_solver_per_active                1400
% 1.80/0.99  --inst_solver_calls_frac                1.
% 1.80/0.99  --inst_passive_queue_type               priority_queues
% 1.80/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.80/0.99  --inst_passive_queues_freq              [25;2]
% 1.80/0.99  --inst_dismatching                      true
% 1.80/0.99  --inst_eager_unprocessed_to_passive     true
% 1.80/0.99  --inst_prop_sim_given                   true
% 1.80/0.99  --inst_prop_sim_new                     false
% 1.80/0.99  --inst_subs_new                         false
% 1.80/0.99  --inst_eq_res_simp                      false
% 1.80/0.99  --inst_subs_given                       false
% 1.80/0.99  --inst_orphan_elimination               true
% 1.80/0.99  --inst_learning_loop_flag               true
% 1.80/0.99  --inst_learning_start                   3000
% 1.80/0.99  --inst_learning_factor                  2
% 1.80/0.99  --inst_start_prop_sim_after_learn       3
% 1.80/0.99  --inst_sel_renew                        solver
% 1.80/0.99  --inst_lit_activity_flag                true
% 1.80/0.99  --inst_restr_to_given                   false
% 1.80/0.99  --inst_activity_threshold               500
% 1.80/0.99  --inst_out_proof                        true
% 1.80/0.99  
% 1.80/0.99  ------ Resolution Options
% 1.80/0.99  
% 1.80/0.99  --resolution_flag                       false
% 1.80/0.99  --res_lit_sel                           adaptive
% 1.80/0.99  --res_lit_sel_side                      none
% 1.80/0.99  --res_ordering                          kbo
% 1.80/0.99  --res_to_prop_solver                    active
% 1.80/0.99  --res_prop_simpl_new                    false
% 1.80/0.99  --res_prop_simpl_given                  true
% 1.80/0.99  --res_passive_queue_type                priority_queues
% 1.80/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.80/0.99  --res_passive_queues_freq               [15;5]
% 1.80/0.99  --res_forward_subs                      full
% 1.80/0.99  --res_backward_subs                     full
% 1.80/0.99  --res_forward_subs_resolution           true
% 1.80/0.99  --res_backward_subs_resolution          true
% 1.80/0.99  --res_orphan_elimination                true
% 1.80/0.99  --res_time_limit                        2.
% 1.80/0.99  --res_out_proof                         true
% 1.80/0.99  
% 1.80/0.99  ------ Superposition Options
% 1.80/0.99  
% 1.80/0.99  --superposition_flag                    true
% 1.80/0.99  --sup_passive_queue_type                priority_queues
% 1.80/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.80/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.80/0.99  --demod_completeness_check              fast
% 1.80/0.99  --demod_use_ground                      true
% 1.80/0.99  --sup_to_prop_solver                    passive
% 1.80/0.99  --sup_prop_simpl_new                    true
% 1.80/0.99  --sup_prop_simpl_given                  true
% 1.80/0.99  --sup_fun_splitting                     false
% 1.80/0.99  --sup_smt_interval                      50000
% 1.80/0.99  
% 1.80/0.99  ------ Superposition Simplification Setup
% 1.80/0.99  
% 1.80/0.99  --sup_indices_passive                   []
% 1.80/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.80/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.80/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.80/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.80/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.80/0.99  --sup_full_bw                           [BwDemod]
% 1.80/0.99  --sup_immed_triv                        [TrivRules]
% 1.80/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.80/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.80/0.99  --sup_immed_bw_main                     []
% 1.80/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.80/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.80/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.80/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.80/0.99  
% 1.80/0.99  ------ Combination Options
% 1.80/0.99  
% 1.80/0.99  --comb_res_mult                         3
% 1.80/0.99  --comb_sup_mult                         2
% 1.80/0.99  --comb_inst_mult                        10
% 1.80/0.99  
% 1.80/0.99  ------ Debug Options
% 1.80/0.99  
% 1.80/0.99  --dbg_backtrace                         false
% 1.80/0.99  --dbg_dump_prop_clauses                 false
% 1.80/0.99  --dbg_dump_prop_clauses_file            -
% 1.80/0.99  --dbg_out_stat                          false
% 1.80/0.99  
% 1.80/0.99  
% 1.80/0.99  
% 1.80/0.99  
% 1.80/0.99  ------ Proving...
% 1.80/0.99  
% 1.80/0.99  
% 1.80/0.99  % SZS status Theorem for theBenchmark.p
% 1.80/0.99  
% 1.80/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 1.80/0.99  
% 1.80/0.99  fof(f1,axiom,(
% 1.80/0.99    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.80/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.80/0.99  
% 1.80/0.99  fof(f12,plain,(
% 1.80/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.80/0.99    inference(ennf_transformation,[],[f1])).
% 1.80/0.99  
% 1.80/0.99  fof(f13,plain,(
% 1.80/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.80/0.99    inference(flattening,[],[f12])).
% 1.80/0.99  
% 1.80/0.99  fof(f38,plain,(
% 1.80/0.99    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 1.80/0.99    inference(cnf_transformation,[],[f13])).
% 1.80/0.99  
% 1.80/0.99  fof(f3,axiom,(
% 1.80/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.80/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.80/0.99  
% 1.80/0.99  fof(f28,plain,(
% 1.80/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.80/0.99    inference(nnf_transformation,[],[f3])).
% 1.80/0.99  
% 1.80/0.99  fof(f42,plain,(
% 1.80/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.80/0.99    inference(cnf_transformation,[],[f28])).
% 1.80/0.99  
% 1.80/0.99  fof(f6,axiom,(
% 1.80/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 1.80/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.80/0.99  
% 1.80/0.99  fof(f17,plain,(
% 1.80/0.99    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.80/0.99    inference(ennf_transformation,[],[f6])).
% 1.80/0.99  
% 1.80/0.99  fof(f18,plain,(
% 1.80/0.99    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.80/0.99    inference(flattening,[],[f17])).
% 1.80/0.99  
% 1.80/0.99  fof(f45,plain,(
% 1.80/0.99    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.80/0.99    inference(cnf_transformation,[],[f18])).
% 1.80/0.99  
% 1.80/0.99  fof(f10,conjecture,(
% 1.80/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 1.80/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.80/0.99  
% 1.80/0.99  fof(f11,negated_conjecture,(
% 1.80/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 1.80/0.99    inference(negated_conjecture,[],[f10])).
% 1.80/0.99  
% 1.80/0.99  fof(f25,plain,(
% 1.80/0.99    ? [X0] : (? [X1] : (? [X2] : ((m1_connsp_2(X2,X0,X1) <~> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.80/0.99    inference(ennf_transformation,[],[f11])).
% 1.80/0.99  
% 1.80/0.99  fof(f26,plain,(
% 1.80/0.99    ? [X0] : (? [X1] : (? [X2] : ((m1_connsp_2(X2,X0,X1) <~> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.80/0.99    inference(flattening,[],[f25])).
% 1.80/0.99  
% 1.80/0.99  fof(f30,plain,(
% 1.80/0.99    ? [X0] : (? [X1] : (? [X2] : (((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1)) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | m1_connsp_2(X2,X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.80/0.99    inference(nnf_transformation,[],[f26])).
% 1.80/0.99  
% 1.80/0.99  fof(f31,plain,(
% 1.80/0.99    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1)) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.80/0.99    inference(flattening,[],[f30])).
% 1.80/0.99  
% 1.80/0.99  fof(f32,plain,(
% 1.80/0.99    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1)) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.80/0.99    inference(rectify,[],[f31])).
% 1.80/0.99  
% 1.80/0.99  fof(f36,plain,(
% 1.80/0.99    ( ! [X2,X0,X1] : (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) => (r2_hidden(X1,sK3) & r1_tarski(sK3,X2) & v3_pre_topc(sK3,X0) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 1.80/0.99    introduced(choice_axiom,[])).
% 1.80/0.99  
% 1.80/0.99  fof(f35,plain,(
% 1.80/0.99    ( ! [X0,X1] : (? [X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1)) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(sK2,X0,X1)) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,sK2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | m1_connsp_2(sK2,X0,X1)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 1.80/0.99    introduced(choice_axiom,[])).
% 1.80/0.99  
% 1.80/0.99  fof(f34,plain,(
% 1.80/0.99    ( ! [X0] : (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1)) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : ((! [X3] : (~r2_hidden(sK1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,sK1)) & (? [X4] : (r2_hidden(sK1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | m1_connsp_2(X2,X0,sK1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK1,u1_struct_0(X0)))) )),
% 1.80/0.99    introduced(choice_axiom,[])).
% 1.80/0.99  
% 1.80/0.99  fof(f33,plain,(
% 1.80/0.99    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1)) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_connsp_2(X2,sK0,X1)) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,sK0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) | m1_connsp_2(X2,sK0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.80/0.99    introduced(choice_axiom,[])).
% 1.80/0.99  
% 1.80/0.99  fof(f37,plain,(
% 1.80/0.99    (((! [X3] : (~r2_hidden(sK1,X3) | ~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_connsp_2(sK2,sK0,sK1)) & ((r2_hidden(sK1,sK3) & r1_tarski(sK3,sK2) & v3_pre_topc(sK3,sK0) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))) | m1_connsp_2(sK2,sK0,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.80/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f32,f36,f35,f34,f33])).
% 1.80/0.99  
% 1.80/0.99  fof(f53,plain,(
% 1.80/0.99    l1_pre_topc(sK0)),
% 1.80/0.99    inference(cnf_transformation,[],[f37])).
% 1.80/0.99  
% 1.80/0.99  fof(f7,axiom,(
% 1.80/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 1.80/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.80/0.99  
% 1.80/0.99  fof(f19,plain,(
% 1.80/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.80/0.99    inference(ennf_transformation,[],[f7])).
% 1.80/0.99  
% 1.80/0.99  fof(f20,plain,(
% 1.80/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.80/0.99    inference(flattening,[],[f19])).
% 1.80/0.99  
% 1.80/0.99  fof(f46,plain,(
% 1.80/0.99    ( ! [X2,X0,X3,X1] : (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.80/0.99    inference(cnf_transformation,[],[f20])).
% 1.80/0.99  
% 1.80/0.99  fof(f52,plain,(
% 1.80/0.99    v2_pre_topc(sK0)),
% 1.80/0.99    inference(cnf_transformation,[],[f37])).
% 1.80/0.99  
% 1.80/0.99  fof(f41,plain,(
% 1.80/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.80/0.99    inference(cnf_transformation,[],[f28])).
% 1.80/0.99  
% 1.80/0.99  fof(f2,axiom,(
% 1.80/0.99    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.80/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.80/0.99  
% 1.80/0.99  fof(f27,plain,(
% 1.80/0.99    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 1.80/0.99    inference(nnf_transformation,[],[f2])).
% 1.80/0.99  
% 1.80/0.99  fof(f39,plain,(
% 1.80/0.99    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 1.80/0.99    inference(cnf_transformation,[],[f27])).
% 1.80/0.99  
% 1.80/0.99  fof(f8,axiom,(
% 1.80/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 1.80/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.80/0.99  
% 1.80/0.99  fof(f21,plain,(
% 1.80/0.99    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.80/0.99    inference(ennf_transformation,[],[f8])).
% 1.80/0.99  
% 1.80/0.99  fof(f22,plain,(
% 1.80/0.99    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.80/0.99    inference(flattening,[],[f21])).
% 1.80/0.99  
% 1.80/0.99  fof(f29,plain,(
% 1.80/0.99    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.80/0.99    inference(nnf_transformation,[],[f22])).
% 1.80/0.99  
% 1.80/0.99  fof(f49,plain,(
% 1.80/0.99    ( ! [X2,X0,X1] : (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.80/0.99    inference(cnf_transformation,[],[f29])).
% 1.80/0.99  
% 1.80/0.99  fof(f51,plain,(
% 1.80/0.99    ~v2_struct_0(sK0)),
% 1.80/0.99    inference(cnf_transformation,[],[f37])).
% 1.80/0.99  
% 1.80/0.99  fof(f60,plain,(
% 1.80/0.99    ( ! [X3] : (~r2_hidden(sK1,X3) | ~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_connsp_2(sK2,sK0,sK1)) )),
% 1.80/0.99    inference(cnf_transformation,[],[f37])).
% 1.80/0.99  
% 1.80/0.99  fof(f48,plain,(
% 1.80/0.99    ( ! [X2,X0,X1] : (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.80/0.99    inference(cnf_transformation,[],[f29])).
% 1.80/0.99  
% 1.80/0.99  fof(f9,axiom,(
% 1.80/0.99    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.80/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.80/0.99  
% 1.80/0.99  fof(f23,plain,(
% 1.80/0.99    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.80/0.99    inference(ennf_transformation,[],[f9])).
% 1.80/0.99  
% 1.80/0.99  fof(f24,plain,(
% 1.80/0.99    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.80/0.99    inference(flattening,[],[f23])).
% 1.80/0.99  
% 1.80/0.99  fof(f50,plain,(
% 1.80/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.80/0.99    inference(cnf_transformation,[],[f24])).
% 1.80/0.99  
% 1.80/0.99  fof(f54,plain,(
% 1.80/0.99    m1_subset_1(sK1,u1_struct_0(sK0))),
% 1.80/0.99    inference(cnf_transformation,[],[f37])).
% 1.80/0.99  
% 1.80/0.99  fof(f5,axiom,(
% 1.80/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 1.80/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.80/0.99  
% 1.80/0.99  fof(f16,plain,(
% 1.80/0.99    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.80/0.99    inference(ennf_transformation,[],[f5])).
% 1.80/0.99  
% 1.80/0.99  fof(f44,plain,(
% 1.80/0.99    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.80/0.99    inference(cnf_transformation,[],[f16])).
% 1.80/0.99  
% 1.80/0.99  fof(f4,axiom,(
% 1.80/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 1.80/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.80/0.99  
% 1.80/0.99  fof(f14,plain,(
% 1.80/0.99    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.80/0.99    inference(ennf_transformation,[],[f4])).
% 1.80/0.99  
% 1.80/0.99  fof(f15,plain,(
% 1.80/0.99    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.80/0.99    inference(flattening,[],[f14])).
% 1.80/0.99  
% 1.80/0.99  fof(f43,plain,(
% 1.80/0.99    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.80/0.99    inference(cnf_transformation,[],[f15])).
% 1.80/0.99  
% 1.80/0.99  fof(f40,plain,(
% 1.80/0.99    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.80/0.99    inference(cnf_transformation,[],[f27])).
% 1.80/0.99  
% 1.80/0.99  fof(f59,plain,(
% 1.80/0.99    r2_hidden(sK1,sK3) | m1_connsp_2(sK2,sK0,sK1)),
% 1.80/0.99    inference(cnf_transformation,[],[f37])).
% 1.80/0.99  
% 1.80/0.99  fof(f58,plain,(
% 1.80/0.99    r1_tarski(sK3,sK2) | m1_connsp_2(sK2,sK0,sK1)),
% 1.80/0.99    inference(cnf_transformation,[],[f37])).
% 1.80/0.99  
% 1.80/0.99  fof(f57,plain,(
% 1.80/0.99    v3_pre_topc(sK3,sK0) | m1_connsp_2(sK2,sK0,sK1)),
% 1.80/0.99    inference(cnf_transformation,[],[f37])).
% 1.80/0.99  
% 1.80/0.99  fof(f56,plain,(
% 1.80/0.99    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | m1_connsp_2(sK2,sK0,sK1)),
% 1.80/0.99    inference(cnf_transformation,[],[f37])).
% 1.80/0.99  
% 1.80/0.99  fof(f55,plain,(
% 1.80/0.99    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.80/0.99    inference(cnf_transformation,[],[f37])).
% 1.80/0.99  
% 1.80/0.99  cnf(c_0,plain,
% 1.80/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 1.80/0.99      inference(cnf_transformation,[],[f38]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_1321,plain,
% 1.80/0.99      ( ~ r1_tarski(X0_44,X1_44)
% 1.80/0.99      | ~ r1_tarski(X2_44,X0_44)
% 1.80/0.99      | r1_tarski(X2_44,X1_44) ),
% 1.80/0.99      inference(subtyping,[status(esa)],[c_0]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_3149,plain,
% 1.80/0.99      ( ~ r1_tarski(X0_44,k1_tops_1(sK0,sK3))
% 1.80/0.99      | r1_tarski(X0_44,k1_tops_1(sK0,sK2))
% 1.80/0.99      | ~ r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2)) ),
% 1.80/0.99      inference(instantiation,[status(thm)],[c_1321]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_3982,plain,
% 1.80/0.99      ( ~ r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2))
% 1.80/0.99      | ~ r1_tarski(k1_tarski(X0_44),k1_tops_1(sK0,sK3))
% 1.80/0.99      | r1_tarski(k1_tarski(X0_44),k1_tops_1(sK0,sK2)) ),
% 1.80/0.99      inference(instantiation,[status(thm)],[c_3149]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_3984,plain,
% 1.80/0.99      ( ~ r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2))
% 1.80/0.99      | ~ r1_tarski(k1_tarski(sK1),k1_tops_1(sK0,sK3))
% 1.80/0.99      | r1_tarski(k1_tarski(sK1),k1_tops_1(sK0,sK2)) ),
% 1.80/0.99      inference(instantiation,[status(thm)],[c_3982]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_1330,plain,
% 1.80/0.99      ( ~ r1_tarski(X0_44,X1_44)
% 1.80/0.99      | r1_tarski(X2_44,X3_44)
% 1.80/0.99      | X2_44 != X0_44
% 1.80/0.99      | X3_44 != X1_44 ),
% 1.80/0.99      theory(equality) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_2216,plain,
% 1.80/0.99      ( r1_tarski(X0_44,X1_44)
% 1.80/0.99      | ~ r1_tarski(k1_tarski(sK1),sK3)
% 1.80/0.99      | X0_44 != k1_tarski(sK1)
% 1.80/0.99      | X1_44 != sK3 ),
% 1.80/0.99      inference(instantiation,[status(thm)],[c_1330]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_2651,plain,
% 1.80/0.99      ( r1_tarski(X0_44,k1_tops_1(sK0,sK3))
% 1.80/0.99      | ~ r1_tarski(k1_tarski(sK1),sK3)
% 1.80/0.99      | X0_44 != k1_tarski(sK1)
% 1.80/0.99      | k1_tops_1(sK0,sK3) != sK3 ),
% 1.80/0.99      inference(instantiation,[status(thm)],[c_2216]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_2830,plain,
% 1.80/0.99      ( r1_tarski(k1_tarski(sK1),k1_tops_1(sK0,sK3))
% 1.80/0.99      | ~ r1_tarski(k1_tarski(sK1),sK3)
% 1.80/0.99      | k1_tops_1(sK0,sK3) != sK3
% 1.80/0.99      | k1_tarski(sK1) != k1_tarski(sK1) ),
% 1.80/0.99      inference(instantiation,[status(thm)],[c_2651]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_3,plain,
% 1.80/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 1.80/0.99      inference(cnf_transformation,[],[f42]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_1320,plain,
% 1.80/0.99      ( m1_subset_1(X0_44,k1_zfmisc_1(X1_44))
% 1.80/0.99      | ~ r1_tarski(X0_44,X1_44) ),
% 1.80/0.99      inference(subtyping,[status(esa)],[c_3]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_2790,plain,
% 1.80/0.99      ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.80/0.99      | ~ r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) ),
% 1.80/0.99      inference(instantiation,[status(thm)],[c_1320]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_2266,plain,
% 1.80/0.99      ( r1_tarski(X0_44,u1_struct_0(sK0))
% 1.80/0.99      | ~ r1_tarski(X0_44,sK2)
% 1.80/0.99      | ~ r1_tarski(sK2,u1_struct_0(sK0)) ),
% 1.80/0.99      inference(instantiation,[status(thm)],[c_1321]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_2617,plain,
% 1.80/0.99      ( r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
% 1.80/0.99      | ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
% 1.80/0.99      | ~ r1_tarski(sK2,u1_struct_0(sK0)) ),
% 1.80/0.99      inference(instantiation,[status(thm)],[c_2266]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_7,plain,
% 1.80/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.80/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.80/0.99      | ~ r1_tarski(X0,X2)
% 1.80/0.99      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 1.80/0.99      | ~ l1_pre_topc(X1) ),
% 1.80/0.99      inference(cnf_transformation,[],[f45]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_20,negated_conjecture,
% 1.80/0.99      ( l1_pre_topc(sK0) ),
% 1.80/0.99      inference(cnf_transformation,[],[f53]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_502,plain,
% 1.80/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.80/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.80/0.99      | ~ r1_tarski(X0,X2)
% 1.80/0.99      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 1.80/0.99      | sK0 != X1 ),
% 1.80/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_20]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_503,plain,
% 1.80/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.80/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.80/0.99      | ~ r1_tarski(X0,X1)
% 1.80/0.99      | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1)) ),
% 1.80/0.99      inference(unflattening,[status(thm)],[c_502]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_1310,plain,
% 1.80/0.99      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.80/0.99      | ~ m1_subset_1(X1_44,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.80/0.99      | ~ r1_tarski(X0_44,X1_44)
% 1.80/0.99      | r1_tarski(k1_tops_1(sK0,X0_44),k1_tops_1(sK0,X1_44)) ),
% 1.80/0.99      inference(subtyping,[status(esa)],[c_503]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_2166,plain,
% 1.80/0.99      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.80/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.80/0.99      | r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,X0_44))
% 1.80/0.99      | ~ r1_tarski(sK3,X0_44) ),
% 1.80/0.99      inference(instantiation,[status(thm)],[c_1310]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_2580,plain,
% 1.80/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.80/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.80/0.99      | r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2))
% 1.80/0.99      | ~ r1_tarski(sK3,sK2) ),
% 1.80/0.99      inference(instantiation,[status(thm)],[c_2166]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_9,plain,
% 1.80/0.99      ( ~ v3_pre_topc(X0,X1)
% 1.80/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 1.80/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.80/0.99      | ~ v2_pre_topc(X3)
% 1.80/0.99      | ~ l1_pre_topc(X3)
% 1.80/0.99      | ~ l1_pre_topc(X1)
% 1.80/0.99      | k1_tops_1(X1,X0) = X0 ),
% 1.80/0.99      inference(cnf_transformation,[],[f46]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_21,negated_conjecture,
% 1.80/0.99      ( v2_pre_topc(sK0) ),
% 1.80/0.99      inference(cnf_transformation,[],[f52]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_444,plain,
% 1.80/0.99      ( ~ v3_pre_topc(X0,X1)
% 1.80/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.80/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 1.80/0.99      | ~ l1_pre_topc(X1)
% 1.80/0.99      | ~ l1_pre_topc(X3)
% 1.80/0.99      | k1_tops_1(X1,X0) = X0
% 1.80/0.99      | sK0 != X3 ),
% 1.80/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_21]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_445,plain,
% 1.80/0.99      ( ~ v3_pre_topc(X0,X1)
% 1.80/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.80/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.80/0.99      | ~ l1_pre_topc(X1)
% 1.80/0.99      | ~ l1_pre_topc(sK0)
% 1.80/0.99      | k1_tops_1(X1,X0) = X0 ),
% 1.80/0.99      inference(unflattening,[status(thm)],[c_444]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_449,plain,
% 1.80/0.99      ( ~ l1_pre_topc(X1)
% 1.80/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.80/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.80/0.99      | ~ v3_pre_topc(X0,X1)
% 1.80/0.99      | k1_tops_1(X1,X0) = X0 ),
% 1.80/0.99      inference(global_propositional_subsumption,
% 1.80/0.99                [status(thm)],
% 1.80/0.99                [c_445,c_20]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_450,plain,
% 1.80/0.99      ( ~ v3_pre_topc(X0,X1)
% 1.80/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.80/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.80/0.99      | ~ l1_pre_topc(X1)
% 1.80/0.99      | k1_tops_1(X1,X0) = X0 ),
% 1.80/0.99      inference(renaming,[status(thm)],[c_449]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_484,plain,
% 1.80/0.99      ( ~ v3_pre_topc(X0,X1)
% 1.80/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.80/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.80/0.99      | k1_tops_1(X1,X0) = X0
% 1.80/0.99      | sK0 != X1 ),
% 1.80/0.99      inference(resolution_lifted,[status(thm)],[c_450,c_20]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_485,plain,
% 1.80/0.99      ( ~ v3_pre_topc(X0,sK0)
% 1.80/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.80/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.80/0.99      | k1_tops_1(sK0,X0) = X0 ),
% 1.80/0.99      inference(unflattening,[status(thm)],[c_484]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_1311,plain,
% 1.80/0.99      ( ~ v3_pre_topc(X0_44,sK0)
% 1.80/0.99      | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.80/0.99      | ~ m1_subset_1(X1_44,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.80/0.99      | k1_tops_1(sK0,X0_44) = X0_44 ),
% 1.80/0.99      inference(subtyping,[status(esa)],[c_485]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_1323,plain,
% 1.80/0.99      ( ~ v3_pre_topc(X0_44,sK0)
% 1.80/0.99      | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.80/0.99      | k1_tops_1(sK0,X0_44) = X0_44
% 1.80/0.99      | ~ sP1_iProver_split ),
% 1.80/0.99      inference(splitting,
% 1.80/0.99                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 1.80/0.99                [c_1311]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_1324,plain,
% 1.80/0.99      ( sP1_iProver_split | sP0_iProver_split ),
% 1.80/0.99      inference(splitting,
% 1.80/0.99                [splitting(split),new_symbols(definition,[])],
% 1.80/0.99                [c_1311]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_1322,plain,
% 1.80/0.99      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.80/0.99      | ~ sP0_iProver_split ),
% 1.80/0.99      inference(splitting,
% 1.80/0.99                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 1.80/1.00                [c_1311]) ).
% 1.80/1.00  
% 1.80/1.00  cnf(c_1440,plain,
% 1.80/1.00      ( k1_tops_1(sK0,X0_44) = X0_44
% 1.80/1.00      | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.80/1.00      | ~ v3_pre_topc(X0_44,sK0) ),
% 1.80/1.00      inference(global_propositional_subsumption,
% 1.80/1.00                [status(thm)],
% 1.80/1.00                [c_1323,c_1324,c_1322]) ).
% 1.80/1.00  
% 1.80/1.00  cnf(c_1441,plain,
% 1.80/1.00      ( ~ v3_pre_topc(X0_44,sK0)
% 1.80/1.00      | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.80/1.00      | k1_tops_1(sK0,X0_44) = X0_44 ),
% 1.80/1.00      inference(renaming,[status(thm)],[c_1440]) ).
% 1.80/1.00  
% 1.80/1.00  cnf(c_2192,plain,
% 1.80/1.00      ( ~ v3_pre_topc(sK3,sK0)
% 1.80/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.80/1.00      | k1_tops_1(sK0,sK3) = sK3 ),
% 1.80/1.00      inference(instantiation,[status(thm)],[c_1441]) ).
% 1.80/1.00  
% 1.80/1.00  cnf(c_4,plain,
% 1.80/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 1.80/1.00      inference(cnf_transformation,[],[f41]) ).
% 1.80/1.00  
% 1.80/1.00  cnf(c_1319,plain,
% 1.80/1.00      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X1_44))
% 1.80/1.00      | r1_tarski(X0_44,X1_44) ),
% 1.80/1.00      inference(subtyping,[status(esa)],[c_4]) ).
% 1.80/1.00  
% 1.80/1.00  cnf(c_2106,plain,
% 1.80/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.80/1.00      | r1_tarski(sK2,u1_struct_0(sK0)) ),
% 1.80/1.00      inference(instantiation,[status(thm)],[c_1319]) ).
% 1.80/1.00  
% 1.80/1.00  cnf(c_2,plain,
% 1.80/1.00      ( r2_hidden(X0,X1) | ~ r1_tarski(k1_tarski(X0),X1) ),
% 1.80/1.00      inference(cnf_transformation,[],[f39]) ).
% 1.80/1.00  
% 1.80/1.00  cnf(c_178,plain,
% 1.80/1.00      ( r2_hidden(X0,X1) | ~ r1_tarski(k1_tarski(X0),X1) ),
% 1.80/1.00      inference(prop_impl,[status(thm)],[c_2]) ).
% 1.80/1.00  
% 1.80/1.00  cnf(c_10,plain,
% 1.80/1.00      ( m1_connsp_2(X0,X1,X2)
% 1.80/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.80/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.80/1.00      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 1.80/1.00      | v2_struct_0(X1)
% 1.80/1.00      | ~ v2_pre_topc(X1)
% 1.80/1.00      | ~ l1_pre_topc(X1) ),
% 1.80/1.00      inference(cnf_transformation,[],[f49]) ).
% 1.80/1.00  
% 1.80/1.00  cnf(c_22,negated_conjecture,
% 1.80/1.00      ( ~ v2_struct_0(sK0) ),
% 1.80/1.00      inference(cnf_transformation,[],[f51]) ).
% 1.80/1.00  
% 1.80/1.00  cnf(c_364,plain,
% 1.80/1.00      ( m1_connsp_2(X0,X1,X2)
% 1.80/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.80/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.80/1.00      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 1.80/1.00      | ~ v2_pre_topc(X1)
% 1.80/1.00      | ~ l1_pre_topc(X1)
% 1.80/1.00      | sK0 != X1 ),
% 1.80/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_22]) ).
% 1.80/1.00  
% 1.80/1.00  cnf(c_365,plain,
% 1.80/1.00      ( m1_connsp_2(X0,sK0,X1)
% 1.80/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 1.80/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.80/1.00      | ~ r2_hidden(X1,k1_tops_1(sK0,X0))
% 1.80/1.00      | ~ v2_pre_topc(sK0)
% 1.80/1.00      | ~ l1_pre_topc(sK0) ),
% 1.80/1.00      inference(unflattening,[status(thm)],[c_364]) ).
% 1.80/1.00  
% 1.80/1.00  cnf(c_369,plain,
% 1.80/1.00      ( m1_connsp_2(X0,sK0,X1)
% 1.80/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 1.80/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.80/1.00      | ~ r2_hidden(X1,k1_tops_1(sK0,X0)) ),
% 1.80/1.00      inference(global_propositional_subsumption,
% 1.80/1.00                [status(thm)],
% 1.80/1.00                [c_365,c_21,c_20]) ).
% 1.80/1.00  
% 1.80/1.00  cnf(c_705,plain,
% 1.80/1.00      ( m1_connsp_2(X0,sK0,X1)
% 1.80/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 1.80/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.80/1.00      | ~ r1_tarski(k1_tarski(X2),X3)
% 1.80/1.00      | X1 != X2
% 1.80/1.00      | k1_tops_1(sK0,X0) != X3 ),
% 1.80/1.00      inference(resolution_lifted,[status(thm)],[c_178,c_369]) ).
% 1.80/1.00  
% 1.80/1.00  cnf(c_706,plain,
% 1.80/1.00      ( m1_connsp_2(X0,sK0,X1)
% 1.80/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 1.80/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.80/1.00      | ~ r1_tarski(k1_tarski(X1),k1_tops_1(sK0,X0)) ),
% 1.80/1.00      inference(unflattening,[status(thm)],[c_705]) ).
% 1.80/1.00  
% 1.80/1.00  cnf(c_1305,plain,
% 1.80/1.00      ( m1_connsp_2(X0_44,sK0,X1_44)
% 1.80/1.00      | ~ m1_subset_1(X1_44,u1_struct_0(sK0))
% 1.80/1.00      | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.80/1.00      | ~ r1_tarski(k1_tarski(X1_44),k1_tops_1(sK0,X0_44)) ),
% 1.80/1.00      inference(subtyping,[status(esa)],[c_706]) ).
% 1.80/1.00  
% 1.80/1.00  cnf(c_2101,plain,
% 1.80/1.00      ( m1_connsp_2(sK2,sK0,X0_44)
% 1.80/1.00      | ~ m1_subset_1(X0_44,u1_struct_0(sK0))
% 1.80/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.80/1.00      | ~ r1_tarski(k1_tarski(X0_44),k1_tops_1(sK0,sK2)) ),
% 1.80/1.00      inference(instantiation,[status(thm)],[c_1305]) ).
% 1.80/1.00  
% 1.80/1.00  cnf(c_2103,plain,
% 1.80/1.00      ( m1_connsp_2(sK2,sK0,sK1)
% 1.80/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.80/1.00      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
% 1.80/1.00      | ~ r1_tarski(k1_tarski(sK1),k1_tops_1(sK0,sK2)) ),
% 1.80/1.00      inference(instantiation,[status(thm)],[c_2101]) ).
% 1.80/1.00  
% 1.80/1.00  cnf(c_13,negated_conjecture,
% 1.80/1.00      ( ~ m1_connsp_2(sK2,sK0,sK1)
% 1.80/1.00      | ~ v3_pre_topc(X0,sK0)
% 1.80/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.80/1.00      | ~ r2_hidden(sK1,X0)
% 1.80/1.00      | ~ r1_tarski(X0,sK2) ),
% 1.80/1.00      inference(cnf_transformation,[],[f60]) ).
% 1.80/1.00  
% 1.80/1.00  cnf(c_11,plain,
% 1.80/1.00      ( ~ m1_connsp_2(X0,X1,X2)
% 1.80/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.80/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.80/1.00      | r2_hidden(X2,k1_tops_1(X1,X0))
% 1.80/1.00      | v2_struct_0(X1)
% 1.80/1.00      | ~ v2_pre_topc(X1)
% 1.80/1.00      | ~ l1_pre_topc(X1) ),
% 1.80/1.00      inference(cnf_transformation,[],[f48]) ).
% 1.80/1.00  
% 1.80/1.00  cnf(c_12,plain,
% 1.80/1.00      ( ~ m1_connsp_2(X0,X1,X2)
% 1.80/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.80/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.80/1.00      | v2_struct_0(X1)
% 1.80/1.00      | ~ v2_pre_topc(X1)
% 1.80/1.00      | ~ l1_pre_topc(X1) ),
% 1.80/1.00      inference(cnf_transformation,[],[f50]) ).
% 1.80/1.00  
% 1.80/1.00  cnf(c_130,plain,
% 1.80/1.00      ( ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.80/1.00      | ~ m1_connsp_2(X0,X1,X2)
% 1.80/1.00      | r2_hidden(X2,k1_tops_1(X1,X0))
% 1.80/1.00      | v2_struct_0(X1)
% 1.80/1.00      | ~ v2_pre_topc(X1)
% 1.80/1.00      | ~ l1_pre_topc(X1) ),
% 1.80/1.00      inference(global_propositional_subsumption,
% 1.80/1.00                [status(thm)],
% 1.80/1.00                [c_11,c_12]) ).
% 1.80/1.00  
% 1.80/1.00  cnf(c_131,plain,
% 1.80/1.00      ( ~ m1_connsp_2(X0,X1,X2)
% 1.80/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.80/1.00      | r2_hidden(X2,k1_tops_1(X1,X0))
% 1.80/1.00      | v2_struct_0(X1)
% 1.80/1.00      | ~ v2_pre_topc(X1)
% 1.80/1.00      | ~ l1_pre_topc(X1) ),
% 1.80/1.00      inference(renaming,[status(thm)],[c_130]) ).
% 1.80/1.00  
% 1.80/1.00  cnf(c_322,plain,
% 1.80/1.00      ( ~ m1_connsp_2(X0,X1,X2)
% 1.80/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.80/1.00      | r2_hidden(X2,k1_tops_1(X1,X0))
% 1.80/1.00      | ~ v2_pre_topc(X1)
% 1.80/1.00      | ~ l1_pre_topc(X1)
% 1.80/1.00      | sK0 != X1 ),
% 1.80/1.00      inference(resolution_lifted,[status(thm)],[c_131,c_22]) ).
% 1.80/1.00  
% 1.80/1.00  cnf(c_323,plain,
% 1.80/1.00      ( ~ m1_connsp_2(X0,sK0,X1)
% 1.80/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 1.80/1.00      | r2_hidden(X1,k1_tops_1(sK0,X0))
% 1.80/1.00      | ~ v2_pre_topc(sK0)
% 1.80/1.00      | ~ l1_pre_topc(sK0) ),
% 1.80/1.00      inference(unflattening,[status(thm)],[c_322]) ).
% 1.80/1.00  
% 1.80/1.00  cnf(c_327,plain,
% 1.80/1.00      ( ~ m1_connsp_2(X0,sK0,X1)
% 1.80/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 1.80/1.00      | r2_hidden(X1,k1_tops_1(sK0,X0)) ),
% 1.80/1.00      inference(global_propositional_subsumption,
% 1.80/1.00                [status(thm)],
% 1.80/1.00                [c_323,c_21,c_20]) ).
% 1.80/1.00  
% 1.80/1.00  cnf(c_740,plain,
% 1.80/1.00      ( ~ m1_connsp_2(X0,sK0,X1)
% 1.80/1.00      | ~ m1_connsp_2(sK2,sK0,sK1)
% 1.80/1.00      | ~ v3_pre_topc(X2,sK0)
% 1.80/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 1.80/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.80/1.00      | ~ r1_tarski(X2,sK2)
% 1.80/1.00      | k1_tops_1(sK0,X0) != X2
% 1.80/1.00      | sK1 != X1 ),
% 1.80/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_327]) ).
% 1.80/1.00  
% 1.80/1.00  cnf(c_741,plain,
% 1.80/1.00      ( ~ m1_connsp_2(X0,sK0,sK1)
% 1.80/1.00      | ~ m1_connsp_2(sK2,sK0,sK1)
% 1.80/1.00      | ~ v3_pre_topc(k1_tops_1(sK0,X0),sK0)
% 1.80/1.00      | ~ m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.80/1.00      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
% 1.80/1.00      | ~ r1_tarski(k1_tops_1(sK0,X0),sK2) ),
% 1.80/1.00      inference(unflattening,[status(thm)],[c_740]) ).
% 1.80/1.00  
% 1.80/1.00  cnf(c_19,negated_conjecture,
% 1.80/1.00      ( m1_subset_1(sK1,u1_struct_0(sK0)) ),
% 1.80/1.00      inference(cnf_transformation,[],[f54]) ).
% 1.80/1.00  
% 1.80/1.00  cnf(c_745,plain,
% 1.80/1.00      ( ~ m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.80/1.00      | ~ v3_pre_topc(k1_tops_1(sK0,X0),sK0)
% 1.80/1.00      | ~ m1_connsp_2(sK2,sK0,sK1)
% 1.80/1.00      | ~ m1_connsp_2(X0,sK0,sK1)
% 1.80/1.00      | ~ r1_tarski(k1_tops_1(sK0,X0),sK2) ),
% 1.80/1.00      inference(global_propositional_subsumption,
% 1.80/1.00                [status(thm)],
% 1.80/1.00                [c_741,c_19]) ).
% 1.80/1.00  
% 1.80/1.00  cnf(c_746,plain,
% 1.80/1.00      ( ~ m1_connsp_2(X0,sK0,sK1)
% 1.80/1.00      | ~ m1_connsp_2(sK2,sK0,sK1)
% 1.80/1.00      | ~ v3_pre_topc(k1_tops_1(sK0,X0),sK0)
% 1.80/1.00      | ~ m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.80/1.00      | ~ r1_tarski(k1_tops_1(sK0,X0),sK2) ),
% 1.80/1.00      inference(renaming,[status(thm)],[c_745]) ).
% 1.80/1.00  
% 1.80/1.00  cnf(c_1303,plain,
% 1.80/1.00      ( ~ m1_connsp_2(X0_44,sK0,sK1)
% 1.80/1.00      | ~ m1_connsp_2(sK2,sK0,sK1)
% 1.80/1.00      | ~ v3_pre_topc(k1_tops_1(sK0,X0_44),sK0)
% 1.80/1.00      | ~ m1_subset_1(k1_tops_1(sK0,X0_44),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.80/1.00      | ~ r1_tarski(k1_tops_1(sK0,X0_44),sK2) ),
% 1.80/1.00      inference(subtyping,[status(esa)],[c_746]) ).
% 1.80/1.00  
% 1.80/1.00  cnf(c_2082,plain,
% 1.80/1.00      ( ~ m1_connsp_2(sK2,sK0,sK1)
% 1.80/1.00      | ~ v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
% 1.80/1.00      | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.80/1.00      | ~ r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
% 1.80/1.00      inference(instantiation,[status(thm)],[c_1303]) ).
% 1.80/1.00  
% 1.80/1.00  cnf(c_6,plain,
% 1.80/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.80/1.00      | r1_tarski(k1_tops_1(X1,X0),X0)
% 1.80/1.00      | ~ l1_pre_topc(X1) ),
% 1.80/1.00      inference(cnf_transformation,[],[f44]) ).
% 1.80/1.00  
% 1.80/1.00  cnf(c_520,plain,
% 1.80/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.80/1.00      | r1_tarski(k1_tops_1(X1,X0),X0)
% 1.80/1.00      | sK0 != X1 ),
% 1.80/1.00      inference(resolution_lifted,[status(thm)],[c_6,c_20]) ).
% 1.80/1.00  
% 1.80/1.00  cnf(c_521,plain,
% 1.80/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.80/1.00      | r1_tarski(k1_tops_1(sK0,X0),X0) ),
% 1.80/1.00      inference(unflattening,[status(thm)],[c_520]) ).
% 1.80/1.00  
% 1.80/1.00  cnf(c_1309,plain,
% 1.80/1.00      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.80/1.00      | r1_tarski(k1_tops_1(sK0,X0_44),X0_44) ),
% 1.80/1.00      inference(subtyping,[status(esa)],[c_521]) ).
% 1.80/1.00  
% 1.80/1.00  cnf(c_2079,plain,
% 1.80/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.80/1.00      | r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
% 1.80/1.00      inference(instantiation,[status(thm)],[c_1309]) ).
% 1.80/1.00  
% 1.80/1.00  cnf(c_5,plain,
% 1.80/1.00      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 1.80/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 1.80/1.00      | ~ v2_pre_topc(X0)
% 1.80/1.00      | ~ l1_pre_topc(X0) ),
% 1.80/1.00      inference(cnf_transformation,[],[f43]) ).
% 1.80/1.00  
% 1.80/1.00  cnf(c_401,plain,
% 1.80/1.00      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 1.80/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 1.80/1.00      | ~ l1_pre_topc(X0)
% 1.80/1.00      | sK0 != X0 ),
% 1.80/1.00      inference(resolution_lifted,[status(thm)],[c_5,c_21]) ).
% 1.80/1.00  
% 1.80/1.00  cnf(c_402,plain,
% 1.80/1.00      ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
% 1.80/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.80/1.00      | ~ l1_pre_topc(sK0) ),
% 1.80/1.00      inference(unflattening,[status(thm)],[c_401]) ).
% 1.80/1.00  
% 1.80/1.00  cnf(c_406,plain,
% 1.80/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.80/1.00      | v3_pre_topc(k1_tops_1(sK0,X0),sK0) ),
% 1.80/1.00      inference(global_propositional_subsumption,
% 1.80/1.00                [status(thm)],
% 1.80/1.00                [c_402,c_20]) ).
% 1.80/1.00  
% 1.80/1.00  cnf(c_407,plain,
% 1.80/1.00      ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
% 1.80/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.80/1.00      inference(renaming,[status(thm)],[c_406]) ).
% 1.80/1.00  
% 1.80/1.00  cnf(c_1312,plain,
% 1.80/1.00      ( v3_pre_topc(k1_tops_1(sK0,X0_44),sK0)
% 1.80/1.00      | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.80/1.00      inference(subtyping,[status(esa)],[c_407]) ).
% 1.80/1.00  
% 1.80/1.00  cnf(c_2076,plain,
% 1.80/1.00      ( v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
% 1.80/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.80/1.00      inference(instantiation,[status(thm)],[c_1312]) ).
% 1.80/1.00  
% 1.80/1.00  cnf(c_1328,plain,( X0_44 = X0_44 ),theory(equality) ).
% 1.80/1.00  
% 1.80/1.00  cnf(c_1343,plain,
% 1.80/1.00      ( sK1 = sK1 ),
% 1.80/1.00      inference(instantiation,[status(thm)],[c_1328]) ).
% 1.80/1.00  
% 1.80/1.00  cnf(c_1331,plain,
% 1.80/1.00      ( X0_44 != X1_44 | k1_tarski(X0_44) = k1_tarski(X1_44) ),
% 1.80/1.00      theory(equality) ).
% 1.80/1.00  
% 1.80/1.00  cnf(c_1337,plain,
% 1.80/1.00      ( k1_tarski(sK1) = k1_tarski(sK1) | sK1 != sK1 ),
% 1.80/1.00      inference(instantiation,[status(thm)],[c_1331]) ).
% 1.80/1.00  
% 1.80/1.00  cnf(c_1,plain,
% 1.80/1.00      ( ~ r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1) ),
% 1.80/1.00      inference(cnf_transformation,[],[f40]) ).
% 1.80/1.00  
% 1.80/1.00  cnf(c_180,plain,
% 1.80/1.00      ( ~ r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1) ),
% 1.80/1.00      inference(prop_impl,[status(thm)],[c_1]) ).
% 1.80/1.00  
% 1.80/1.00  cnf(c_14,negated_conjecture,
% 1.80/1.00      ( m1_connsp_2(sK2,sK0,sK1) | r2_hidden(sK1,sK3) ),
% 1.80/1.00      inference(cnf_transformation,[],[f59]) ).
% 1.80/1.00  
% 1.80/1.00  cnf(c_695,plain,
% 1.80/1.00      ( m1_connsp_2(sK2,sK0,sK1)
% 1.80/1.00      | r1_tarski(k1_tarski(X0),X1)
% 1.80/1.00      | sK3 != X1
% 1.80/1.00      | sK1 != X0 ),
% 1.80/1.00      inference(resolution_lifted,[status(thm)],[c_180,c_14]) ).
% 1.80/1.00  
% 1.80/1.00  cnf(c_696,plain,
% 1.80/1.00      ( m1_connsp_2(sK2,sK0,sK1) | r1_tarski(k1_tarski(sK1),sK3) ),
% 1.80/1.00      inference(unflattening,[status(thm)],[c_695]) ).
% 1.80/1.00  
% 1.80/1.00  cnf(c_15,negated_conjecture,
% 1.80/1.00      ( m1_connsp_2(sK2,sK0,sK1) | r1_tarski(sK3,sK2) ),
% 1.80/1.00      inference(cnf_transformation,[],[f58]) ).
% 1.80/1.00  
% 1.80/1.00  cnf(c_16,negated_conjecture,
% 1.80/1.00      ( m1_connsp_2(sK2,sK0,sK1) | v3_pre_topc(sK3,sK0) ),
% 1.80/1.00      inference(cnf_transformation,[],[f57]) ).
% 1.80/1.00  
% 1.80/1.00  cnf(c_17,negated_conjecture,
% 1.80/1.00      ( m1_connsp_2(sK2,sK0,sK1)
% 1.80/1.00      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.80/1.00      inference(cnf_transformation,[],[f56]) ).
% 1.80/1.00  
% 1.80/1.00  cnf(c_18,negated_conjecture,
% 1.80/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.80/1.00      inference(cnf_transformation,[],[f55]) ).
% 1.80/1.00  
% 1.80/1.00  cnf(contradiction,plain,
% 1.80/1.00      ( $false ),
% 1.80/1.00      inference(minisat,
% 1.80/1.00                [status(thm)],
% 1.80/1.00                [c_3984,c_2830,c_2790,c_2617,c_2580,c_2192,c_2106,c_2103,
% 1.80/1.00                 c_2082,c_2079,c_2076,c_1343,c_1337,c_696,c_15,c_16,c_17,
% 1.80/1.00                 c_18,c_19]) ).
% 1.80/1.00  
% 1.80/1.00  
% 1.80/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 1.80/1.00  
% 1.80/1.00  ------                               Statistics
% 1.80/1.00  
% 1.80/1.00  ------ General
% 1.80/1.00  
% 1.80/1.00  abstr_ref_over_cycles:                  0
% 1.80/1.00  abstr_ref_under_cycles:                 0
% 1.80/1.00  gc_basic_clause_elim:                   0
% 1.80/1.00  forced_gc_time:                         0
% 1.80/1.00  parsing_time:                           0.008
% 1.80/1.00  unif_index_cands_time:                  0.
% 1.80/1.00  unif_index_add_time:                    0.
% 1.80/1.00  orderings_time:                         0.
% 1.80/1.00  out_proof_time:                         0.015
% 1.80/1.00  total_time:                             0.139
% 1.80/1.00  num_of_symbols:                         49
% 1.80/1.00  num_of_terms:                           1803
% 1.80/1.00  
% 1.80/1.00  ------ Preprocessing
% 1.80/1.00  
% 1.80/1.00  num_of_splits:                          4
% 1.80/1.00  num_of_split_atoms:                     3
% 1.80/1.00  num_of_reused_defs:                     1
% 1.80/1.00  num_eq_ax_congr_red:                    9
% 1.80/1.00  num_of_sem_filtered_clauses:            4
% 1.80/1.00  num_of_subtypes:                        2
% 1.80/1.00  monotx_restored_types:                  1
% 1.80/1.00  sat_num_of_epr_types:                   0
% 1.80/1.00  sat_num_of_non_cyclic_types:            0
% 1.80/1.00  sat_guarded_non_collapsed_types:        0
% 1.80/1.00  num_pure_diseq_elim:                    0
% 1.80/1.00  simp_replaced_by:                       0
% 1.80/1.00  res_preprocessed:                       103
% 1.80/1.00  prep_upred:                             0
% 1.80/1.00  prep_unflattend:                        36
% 1.80/1.00  smt_new_axioms:                         0
% 1.80/1.00  pred_elim_cands:                        4
% 1.80/1.00  pred_elim:                              4
% 1.80/1.00  pred_elim_cl:                           3
% 1.80/1.00  pred_elim_cycles:                       7
% 1.80/1.00  merged_defs:                            10
% 1.80/1.00  merged_defs_ncl:                        0
% 1.80/1.00  bin_hyper_res:                          10
% 1.80/1.00  prep_cycles:                            4
% 1.80/1.00  pred_elim_time:                         0.018
% 1.80/1.00  splitting_time:                         0.
% 1.80/1.00  sem_filter_time:                        0.
% 1.80/1.00  monotx_time:                            0.001
% 1.80/1.00  subtype_inf_time:                       0.001
% 1.80/1.00  
% 1.80/1.00  ------ Problem properties
% 1.80/1.00  
% 1.80/1.00  clauses:                                24
% 1.80/1.00  conjectures:                            5
% 1.80/1.00  epr:                                    5
% 1.80/1.00  horn:                                   17
% 1.80/1.00  ground:                                 8
% 1.80/1.00  unary:                                  2
% 1.80/1.00  binary:                                 12
% 1.80/1.00  lits:                                   65
% 1.80/1.00  lits_eq:                                3
% 1.80/1.00  fd_pure:                                0
% 1.80/1.00  fd_pseudo:                              0
% 1.80/1.00  fd_cond:                                0
% 1.80/1.00  fd_pseudo_cond:                         0
% 1.80/1.00  ac_symbols:                             0
% 1.80/1.00  
% 1.80/1.00  ------ Propositional Solver
% 1.80/1.00  
% 1.80/1.00  prop_solver_calls:                      28
% 1.80/1.00  prop_fast_solver_calls:                 933
% 1.80/1.00  smt_solver_calls:                       0
% 1.80/1.00  smt_fast_solver_calls:                  0
% 1.80/1.00  prop_num_of_clauses:                    1071
% 1.80/1.00  prop_preprocess_simplified:             4180
% 1.80/1.00  prop_fo_subsumed:                       35
% 1.80/1.00  prop_solver_time:                       0.
% 1.80/1.00  smt_solver_time:                        0.
% 1.80/1.00  smt_fast_solver_time:                   0.
% 1.80/1.00  prop_fast_solver_time:                  0.
% 1.80/1.00  prop_unsat_core_time:                   0.
% 1.80/1.00  
% 1.80/1.00  ------ QBF
% 1.80/1.00  
% 1.80/1.00  qbf_q_res:                              0
% 1.80/1.00  qbf_num_tautologies:                    0
% 1.80/1.00  qbf_prep_cycles:                        0
% 1.80/1.00  
% 1.80/1.00  ------ BMC1
% 1.80/1.00  
% 1.80/1.00  bmc1_current_bound:                     -1
% 1.80/1.00  bmc1_last_solved_bound:                 -1
% 1.80/1.00  bmc1_unsat_core_size:                   -1
% 1.80/1.00  bmc1_unsat_core_parents_size:           -1
% 1.80/1.00  bmc1_merge_next_fun:                    0
% 1.80/1.00  bmc1_unsat_core_clauses_time:           0.
% 1.80/1.00  
% 1.80/1.00  ------ Instantiation
% 1.80/1.00  
% 1.80/1.00  inst_num_of_clauses:                    259
% 1.80/1.00  inst_num_in_passive:                    69
% 1.80/1.00  inst_num_in_active:                     176
% 1.80/1.00  inst_num_in_unprocessed:                13
% 1.80/1.00  inst_num_of_loops:                      256
% 1.80/1.00  inst_num_of_learning_restarts:          0
% 1.80/1.00  inst_num_moves_active_passive:          76
% 1.80/1.00  inst_lit_activity:                      0
% 1.80/1.00  inst_lit_activity_moves:                0
% 1.80/1.00  inst_num_tautologies:                   0
% 1.80/1.00  inst_num_prop_implied:                  0
% 1.80/1.00  inst_num_existing_simplified:           0
% 1.80/1.00  inst_num_eq_res_simplified:             0
% 1.80/1.00  inst_num_child_elim:                    0
% 1.80/1.00  inst_num_of_dismatching_blockings:      5
% 1.80/1.00  inst_num_of_non_proper_insts:           279
% 1.80/1.00  inst_num_of_duplicates:                 0
% 1.80/1.00  inst_inst_num_from_inst_to_res:         0
% 1.80/1.00  inst_dismatching_checking_time:         0.
% 1.80/1.00  
% 1.80/1.00  ------ Resolution
% 1.80/1.00  
% 1.80/1.00  res_num_of_clauses:                     0
% 1.80/1.00  res_num_in_passive:                     0
% 1.80/1.00  res_num_in_active:                      0
% 1.80/1.00  res_num_of_loops:                       107
% 1.80/1.00  res_forward_subset_subsumed:            25
% 1.80/1.00  res_backward_subset_subsumed:           0
% 1.80/1.00  res_forward_subsumed:                   0
% 1.80/1.00  res_backward_subsumed:                  0
% 1.80/1.00  res_forward_subsumption_resolution:     0
% 1.80/1.00  res_backward_subsumption_resolution:    0
% 1.80/1.00  res_clause_to_clause_subsumption:       327
% 1.80/1.00  res_orphan_elimination:                 0
% 1.80/1.00  res_tautology_del:                      73
% 1.80/1.00  res_num_eq_res_simplified:              0
% 1.80/1.00  res_num_sel_changes:                    0
% 1.80/1.00  res_moves_from_active_to_pass:          0
% 1.80/1.00  
% 1.80/1.00  ------ Superposition
% 1.80/1.00  
% 1.80/1.00  sup_time_total:                         0.
% 1.80/1.00  sup_time_generating:                    0.
% 1.80/1.00  sup_time_sim_full:                      0.
% 1.80/1.00  sup_time_sim_immed:                     0.
% 1.80/1.00  
% 1.80/1.00  sup_num_of_clauses:                     74
% 1.80/1.00  sup_num_in_active:                      46
% 1.80/1.00  sup_num_in_passive:                     28
% 1.80/1.00  sup_num_of_loops:                       50
% 1.80/1.00  sup_fw_superposition:                   59
% 1.80/1.00  sup_bw_superposition:                   30
% 1.80/1.00  sup_immediate_simplified:               25
% 1.80/1.00  sup_given_eliminated:                   1
% 1.80/1.00  comparisons_done:                       0
% 1.80/1.00  comparisons_avoided:                    0
% 1.80/1.00  
% 1.80/1.00  ------ Simplifications
% 1.80/1.00  
% 1.80/1.00  
% 1.80/1.00  sim_fw_subset_subsumed:                 21
% 1.80/1.00  sim_bw_subset_subsumed:                 2
% 1.80/1.00  sim_fw_subsumed:                        1
% 1.80/1.00  sim_bw_subsumed:                        2
% 1.80/1.00  sim_fw_subsumption_res:                 0
% 1.80/1.00  sim_bw_subsumption_res:                 0
% 1.80/1.00  sim_tautology_del:                      5
% 1.80/1.00  sim_eq_tautology_del:                   0
% 1.80/1.00  sim_eq_res_simp:                        0
% 1.80/1.00  sim_fw_demodulated:                     0
% 1.80/1.00  sim_bw_demodulated:                     2
% 1.80/1.00  sim_light_normalised:                   4
% 1.80/1.00  sim_joinable_taut:                      0
% 1.80/1.00  sim_joinable_simp:                      0
% 1.80/1.00  sim_ac_normalised:                      0
% 1.80/1.00  sim_smt_subsumption:                    0
% 1.80/1.00  
%------------------------------------------------------------------------------
