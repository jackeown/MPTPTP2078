%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:18:22 EST 2020

% Result     : Theorem 1.71s
% Output     : CNFRefutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :  200 (3312 expanded)
%              Number of clauses        :  145 ( 702 expanded)
%              Number of leaves         :   15 ( 974 expanded)
%              Depth                    :   26
%              Number of atoms          :  858 (37607 expanded)
%              Number of equality atoms :  145 ( 648 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   30 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

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

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X2,X0)
      | k1_tops_1(X0,X2) != X2
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f9,conjecture,(
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

fof(f10,negated_conjecture,(
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
    inference(negated_conjecture,[],[f9])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f33,plain,(
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

fof(f32,plain,(
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

fof(f31,plain,(
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

fof(f30,plain,
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

fof(f34,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f29,f33,f32,f31,f30])).

fof(f47,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f48,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f55,plain,(
    ! [X3] :
      ( ~ r2_hidden(sK1,X3)
      | ~ r1_tarski(X3,sK2)
      | ~ v3_pre_topc(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_connsp_2(sK2,sK0,sK1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f49,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f34])).

fof(f50,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f34])).

fof(f53,plain,
    ( r1_tarski(sK3,sK2)
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f34])).

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

fof(f26,plain,(
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

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f46,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f54,plain,
    ( r2_hidden(sK1,sK3)
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f52,plain,
    ( v3_pre_topc(sK3,sK0)
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f51,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

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

fof(f40,plain,(
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

fof(f39,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

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

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_156,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_1])).

cnf(c_205,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(bin_hyper_res,[status(thm)],[c_0,c_156])).

cnf(c_1461,plain,
    ( ~ r1_tarski(X0_43,X1_43)
    | ~ r2_hidden(X2_43,X0_43)
    | r2_hidden(X2_43,X1_43) ),
    inference(subtyping,[status(esa)],[c_205])).

cnf(c_3230,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2))
    | ~ r2_hidden(X0_43,k1_tops_1(sK0,sK3))
    | r2_hidden(X0_43,k1_tops_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_1461])).

cnf(c_3235,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2))
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK3))
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_3230])).

cnf(c_7,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_19,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_342,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X1,X0) != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_19])).

cnf(c_343,plain,
    ( v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(sK0)
    | k1_tops_1(sK0,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_342])).

cnf(c_18,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_347,plain,
    ( ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | v3_pre_topc(X0,sK0)
    | k1_tops_1(sK0,X0) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_343,c_18])).

cnf(c_348,plain,
    ( v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(X2)
    | k1_tops_1(sK0,X0) != X0 ),
    inference(renaming,[status(thm)],[c_347])).

cnf(c_467,plain,
    ( v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) != X0
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_348,c_18])).

cnf(c_468,plain,
    ( v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_467])).

cnf(c_11,negated_conjecture,
    ( ~ m1_connsp_2(sK2,sK0,sK1)
    | ~ v3_pre_topc(X0,sK0)
    | ~ r1_tarski(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_525,plain,
    ( ~ m1_connsp_2(sK2,sK0,sK1)
    | ~ r1_tarski(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1,X0)
    | k1_tops_1(sK0,X0) != X0 ),
    inference(resolution,[status(thm)],[c_468,c_11])).

cnf(c_1455,plain,
    ( ~ m1_connsp_2(sK2,sK0,sK1)
    | ~ r1_tarski(X0_43,sK2)
    | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1_43,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1,X0_43)
    | k1_tops_1(sK0,X0_43) != X0_43 ),
    inference(subtyping,[status(esa)],[c_525])).

cnf(c_1470,plain,
    ( ~ r1_tarski(X0_43,sK2)
    | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1,X0_43)
    | k1_tops_1(sK0,X0_43) != X0_43
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_1455])).

cnf(c_1995,plain,
    ( k1_tops_1(sK0,X0_43) != X0_43
    | r1_tarski(X0_43,sK2) != iProver_top
    | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r2_hidden(sK1,X0_43) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1470])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_24,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_25,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_13,negated_conjecture,
    ( m1_connsp_2(sK2,sK0,sK1)
    | r1_tarski(sK3,sK2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_10,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_20,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_284,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_20])).

cnf(c_285,plain,
    ( ~ m1_connsp_2(X0,sK0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(X1,k1_tops_1(sK0,X0))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_284])).

cnf(c_289,plain,
    ( ~ m1_connsp_2(X0,sK0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(X1,k1_tops_1(sK0,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_285,c_19,c_18])).

cnf(c_839,plain,
    ( r1_tarski(sK3,sK2)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(X0,k1_tops_1(sK0,X1))
    | sK0 != sK0
    | sK2 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_289])).

cnf(c_840,plain,
    ( r1_tarski(sK3,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(unflattening,[status(thm)],[c_839])).

cnf(c_842,plain,
    ( r1_tarski(sK3,sK2)
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_840,c_17,c_16])).

cnf(c_844,plain,
    ( r1_tarski(sK3,sK2) = iProver_top
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_842])).

cnf(c_12,negated_conjecture,
    ( m1_connsp_2(sK2,sK0,sK1)
    | r2_hidden(sK1,sK3) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_853,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(X0,k1_tops_1(sK0,X1))
    | r2_hidden(sK1,sK3)
    | sK0 != sK0
    | sK2 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_289])).

cnf(c_854,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | r2_hidden(sK1,sK3) ),
    inference(unflattening,[status(thm)],[c_853])).

cnf(c_856,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | r2_hidden(sK1,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_854,c_17,c_16])).

cnf(c_858,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top
    | r2_hidden(sK1,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_856])).

cnf(c_8,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_385,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X1,X0) = X0
    | sK0 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_19])).

cnf(c_386,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK0)
    | k1_tops_1(X1,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_385])).

cnf(c_390,plain,
    ( ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X0,X1)
    | k1_tops_1(X1,X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_386,c_18])).

cnf(c_391,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = X0 ),
    inference(renaming,[status(thm)],[c_390])).

cnf(c_425,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(X1,X0) = X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_391,c_18])).

cnf(c_426,plain,
    ( ~ v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_425])).

cnf(c_14,negated_conjecture,
    ( m1_connsp_2(sK2,sK0,sK1)
    | v3_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_548,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) = X0
    | sK3 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_426,c_14])).

cnf(c_549,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,sK3) = sK3 ),
    inference(unflattening,[status(thm)],[c_548])).

cnf(c_15,negated_conjecture,
    ( m1_connsp_2(sK2,sK0,sK1)
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_553,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_connsp_2(sK2,sK0,sK1)
    | k1_tops_1(sK0,sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_549,c_15])).

cnf(c_554,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,sK3) = sK3 ),
    inference(renaming,[status(thm)],[c_553])).

cnf(c_1454,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,sK3) = sK3 ),
    inference(subtyping,[status(esa)],[c_554])).

cnf(c_1472,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | sP0_iProver_split
    | k1_tops_1(sK0,sK3) = sK3 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_1454])).

cnf(c_1526,plain,
    ( k1_tops_1(sK0,sK3) = sK3
    | m1_connsp_2(sK2,sK0,sK1) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1472])).

cnf(c_1469,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_1455])).

cnf(c_2152,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ sP0_iProver_split ),
    inference(instantiation,[status(thm)],[c_1469])).

cnf(c_2153,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2152])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_443,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_18])).

cnf(c_444,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_443])).

cnf(c_1458,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k1_tops_1(sK0,X0_43),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_444])).

cnf(c_2155,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_1458])).

cnf(c_2156,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2155])).

cnf(c_5,plain,
    ( r1_tarski(k1_tops_1(X0,X1),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_455,plain,
    ( r1_tarski(k1_tops_1(X0,X1),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_18])).

cnf(c_456,plain,
    ( r1_tarski(k1_tops_1(sK0,X0),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_455])).

cnf(c_1457,plain,
    ( r1_tarski(k1_tops_1(sK0,X0_43),X0_43)
    | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_456])).

cnf(c_2162,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_1457])).

cnf(c_2163,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2162])).

cnf(c_4,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_367,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_19])).

cnf(c_368,plain,
    ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_367])).

cnf(c_372,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(k1_tops_1(sK0,X0),sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_368,c_18])).

cnf(c_373,plain,
    ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(renaming,[status(thm)],[c_372])).

cnf(c_571,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X2) != X0
    | k1_tops_1(sK0,X0) = X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_426,c_373])).

cnf(c_572,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tops_1(sK0,X1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,k1_tops_1(sK0,X1)) = k1_tops_1(sK0,X1) ),
    inference(unflattening,[status(thm)],[c_571])).

cnf(c_584,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,k1_tops_1(sK0,X1)) = k1_tops_1(sK0,X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_572,c_444])).

cnf(c_1453,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1_43,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,k1_tops_1(sK0,X1_43)) = k1_tops_1(sK0,X1_43) ),
    inference(subtyping,[status(esa)],[c_584])).

cnf(c_1473,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,k1_tops_1(sK0,X0_43)) = k1_tops_1(sK0,X0_43)
    | ~ sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP2_iProver_split])],[c_1453])).

cnf(c_1474,plain,
    ( sP2_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_1453])).

cnf(c_1587,plain,
    ( k1_tops_1(sK0,k1_tops_1(sK0,X0_43)) = k1_tops_1(sK0,X0_43)
    | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1473,c_1469,c_1474])).

cnf(c_1588,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,k1_tops_1(sK0,X0_43)) = k1_tops_1(sK0,X0_43) ),
    inference(renaming,[status(thm)],[c_1587])).

cnf(c_2180,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,k1_tops_1(sK0,sK2)) = k1_tops_1(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_1588])).

cnf(c_2411,plain,
    ( ~ r1_tarski(sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1,sK3)
    | ~ sP1_iProver_split
    | k1_tops_1(sK0,sK3) != sK3 ),
    inference(instantiation,[status(thm)],[c_1470])).

cnf(c_2412,plain,
    ( k1_tops_1(sK0,sK3) != sK3
    | r1_tarski(sK3,sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r2_hidden(sK1,sK3) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2411])).

cnf(c_2414,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ sP1_iProver_split
    | k1_tops_1(sK0,k1_tops_1(sK0,sK2)) != k1_tops_1(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_1470])).

cnf(c_2415,plain,
    ( k1_tops_1(sK0,k1_tops_1(sK0,sK2)) != k1_tops_1(sK0,sK2)
    | r1_tarski(k1_tops_1(sK0,sK2),sK2) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2414])).

cnf(c_1464,negated_conjecture,
    ( m1_connsp_2(sK2,sK0,sK1)
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1985,plain,
    ( m1_connsp_2(sK2,sK0,sK1) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1464])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1467,plain,
    ( r1_tarski(X0_43,X1_43)
    | ~ m1_subset_1(X0_43,k1_zfmisc_1(X1_43)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1982,plain,
    ( r1_tarski(X0_43,X1_43) = iProver_top
    | m1_subset_1(X0_43,k1_zfmisc_1(X1_43)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1467])).

cnf(c_2440,plain,
    ( m1_connsp_2(sK2,sK0,sK1) = iProver_top
    | r1_tarski(sK3,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1985,c_1982])).

cnf(c_825,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(X0,k1_tops_1(sK0,X1))
    | sK0 != sK0
    | sK2 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_289])).

cnf(c_826,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(unflattening,[status(thm)],[c_825])).

cnf(c_828,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_826,c_17,c_16])).

cnf(c_830,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_828])).

cnf(c_591,plain,
    ( ~ m1_connsp_2(sK2,sK0,sK1)
    | ~ r1_tarski(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1,X0)
    | k1_tops_1(sK0,X1) != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_373])).

cnf(c_592,plain,
    ( ~ m1_connsp_2(sK2,sK0,sK1)
    | ~ r1_tarski(k1_tops_1(sK0,X0),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1,k1_tops_1(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_591])).

cnf(c_596,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k1_tops_1(sK0,X0),sK2)
    | ~ m1_connsp_2(sK2,sK0,sK1)
    | ~ r2_hidden(sK1,k1_tops_1(sK0,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_592,c_444])).

cnf(c_597,plain,
    ( ~ m1_connsp_2(sK2,sK0,sK1)
    | ~ r1_tarski(k1_tops_1(sK0,X0),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1,k1_tops_1(sK0,X0)) ),
    inference(renaming,[status(thm)],[c_596])).

cnf(c_1452,plain,
    ( ~ m1_connsp_2(sK2,sK0,sK1)
    | ~ r1_tarski(k1_tops_1(sK0,X0_43),sK2)
    | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1,k1_tops_1(sK0,X0_43)) ),
    inference(subtyping,[status(esa)],[c_597])).

cnf(c_2270,plain,
    ( ~ m1_connsp_2(sK2,sK0,sK1)
    | ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_1452])).

cnf(c_2271,plain,
    ( m1_connsp_2(sK2,sK0,sK1) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK2),sK2) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2270])).

cnf(c_2370,plain,
    ( r1_tarski(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_1467])).

cnf(c_2371,plain,
    ( r1_tarski(sK3,u1_struct_0(sK0)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2370])).

cnf(c_2519,plain,
    ( r1_tarski(sK3,u1_struct_0(sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2440,c_25,c_830,c_2163,c_2271,c_2371])).

cnf(c_1468,plain,
    ( ~ r1_tarski(X0_43,X1_43)
    | m1_subset_1(X0_43,k1_zfmisc_1(X1_43)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_2611,plain,
    ( ~ r1_tarski(sK3,u1_struct_0(sK0))
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_1468])).

cnf(c_2612,plain,
    ( r1_tarski(sK3,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2611])).

cnf(c_1463,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1986,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1463])).

cnf(c_1460,plain,
    ( ~ m1_connsp_2(X0_43,sK0,X1_43)
    | ~ m1_subset_1(X1_43,u1_struct_0(sK0))
    | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(X1_43,k1_tops_1(sK0,X0_43)) ),
    inference(subtyping,[status(esa)],[c_289])).

cnf(c_1989,plain,
    ( m1_connsp_2(X0_43,sK0,X1_43) != iProver_top
    | m1_subset_1(X1_43,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r2_hidden(X1_43,k1_tops_1(sK0,X0_43)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1460])).

cnf(c_2705,plain,
    ( m1_connsp_2(sK2,sK0,X0_43) != iProver_top
    | m1_subset_1(X0_43,u1_struct_0(sK0)) != iProver_top
    | r2_hidden(X0_43,k1_tops_1(sK0,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1986,c_1989])).

cnf(c_2742,plain,
    ( m1_connsp_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK1,u1_struct_0(sK0)) != iProver_top
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2705])).

cnf(c_2967,plain,
    ( sP1_iProver_split != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1995,c_24,c_16,c_25,c_830,c_844,c_858,c_1526,c_2153,c_2156,c_2163,c_2180,c_2271,c_2371,c_2412,c_2415,c_2440,c_2612,c_2742])).

cnf(c_2969,plain,
    ( ~ sP1_iProver_split ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2967])).

cnf(c_9,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_308,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_20])).

cnf(c_309,plain,
    ( m1_connsp_2(X0,sK0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(X1,k1_tops_1(sK0,X0))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_308])).

cnf(c_313,plain,
    ( m1_connsp_2(X0,sK0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(X1,k1_tops_1(sK0,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_309,c_19,c_18])).

cnf(c_1459,plain,
    ( m1_connsp_2(X0_43,sK0,X1_43)
    | ~ m1_subset_1(X1_43,u1_struct_0(sK0))
    | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(X1_43,k1_tops_1(sK0,X0_43)) ),
    inference(subtyping,[status(esa)],[c_313])).

cnf(c_1990,plain,
    ( m1_connsp_2(X0_43,sK0,X1_43) = iProver_top
    | m1_subset_1(X1_43,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r2_hidden(X1_43,k1_tops_1(sK0,X0_43)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1459])).

cnf(c_2838,plain,
    ( m1_connsp_2(sK2,sK0,X0_43) = iProver_top
    | m1_subset_1(X0_43,u1_struct_0(sK0)) != iProver_top
    | r2_hidden(X0_43,k1_tops_1(sK0,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1986,c_1990])).

cnf(c_2874,plain,
    ( m1_connsp_2(sK2,sK0,X0_43)
    | ~ m1_subset_1(X0_43,u1_struct_0(sK0))
    | ~ r2_hidden(X0_43,k1_tops_1(sK0,sK2)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2838])).

cnf(c_2876,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_2874])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_tops_1(X2,X0),k1_tops_1(X2,X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_485,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_tops_1(X2,X0),k1_tops_1(X2,X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_18])).

cnf(c_486,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_485])).

cnf(c_1456,plain,
    ( ~ r1_tarski(X0_43,X1_43)
    | r1_tarski(k1_tops_1(sK0,X0_43),k1_tops_1(sK0,X1_43))
    | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1_43,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_486])).

cnf(c_2346,plain,
    ( r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,X0_43))
    | ~ r1_tarski(sK3,X0_43)
    | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_1456])).

cnf(c_2657,plain,
    ( r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2))
    | ~ r1_tarski(sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_2346])).

cnf(c_2521,plain,
    ( r1_tarski(sK3,u1_struct_0(sK0)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2519])).

cnf(c_1478,plain,
    ( ~ r2_hidden(X0_43,X1_43)
    | r2_hidden(X2_43,X3_43)
    | X2_43 != X0_43
    | X3_43 != X1_43 ),
    theory(equality)).

cnf(c_2200,plain,
    ( r2_hidden(X0_43,X1_43)
    | ~ r2_hidden(sK1,sK3)
    | X1_43 != sK3
    | X0_43 != sK1 ),
    inference(instantiation,[status(thm)],[c_1478])).

cnf(c_2378,plain,
    ( r2_hidden(X0_43,k1_tops_1(sK0,sK3))
    | ~ r2_hidden(sK1,sK3)
    | X0_43 != sK1
    | k1_tops_1(sK0,sK3) != sK3 ),
    inference(instantiation,[status(thm)],[c_2200])).

cnf(c_2380,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK3))
    | ~ r2_hidden(sK1,sK3)
    | k1_tops_1(sK0,sK3) != sK3
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_2378])).

cnf(c_1471,plain,
    ( ~ m1_connsp_2(sK2,sK0,sK1)
    | sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_1455])).

cnf(c_1519,plain,
    ( m1_connsp_2(sK2,sK0,sK1) != iProver_top
    | sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1471])).

cnf(c_1476,plain,
    ( X0_43 = X0_43 ),
    theory(equality)).

cnf(c_1491,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_1476])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3235,c_2969,c_2967,c_2876,c_2657,c_2611,c_2521,c_2380,c_2153,c_2152,c_1526,c_1519,c_1471,c_1491,c_12,c_13,c_25,c_16,c_17])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n025.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 09:51:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.71/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.71/0.99  
% 1.71/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.71/0.99  
% 1.71/0.99  ------  iProver source info
% 1.71/0.99  
% 1.71/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.71/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.71/0.99  git: non_committed_changes: false
% 1.71/0.99  git: last_make_outside_of_git: false
% 1.71/0.99  
% 1.71/0.99  ------ 
% 1.71/0.99  
% 1.71/0.99  ------ Input Options
% 1.71/0.99  
% 1.71/0.99  --out_options                           all
% 1.71/0.99  --tptp_safe_out                         true
% 1.71/0.99  --problem_path                          ""
% 1.71/0.99  --include_path                          ""
% 1.71/0.99  --clausifier                            res/vclausify_rel
% 1.71/0.99  --clausifier_options                    --mode clausify
% 1.71/0.99  --stdin                                 false
% 1.71/0.99  --stats_out                             all
% 1.71/0.99  
% 1.71/0.99  ------ General Options
% 1.71/0.99  
% 1.71/0.99  --fof                                   false
% 1.71/0.99  --time_out_real                         305.
% 1.71/0.99  --time_out_virtual                      -1.
% 1.71/0.99  --symbol_type_check                     false
% 1.71/0.99  --clausify_out                          false
% 1.71/0.99  --sig_cnt_out                           false
% 1.71/0.99  --trig_cnt_out                          false
% 1.71/0.99  --trig_cnt_out_tolerance                1.
% 1.71/0.99  --trig_cnt_out_sk_spl                   false
% 1.71/0.99  --abstr_cl_out                          false
% 1.71/0.99  
% 1.71/0.99  ------ Global Options
% 1.71/0.99  
% 1.71/0.99  --schedule                              default
% 1.71/0.99  --add_important_lit                     false
% 1.71/0.99  --prop_solver_per_cl                    1000
% 1.71/0.99  --min_unsat_core                        false
% 1.71/0.99  --soft_assumptions                      false
% 1.71/0.99  --soft_lemma_size                       3
% 1.71/0.99  --prop_impl_unit_size                   0
% 1.71/0.99  --prop_impl_unit                        []
% 1.71/0.99  --share_sel_clauses                     true
% 1.71/0.99  --reset_solvers                         false
% 1.71/0.99  --bc_imp_inh                            [conj_cone]
% 1.71/0.99  --conj_cone_tolerance                   3.
% 1.71/0.99  --extra_neg_conj                        none
% 1.71/0.99  --large_theory_mode                     true
% 1.71/0.99  --prolific_symb_bound                   200
% 1.71/0.99  --lt_threshold                          2000
% 1.71/0.99  --clause_weak_htbl                      true
% 1.71/0.99  --gc_record_bc_elim                     false
% 1.71/0.99  
% 1.71/0.99  ------ Preprocessing Options
% 1.71/0.99  
% 1.71/0.99  --preprocessing_flag                    true
% 1.71/0.99  --time_out_prep_mult                    0.1
% 1.71/0.99  --splitting_mode                        input
% 1.71/0.99  --splitting_grd                         true
% 1.71/0.99  --splitting_cvd                         false
% 1.71/0.99  --splitting_cvd_svl                     false
% 1.71/0.99  --splitting_nvd                         32
% 1.71/0.99  --sub_typing                            true
% 1.71/0.99  --prep_gs_sim                           true
% 1.71/0.99  --prep_unflatten                        true
% 1.71/0.99  --prep_res_sim                          true
% 1.71/0.99  --prep_upred                            true
% 1.71/0.99  --prep_sem_filter                       exhaustive
% 1.71/0.99  --prep_sem_filter_out                   false
% 1.71/0.99  --pred_elim                             true
% 1.71/0.99  --res_sim_input                         true
% 1.71/0.99  --eq_ax_congr_red                       true
% 1.71/0.99  --pure_diseq_elim                       true
% 1.71/0.99  --brand_transform                       false
% 1.71/0.99  --non_eq_to_eq                          false
% 1.71/0.99  --prep_def_merge                        true
% 1.71/0.99  --prep_def_merge_prop_impl              false
% 1.71/0.99  --prep_def_merge_mbd                    true
% 1.71/0.99  --prep_def_merge_tr_red                 false
% 1.71/0.99  --prep_def_merge_tr_cl                  false
% 1.71/0.99  --smt_preprocessing                     true
% 1.71/0.99  --smt_ac_axioms                         fast
% 1.71/0.99  --preprocessed_out                      false
% 1.71/0.99  --preprocessed_stats                    false
% 1.71/0.99  
% 1.71/0.99  ------ Abstraction refinement Options
% 1.71/0.99  
% 1.71/0.99  --abstr_ref                             []
% 1.71/0.99  --abstr_ref_prep                        false
% 1.71/0.99  --abstr_ref_until_sat                   false
% 1.71/0.99  --abstr_ref_sig_restrict                funpre
% 1.71/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.71/0.99  --abstr_ref_under                       []
% 1.71/0.99  
% 1.71/0.99  ------ SAT Options
% 1.71/0.99  
% 1.71/0.99  --sat_mode                              false
% 1.71/0.99  --sat_fm_restart_options                ""
% 1.71/0.99  --sat_gr_def                            false
% 1.71/0.99  --sat_epr_types                         true
% 1.71/0.99  --sat_non_cyclic_types                  false
% 1.71/0.99  --sat_finite_models                     false
% 1.71/0.99  --sat_fm_lemmas                         false
% 1.71/0.99  --sat_fm_prep                           false
% 1.71/0.99  --sat_fm_uc_incr                        true
% 1.71/0.99  --sat_out_model                         small
% 1.71/0.99  --sat_out_clauses                       false
% 1.71/0.99  
% 1.71/0.99  ------ QBF Options
% 1.71/0.99  
% 1.71/0.99  --qbf_mode                              false
% 1.71/0.99  --qbf_elim_univ                         false
% 1.71/0.99  --qbf_dom_inst                          none
% 1.71/0.99  --qbf_dom_pre_inst                      false
% 1.71/0.99  --qbf_sk_in                             false
% 1.71/0.99  --qbf_pred_elim                         true
% 1.71/0.99  --qbf_split                             512
% 1.71/0.99  
% 1.71/0.99  ------ BMC1 Options
% 1.71/0.99  
% 1.71/0.99  --bmc1_incremental                      false
% 1.71/0.99  --bmc1_axioms                           reachable_all
% 1.71/0.99  --bmc1_min_bound                        0
% 1.71/0.99  --bmc1_max_bound                        -1
% 1.71/0.99  --bmc1_max_bound_default                -1
% 1.71/0.99  --bmc1_symbol_reachability              true
% 1.71/0.99  --bmc1_property_lemmas                  false
% 1.71/0.99  --bmc1_k_induction                      false
% 1.71/0.99  --bmc1_non_equiv_states                 false
% 1.71/0.99  --bmc1_deadlock                         false
% 1.71/0.99  --bmc1_ucm                              false
% 1.71/0.99  --bmc1_add_unsat_core                   none
% 1.71/0.99  --bmc1_unsat_core_children              false
% 1.71/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.71/0.99  --bmc1_out_stat                         full
% 1.71/0.99  --bmc1_ground_init                      false
% 1.71/0.99  --bmc1_pre_inst_next_state              false
% 1.71/0.99  --bmc1_pre_inst_state                   false
% 1.71/0.99  --bmc1_pre_inst_reach_state             false
% 1.71/0.99  --bmc1_out_unsat_core                   false
% 1.71/0.99  --bmc1_aig_witness_out                  false
% 1.71/0.99  --bmc1_verbose                          false
% 1.71/0.99  --bmc1_dump_clauses_tptp                false
% 1.71/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.71/0.99  --bmc1_dump_file                        -
% 1.71/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.71/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.71/0.99  --bmc1_ucm_extend_mode                  1
% 1.71/0.99  --bmc1_ucm_init_mode                    2
% 1.71/0.99  --bmc1_ucm_cone_mode                    none
% 1.71/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.71/0.99  --bmc1_ucm_relax_model                  4
% 1.71/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.71/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.71/0.99  --bmc1_ucm_layered_model                none
% 1.71/0.99  --bmc1_ucm_max_lemma_size               10
% 1.71/0.99  
% 1.71/0.99  ------ AIG Options
% 1.71/0.99  
% 1.71/0.99  --aig_mode                              false
% 1.71/0.99  
% 1.71/0.99  ------ Instantiation Options
% 1.71/0.99  
% 1.71/0.99  --instantiation_flag                    true
% 1.71/0.99  --inst_sos_flag                         false
% 1.71/0.99  --inst_sos_phase                        true
% 1.71/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.71/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.71/0.99  --inst_lit_sel_side                     num_symb
% 1.71/0.99  --inst_solver_per_active                1400
% 1.71/0.99  --inst_solver_calls_frac                1.
% 1.71/0.99  --inst_passive_queue_type               priority_queues
% 1.71/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.71/0.99  --inst_passive_queues_freq              [25;2]
% 1.71/0.99  --inst_dismatching                      true
% 1.71/0.99  --inst_eager_unprocessed_to_passive     true
% 1.71/0.99  --inst_prop_sim_given                   true
% 1.71/0.99  --inst_prop_sim_new                     false
% 1.71/0.99  --inst_subs_new                         false
% 1.71/0.99  --inst_eq_res_simp                      false
% 1.71/0.99  --inst_subs_given                       false
% 1.71/0.99  --inst_orphan_elimination               true
% 1.71/0.99  --inst_learning_loop_flag               true
% 1.71/0.99  --inst_learning_start                   3000
% 1.71/0.99  --inst_learning_factor                  2
% 1.71/0.99  --inst_start_prop_sim_after_learn       3
% 1.71/0.99  --inst_sel_renew                        solver
% 1.71/0.99  --inst_lit_activity_flag                true
% 1.71/0.99  --inst_restr_to_given                   false
% 1.71/0.99  --inst_activity_threshold               500
% 1.71/0.99  --inst_out_proof                        true
% 1.71/0.99  
% 1.71/0.99  ------ Resolution Options
% 1.71/0.99  
% 1.71/0.99  --resolution_flag                       true
% 1.71/0.99  --res_lit_sel                           adaptive
% 1.71/0.99  --res_lit_sel_side                      none
% 1.71/0.99  --res_ordering                          kbo
% 1.71/0.99  --res_to_prop_solver                    active
% 1.71/0.99  --res_prop_simpl_new                    false
% 1.71/0.99  --res_prop_simpl_given                  true
% 1.71/0.99  --res_passive_queue_type                priority_queues
% 1.71/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.71/0.99  --res_passive_queues_freq               [15;5]
% 1.71/0.99  --res_forward_subs                      full
% 1.71/0.99  --res_backward_subs                     full
% 1.71/0.99  --res_forward_subs_resolution           true
% 1.71/0.99  --res_backward_subs_resolution          true
% 1.71/0.99  --res_orphan_elimination                true
% 1.71/0.99  --res_time_limit                        2.
% 1.71/0.99  --res_out_proof                         true
% 1.71/0.99  
% 1.71/0.99  ------ Superposition Options
% 1.71/0.99  
% 1.71/0.99  --superposition_flag                    true
% 1.71/0.99  --sup_passive_queue_type                priority_queues
% 1.71/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.71/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.71/0.99  --demod_completeness_check              fast
% 1.71/0.99  --demod_use_ground                      true
% 1.71/0.99  --sup_to_prop_solver                    passive
% 1.71/0.99  --sup_prop_simpl_new                    true
% 1.71/0.99  --sup_prop_simpl_given                  true
% 1.71/0.99  --sup_fun_splitting                     false
% 1.71/0.99  --sup_smt_interval                      50000
% 1.71/0.99  
% 1.71/0.99  ------ Superposition Simplification Setup
% 1.71/0.99  
% 1.71/0.99  --sup_indices_passive                   []
% 1.71/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.71/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.71/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.71/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.71/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.71/0.99  --sup_full_bw                           [BwDemod]
% 1.71/0.99  --sup_immed_triv                        [TrivRules]
% 1.71/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.71/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.71/0.99  --sup_immed_bw_main                     []
% 1.71/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.71/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.71/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.71/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.71/0.99  
% 1.71/0.99  ------ Combination Options
% 1.71/0.99  
% 1.71/0.99  --comb_res_mult                         3
% 1.71/0.99  --comb_sup_mult                         2
% 1.71/0.99  --comb_inst_mult                        10
% 1.71/0.99  
% 1.71/0.99  ------ Debug Options
% 1.71/0.99  
% 1.71/0.99  --dbg_backtrace                         false
% 1.71/0.99  --dbg_dump_prop_clauses                 false
% 1.71/0.99  --dbg_dump_prop_clauses_file            -
% 1.71/0.99  --dbg_out_stat                          false
% 1.71/0.99  ------ Parsing...
% 1.71/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.71/0.99  
% 1.71/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 1.71/0.99  
% 1.71/0.99  ------ Preprocessing... gs_s  sp: 5 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.71/0.99  
% 1.71/0.99  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.71/0.99  ------ Proving...
% 1.71/0.99  ------ Problem Properties 
% 1.71/0.99  
% 1.71/0.99  
% 1.71/0.99  clauses                                 22
% 1.71/0.99  conjectures                             5
% 1.71/0.99  EPR                                     5
% 1.71/0.99  Horn                                    16
% 1.71/0.99  unary                                   2
% 1.71/0.99  binary                                  11
% 1.71/0.99  lits                                    57
% 1.71/0.99  lits eq                                 3
% 1.71/0.99  fd_pure                                 0
% 1.71/0.99  fd_pseudo                               0
% 1.71/0.99  fd_cond                                 0
% 1.71/0.99  fd_pseudo_cond                          0
% 1.71/0.99  AC symbols                              0
% 1.71/0.99  
% 1.71/0.99  ------ Schedule dynamic 5 is on 
% 1.71/0.99  
% 1.71/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.71/0.99  
% 1.71/0.99  
% 1.71/0.99  ------ 
% 1.71/0.99  Current options:
% 1.71/0.99  ------ 
% 1.71/0.99  
% 1.71/0.99  ------ Input Options
% 1.71/0.99  
% 1.71/0.99  --out_options                           all
% 1.71/0.99  --tptp_safe_out                         true
% 1.71/0.99  --problem_path                          ""
% 1.71/0.99  --include_path                          ""
% 1.71/0.99  --clausifier                            res/vclausify_rel
% 1.71/0.99  --clausifier_options                    --mode clausify
% 1.71/0.99  --stdin                                 false
% 1.71/0.99  --stats_out                             all
% 1.71/0.99  
% 1.71/0.99  ------ General Options
% 1.71/0.99  
% 1.71/0.99  --fof                                   false
% 1.71/0.99  --time_out_real                         305.
% 1.71/0.99  --time_out_virtual                      -1.
% 1.71/0.99  --symbol_type_check                     false
% 1.71/0.99  --clausify_out                          false
% 1.71/0.99  --sig_cnt_out                           false
% 1.71/0.99  --trig_cnt_out                          false
% 1.71/0.99  --trig_cnt_out_tolerance                1.
% 1.71/0.99  --trig_cnt_out_sk_spl                   false
% 1.71/0.99  --abstr_cl_out                          false
% 1.71/0.99  
% 1.71/0.99  ------ Global Options
% 1.71/0.99  
% 1.71/0.99  --schedule                              default
% 1.71/0.99  --add_important_lit                     false
% 1.71/0.99  --prop_solver_per_cl                    1000
% 1.71/0.99  --min_unsat_core                        false
% 1.71/0.99  --soft_assumptions                      false
% 1.71/0.99  --soft_lemma_size                       3
% 1.71/0.99  --prop_impl_unit_size                   0
% 1.71/0.99  --prop_impl_unit                        []
% 1.71/0.99  --share_sel_clauses                     true
% 1.71/0.99  --reset_solvers                         false
% 1.71/0.99  --bc_imp_inh                            [conj_cone]
% 1.71/0.99  --conj_cone_tolerance                   3.
% 1.71/0.99  --extra_neg_conj                        none
% 1.71/0.99  --large_theory_mode                     true
% 1.71/0.99  --prolific_symb_bound                   200
% 1.71/0.99  --lt_threshold                          2000
% 1.71/0.99  --clause_weak_htbl                      true
% 1.71/0.99  --gc_record_bc_elim                     false
% 1.71/0.99  
% 1.71/0.99  ------ Preprocessing Options
% 1.71/0.99  
% 1.71/0.99  --preprocessing_flag                    true
% 1.71/0.99  --time_out_prep_mult                    0.1
% 1.71/0.99  --splitting_mode                        input
% 1.71/0.99  --splitting_grd                         true
% 1.71/0.99  --splitting_cvd                         false
% 1.71/0.99  --splitting_cvd_svl                     false
% 1.71/0.99  --splitting_nvd                         32
% 1.71/0.99  --sub_typing                            true
% 1.71/0.99  --prep_gs_sim                           true
% 1.71/0.99  --prep_unflatten                        true
% 1.71/0.99  --prep_res_sim                          true
% 1.71/0.99  --prep_upred                            true
% 1.71/0.99  --prep_sem_filter                       exhaustive
% 1.71/0.99  --prep_sem_filter_out                   false
% 1.71/0.99  --pred_elim                             true
% 1.71/0.99  --res_sim_input                         true
% 1.71/0.99  --eq_ax_congr_red                       true
% 1.71/0.99  --pure_diseq_elim                       true
% 1.71/0.99  --brand_transform                       false
% 1.71/0.99  --non_eq_to_eq                          false
% 1.71/0.99  --prep_def_merge                        true
% 1.71/0.99  --prep_def_merge_prop_impl              false
% 1.71/0.99  --prep_def_merge_mbd                    true
% 1.71/0.99  --prep_def_merge_tr_red                 false
% 1.71/0.99  --prep_def_merge_tr_cl                  false
% 1.71/0.99  --smt_preprocessing                     true
% 1.71/0.99  --smt_ac_axioms                         fast
% 1.71/0.99  --preprocessed_out                      false
% 1.71/0.99  --preprocessed_stats                    false
% 1.71/0.99  
% 1.71/0.99  ------ Abstraction refinement Options
% 1.71/0.99  
% 1.71/0.99  --abstr_ref                             []
% 1.71/0.99  --abstr_ref_prep                        false
% 1.71/0.99  --abstr_ref_until_sat                   false
% 1.71/0.99  --abstr_ref_sig_restrict                funpre
% 1.71/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.71/0.99  --abstr_ref_under                       []
% 1.71/0.99  
% 1.71/0.99  ------ SAT Options
% 1.71/0.99  
% 1.71/0.99  --sat_mode                              false
% 1.71/0.99  --sat_fm_restart_options                ""
% 1.71/0.99  --sat_gr_def                            false
% 1.71/0.99  --sat_epr_types                         true
% 1.71/0.99  --sat_non_cyclic_types                  false
% 1.71/0.99  --sat_finite_models                     false
% 1.71/0.99  --sat_fm_lemmas                         false
% 1.71/0.99  --sat_fm_prep                           false
% 1.71/0.99  --sat_fm_uc_incr                        true
% 1.71/0.99  --sat_out_model                         small
% 1.71/0.99  --sat_out_clauses                       false
% 1.71/0.99  
% 1.71/0.99  ------ QBF Options
% 1.71/0.99  
% 1.71/0.99  --qbf_mode                              false
% 1.71/0.99  --qbf_elim_univ                         false
% 1.71/0.99  --qbf_dom_inst                          none
% 1.71/0.99  --qbf_dom_pre_inst                      false
% 1.71/0.99  --qbf_sk_in                             false
% 1.71/0.99  --qbf_pred_elim                         true
% 1.71/0.99  --qbf_split                             512
% 1.71/0.99  
% 1.71/0.99  ------ BMC1 Options
% 1.71/0.99  
% 1.71/0.99  --bmc1_incremental                      false
% 1.71/0.99  --bmc1_axioms                           reachable_all
% 1.71/0.99  --bmc1_min_bound                        0
% 1.71/0.99  --bmc1_max_bound                        -1
% 1.71/0.99  --bmc1_max_bound_default                -1
% 1.71/0.99  --bmc1_symbol_reachability              true
% 1.71/0.99  --bmc1_property_lemmas                  false
% 1.71/0.99  --bmc1_k_induction                      false
% 1.71/0.99  --bmc1_non_equiv_states                 false
% 1.71/0.99  --bmc1_deadlock                         false
% 1.71/0.99  --bmc1_ucm                              false
% 1.71/0.99  --bmc1_add_unsat_core                   none
% 1.71/0.99  --bmc1_unsat_core_children              false
% 1.71/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.71/0.99  --bmc1_out_stat                         full
% 1.71/0.99  --bmc1_ground_init                      false
% 1.71/0.99  --bmc1_pre_inst_next_state              false
% 1.71/0.99  --bmc1_pre_inst_state                   false
% 1.71/0.99  --bmc1_pre_inst_reach_state             false
% 1.71/0.99  --bmc1_out_unsat_core                   false
% 1.71/0.99  --bmc1_aig_witness_out                  false
% 1.71/0.99  --bmc1_verbose                          false
% 1.71/0.99  --bmc1_dump_clauses_tptp                false
% 1.71/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.71/0.99  --bmc1_dump_file                        -
% 1.71/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.71/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.71/0.99  --bmc1_ucm_extend_mode                  1
% 1.71/0.99  --bmc1_ucm_init_mode                    2
% 1.71/0.99  --bmc1_ucm_cone_mode                    none
% 1.71/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.71/0.99  --bmc1_ucm_relax_model                  4
% 1.71/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.71/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.71/0.99  --bmc1_ucm_layered_model                none
% 1.71/0.99  --bmc1_ucm_max_lemma_size               10
% 1.71/0.99  
% 1.71/0.99  ------ AIG Options
% 1.71/0.99  
% 1.71/0.99  --aig_mode                              false
% 1.71/0.99  
% 1.71/0.99  ------ Instantiation Options
% 1.71/0.99  
% 1.71/0.99  --instantiation_flag                    true
% 1.71/0.99  --inst_sos_flag                         false
% 1.71/0.99  --inst_sos_phase                        true
% 1.71/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.71/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.71/0.99  --inst_lit_sel_side                     none
% 1.71/0.99  --inst_solver_per_active                1400
% 1.71/0.99  --inst_solver_calls_frac                1.
% 1.71/0.99  --inst_passive_queue_type               priority_queues
% 1.71/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.71/0.99  --inst_passive_queues_freq              [25;2]
% 1.71/0.99  --inst_dismatching                      true
% 1.71/0.99  --inst_eager_unprocessed_to_passive     true
% 1.71/0.99  --inst_prop_sim_given                   true
% 1.71/0.99  --inst_prop_sim_new                     false
% 1.71/0.99  --inst_subs_new                         false
% 1.71/0.99  --inst_eq_res_simp                      false
% 1.71/0.99  --inst_subs_given                       false
% 1.71/0.99  --inst_orphan_elimination               true
% 1.71/0.99  --inst_learning_loop_flag               true
% 1.71/0.99  --inst_learning_start                   3000
% 1.71/0.99  --inst_learning_factor                  2
% 1.71/0.99  --inst_start_prop_sim_after_learn       3
% 1.71/0.99  --inst_sel_renew                        solver
% 1.71/0.99  --inst_lit_activity_flag                true
% 1.71/0.99  --inst_restr_to_given                   false
% 1.71/0.99  --inst_activity_threshold               500
% 1.71/0.99  --inst_out_proof                        true
% 1.71/0.99  
% 1.71/0.99  ------ Resolution Options
% 1.71/0.99  
% 1.71/0.99  --resolution_flag                       false
% 1.71/0.99  --res_lit_sel                           adaptive
% 1.71/0.99  --res_lit_sel_side                      none
% 1.71/0.99  --res_ordering                          kbo
% 1.71/0.99  --res_to_prop_solver                    active
% 1.71/0.99  --res_prop_simpl_new                    false
% 1.71/0.99  --res_prop_simpl_given                  true
% 1.71/0.99  --res_passive_queue_type                priority_queues
% 1.71/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.71/0.99  --res_passive_queues_freq               [15;5]
% 1.71/0.99  --res_forward_subs                      full
% 1.71/0.99  --res_backward_subs                     full
% 1.71/0.99  --res_forward_subs_resolution           true
% 1.71/0.99  --res_backward_subs_resolution          true
% 1.71/0.99  --res_orphan_elimination                true
% 1.71/0.99  --res_time_limit                        2.
% 1.71/0.99  --res_out_proof                         true
% 1.71/0.99  
% 1.71/0.99  ------ Superposition Options
% 1.71/0.99  
% 1.71/0.99  --superposition_flag                    true
% 1.71/0.99  --sup_passive_queue_type                priority_queues
% 1.71/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.71/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.71/0.99  --demod_completeness_check              fast
% 1.71/0.99  --demod_use_ground                      true
% 1.71/0.99  --sup_to_prop_solver                    passive
% 1.71/0.99  --sup_prop_simpl_new                    true
% 1.71/0.99  --sup_prop_simpl_given                  true
% 1.71/0.99  --sup_fun_splitting                     false
% 1.71/0.99  --sup_smt_interval                      50000
% 1.71/0.99  
% 1.71/0.99  ------ Superposition Simplification Setup
% 1.71/0.99  
% 1.71/0.99  --sup_indices_passive                   []
% 1.71/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.71/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.71/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.71/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.71/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.71/0.99  --sup_full_bw                           [BwDemod]
% 1.71/0.99  --sup_immed_triv                        [TrivRules]
% 1.71/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.71/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.71/0.99  --sup_immed_bw_main                     []
% 1.71/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.71/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.71/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.71/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.71/0.99  
% 1.71/0.99  ------ Combination Options
% 1.71/0.99  
% 1.71/0.99  --comb_res_mult                         3
% 1.71/0.99  --comb_sup_mult                         2
% 1.71/0.99  --comb_inst_mult                        10
% 1.71/0.99  
% 1.71/0.99  ------ Debug Options
% 1.71/0.99  
% 1.71/0.99  --dbg_backtrace                         false
% 1.71/0.99  --dbg_dump_prop_clauses                 false
% 1.71/0.99  --dbg_dump_prop_clauses_file            -
% 1.71/0.99  --dbg_out_stat                          false
% 1.71/0.99  
% 1.71/0.99  
% 1.71/0.99  
% 1.71/0.99  
% 1.71/0.99  ------ Proving...
% 1.71/0.99  
% 1.71/0.99  
% 1.71/0.99  % SZS status Theorem for theBenchmark.p
% 1.71/0.99  
% 1.71/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 1.71/0.99  
% 1.71/0.99  fof(f1,axiom,(
% 1.71/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.71/0.99  
% 1.71/0.99  fof(f11,plain,(
% 1.71/0.99    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.71/0.99    inference(ennf_transformation,[],[f1])).
% 1.71/0.99  
% 1.71/0.99  fof(f35,plain,(
% 1.71/0.99    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.71/0.99    inference(cnf_transformation,[],[f11])).
% 1.71/0.99  
% 1.71/0.99  fof(f2,axiom,(
% 1.71/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.71/0.99  
% 1.71/0.99  fof(f25,plain,(
% 1.71/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.71/0.99    inference(nnf_transformation,[],[f2])).
% 1.71/0.99  
% 1.71/0.99  fof(f37,plain,(
% 1.71/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.71/0.99    inference(cnf_transformation,[],[f25])).
% 1.71/0.99  
% 1.71/0.99  fof(f7,axiom,(
% 1.71/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 1.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.71/0.99  
% 1.71/0.99  fof(f19,plain,(
% 1.71/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.71/0.99    inference(ennf_transformation,[],[f7])).
% 1.71/0.99  
% 1.71/0.99  fof(f20,plain,(
% 1.71/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.71/0.99    inference(flattening,[],[f19])).
% 1.71/0.99  
% 1.71/0.99  fof(f43,plain,(
% 1.71/0.99    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.71/0.99    inference(cnf_transformation,[],[f20])).
% 1.71/0.99  
% 1.71/0.99  fof(f9,conjecture,(
% 1.71/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 1.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.71/0.99  
% 1.71/0.99  fof(f10,negated_conjecture,(
% 1.71/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 1.71/0.99    inference(negated_conjecture,[],[f9])).
% 1.71/0.99  
% 1.71/0.99  fof(f23,plain,(
% 1.71/0.99    ? [X0] : (? [X1] : (? [X2] : ((m1_connsp_2(X2,X0,X1) <~> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.71/0.99    inference(ennf_transformation,[],[f10])).
% 1.71/0.99  
% 1.71/0.99  fof(f24,plain,(
% 1.71/0.99    ? [X0] : (? [X1] : (? [X2] : ((m1_connsp_2(X2,X0,X1) <~> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.71/0.99    inference(flattening,[],[f23])).
% 1.71/0.99  
% 1.71/0.99  fof(f27,plain,(
% 1.71/0.99    ? [X0] : (? [X1] : (? [X2] : (((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1)) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | m1_connsp_2(X2,X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.71/0.99    inference(nnf_transformation,[],[f24])).
% 1.71/0.99  
% 1.71/0.99  fof(f28,plain,(
% 1.71/0.99    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1)) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.71/0.99    inference(flattening,[],[f27])).
% 1.71/0.99  
% 1.71/0.99  fof(f29,plain,(
% 1.71/0.99    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1)) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.71/0.99    inference(rectify,[],[f28])).
% 1.71/0.99  
% 1.71/0.99  fof(f33,plain,(
% 1.71/0.99    ( ! [X2,X0,X1] : (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) => (r2_hidden(X1,sK3) & r1_tarski(sK3,X2) & v3_pre_topc(sK3,X0) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 1.71/0.99    introduced(choice_axiom,[])).
% 1.71/0.99  
% 1.71/0.99  fof(f32,plain,(
% 1.71/0.99    ( ! [X0,X1] : (? [X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1)) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(sK2,X0,X1)) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,sK2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | m1_connsp_2(sK2,X0,X1)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 1.71/0.99    introduced(choice_axiom,[])).
% 1.71/0.99  
% 1.71/0.99  fof(f31,plain,(
% 1.71/0.99    ( ! [X0] : (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1)) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : ((! [X3] : (~r2_hidden(sK1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,sK1)) & (? [X4] : (r2_hidden(sK1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | m1_connsp_2(X2,X0,sK1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK1,u1_struct_0(X0)))) )),
% 1.71/0.99    introduced(choice_axiom,[])).
% 1.71/0.99  
% 1.71/0.99  fof(f30,plain,(
% 1.71/0.99    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1)) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_connsp_2(X2,sK0,X1)) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,sK0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) | m1_connsp_2(X2,sK0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.71/0.99    introduced(choice_axiom,[])).
% 1.71/0.99  
% 1.71/0.99  fof(f34,plain,(
% 1.71/0.99    (((! [X3] : (~r2_hidden(sK1,X3) | ~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_connsp_2(sK2,sK0,sK1)) & ((r2_hidden(sK1,sK3) & r1_tarski(sK3,sK2) & v3_pre_topc(sK3,sK0) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))) | m1_connsp_2(sK2,sK0,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.71/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f29,f33,f32,f31,f30])).
% 1.71/0.99  
% 1.71/0.99  fof(f47,plain,(
% 1.71/0.99    v2_pre_topc(sK0)),
% 1.71/0.99    inference(cnf_transformation,[],[f34])).
% 1.71/0.99  
% 1.71/0.99  fof(f48,plain,(
% 1.71/0.99    l1_pre_topc(sK0)),
% 1.71/0.99    inference(cnf_transformation,[],[f34])).
% 1.71/0.99  
% 1.71/0.99  fof(f55,plain,(
% 1.71/0.99    ( ! [X3] : (~r2_hidden(sK1,X3) | ~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_connsp_2(sK2,sK0,sK1)) )),
% 1.71/0.99    inference(cnf_transformation,[],[f34])).
% 1.71/0.99  
% 1.71/0.99  fof(f49,plain,(
% 1.71/0.99    m1_subset_1(sK1,u1_struct_0(sK0))),
% 1.71/0.99    inference(cnf_transformation,[],[f34])).
% 1.71/0.99  
% 1.71/0.99  fof(f50,plain,(
% 1.71/0.99    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.71/0.99    inference(cnf_transformation,[],[f34])).
% 1.71/0.99  
% 1.71/0.99  fof(f53,plain,(
% 1.71/0.99    r1_tarski(sK3,sK2) | m1_connsp_2(sK2,sK0,sK1)),
% 1.71/0.99    inference(cnf_transformation,[],[f34])).
% 1.71/0.99  
% 1.71/0.99  fof(f8,axiom,(
% 1.71/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 1.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.71/0.99  
% 1.71/0.99  fof(f21,plain,(
% 1.71/0.99    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.71/0.99    inference(ennf_transformation,[],[f8])).
% 1.71/0.99  
% 1.71/0.99  fof(f22,plain,(
% 1.71/0.99    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.71/0.99    inference(flattening,[],[f21])).
% 1.71/0.99  
% 1.71/0.99  fof(f26,plain,(
% 1.71/0.99    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.71/0.99    inference(nnf_transformation,[],[f22])).
% 1.71/0.99  
% 1.71/0.99  fof(f44,plain,(
% 1.71/0.99    ( ! [X2,X0,X1] : (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.71/0.99    inference(cnf_transformation,[],[f26])).
% 1.71/0.99  
% 1.71/0.99  fof(f46,plain,(
% 1.71/0.99    ~v2_struct_0(sK0)),
% 1.71/0.99    inference(cnf_transformation,[],[f34])).
% 1.71/0.99  
% 1.71/0.99  fof(f54,plain,(
% 1.71/0.99    r2_hidden(sK1,sK3) | m1_connsp_2(sK2,sK0,sK1)),
% 1.71/0.99    inference(cnf_transformation,[],[f34])).
% 1.71/0.99  
% 1.71/0.99  fof(f42,plain,(
% 1.71/0.99    ( ! [X2,X0,X3,X1] : (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.71/0.99    inference(cnf_transformation,[],[f20])).
% 1.71/0.99  
% 1.71/0.99  fof(f52,plain,(
% 1.71/0.99    v3_pre_topc(sK3,sK0) | m1_connsp_2(sK2,sK0,sK1)),
% 1.71/0.99    inference(cnf_transformation,[],[f34])).
% 1.71/0.99  
% 1.71/0.99  fof(f51,plain,(
% 1.71/0.99    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | m1_connsp_2(sK2,sK0,sK1)),
% 1.71/0.99    inference(cnf_transformation,[],[f34])).
% 1.71/0.99  
% 1.71/0.99  fof(f3,axiom,(
% 1.71/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.71/0.99  
% 1.71/0.99  fof(f12,plain,(
% 1.71/0.99    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.71/0.99    inference(ennf_transformation,[],[f3])).
% 1.71/0.99  
% 1.71/0.99  fof(f13,plain,(
% 1.71/0.99    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.71/0.99    inference(flattening,[],[f12])).
% 1.71/0.99  
% 1.71/0.99  fof(f38,plain,(
% 1.71/0.99    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.71/0.99    inference(cnf_transformation,[],[f13])).
% 1.71/0.99  
% 1.71/0.99  fof(f5,axiom,(
% 1.71/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 1.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.71/0.99  
% 1.71/0.99  fof(f16,plain,(
% 1.71/0.99    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.71/0.99    inference(ennf_transformation,[],[f5])).
% 1.71/0.99  
% 1.71/0.99  fof(f40,plain,(
% 1.71/0.99    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.71/0.99    inference(cnf_transformation,[],[f16])).
% 1.71/0.99  
% 1.71/0.99  fof(f4,axiom,(
% 1.71/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 1.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.71/0.99  
% 1.71/0.99  fof(f14,plain,(
% 1.71/0.99    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.71/0.99    inference(ennf_transformation,[],[f4])).
% 1.71/0.99  
% 1.71/0.99  fof(f15,plain,(
% 1.71/0.99    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.71/0.99    inference(flattening,[],[f14])).
% 1.71/0.99  
% 1.71/0.99  fof(f39,plain,(
% 1.71/0.99    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.71/0.99    inference(cnf_transformation,[],[f15])).
% 1.71/0.99  
% 1.71/0.99  fof(f36,plain,(
% 1.71/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.71/0.99    inference(cnf_transformation,[],[f25])).
% 1.71/0.99  
% 1.71/0.99  fof(f45,plain,(
% 1.71/0.99    ( ! [X2,X0,X1] : (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.71/0.99    inference(cnf_transformation,[],[f26])).
% 1.71/0.99  
% 1.71/0.99  fof(f6,axiom,(
% 1.71/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 1.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.71/0.99  
% 1.71/0.99  fof(f17,plain,(
% 1.71/0.99    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.71/0.99    inference(ennf_transformation,[],[f6])).
% 1.71/0.99  
% 1.71/0.99  fof(f18,plain,(
% 1.71/0.99    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.71/0.99    inference(flattening,[],[f17])).
% 1.71/0.99  
% 1.71/0.99  fof(f41,plain,(
% 1.71/0.99    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.71/0.99    inference(cnf_transformation,[],[f18])).
% 1.71/0.99  
% 1.71/0.99  cnf(c_0,plain,
% 1.71/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.71/0.99      | ~ r2_hidden(X2,X0)
% 1.71/0.99      | r2_hidden(X2,X1) ),
% 1.71/0.99      inference(cnf_transformation,[],[f35]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_1,plain,
% 1.71/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 1.71/0.99      inference(cnf_transformation,[],[f37]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_156,plain,
% 1.71/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 1.71/0.99      inference(prop_impl,[status(thm)],[c_1]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_205,plain,
% 1.71/0.99      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 1.71/0.99      inference(bin_hyper_res,[status(thm)],[c_0,c_156]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_1461,plain,
% 1.71/0.99      ( ~ r1_tarski(X0_43,X1_43)
% 1.71/0.99      | ~ r2_hidden(X2_43,X0_43)
% 1.71/0.99      | r2_hidden(X2_43,X1_43) ),
% 1.71/0.99      inference(subtyping,[status(esa)],[c_205]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_3230,plain,
% 1.71/0.99      ( ~ r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2))
% 1.71/0.99      | ~ r2_hidden(X0_43,k1_tops_1(sK0,sK3))
% 1.71/0.99      | r2_hidden(X0_43,k1_tops_1(sK0,sK2)) ),
% 1.71/0.99      inference(instantiation,[status(thm)],[c_1461]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_3235,plain,
% 1.71/0.99      ( ~ r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2))
% 1.71/0.99      | ~ r2_hidden(sK1,k1_tops_1(sK0,sK3))
% 1.71/0.99      | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
% 1.71/0.99      inference(instantiation,[status(thm)],[c_3230]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_7,plain,
% 1.71/0.99      ( v3_pre_topc(X0,X1)
% 1.71/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.71/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 1.71/0.99      | ~ v2_pre_topc(X1)
% 1.71/0.99      | ~ l1_pre_topc(X1)
% 1.71/0.99      | ~ l1_pre_topc(X3)
% 1.71/0.99      | k1_tops_1(X1,X0) != X0 ),
% 1.71/0.99      inference(cnf_transformation,[],[f43]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_19,negated_conjecture,
% 1.71/0.99      ( v2_pre_topc(sK0) ),
% 1.71/0.99      inference(cnf_transformation,[],[f47]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_342,plain,
% 1.71/0.99      ( v3_pre_topc(X0,X1)
% 1.71/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.71/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 1.71/0.99      | ~ l1_pre_topc(X1)
% 1.71/0.99      | ~ l1_pre_topc(X3)
% 1.71/0.99      | k1_tops_1(X1,X0) != X0
% 1.71/0.99      | sK0 != X1 ),
% 1.71/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_19]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_343,plain,
% 1.71/0.99      ( v3_pre_topc(X0,sK0)
% 1.71/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.71/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/0.99      | ~ l1_pre_topc(X2)
% 1.71/0.99      | ~ l1_pre_topc(sK0)
% 1.71/0.99      | k1_tops_1(sK0,X0) != X0 ),
% 1.71/0.99      inference(unflattening,[status(thm)],[c_342]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_18,negated_conjecture,
% 1.71/0.99      ( l1_pre_topc(sK0) ),
% 1.71/0.99      inference(cnf_transformation,[],[f48]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_347,plain,
% 1.71/0.99      ( ~ l1_pre_topc(X2)
% 1.71/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.71/0.99      | v3_pre_topc(X0,sK0)
% 1.71/0.99      | k1_tops_1(sK0,X0) != X0 ),
% 1.71/0.99      inference(global_propositional_subsumption,
% 1.71/0.99                [status(thm)],
% 1.71/0.99                [c_343,c_18]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_348,plain,
% 1.71/0.99      ( v3_pre_topc(X0,sK0)
% 1.71/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.71/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/0.99      | ~ l1_pre_topc(X2)
% 1.71/0.99      | k1_tops_1(sK0,X0) != X0 ),
% 1.71/0.99      inference(renaming,[status(thm)],[c_347]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_467,plain,
% 1.71/0.99      ( v3_pre_topc(X0,sK0)
% 1.71/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.71/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/0.99      | k1_tops_1(sK0,X0) != X0
% 1.71/0.99      | sK0 != X2 ),
% 1.71/0.99      inference(resolution_lifted,[status(thm)],[c_348,c_18]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_468,plain,
% 1.71/0.99      ( v3_pre_topc(X0,sK0)
% 1.71/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/0.99      | k1_tops_1(sK0,X0) != X0 ),
% 1.71/0.99      inference(unflattening,[status(thm)],[c_467]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_11,negated_conjecture,
% 1.71/0.99      ( ~ m1_connsp_2(sK2,sK0,sK1)
% 1.71/0.99      | ~ v3_pre_topc(X0,sK0)
% 1.71/0.99      | ~ r1_tarski(X0,sK2)
% 1.71/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/0.99      | ~ r2_hidden(sK1,X0) ),
% 1.71/0.99      inference(cnf_transformation,[],[f55]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_525,plain,
% 1.71/0.99      ( ~ m1_connsp_2(sK2,sK0,sK1)
% 1.71/0.99      | ~ r1_tarski(X0,sK2)
% 1.71/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/0.99      | ~ r2_hidden(sK1,X0)
% 1.71/0.99      | k1_tops_1(sK0,X0) != X0 ),
% 1.71/0.99      inference(resolution,[status(thm)],[c_468,c_11]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_1455,plain,
% 1.71/0.99      ( ~ m1_connsp_2(sK2,sK0,sK1)
% 1.71/0.99      | ~ r1_tarski(X0_43,sK2)
% 1.71/0.99      | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/0.99      | ~ m1_subset_1(X1_43,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/0.99      | ~ r2_hidden(sK1,X0_43)
% 1.71/0.99      | k1_tops_1(sK0,X0_43) != X0_43 ),
% 1.71/0.99      inference(subtyping,[status(esa)],[c_525]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_1470,plain,
% 1.71/0.99      ( ~ r1_tarski(X0_43,sK2)
% 1.71/0.99      | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/0.99      | ~ r2_hidden(sK1,X0_43)
% 1.71/0.99      | k1_tops_1(sK0,X0_43) != X0_43
% 1.71/0.99      | ~ sP1_iProver_split ),
% 1.71/0.99      inference(splitting,
% 1.71/0.99                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 1.71/0.99                [c_1455]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_1995,plain,
% 1.71/0.99      ( k1_tops_1(sK0,X0_43) != X0_43
% 1.71/0.99      | r1_tarski(X0_43,sK2) != iProver_top
% 1.71/0.99      | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 1.71/0.99      | r2_hidden(sK1,X0_43) != iProver_top
% 1.71/0.99      | sP1_iProver_split != iProver_top ),
% 1.71/0.99      inference(predicate_to_equality,[status(thm)],[c_1470]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_17,negated_conjecture,
% 1.71/0.99      ( m1_subset_1(sK1,u1_struct_0(sK0)) ),
% 1.71/0.99      inference(cnf_transformation,[],[f49]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_24,plain,
% 1.71/0.99      ( m1_subset_1(sK1,u1_struct_0(sK0)) = iProver_top ),
% 1.71/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_16,negated_conjecture,
% 1.71/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.71/0.99      inference(cnf_transformation,[],[f50]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_25,plain,
% 1.71/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 1.71/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_13,negated_conjecture,
% 1.71/0.99      ( m1_connsp_2(sK2,sK0,sK1) | r1_tarski(sK3,sK2) ),
% 1.71/0.99      inference(cnf_transformation,[],[f53]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_10,plain,
% 1.71/0.99      ( ~ m1_connsp_2(X0,X1,X2)
% 1.71/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.71/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.71/0.99      | r2_hidden(X2,k1_tops_1(X1,X0))
% 1.71/0.99      | v2_struct_0(X1)
% 1.71/0.99      | ~ v2_pre_topc(X1)
% 1.71/0.99      | ~ l1_pre_topc(X1) ),
% 1.71/0.99      inference(cnf_transformation,[],[f44]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_20,negated_conjecture,
% 1.71/0.99      ( ~ v2_struct_0(sK0) ),
% 1.71/0.99      inference(cnf_transformation,[],[f46]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_284,plain,
% 1.71/0.99      ( ~ m1_connsp_2(X0,X1,X2)
% 1.71/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.71/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.71/0.99      | r2_hidden(X2,k1_tops_1(X1,X0))
% 1.71/0.99      | ~ v2_pre_topc(X1)
% 1.71/0.99      | ~ l1_pre_topc(X1)
% 1.71/0.99      | sK0 != X1 ),
% 1.71/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_20]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_285,plain,
% 1.71/0.99      ( ~ m1_connsp_2(X0,sK0,X1)
% 1.71/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 1.71/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/0.99      | r2_hidden(X1,k1_tops_1(sK0,X0))
% 1.71/0.99      | ~ v2_pre_topc(sK0)
% 1.71/0.99      | ~ l1_pre_topc(sK0) ),
% 1.71/0.99      inference(unflattening,[status(thm)],[c_284]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_289,plain,
% 1.71/0.99      ( ~ m1_connsp_2(X0,sK0,X1)
% 1.71/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 1.71/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/0.99      | r2_hidden(X1,k1_tops_1(sK0,X0)) ),
% 1.71/0.99      inference(global_propositional_subsumption,
% 1.71/0.99                [status(thm)],
% 1.71/0.99                [c_285,c_19,c_18]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_839,plain,
% 1.71/0.99      ( r1_tarski(sK3,sK2)
% 1.71/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 1.71/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/0.99      | r2_hidden(X0,k1_tops_1(sK0,X1))
% 1.71/0.99      | sK0 != sK0
% 1.71/0.99      | sK2 != X1
% 1.71/0.99      | sK1 != X0 ),
% 1.71/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_289]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_840,plain,
% 1.71/0.99      ( r1_tarski(sK3,sK2)
% 1.71/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/0.99      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
% 1.71/0.99      | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
% 1.71/0.99      inference(unflattening,[status(thm)],[c_839]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_842,plain,
% 1.71/0.99      ( r1_tarski(sK3,sK2) | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
% 1.71/0.99      inference(global_propositional_subsumption,
% 1.71/0.99                [status(thm)],
% 1.71/0.99                [c_840,c_17,c_16]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_844,plain,
% 1.71/0.99      ( r1_tarski(sK3,sK2) = iProver_top
% 1.71/0.99      | r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top ),
% 1.71/0.99      inference(predicate_to_equality,[status(thm)],[c_842]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_12,negated_conjecture,
% 1.71/0.99      ( m1_connsp_2(sK2,sK0,sK1) | r2_hidden(sK1,sK3) ),
% 1.71/0.99      inference(cnf_transformation,[],[f54]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_853,plain,
% 1.71/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 1.71/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/0.99      | r2_hidden(X0,k1_tops_1(sK0,X1))
% 1.71/0.99      | r2_hidden(sK1,sK3)
% 1.71/0.99      | sK0 != sK0
% 1.71/0.99      | sK2 != X1
% 1.71/0.99      | sK1 != X0 ),
% 1.71/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_289]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_854,plain,
% 1.71/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/0.99      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
% 1.71/0.99      | r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 1.71/0.99      | r2_hidden(sK1,sK3) ),
% 1.71/0.99      inference(unflattening,[status(thm)],[c_853]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_856,plain,
% 1.71/0.99      ( r2_hidden(sK1,k1_tops_1(sK0,sK2)) | r2_hidden(sK1,sK3) ),
% 1.71/0.99      inference(global_propositional_subsumption,
% 1.71/0.99                [status(thm)],
% 1.71/0.99                [c_854,c_17,c_16]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_858,plain,
% 1.71/0.99      ( r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top
% 1.71/0.99      | r2_hidden(sK1,sK3) = iProver_top ),
% 1.71/0.99      inference(predicate_to_equality,[status(thm)],[c_856]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_8,plain,
% 1.71/0.99      ( ~ v3_pre_topc(X0,X1)
% 1.71/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 1.71/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.71/0.99      | ~ v2_pre_topc(X3)
% 1.71/0.99      | ~ l1_pre_topc(X3)
% 1.71/0.99      | ~ l1_pre_topc(X1)
% 1.71/0.99      | k1_tops_1(X1,X0) = X0 ),
% 1.71/0.99      inference(cnf_transformation,[],[f42]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_385,plain,
% 1.71/0.99      ( ~ v3_pre_topc(X0,X1)
% 1.71/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.71/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 1.71/0.99      | ~ l1_pre_topc(X1)
% 1.71/0.99      | ~ l1_pre_topc(X3)
% 1.71/0.99      | k1_tops_1(X1,X0) = X0
% 1.71/0.99      | sK0 != X3 ),
% 1.71/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_19]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_386,plain,
% 1.71/0.99      ( ~ v3_pre_topc(X0,X1)
% 1.71/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.71/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/0.99      | ~ l1_pre_topc(X1)
% 1.71/0.99      | ~ l1_pre_topc(sK0)
% 1.71/0.99      | k1_tops_1(X1,X0) = X0 ),
% 1.71/0.99      inference(unflattening,[status(thm)],[c_385]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_390,plain,
% 1.71/0.99      ( ~ l1_pre_topc(X1)
% 1.71/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.71/0.99      | ~ v3_pre_topc(X0,X1)
% 1.71/0.99      | k1_tops_1(X1,X0) = X0 ),
% 1.71/0.99      inference(global_propositional_subsumption,
% 1.71/0.99                [status(thm)],
% 1.71/0.99                [c_386,c_18]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_391,plain,
% 1.71/0.99      ( ~ v3_pre_topc(X0,X1)
% 1.71/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.71/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/0.99      | ~ l1_pre_topc(X1)
% 1.71/0.99      | k1_tops_1(X1,X0) = X0 ),
% 1.71/0.99      inference(renaming,[status(thm)],[c_390]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_425,plain,
% 1.71/0.99      ( ~ v3_pre_topc(X0,X1)
% 1.71/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.71/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/0.99      | k1_tops_1(X1,X0) = X0
% 1.71/0.99      | sK0 != X1 ),
% 1.71/0.99      inference(resolution_lifted,[status(thm)],[c_391,c_18]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_426,plain,
% 1.71/0.99      ( ~ v3_pre_topc(X0,sK0)
% 1.71/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/0.99      | k1_tops_1(sK0,X0) = X0 ),
% 1.71/0.99      inference(unflattening,[status(thm)],[c_425]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_14,negated_conjecture,
% 1.71/0.99      ( m1_connsp_2(sK2,sK0,sK1) | v3_pre_topc(sK3,sK0) ),
% 1.71/0.99      inference(cnf_transformation,[],[f52]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_548,plain,
% 1.71/0.99      ( m1_connsp_2(sK2,sK0,sK1)
% 1.71/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/0.99      | k1_tops_1(sK0,X0) = X0
% 1.71/0.99      | sK3 != X0
% 1.71/0.99      | sK0 != sK0 ),
% 1.71/0.99      inference(resolution_lifted,[status(thm)],[c_426,c_14]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_549,plain,
% 1.71/0.99      ( m1_connsp_2(sK2,sK0,sK1)
% 1.71/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/0.99      | k1_tops_1(sK0,sK3) = sK3 ),
% 1.71/0.99      inference(unflattening,[status(thm)],[c_548]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_15,negated_conjecture,
% 1.71/0.99      ( m1_connsp_2(sK2,sK0,sK1)
% 1.71/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.71/0.99      inference(cnf_transformation,[],[f51]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_553,plain,
% 1.71/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/0.99      | m1_connsp_2(sK2,sK0,sK1)
% 1.71/0.99      | k1_tops_1(sK0,sK3) = sK3 ),
% 1.71/0.99      inference(global_propositional_subsumption,
% 1.71/0.99                [status(thm)],
% 1.71/0.99                [c_549,c_15]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_554,plain,
% 1.71/0.99      ( m1_connsp_2(sK2,sK0,sK1)
% 1.71/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/0.99      | k1_tops_1(sK0,sK3) = sK3 ),
% 1.71/0.99      inference(renaming,[status(thm)],[c_553]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_1454,plain,
% 1.71/0.99      ( m1_connsp_2(sK2,sK0,sK1)
% 1.71/0.99      | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/0.99      | k1_tops_1(sK0,sK3) = sK3 ),
% 1.71/0.99      inference(subtyping,[status(esa)],[c_554]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_1472,plain,
% 1.71/0.99      ( m1_connsp_2(sK2,sK0,sK1)
% 1.71/0.99      | sP0_iProver_split
% 1.71/0.99      | k1_tops_1(sK0,sK3) = sK3 ),
% 1.71/0.99      inference(splitting,
% 1.71/0.99                [splitting(split),new_symbols(definition,[])],
% 1.71/0.99                [c_1454]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_1526,plain,
% 1.71/0.99      ( k1_tops_1(sK0,sK3) = sK3
% 1.71/0.99      | m1_connsp_2(sK2,sK0,sK1) = iProver_top
% 1.71/0.99      | sP0_iProver_split = iProver_top ),
% 1.71/0.99      inference(predicate_to_equality,[status(thm)],[c_1472]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_1469,plain,
% 1.71/0.99      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/0.99      | ~ sP0_iProver_split ),
% 1.71/0.99      inference(splitting,
% 1.71/0.99                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 1.71/0.99                [c_1455]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_2152,plain,
% 1.71/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/0.99      | ~ sP0_iProver_split ),
% 1.71/0.99      inference(instantiation,[status(thm)],[c_1469]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_2153,plain,
% 1.71/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 1.71/0.99      | sP0_iProver_split != iProver_top ),
% 1.71/0.99      inference(predicate_to_equality,[status(thm)],[c_2152]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_3,plain,
% 1.71/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.71/0.99      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.71/0.99      | ~ l1_pre_topc(X1) ),
% 1.71/0.99      inference(cnf_transformation,[],[f38]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_443,plain,
% 1.71/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.71/0.99      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.71/0.99      | sK0 != X1 ),
% 1.71/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_18]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_444,plain,
% 1.71/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/0.99      | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.71/0.99      inference(unflattening,[status(thm)],[c_443]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_1458,plain,
% 1.71/0.99      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/0.99      | m1_subset_1(k1_tops_1(sK0,X0_43),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.71/0.99      inference(subtyping,[status(esa)],[c_444]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_2155,plain,
% 1.71/0.99      ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.71/0.99      inference(instantiation,[status(thm)],[c_1458]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_2156,plain,
% 1.71/0.99      ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 1.71/0.99      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 1.71/0.99      inference(predicate_to_equality,[status(thm)],[c_2155]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_5,plain,
% 1.71/0.99      ( r1_tarski(k1_tops_1(X0,X1),X1)
% 1.71/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 1.71/0.99      | ~ l1_pre_topc(X0) ),
% 1.71/0.99      inference(cnf_transformation,[],[f40]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_455,plain,
% 1.71/0.99      ( r1_tarski(k1_tops_1(X0,X1),X1)
% 1.71/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 1.71/0.99      | sK0 != X0 ),
% 1.71/0.99      inference(resolution_lifted,[status(thm)],[c_5,c_18]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_456,plain,
% 1.71/0.99      ( r1_tarski(k1_tops_1(sK0,X0),X0)
% 1.71/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.71/0.99      inference(unflattening,[status(thm)],[c_455]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_1457,plain,
% 1.71/0.99      ( r1_tarski(k1_tops_1(sK0,X0_43),X0_43)
% 1.71/0.99      | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.71/0.99      inference(subtyping,[status(esa)],[c_456]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_2162,plain,
% 1.71/0.99      ( r1_tarski(k1_tops_1(sK0,sK2),sK2)
% 1.71/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.71/0.99      inference(instantiation,[status(thm)],[c_1457]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_2163,plain,
% 1.71/0.99      ( r1_tarski(k1_tops_1(sK0,sK2),sK2) = iProver_top
% 1.71/0.99      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 1.71/0.99      inference(predicate_to_equality,[status(thm)],[c_2162]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_4,plain,
% 1.71/0.99      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 1.71/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 1.71/0.99      | ~ v2_pre_topc(X0)
% 1.71/0.99      | ~ l1_pre_topc(X0) ),
% 1.71/0.99      inference(cnf_transformation,[],[f39]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_367,plain,
% 1.71/0.99      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 1.71/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 1.71/0.99      | ~ l1_pre_topc(X0)
% 1.71/0.99      | sK0 != X0 ),
% 1.71/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_19]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_368,plain,
% 1.71/0.99      ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
% 1.71/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/0.99      | ~ l1_pre_topc(sK0) ),
% 1.71/0.99      inference(unflattening,[status(thm)],[c_367]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_372,plain,
% 1.71/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/0.99      | v3_pre_topc(k1_tops_1(sK0,X0),sK0) ),
% 1.71/0.99      inference(global_propositional_subsumption,
% 1.71/0.99                [status(thm)],
% 1.71/0.99                [c_368,c_18]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_373,plain,
% 1.71/0.99      ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
% 1.71/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.71/0.99      inference(renaming,[status(thm)],[c_372]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_571,plain,
% 1.71/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/0.99      | k1_tops_1(sK0,X2) != X0
% 1.71/0.99      | k1_tops_1(sK0,X0) = X0
% 1.71/0.99      | sK0 != sK0 ),
% 1.71/0.99      inference(resolution_lifted,[status(thm)],[c_426,c_373]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_572,plain,
% 1.71/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/0.99      | ~ m1_subset_1(k1_tops_1(sK0,X1),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/0.99      | k1_tops_1(sK0,k1_tops_1(sK0,X1)) = k1_tops_1(sK0,X1) ),
% 1.71/0.99      inference(unflattening,[status(thm)],[c_571]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_584,plain,
% 1.71/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/0.99      | k1_tops_1(sK0,k1_tops_1(sK0,X1)) = k1_tops_1(sK0,X1) ),
% 1.71/0.99      inference(forward_subsumption_resolution,
% 1.71/0.99                [status(thm)],
% 1.71/0.99                [c_572,c_444]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_1453,plain,
% 1.71/0.99      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/0.99      | ~ m1_subset_1(X1_43,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/0.99      | k1_tops_1(sK0,k1_tops_1(sK0,X1_43)) = k1_tops_1(sK0,X1_43) ),
% 1.71/0.99      inference(subtyping,[status(esa)],[c_584]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_1473,plain,
% 1.71/0.99      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/0.99      | k1_tops_1(sK0,k1_tops_1(sK0,X0_43)) = k1_tops_1(sK0,X0_43)
% 1.71/0.99      | ~ sP2_iProver_split ),
% 1.71/0.99      inference(splitting,
% 1.71/0.99                [splitting(split),new_symbols(definition,[sP2_iProver_split])],
% 1.71/0.99                [c_1453]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_1474,plain,
% 1.71/0.99      ( sP2_iProver_split | sP0_iProver_split ),
% 1.71/0.99      inference(splitting,
% 1.71/0.99                [splitting(split),new_symbols(definition,[])],
% 1.71/0.99                [c_1453]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_1587,plain,
% 1.71/0.99      ( k1_tops_1(sK0,k1_tops_1(sK0,X0_43)) = k1_tops_1(sK0,X0_43)
% 1.71/0.99      | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.71/0.99      inference(global_propositional_subsumption,
% 1.71/0.99                [status(thm)],
% 1.71/0.99                [c_1473,c_1469,c_1474]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_1588,plain,
% 1.71/0.99      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/0.99      | k1_tops_1(sK0,k1_tops_1(sK0,X0_43)) = k1_tops_1(sK0,X0_43) ),
% 1.71/0.99      inference(renaming,[status(thm)],[c_1587]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_2180,plain,
% 1.71/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/0.99      | k1_tops_1(sK0,k1_tops_1(sK0,sK2)) = k1_tops_1(sK0,sK2) ),
% 1.71/0.99      inference(instantiation,[status(thm)],[c_1588]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_2411,plain,
% 1.71/0.99      ( ~ r1_tarski(sK3,sK2)
% 1.71/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/0.99      | ~ r2_hidden(sK1,sK3)
% 1.71/0.99      | ~ sP1_iProver_split
% 1.71/0.99      | k1_tops_1(sK0,sK3) != sK3 ),
% 1.71/0.99      inference(instantiation,[status(thm)],[c_1470]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_2412,plain,
% 1.71/0.99      ( k1_tops_1(sK0,sK3) != sK3
% 1.71/0.99      | r1_tarski(sK3,sK2) != iProver_top
% 1.71/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 1.71/0.99      | r2_hidden(sK1,sK3) != iProver_top
% 1.71/0.99      | sP1_iProver_split != iProver_top ),
% 1.71/0.99      inference(predicate_to_equality,[status(thm)],[c_2411]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_2414,plain,
% 1.71/0.99      ( ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
% 1.71/0.99      | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/0.99      | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 1.71/0.99      | ~ sP1_iProver_split
% 1.71/0.99      | k1_tops_1(sK0,k1_tops_1(sK0,sK2)) != k1_tops_1(sK0,sK2) ),
% 1.71/0.99      inference(instantiation,[status(thm)],[c_1470]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_2415,plain,
% 1.71/0.99      ( k1_tops_1(sK0,k1_tops_1(sK0,sK2)) != k1_tops_1(sK0,sK2)
% 1.71/0.99      | r1_tarski(k1_tops_1(sK0,sK2),sK2) != iProver_top
% 1.71/0.99      | m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 1.71/0.99      | r2_hidden(sK1,k1_tops_1(sK0,sK2)) != iProver_top
% 1.71/0.99      | sP1_iProver_split != iProver_top ),
% 1.71/0.99      inference(predicate_to_equality,[status(thm)],[c_2414]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_1464,negated_conjecture,
% 1.71/0.99      ( m1_connsp_2(sK2,sK0,sK1)
% 1.71/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.71/0.99      inference(subtyping,[status(esa)],[c_15]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_1985,plain,
% 1.71/0.99      ( m1_connsp_2(sK2,sK0,sK1) = iProver_top
% 1.71/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 1.71/0.99      inference(predicate_to_equality,[status(thm)],[c_1464]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_2,plain,
% 1.71/0.99      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 1.71/0.99      inference(cnf_transformation,[],[f36]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_1467,plain,
% 1.71/0.99      ( r1_tarski(X0_43,X1_43)
% 1.71/0.99      | ~ m1_subset_1(X0_43,k1_zfmisc_1(X1_43)) ),
% 1.71/0.99      inference(subtyping,[status(esa)],[c_2]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_1982,plain,
% 1.71/0.99      ( r1_tarski(X0_43,X1_43) = iProver_top
% 1.71/0.99      | m1_subset_1(X0_43,k1_zfmisc_1(X1_43)) != iProver_top ),
% 1.71/0.99      inference(predicate_to_equality,[status(thm)],[c_1467]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_2440,plain,
% 1.71/0.99      ( m1_connsp_2(sK2,sK0,sK1) = iProver_top
% 1.71/0.99      | r1_tarski(sK3,u1_struct_0(sK0)) = iProver_top ),
% 1.71/0.99      inference(superposition,[status(thm)],[c_1985,c_1982]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_825,plain,
% 1.71/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 1.71/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/0.99      | r2_hidden(X0,k1_tops_1(sK0,X1))
% 1.71/0.99      | sK0 != sK0
% 1.71/0.99      | sK2 != X1
% 1.71/0.99      | sK1 != X0 ),
% 1.71/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_289]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_826,plain,
% 1.71/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/0.99      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
% 1.71/0.99      | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
% 1.71/0.99      inference(unflattening,[status(thm)],[c_825]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_828,plain,
% 1.71/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/0.99      | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
% 1.71/0.99      inference(global_propositional_subsumption,
% 1.71/0.99                [status(thm)],
% 1.71/0.99                [c_826,c_17,c_16]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_830,plain,
% 1.71/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 1.71/0.99      | r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top ),
% 1.71/0.99      inference(predicate_to_equality,[status(thm)],[c_828]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_591,plain,
% 1.71/0.99      ( ~ m1_connsp_2(sK2,sK0,sK1)
% 1.71/0.99      | ~ r1_tarski(X0,sK2)
% 1.71/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/0.99      | ~ r2_hidden(sK1,X0)
% 1.71/0.99      | k1_tops_1(sK0,X1) != X0
% 1.71/0.99      | sK0 != sK0 ),
% 1.71/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_373]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_592,plain,
% 1.71/0.99      ( ~ m1_connsp_2(sK2,sK0,sK1)
% 1.71/0.99      | ~ r1_tarski(k1_tops_1(sK0,X0),sK2)
% 1.71/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/0.99      | ~ m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/0.99      | ~ r2_hidden(sK1,k1_tops_1(sK0,X0)) ),
% 1.71/0.99      inference(unflattening,[status(thm)],[c_591]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_596,plain,
% 1.71/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/0.99      | ~ r1_tarski(k1_tops_1(sK0,X0),sK2)
% 1.71/0.99      | ~ m1_connsp_2(sK2,sK0,sK1)
% 1.71/0.99      | ~ r2_hidden(sK1,k1_tops_1(sK0,X0)) ),
% 1.71/0.99      inference(global_propositional_subsumption,
% 1.71/0.99                [status(thm)],
% 1.71/0.99                [c_592,c_444]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_597,plain,
% 1.71/0.99      ( ~ m1_connsp_2(sK2,sK0,sK1)
% 1.71/0.99      | ~ r1_tarski(k1_tops_1(sK0,X0),sK2)
% 1.71/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/0.99      | ~ r2_hidden(sK1,k1_tops_1(sK0,X0)) ),
% 1.71/0.99      inference(renaming,[status(thm)],[c_596]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_1452,plain,
% 1.71/0.99      ( ~ m1_connsp_2(sK2,sK0,sK1)
% 1.71/0.99      | ~ r1_tarski(k1_tops_1(sK0,X0_43),sK2)
% 1.71/0.99      | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/0.99      | ~ r2_hidden(sK1,k1_tops_1(sK0,X0_43)) ),
% 1.71/0.99      inference(subtyping,[status(esa)],[c_597]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_2270,plain,
% 1.71/0.99      ( ~ m1_connsp_2(sK2,sK0,sK1)
% 1.71/0.99      | ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
% 1.71/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/0.99      | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
% 1.71/0.99      inference(instantiation,[status(thm)],[c_1452]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_2271,plain,
% 1.71/0.99      ( m1_connsp_2(sK2,sK0,sK1) != iProver_top
% 1.71/0.99      | r1_tarski(k1_tops_1(sK0,sK2),sK2) != iProver_top
% 1.71/0.99      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 1.71/0.99      | r2_hidden(sK1,k1_tops_1(sK0,sK2)) != iProver_top ),
% 1.71/0.99      inference(predicate_to_equality,[status(thm)],[c_2270]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_2370,plain,
% 1.71/0.99      ( r1_tarski(sK3,u1_struct_0(sK0))
% 1.71/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.71/0.99      inference(instantiation,[status(thm)],[c_1467]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_2371,plain,
% 1.71/0.99      ( r1_tarski(sK3,u1_struct_0(sK0)) = iProver_top
% 1.71/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 1.71/0.99      inference(predicate_to_equality,[status(thm)],[c_2370]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_2519,plain,
% 1.71/0.99      ( r1_tarski(sK3,u1_struct_0(sK0)) = iProver_top ),
% 1.71/0.99      inference(global_propositional_subsumption,
% 1.71/0.99                [status(thm)],
% 1.71/0.99                [c_2440,c_25,c_830,c_2163,c_2271,c_2371]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_1468,plain,
% 1.71/0.99      ( ~ r1_tarski(X0_43,X1_43)
% 1.71/0.99      | m1_subset_1(X0_43,k1_zfmisc_1(X1_43)) ),
% 1.71/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_2611,plain,
% 1.71/0.99      ( ~ r1_tarski(sK3,u1_struct_0(sK0))
% 1.71/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.71/0.99      inference(instantiation,[status(thm)],[c_1468]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_2612,plain,
% 1.71/0.99      ( r1_tarski(sK3,u1_struct_0(sK0)) != iProver_top
% 1.71/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 1.71/0.99      inference(predicate_to_equality,[status(thm)],[c_2611]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_1463,negated_conjecture,
% 1.71/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.71/0.99      inference(subtyping,[status(esa)],[c_16]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_1986,plain,
% 1.71/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 1.71/0.99      inference(predicate_to_equality,[status(thm)],[c_1463]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_1460,plain,
% 1.71/0.99      ( ~ m1_connsp_2(X0_43,sK0,X1_43)
% 1.71/0.99      | ~ m1_subset_1(X1_43,u1_struct_0(sK0))
% 1.71/0.99      | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/0.99      | r2_hidden(X1_43,k1_tops_1(sK0,X0_43)) ),
% 1.71/0.99      inference(subtyping,[status(esa)],[c_289]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_1989,plain,
% 1.71/0.99      ( m1_connsp_2(X0_43,sK0,X1_43) != iProver_top
% 1.71/0.99      | m1_subset_1(X1_43,u1_struct_0(sK0)) != iProver_top
% 1.71/0.99      | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 1.71/0.99      | r2_hidden(X1_43,k1_tops_1(sK0,X0_43)) = iProver_top ),
% 1.71/0.99      inference(predicate_to_equality,[status(thm)],[c_1460]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_2705,plain,
% 1.71/0.99      ( m1_connsp_2(sK2,sK0,X0_43) != iProver_top
% 1.71/0.99      | m1_subset_1(X0_43,u1_struct_0(sK0)) != iProver_top
% 1.71/0.99      | r2_hidden(X0_43,k1_tops_1(sK0,sK2)) = iProver_top ),
% 1.71/0.99      inference(superposition,[status(thm)],[c_1986,c_1989]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_2742,plain,
% 1.71/0.99      ( m1_connsp_2(sK2,sK0,sK1) != iProver_top
% 1.71/0.99      | m1_subset_1(sK1,u1_struct_0(sK0)) != iProver_top
% 1.71/0.99      | r2_hidden(sK1,k1_tops_1(sK0,sK2)) = iProver_top ),
% 1.71/0.99      inference(instantiation,[status(thm)],[c_2705]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_2967,plain,
% 1.71/0.99      ( sP1_iProver_split != iProver_top ),
% 1.71/0.99      inference(global_propositional_subsumption,
% 1.71/0.99                [status(thm)],
% 1.71/0.99                [c_1995,c_24,c_16,c_25,c_830,c_844,c_858,c_1526,c_2153,
% 1.71/0.99                 c_2156,c_2163,c_2180,c_2271,c_2371,c_2412,c_2415,c_2440,
% 1.71/0.99                 c_2612,c_2742]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_2969,plain,
% 1.71/0.99      ( ~ sP1_iProver_split ),
% 1.71/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_2967]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_9,plain,
% 1.71/0.99      ( m1_connsp_2(X0,X1,X2)
% 1.71/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.71/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.71/0.99      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 1.71/0.99      | v2_struct_0(X1)
% 1.71/0.99      | ~ v2_pre_topc(X1)
% 1.71/0.99      | ~ l1_pre_topc(X1) ),
% 1.71/0.99      inference(cnf_transformation,[],[f45]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_308,plain,
% 1.71/0.99      ( m1_connsp_2(X0,X1,X2)
% 1.71/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.71/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.71/0.99      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 1.71/0.99      | ~ v2_pre_topc(X1)
% 1.71/0.99      | ~ l1_pre_topc(X1)
% 1.71/0.99      | sK0 != X1 ),
% 1.71/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_20]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_309,plain,
% 1.71/0.99      ( m1_connsp_2(X0,sK0,X1)
% 1.71/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 1.71/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/0.99      | ~ r2_hidden(X1,k1_tops_1(sK0,X0))
% 1.71/0.99      | ~ v2_pre_topc(sK0)
% 1.71/0.99      | ~ l1_pre_topc(sK0) ),
% 1.71/0.99      inference(unflattening,[status(thm)],[c_308]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_313,plain,
% 1.71/0.99      ( m1_connsp_2(X0,sK0,X1)
% 1.71/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 1.71/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/0.99      | ~ r2_hidden(X1,k1_tops_1(sK0,X0)) ),
% 1.71/0.99      inference(global_propositional_subsumption,
% 1.71/0.99                [status(thm)],
% 1.71/0.99                [c_309,c_19,c_18]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_1459,plain,
% 1.71/0.99      ( m1_connsp_2(X0_43,sK0,X1_43)
% 1.71/0.99      | ~ m1_subset_1(X1_43,u1_struct_0(sK0))
% 1.71/0.99      | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/0.99      | ~ r2_hidden(X1_43,k1_tops_1(sK0,X0_43)) ),
% 1.71/0.99      inference(subtyping,[status(esa)],[c_313]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_1990,plain,
% 1.71/0.99      ( m1_connsp_2(X0_43,sK0,X1_43) = iProver_top
% 1.71/0.99      | m1_subset_1(X1_43,u1_struct_0(sK0)) != iProver_top
% 1.71/0.99      | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 1.71/0.99      | r2_hidden(X1_43,k1_tops_1(sK0,X0_43)) != iProver_top ),
% 1.71/0.99      inference(predicate_to_equality,[status(thm)],[c_1459]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_2838,plain,
% 1.71/0.99      ( m1_connsp_2(sK2,sK0,X0_43) = iProver_top
% 1.71/0.99      | m1_subset_1(X0_43,u1_struct_0(sK0)) != iProver_top
% 1.71/0.99      | r2_hidden(X0_43,k1_tops_1(sK0,sK2)) != iProver_top ),
% 1.71/0.99      inference(superposition,[status(thm)],[c_1986,c_1990]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_2874,plain,
% 1.71/0.99      ( m1_connsp_2(sK2,sK0,X0_43)
% 1.71/0.99      | ~ m1_subset_1(X0_43,u1_struct_0(sK0))
% 1.71/0.99      | ~ r2_hidden(X0_43,k1_tops_1(sK0,sK2)) ),
% 1.71/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_2838]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_2876,plain,
% 1.71/0.99      ( m1_connsp_2(sK2,sK0,sK1)
% 1.71/0.99      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
% 1.71/0.99      | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
% 1.71/0.99      inference(instantiation,[status(thm)],[c_2874]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_6,plain,
% 1.71/0.99      ( ~ r1_tarski(X0,X1)
% 1.71/0.99      | r1_tarski(k1_tops_1(X2,X0),k1_tops_1(X2,X1))
% 1.71/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 1.71/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.71/0.99      | ~ l1_pre_topc(X2) ),
% 1.71/0.99      inference(cnf_transformation,[],[f41]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_485,plain,
% 1.71/0.99      ( ~ r1_tarski(X0,X1)
% 1.71/0.99      | r1_tarski(k1_tops_1(X2,X0),k1_tops_1(X2,X1))
% 1.71/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 1.71/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.71/0.99      | sK0 != X2 ),
% 1.71/0.99      inference(resolution_lifted,[status(thm)],[c_6,c_18]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_486,plain,
% 1.71/0.99      ( ~ r1_tarski(X0,X1)
% 1.71/0.99      | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1))
% 1.71/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.71/0.99      inference(unflattening,[status(thm)],[c_485]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_1456,plain,
% 1.71/0.99      ( ~ r1_tarski(X0_43,X1_43)
% 1.71/0.99      | r1_tarski(k1_tops_1(sK0,X0_43),k1_tops_1(sK0,X1_43))
% 1.71/0.99      | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/0.99      | ~ m1_subset_1(X1_43,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.71/0.99      inference(subtyping,[status(esa)],[c_486]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_2346,plain,
% 1.71/0.99      ( r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,X0_43))
% 1.71/0.99      | ~ r1_tarski(sK3,X0_43)
% 1.71/0.99      | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.71/0.99      inference(instantiation,[status(thm)],[c_1456]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_2657,plain,
% 1.71/0.99      ( r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2))
% 1.71/0.99      | ~ r1_tarski(sK3,sK2)
% 1.71/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.71/0.99      inference(instantiation,[status(thm)],[c_2346]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_2521,plain,
% 1.71/0.99      ( r1_tarski(sK3,u1_struct_0(sK0)) ),
% 1.71/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_2519]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_1478,plain,
% 1.71/0.99      ( ~ r2_hidden(X0_43,X1_43)
% 1.71/0.99      | r2_hidden(X2_43,X3_43)
% 1.71/0.99      | X2_43 != X0_43
% 1.71/0.99      | X3_43 != X1_43 ),
% 1.71/0.99      theory(equality) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_2200,plain,
% 1.71/0.99      ( r2_hidden(X0_43,X1_43)
% 1.71/0.99      | ~ r2_hidden(sK1,sK3)
% 1.71/0.99      | X1_43 != sK3
% 1.71/0.99      | X0_43 != sK1 ),
% 1.71/0.99      inference(instantiation,[status(thm)],[c_1478]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_2378,plain,
% 1.71/0.99      ( r2_hidden(X0_43,k1_tops_1(sK0,sK3))
% 1.71/0.99      | ~ r2_hidden(sK1,sK3)
% 1.71/0.99      | X0_43 != sK1
% 1.71/0.99      | k1_tops_1(sK0,sK3) != sK3 ),
% 1.71/0.99      inference(instantiation,[status(thm)],[c_2200]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_2380,plain,
% 1.71/0.99      ( r2_hidden(sK1,k1_tops_1(sK0,sK3))
% 1.71/0.99      | ~ r2_hidden(sK1,sK3)
% 1.71/0.99      | k1_tops_1(sK0,sK3) != sK3
% 1.71/0.99      | sK1 != sK1 ),
% 1.71/0.99      inference(instantiation,[status(thm)],[c_2378]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_1471,plain,
% 1.71/0.99      ( ~ m1_connsp_2(sK2,sK0,sK1)
% 1.71/0.99      | sP1_iProver_split
% 1.71/0.99      | sP0_iProver_split ),
% 1.71/0.99      inference(splitting,
% 1.71/0.99                [splitting(split),new_symbols(definition,[])],
% 1.71/0.99                [c_1455]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_1519,plain,
% 1.71/0.99      ( m1_connsp_2(sK2,sK0,sK1) != iProver_top
% 1.71/0.99      | sP1_iProver_split = iProver_top
% 1.71/0.99      | sP0_iProver_split = iProver_top ),
% 1.71/0.99      inference(predicate_to_equality,[status(thm)],[c_1471]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_1476,plain,( X0_43 = X0_43 ),theory(equality) ).
% 1.71/0.99  
% 1.71/0.99  cnf(c_1491,plain,
% 1.71/0.99      ( sK1 = sK1 ),
% 1.71/0.99      inference(instantiation,[status(thm)],[c_1476]) ).
% 1.71/0.99  
% 1.71/0.99  cnf(contradiction,plain,
% 1.71/0.99      ( $false ),
% 1.71/0.99      inference(minisat,
% 1.71/0.99                [status(thm)],
% 1.71/0.99                [c_3235,c_2969,c_2967,c_2876,c_2657,c_2611,c_2521,c_2380,
% 1.71/0.99                 c_2153,c_2152,c_1526,c_1519,c_1471,c_1491,c_12,c_13,
% 1.71/0.99                 c_25,c_16,c_17]) ).
% 1.71/0.99  
% 1.71/0.99  
% 1.71/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 1.71/0.99  
% 1.71/0.99  ------                               Statistics
% 1.71/0.99  
% 1.71/0.99  ------ General
% 1.71/0.99  
% 1.71/0.99  abstr_ref_over_cycles:                  0
% 1.71/0.99  abstr_ref_under_cycles:                 0
% 1.71/0.99  gc_basic_clause_elim:                   0
% 1.71/0.99  forced_gc_time:                         0
% 1.71/0.99  parsing_time:                           0.009
% 1.71/0.99  unif_index_cands_time:                  0.
% 1.71/0.99  unif_index_add_time:                    0.
% 1.71/0.99  orderings_time:                         0.
% 1.71/0.99  out_proof_time:                         0.011
% 1.71/0.99  total_time:                             0.112
% 1.71/0.99  num_of_symbols:                         48
% 1.71/0.99  num_of_terms:                           1678
% 1.71/0.99  
% 1.71/0.99  ------ Preprocessing
% 1.71/0.99  
% 1.71/0.99  num_of_splits:                          5
% 1.71/0.99  num_of_split_atoms:                     3
% 1.71/0.99  num_of_reused_defs:                     2
% 1.71/0.99  num_eq_ax_congr_red:                    5
% 1.71/0.99  num_of_sem_filtered_clauses:            2
% 1.71/0.99  num_of_subtypes:                        2
% 1.71/0.99  monotx_restored_types:                  0
% 1.71/0.99  sat_num_of_epr_types:                   0
% 1.71/0.99  sat_num_of_non_cyclic_types:            0
% 1.71/0.99  sat_guarded_non_collapsed_types:        0
% 1.71/0.99  num_pure_diseq_elim:                    0
% 1.71/0.99  simp_replaced_by:                       0
% 1.71/0.99  res_preprocessed:                       94
% 1.71/0.99  prep_upred:                             0
% 1.71/0.99  prep_unflattend:                        38
% 1.71/0.99  smt_new_axioms:                         0
% 1.71/0.99  pred_elim_cands:                        4
% 1.71/0.99  pred_elim:                              4
% 1.71/0.99  pred_elim_cl:                           4
% 1.71/0.99  pred_elim_cycles:                       6
% 1.71/0.99  merged_defs:                            8
% 1.71/0.99  merged_defs_ncl:                        0
% 1.71/0.99  bin_hyper_res:                          9
% 1.71/0.99  prep_cycles:                            4
% 1.71/0.99  pred_elim_time:                         0.019
% 1.71/0.99  splitting_time:                         0.
% 1.71/0.99  sem_filter_time:                        0.
% 1.71/0.99  monotx_time:                            0.
% 1.71/0.99  subtype_inf_time:                       0.
% 1.71/0.99  
% 1.71/0.99  ------ Problem properties
% 1.71/0.99  
% 1.71/0.99  clauses:                                22
% 1.71/0.99  conjectures:                            5
% 1.71/0.99  epr:                                    5
% 1.71/0.99  horn:                                   16
% 1.71/0.99  ground:                                 8
% 1.71/0.99  unary:                                  2
% 1.71/0.99  binary:                                 11
% 1.71/0.99  lits:                                   57
% 1.71/0.99  lits_eq:                                3
% 1.71/0.99  fd_pure:                                0
% 1.71/0.99  fd_pseudo:                              0
% 1.71/0.99  fd_cond:                                0
% 1.71/0.99  fd_pseudo_cond:                         0
% 1.71/0.99  ac_symbols:                             0
% 1.71/0.99  
% 1.71/0.99  ------ Propositional Solver
% 1.71/0.99  
% 1.71/0.99  prop_solver_calls:                      25
% 1.71/0.99  prop_fast_solver_calls:                 893
% 1.71/0.99  smt_solver_calls:                       0
% 1.71/0.99  smt_fast_solver_calls:                  0
% 1.71/0.99  prop_num_of_clauses:                    884
% 1.71/0.99  prop_preprocess_simplified:             3373
% 1.71/0.99  prop_fo_subsumed:                       48
% 1.71/0.99  prop_solver_time:                       0.
% 1.71/0.99  smt_solver_time:                        0.
% 1.71/0.99  smt_fast_solver_time:                   0.
% 1.71/0.99  prop_fast_solver_time:                  0.
% 1.71/0.99  prop_unsat_core_time:                   0.
% 1.71/0.99  
% 1.71/0.99  ------ QBF
% 1.71/0.99  
% 1.71/0.99  qbf_q_res:                              0
% 1.71/0.99  qbf_num_tautologies:                    0
% 1.71/0.99  qbf_prep_cycles:                        0
% 1.71/0.99  
% 1.71/0.99  ------ BMC1
% 1.71/0.99  
% 1.71/0.99  bmc1_current_bound:                     -1
% 1.71/0.99  bmc1_last_solved_bound:                 -1
% 1.71/0.99  bmc1_unsat_core_size:                   -1
% 1.71/0.99  bmc1_unsat_core_parents_size:           -1
% 1.71/0.99  bmc1_merge_next_fun:                    0
% 1.71/0.99  bmc1_unsat_core_clauses_time:           0.
% 1.71/0.99  
% 1.71/0.99  ------ Instantiation
% 1.71/0.99  
% 1.71/0.99  inst_num_of_clauses:                    209
% 1.71/0.99  inst_num_in_passive:                    87
% 1.71/0.99  inst_num_in_active:                     120
% 1.71/0.99  inst_num_in_unprocessed:                1
% 1.71/0.99  inst_num_of_loops:                      130
% 1.71/0.99  inst_num_of_learning_restarts:          0
% 1.71/0.99  inst_num_moves_active_passive:          6
% 1.71/0.99  inst_lit_activity:                      0
% 1.71/0.99  inst_lit_activity_moves:                0
% 1.71/0.99  inst_num_tautologies:                   0
% 1.71/0.99  inst_num_prop_implied:                  0
% 1.71/0.99  inst_num_existing_simplified:           0
% 1.71/0.99  inst_num_eq_res_simplified:             0
% 1.71/0.99  inst_num_child_elim:                    0
% 1.71/0.99  inst_num_of_dismatching_blockings:      2
% 1.71/0.99  inst_num_of_non_proper_insts:           136
% 1.71/0.99  inst_num_of_duplicates:                 0
% 1.71/0.99  inst_inst_num_from_inst_to_res:         0
% 1.71/0.99  inst_dismatching_checking_time:         0.
% 1.71/0.99  
% 1.71/0.99  ------ Resolution
% 1.71/0.99  
% 1.71/0.99  res_num_of_clauses:                     0
% 1.71/0.99  res_num_in_passive:                     0
% 1.71/0.99  res_num_in_active:                      0
% 1.71/0.99  res_num_of_loops:                       98
% 1.71/0.99  res_forward_subset_subsumed:            4
% 1.71/0.99  res_backward_subset_subsumed:           0
% 1.71/0.99  res_forward_subsumed:                   0
% 1.71/0.99  res_backward_subsumed:                  0
% 1.71/0.99  res_forward_subsumption_resolution:     1
% 1.71/0.99  res_backward_subsumption_resolution:    0
% 1.71/0.99  res_clause_to_clause_subsumption:       269
% 1.71/0.99  res_orphan_elimination:                 0
% 1.71/0.99  res_tautology_del:                      29
% 1.71/0.99  res_num_eq_res_simplified:              0
% 1.71/0.99  res_num_sel_changes:                    0
% 1.71/0.99  res_moves_from_active_to_pass:          0
% 1.71/0.99  
% 1.71/0.99  ------ Superposition
% 1.71/0.99  
% 1.71/0.99  sup_time_total:                         0.
% 1.71/0.99  sup_time_generating:                    0.
% 1.71/0.99  sup_time_sim_full:                      0.
% 1.71/0.99  sup_time_sim_immed:                     0.
% 1.71/0.99  
% 1.71/0.99  sup_num_of_clauses:                     43
% 1.71/0.99  sup_num_in_active:                      24
% 1.71/0.99  sup_num_in_passive:                     19
% 1.71/0.99  sup_num_of_loops:                       24
% 1.71/0.99  sup_fw_superposition:                   21
% 1.71/0.99  sup_bw_superposition:                   4
% 1.71/0.99  sup_immediate_simplified:               0
% 1.71/0.99  sup_given_eliminated:                   0
% 1.71/0.99  comparisons_done:                       0
% 1.71/0.99  comparisons_avoided:                    0
% 1.71/0.99  
% 1.71/0.99  ------ Simplifications
% 1.71/0.99  
% 1.71/0.99  
% 1.71/0.99  sim_fw_subset_subsumed:                 0
% 1.71/0.99  sim_bw_subset_subsumed:                 1
% 1.71/0.99  sim_fw_subsumed:                        0
% 1.71/0.99  sim_bw_subsumed:                        0
% 1.71/0.99  sim_fw_subsumption_res:                 0
% 1.71/0.99  sim_bw_subsumption_res:                 0
% 1.71/0.99  sim_tautology_del:                      1
% 1.71/0.99  sim_eq_tautology_del:                   0
% 1.71/0.99  sim_eq_res_simp:                        0
% 1.71/0.99  sim_fw_demodulated:                     0
% 1.71/0.99  sim_bw_demodulated:                     0
% 1.71/0.99  sim_light_normalised:                   0
% 1.71/0.99  sim_joinable_taut:                      0
% 1.71/0.99  sim_joinable_simp:                      0
% 1.71/0.99  sim_ac_normalised:                      0
% 1.71/0.99  sim_smt_subsumption:                    0
% 1.71/0.99  
%------------------------------------------------------------------------------
