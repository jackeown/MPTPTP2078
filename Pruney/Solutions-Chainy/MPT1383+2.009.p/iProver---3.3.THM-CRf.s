%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:18:22 EST 2020

% Result     : Theorem 2.00s
% Output     : CNFRefutation 2.00s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 868 expanded)
%              Number of clauses        :   93 ( 177 expanded)
%              Number of leaves         :   15 ( 250 expanded)
%              Depth                    :   19
%              Number of atoms          :  744 (9283 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   30 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f7])).

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
    inference(nnf_transformation,[],[f22])).

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
               => ( m1_connsp_2(X2,X0,X1)
                <=> ? [X3] :
                      ( r2_hidden(X1,X3)
                      & r1_tarski(X3,X2)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f27,plain,(
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

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ? [X4] :
          ( r2_hidden(X1,X4)
          & r1_tarski(X4,X2)
          & v3_pre_topc(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r2_hidden(X1,sK4)
        & r1_tarski(sK4,X2)
        & v3_pre_topc(sK4,X0)
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
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
              | ~ r1_tarski(X3,sK3)
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_connsp_2(sK3,X0,X1) )
        & ( ? [X4] :
              ( r2_hidden(X1,X4)
              & r1_tarski(X4,sK3)
              & v3_pre_topc(X4,X0)
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
          | m1_connsp_2(sK3,X0,X1) )
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
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
                  ( ~ r2_hidden(sK2,X3)
                  | ~ r1_tarski(X3,X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_connsp_2(X2,X0,sK2) )
            & ( ? [X4] :
                  ( r2_hidden(sK2,X4)
                  & r1_tarski(X4,X2)
                  & v3_pre_topc(X4,X0)
                  & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | m1_connsp_2(X2,X0,sK2) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
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
                    | ~ v3_pre_topc(X3,sK1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
                | ~ m1_connsp_2(X2,sK1,X1) )
              & ( ? [X4] :
                    ( r2_hidden(X1,X4)
                    & r1_tarski(X4,X2)
                    & v3_pre_topc(X4,sK1)
                    & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1))) )
                | m1_connsp_2(X2,sK1,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) )
          & m1_subset_1(X1,u1_struct_0(sK1)) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ( ! [X3] :
          ( ~ r2_hidden(sK2,X3)
          | ~ r1_tarski(X3,sK3)
          | ~ v3_pre_topc(X3,sK1)
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
      | ~ m1_connsp_2(sK3,sK1,sK2) )
    & ( ( r2_hidden(sK2,sK4)
        & r1_tarski(sK4,sK3)
        & v3_pre_topc(sK4,sK1)
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) )
      | m1_connsp_2(sK3,sK1,sK2) )
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f35,f39,f38,f37,f36])).

fof(f54,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f55,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f56,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f9,axiom,(
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

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ m1_connsp_2(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

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

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

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

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f63,plain,(
    ! [X3] :
      ( ~ r2_hidden(sK2,X3)
      | ~ r1_tarski(X3,sK3)
      | ~ v3_pre_topc(X3,sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_connsp_2(sK3,sK1,sK2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                 => r2_hidden(X3,X2) ) )
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f13])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,X0) )
     => ( ~ r2_hidden(sK0(X0,X1,X2),X2)
        & r2_hidden(sK0(X0,X1,X2),X1)
        & m1_subset_1(sK0(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ( ~ r2_hidden(sK0(X0,X1,X2),X2)
            & r2_hidden(sK0(X0,X1,X2),X1)
            & m1_subset_1(sK0(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f29])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r2_hidden(sK0(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | m1_subset_1(sK0(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v3_pre_topc(X1,X0) )
               => r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f60,plain,
    ( v3_pre_topc(sK4,sK1)
    | m1_connsp_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f59,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_connsp_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f40])).

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

fof(f62,plain,
    ( r2_hidden(sK2,sK4)
    | m1_connsp_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f57,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f40])).

fof(f61,plain,
    ( r1_tarski(sK4,sK3)
    | m1_connsp_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f58,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_9,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_22,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_358,plain,
    ( m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X1,k1_tops_1(sK1,X0))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[status(thm)],[c_9,c_22])).

cnf(c_21,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_20,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_362,plain,
    ( m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X1,k1_tops_1(sK1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_358,c_21,c_20])).

cnf(c_1265,plain,
    ( m1_connsp_2(X0_44,sK1,X1_44)
    | ~ m1_subset_1(X1_44,u1_struct_0(sK1))
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X1_44,k1_tops_1(sK1,X0_44)) ),
    inference(subtyping,[status(esa)],[c_362])).

cnf(c_1392,plain,
    ( m1_connsp_2(sK3,sK1,X0_44)
    | ~ m1_subset_1(X0_44,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X0_44,k1_tops_1(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_1265])).

cnf(c_3262,plain,
    ( m1_connsp_2(sK3,sK1,sK0(u1_struct_0(sK1),k1_tops_1(sK1,k1_tops_1(sK1,sK3)),sK3))
    | ~ m1_subset_1(sK0(u1_struct_0(sK1),k1_tops_1(sK1,k1_tops_1(sK1,sK3)),sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK0(u1_struct_0(sK1),k1_tops_1(sK1,k1_tops_1(sK1,sK3)),sK3),k1_tops_1(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_1392])).

cnf(c_12,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_11,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_123,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X0,X1,X2)
    | r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12,c_11])).

cnf(c_124,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_123])).

cnf(c_318,plain,
    ( ~ m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | r2_hidden(X1,X0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[status(thm)],[c_124,c_22])).

cnf(c_322,plain,
    ( ~ m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | r2_hidden(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_318,c_21,c_20])).

cnf(c_1267,plain,
    ( ~ m1_connsp_2(X0_44,sK1,X1_44)
    | ~ m1_subset_1(X1_44,u1_struct_0(sK1))
    | r2_hidden(X1_44,X0_44) ),
    inference(subtyping,[status(esa)],[c_322])).

cnf(c_1714,plain,
    ( ~ m1_connsp_2(sK3,sK1,X0_44)
    | ~ m1_subset_1(X0_44,u1_struct_0(sK1))
    | r2_hidden(X0_44,sK3) ),
    inference(instantiation,[status(thm)],[c_1267])).

cnf(c_2510,plain,
    ( ~ m1_connsp_2(sK3,sK1,sK0(u1_struct_0(sK1),k1_tops_1(sK1,k1_tops_1(sK1,sK3)),sK3))
    | ~ m1_subset_1(sK0(u1_struct_0(sK1),k1_tops_1(sK1,k1_tops_1(sK1,sK3)),sK3),u1_struct_0(sK1))
    | r2_hidden(sK0(u1_struct_0(sK1),k1_tops_1(sK1,k1_tops_1(sK1,sK3)),sK3),sK3) ),
    inference(instantiation,[status(thm)],[c_1714])).

cnf(c_2363,plain,
    ( ~ m1_connsp_2(k1_tops_1(sK1,sK3),sK1,sK0(u1_struct_0(sK1),k1_tops_1(sK1,k1_tops_1(sK1,sK3)),sK3))
    | ~ m1_subset_1(sK0(u1_struct_0(sK1),k1_tops_1(sK1,k1_tops_1(sK1,sK3)),sK3),u1_struct_0(sK1))
    | r2_hidden(sK0(u1_struct_0(sK1),k1_tops_1(sK1,k1_tops_1(sK1,sK3)),sK3),k1_tops_1(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_1267])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_178,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_4])).

cnf(c_226,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(bin_hyper_res,[status(thm)],[c_0,c_178])).

cnf(c_1269,plain,
    ( ~ r1_tarski(X0_44,X1_44)
    | ~ r2_hidden(X2_44,X0_44)
    | r2_hidden(X2_44,X1_44) ),
    inference(subtyping,[status(esa)],[c_226])).

cnf(c_2329,plain,
    ( ~ r1_tarski(k1_tops_1(sK1,sK3),k1_tops_1(sK1,k1_tops_1(sK1,sK3)))
    | r2_hidden(X0_44,k1_tops_1(sK1,k1_tops_1(sK1,sK3)))
    | ~ r2_hidden(X0_44,k1_tops_1(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_1269])).

cnf(c_2334,plain,
    ( ~ r1_tarski(k1_tops_1(sK1,sK3),k1_tops_1(sK1,k1_tops_1(sK1,sK3)))
    | r2_hidden(sK2,k1_tops_1(sK1,k1_tops_1(sK1,sK3)))
    | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_2329])).

cnf(c_2130,plain,
    ( ~ r1_tarski(sK4,k1_tops_1(sK1,sK3))
    | r2_hidden(X0_44,k1_tops_1(sK1,sK3))
    | ~ r2_hidden(X0_44,sK4) ),
    inference(instantiation,[status(thm)],[c_1269])).

cnf(c_2135,plain,
    ( ~ r1_tarski(sK4,k1_tops_1(sK1,sK3))
    | r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | ~ r2_hidden(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_2130])).

cnf(c_13,negated_conjecture,
    ( ~ m1_connsp_2(sK3,sK1,sK2)
    | ~ v3_pre_topc(X0,sK1)
    | ~ r1_tarski(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK2,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_7,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_398,plain,
    ( v3_pre_topc(k1_tops_1(sK1,X0),sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[status(thm)],[c_7,c_21])).

cnf(c_402,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v3_pre_topc(k1_tops_1(sK1,X0),sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_398,c_20])).

cnf(c_403,plain,
    ( v3_pre_topc(k1_tops_1(sK1,X0),sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(renaming,[status(thm)],[c_402])).

cnf(c_505,plain,
    ( ~ m1_connsp_2(sK3,sK1,sK2)
    | ~ r1_tarski(k1_tops_1(sK1,X0),sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k1_tops_1(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK2,k1_tops_1(sK1,X0)) ),
    inference(resolution,[status(thm)],[c_13,c_403])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_438,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k1_tops_1(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(resolution,[status(thm)],[c_6,c_20])).

cnf(c_509,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(k1_tops_1(sK1,X0),sK3)
    | ~ m1_connsp_2(sK3,sK1,sK2)
    | ~ r2_hidden(sK2,k1_tops_1(sK1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_505,c_438])).

cnf(c_510,plain,
    ( ~ m1_connsp_2(sK3,sK1,sK2)
    | ~ r1_tarski(k1_tops_1(sK1,X0),sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK2,k1_tops_1(sK1,X0)) ),
    inference(renaming,[status(thm)],[c_509])).

cnf(c_1261,plain,
    ( ~ m1_connsp_2(sK3,sK1,sK2)
    | ~ r1_tarski(k1_tops_1(sK1,X0_44),sK3)
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK2,k1_tops_1(sK1,X0_44)) ),
    inference(subtyping,[status(esa)],[c_510])).

cnf(c_1936,plain,
    ( ~ m1_connsp_2(sK3,sK1,sK2)
    | ~ r1_tarski(k1_tops_1(sK1,k1_tops_1(sK1,sK3)),sK3)
    | ~ m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK2,k1_tops_1(sK1,k1_tops_1(sK1,sK3))) ),
    inference(instantiation,[status(thm)],[c_1261])).

cnf(c_1429,plain,
    ( m1_connsp_2(k1_tops_1(sK1,sK3),sK1,X0_44)
    | ~ m1_subset_1(X0_44,u1_struct_0(sK1))
    | ~ m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X0_44,k1_tops_1(sK1,k1_tops_1(sK1,sK3))) ),
    inference(instantiation,[status(thm)],[c_1265])).

cnf(c_1933,plain,
    ( m1_connsp_2(k1_tops_1(sK1,sK3),sK1,sK0(u1_struct_0(sK1),k1_tops_1(sK1,k1_tops_1(sK1,sK3)),sK3))
    | ~ m1_subset_1(sK0(u1_struct_0(sK1),k1_tops_1(sK1,k1_tops_1(sK1,sK3)),sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK0(u1_struct_0(sK1),k1_tops_1(sK1,k1_tops_1(sK1,sK3)),sK3),k1_tops_1(sK1,k1_tops_1(sK1,sK3))) ),
    inference(instantiation,[status(thm)],[c_1429])).

cnf(c_1,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(sK0(X2,X0,X1),X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1279,plain,
    ( r1_tarski(X0_44,X1_44)
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(X2_44))
    | ~ m1_subset_1(X1_44,k1_zfmisc_1(X2_44))
    | ~ r2_hidden(sK0(X2_44,X0_44,X1_44),X1_44) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1588,plain,
    ( r1_tarski(k1_tops_1(sK1,k1_tops_1(sK1,sK3)),X0_44)
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k1_tops_1(sK1,k1_tops_1(sK1,sK3)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK0(u1_struct_0(sK1),k1_tops_1(sK1,k1_tops_1(sK1,sK3)),X0_44),X0_44) ),
    inference(instantiation,[status(thm)],[c_1279])).

cnf(c_1905,plain,
    ( r1_tarski(k1_tops_1(sK1,k1_tops_1(sK1,sK3)),sK3)
    | ~ m1_subset_1(k1_tops_1(sK1,k1_tops_1(sK1,sK3)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK0(u1_struct_0(sK1),k1_tops_1(sK1,k1_tops_1(sK1,sK3)),sK3),sK3) ),
    inference(instantiation,[status(thm)],[c_1588])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | m1_subset_1(sK0(X2,X0,X1),X2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1277,plain,
    ( r1_tarski(X0_44,X1_44)
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(X2_44))
    | ~ m1_subset_1(X1_44,k1_zfmisc_1(X2_44))
    | m1_subset_1(sK0(X2_44,X0_44,X1_44),X2_44) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1590,plain,
    ( r1_tarski(k1_tops_1(sK1,k1_tops_1(sK1,sK3)),X0_44)
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(sK0(u1_struct_0(sK1),k1_tops_1(sK1,k1_tops_1(sK1,sK3)),X0_44),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_tops_1(sK1,k1_tops_1(sK1,sK3)),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_1277])).

cnf(c_1893,plain,
    ( r1_tarski(k1_tops_1(sK1,k1_tops_1(sK1,sK3)),sK3)
    | m1_subset_1(sK0(u1_struct_0(sK1),k1_tops_1(sK1,k1_tops_1(sK1,sK3)),sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_tops_1(sK1,k1_tops_1(sK1,sK3)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_1590])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | r2_hidden(sK0(X2,X0,X1),X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1278,plain,
    ( r1_tarski(X0_44,X1_44)
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(X2_44))
    | ~ m1_subset_1(X1_44,k1_zfmisc_1(X2_44))
    | r2_hidden(sK0(X2_44,X0_44,X1_44),X0_44) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1589,plain,
    ( r1_tarski(k1_tops_1(sK1,k1_tops_1(sK1,sK3)),X0_44)
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k1_tops_1(sK1,k1_tops_1(sK1,sK3)),k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(sK0(u1_struct_0(sK1),k1_tops_1(sK1,k1_tops_1(sK1,sK3)),X0_44),k1_tops_1(sK1,k1_tops_1(sK1,sK3))) ),
    inference(instantiation,[status(thm)],[c_1278])).

cnf(c_1881,plain,
    ( r1_tarski(k1_tops_1(sK1,k1_tops_1(sK1,sK3)),sK3)
    | ~ m1_subset_1(k1_tops_1(sK1,k1_tops_1(sK1,sK3)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(sK0(u1_struct_0(sK1),k1_tops_1(sK1,k1_tops_1(sK1,sK3)),sK3),k1_tops_1(sK1,k1_tops_1(sK1,sK3))) ),
    inference(instantiation,[status(thm)],[c_1589])).

cnf(c_1444,plain,
    ( r1_tarski(k1_tops_1(sK1,sK3),X0_44)
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK0(u1_struct_0(sK1),k1_tops_1(sK1,sK3),X0_44),X0_44) ),
    inference(instantiation,[status(thm)],[c_1279])).

cnf(c_1835,plain,
    ( r1_tarski(k1_tops_1(sK1,sK3),k1_tops_1(sK1,sK3))
    | ~ m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK0(u1_struct_0(sK1),k1_tops_1(sK1,sK3),k1_tops_1(sK1,sK3)),k1_tops_1(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_1444])).

cnf(c_8,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k1_tops_1(X1,X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_418,plain,
    ( ~ v3_pre_topc(X0,sK1)
    | ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k1_tops_1(sK1,X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(resolution,[status(thm)],[c_8,c_20])).

cnf(c_482,plain,
    ( ~ r1_tarski(k1_tops_1(sK1,X0),X1)
    | r1_tarski(k1_tops_1(sK1,X0),k1_tops_1(sK1,X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k1_tops_1(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(resolution,[status(thm)],[c_418,c_403])).

cnf(c_486,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(k1_tops_1(sK1,X0),k1_tops_1(sK1,X1))
    | ~ r1_tarski(k1_tops_1(sK1,X0),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_482,c_438])).

cnf(c_487,plain,
    ( ~ r1_tarski(k1_tops_1(sK1,X0),X1)
    | r1_tarski(k1_tops_1(sK1,X0),k1_tops_1(sK1,X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(renaming,[status(thm)],[c_486])).

cnf(c_1262,plain,
    ( ~ r1_tarski(k1_tops_1(sK1,X0_44),X1_44)
    | r1_tarski(k1_tops_1(sK1,X0_44),k1_tops_1(sK1,X1_44))
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1_44,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_487])).

cnf(c_1397,plain,
    ( ~ r1_tarski(k1_tops_1(sK1,sK3),X0_44)
    | r1_tarski(k1_tops_1(sK1,sK3),k1_tops_1(sK1,X0_44))
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_1262])).

cnf(c_1803,plain,
    ( r1_tarski(k1_tops_1(sK1,sK3),k1_tops_1(sK1,k1_tops_1(sK1,sK3)))
    | ~ r1_tarski(k1_tops_1(sK1,sK3),k1_tops_1(sK1,sK3))
    | ~ m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_1397])).

cnf(c_1445,plain,
    ( r1_tarski(k1_tops_1(sK1,sK3),X0_44)
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(sK0(u1_struct_0(sK1),k1_tops_1(sK1,sK3),X0_44),k1_tops_1(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_1278])).

cnf(c_1640,plain,
    ( r1_tarski(k1_tops_1(sK1,sK3),k1_tops_1(sK1,sK3))
    | ~ m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(sK0(u1_struct_0(sK1),k1_tops_1(sK1,sK3),k1_tops_1(sK1,sK3)),k1_tops_1(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_1445])).

cnf(c_16,negated_conjecture,
    ( m1_connsp_2(sK3,sK1,sK2)
    | v3_pre_topc(sK4,sK1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_458,plain,
    ( m1_connsp_2(sK3,sK1,sK2)
    | ~ r1_tarski(sK4,X0)
    | r1_tarski(sK4,k1_tops_1(sK1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(resolution,[status(thm)],[c_418,c_16])).

cnf(c_17,negated_conjecture,
    ( m1_connsp_2(sK3,sK1,sK2)
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_462,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(sK4,k1_tops_1(sK1,X0))
    | ~ r1_tarski(sK4,X0)
    | m1_connsp_2(sK3,sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_458,c_17])).

cnf(c_463,plain,
    ( m1_connsp_2(sK3,sK1,sK2)
    | ~ r1_tarski(sK4,X0)
    | r1_tarski(sK4,k1_tops_1(sK1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(renaming,[status(thm)],[c_462])).

cnf(c_1263,plain,
    ( m1_connsp_2(sK3,sK1,sK2)
    | ~ r1_tarski(sK4,X0_44)
    | r1_tarski(sK4,k1_tops_1(sK1,X0_44))
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_463])).

cnf(c_1551,plain,
    ( m1_connsp_2(sK3,sK1,sK2)
    | r1_tarski(sK4,k1_tops_1(sK1,sK3))
    | ~ r1_tarski(sK4,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_1263])).

cnf(c_1264,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k1_tops_1(sK1,X0_44),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_438])).

cnf(c_1430,plain,
    ( m1_subset_1(k1_tops_1(sK1,k1_tops_1(sK1,sK3)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_1264])).

cnf(c_1394,plain,
    ( m1_connsp_2(sK3,sK1,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_1392])).

cnf(c_10,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_131,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X0,X1,X2)
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10,c_11])).

cnf(c_132,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_131])).

cnf(c_298,plain,
    ( ~ m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | r2_hidden(X1,k1_tops_1(sK1,X0))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[status(thm)],[c_132,c_22])).

cnf(c_302,plain,
    ( ~ m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | r2_hidden(X1,k1_tops_1(sK1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_298,c_21,c_20])).

cnf(c_1268,plain,
    ( ~ m1_connsp_2(X0_44,sK1,X1_44)
    | ~ m1_subset_1(X1_44,u1_struct_0(sK1))
    | r2_hidden(X1_44,k1_tops_1(sK1,X0_44)) ),
    inference(subtyping,[status(esa)],[c_302])).

cnf(c_1389,plain,
    ( ~ m1_connsp_2(sK3,sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_1268])).

cnf(c_1382,plain,
    ( m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_1264])).

cnf(c_14,negated_conjecture,
    ( m1_connsp_2(sK3,sK1,sK2)
    | r2_hidden(sK2,sK4) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_751,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | r2_hidden(sK2,sK4) ),
    inference(resolution,[status(thm)],[c_14,c_302])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_753,plain,
    ( r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | r2_hidden(sK2,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_751,c_19])).

cnf(c_15,negated_conjecture,
    ( m1_connsp_2(sK3,sK1,sK2)
    | r1_tarski(sK4,sK3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_724,plain,
    ( r1_tarski(sK4,sK3)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
    inference(resolution,[status(thm)],[c_15,c_302])).

cnf(c_726,plain,
    ( r1_tarski(sK4,sK3)
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_724,c_19])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f58])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3262,c_2510,c_2363,c_2334,c_2135,c_1936,c_1933,c_1905,c_1893,c_1881,c_1835,c_1803,c_1640,c_1551,c_1430,c_1394,c_1389,c_1382,c_753,c_726,c_18,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:38:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.00/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/0.99  
% 2.00/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.00/0.99  
% 2.00/0.99  ------  iProver source info
% 2.00/0.99  
% 2.00/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.00/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.00/0.99  git: non_committed_changes: false
% 2.00/0.99  git: last_make_outside_of_git: false
% 2.00/0.99  
% 2.00/0.99  ------ 
% 2.00/0.99  
% 2.00/0.99  ------ Input Options
% 2.00/0.99  
% 2.00/0.99  --out_options                           all
% 2.00/0.99  --tptp_safe_out                         true
% 2.00/0.99  --problem_path                          ""
% 2.00/0.99  --include_path                          ""
% 2.00/0.99  --clausifier                            res/vclausify_rel
% 2.00/0.99  --clausifier_options                    --mode clausify
% 2.00/0.99  --stdin                                 false
% 2.00/0.99  --stats_out                             all
% 2.00/0.99  
% 2.00/0.99  ------ General Options
% 2.00/0.99  
% 2.00/0.99  --fof                                   false
% 2.00/0.99  --time_out_real                         305.
% 2.00/0.99  --time_out_virtual                      -1.
% 2.00/0.99  --symbol_type_check                     false
% 2.00/0.99  --clausify_out                          false
% 2.00/0.99  --sig_cnt_out                           false
% 2.00/0.99  --trig_cnt_out                          false
% 2.00/0.99  --trig_cnt_out_tolerance                1.
% 2.00/0.99  --trig_cnt_out_sk_spl                   false
% 2.00/0.99  --abstr_cl_out                          false
% 2.00/0.99  
% 2.00/0.99  ------ Global Options
% 2.00/0.99  
% 2.00/0.99  --schedule                              default
% 2.00/0.99  --add_important_lit                     false
% 2.00/0.99  --prop_solver_per_cl                    1000
% 2.00/0.99  --min_unsat_core                        false
% 2.00/0.99  --soft_assumptions                      false
% 2.00/0.99  --soft_lemma_size                       3
% 2.00/0.99  --prop_impl_unit_size                   0
% 2.00/0.99  --prop_impl_unit                        []
% 2.00/0.99  --share_sel_clauses                     true
% 2.00/0.99  --reset_solvers                         false
% 2.00/0.99  --bc_imp_inh                            [conj_cone]
% 2.00/0.99  --conj_cone_tolerance                   3.
% 2.00/0.99  --extra_neg_conj                        none
% 2.00/0.99  --large_theory_mode                     true
% 2.00/0.99  --prolific_symb_bound                   200
% 2.00/0.99  --lt_threshold                          2000
% 2.00/0.99  --clause_weak_htbl                      true
% 2.00/0.99  --gc_record_bc_elim                     false
% 2.00/0.99  
% 2.00/0.99  ------ Preprocessing Options
% 2.00/0.99  
% 2.00/0.99  --preprocessing_flag                    true
% 2.00/0.99  --time_out_prep_mult                    0.1
% 2.00/0.99  --splitting_mode                        input
% 2.00/0.99  --splitting_grd                         true
% 2.00/0.99  --splitting_cvd                         false
% 2.00/0.99  --splitting_cvd_svl                     false
% 2.00/0.99  --splitting_nvd                         32
% 2.00/0.99  --sub_typing                            true
% 2.00/0.99  --prep_gs_sim                           true
% 2.00/0.99  --prep_unflatten                        true
% 2.00/0.99  --prep_res_sim                          true
% 2.00/0.99  --prep_upred                            true
% 2.00/0.99  --prep_sem_filter                       exhaustive
% 2.00/0.99  --prep_sem_filter_out                   false
% 2.00/0.99  --pred_elim                             true
% 2.00/0.99  --res_sim_input                         true
% 2.00/0.99  --eq_ax_congr_red                       true
% 2.00/0.99  --pure_diseq_elim                       true
% 2.00/0.99  --brand_transform                       false
% 2.00/0.99  --non_eq_to_eq                          false
% 2.00/0.99  --prep_def_merge                        true
% 2.00/0.99  --prep_def_merge_prop_impl              false
% 2.00/0.99  --prep_def_merge_mbd                    true
% 2.00/0.99  --prep_def_merge_tr_red                 false
% 2.00/0.99  --prep_def_merge_tr_cl                  false
% 2.00/0.99  --smt_preprocessing                     true
% 2.00/0.99  --smt_ac_axioms                         fast
% 2.00/0.99  --preprocessed_out                      false
% 2.00/0.99  --preprocessed_stats                    false
% 2.00/0.99  
% 2.00/0.99  ------ Abstraction refinement Options
% 2.00/0.99  
% 2.00/0.99  --abstr_ref                             []
% 2.00/0.99  --abstr_ref_prep                        false
% 2.00/0.99  --abstr_ref_until_sat                   false
% 2.00/0.99  --abstr_ref_sig_restrict                funpre
% 2.00/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.00/0.99  --abstr_ref_under                       []
% 2.00/0.99  
% 2.00/0.99  ------ SAT Options
% 2.00/0.99  
% 2.00/0.99  --sat_mode                              false
% 2.00/0.99  --sat_fm_restart_options                ""
% 2.00/0.99  --sat_gr_def                            false
% 2.00/0.99  --sat_epr_types                         true
% 2.00/0.99  --sat_non_cyclic_types                  false
% 2.00/0.99  --sat_finite_models                     false
% 2.00/0.99  --sat_fm_lemmas                         false
% 2.00/0.99  --sat_fm_prep                           false
% 2.00/0.99  --sat_fm_uc_incr                        true
% 2.00/0.99  --sat_out_model                         small
% 2.00/0.99  --sat_out_clauses                       false
% 2.00/0.99  
% 2.00/0.99  ------ QBF Options
% 2.00/0.99  
% 2.00/0.99  --qbf_mode                              false
% 2.00/0.99  --qbf_elim_univ                         false
% 2.00/0.99  --qbf_dom_inst                          none
% 2.00/0.99  --qbf_dom_pre_inst                      false
% 2.00/0.99  --qbf_sk_in                             false
% 2.00/0.99  --qbf_pred_elim                         true
% 2.00/0.99  --qbf_split                             512
% 2.00/0.99  
% 2.00/0.99  ------ BMC1 Options
% 2.00/0.99  
% 2.00/0.99  --bmc1_incremental                      false
% 2.00/0.99  --bmc1_axioms                           reachable_all
% 2.00/0.99  --bmc1_min_bound                        0
% 2.00/0.99  --bmc1_max_bound                        -1
% 2.00/0.99  --bmc1_max_bound_default                -1
% 2.00/0.99  --bmc1_symbol_reachability              true
% 2.00/0.99  --bmc1_property_lemmas                  false
% 2.00/0.99  --bmc1_k_induction                      false
% 2.00/0.99  --bmc1_non_equiv_states                 false
% 2.00/0.99  --bmc1_deadlock                         false
% 2.00/0.99  --bmc1_ucm                              false
% 2.00/0.99  --bmc1_add_unsat_core                   none
% 2.00/0.99  --bmc1_unsat_core_children              false
% 2.00/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.00/0.99  --bmc1_out_stat                         full
% 2.00/0.99  --bmc1_ground_init                      false
% 2.00/0.99  --bmc1_pre_inst_next_state              false
% 2.00/0.99  --bmc1_pre_inst_state                   false
% 2.00/0.99  --bmc1_pre_inst_reach_state             false
% 2.00/0.99  --bmc1_out_unsat_core                   false
% 2.00/0.99  --bmc1_aig_witness_out                  false
% 2.00/0.99  --bmc1_verbose                          false
% 2.00/0.99  --bmc1_dump_clauses_tptp                false
% 2.00/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.00/0.99  --bmc1_dump_file                        -
% 2.00/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.00/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.00/0.99  --bmc1_ucm_extend_mode                  1
% 2.00/0.99  --bmc1_ucm_init_mode                    2
% 2.00/0.99  --bmc1_ucm_cone_mode                    none
% 2.00/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.00/0.99  --bmc1_ucm_relax_model                  4
% 2.00/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.00/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.00/0.99  --bmc1_ucm_layered_model                none
% 2.00/0.99  --bmc1_ucm_max_lemma_size               10
% 2.00/0.99  
% 2.00/0.99  ------ AIG Options
% 2.00/0.99  
% 2.00/0.99  --aig_mode                              false
% 2.00/0.99  
% 2.00/0.99  ------ Instantiation Options
% 2.00/0.99  
% 2.00/0.99  --instantiation_flag                    true
% 2.00/0.99  --inst_sos_flag                         false
% 2.00/0.99  --inst_sos_phase                        true
% 2.00/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.00/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.00/0.99  --inst_lit_sel_side                     num_symb
% 2.00/0.99  --inst_solver_per_active                1400
% 2.00/0.99  --inst_solver_calls_frac                1.
% 2.00/0.99  --inst_passive_queue_type               priority_queues
% 2.00/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.00/0.99  --inst_passive_queues_freq              [25;2]
% 2.00/0.99  --inst_dismatching                      true
% 2.00/0.99  --inst_eager_unprocessed_to_passive     true
% 2.00/0.99  --inst_prop_sim_given                   true
% 2.00/0.99  --inst_prop_sim_new                     false
% 2.00/0.99  --inst_subs_new                         false
% 2.00/0.99  --inst_eq_res_simp                      false
% 2.00/0.99  --inst_subs_given                       false
% 2.00/0.99  --inst_orphan_elimination               true
% 2.00/0.99  --inst_learning_loop_flag               true
% 2.00/0.99  --inst_learning_start                   3000
% 2.00/0.99  --inst_learning_factor                  2
% 2.00/0.99  --inst_start_prop_sim_after_learn       3
% 2.00/0.99  --inst_sel_renew                        solver
% 2.00/0.99  --inst_lit_activity_flag                true
% 2.00/0.99  --inst_restr_to_given                   false
% 2.00/0.99  --inst_activity_threshold               500
% 2.00/0.99  --inst_out_proof                        true
% 2.00/0.99  
% 2.00/0.99  ------ Resolution Options
% 2.00/0.99  
% 2.00/0.99  --resolution_flag                       true
% 2.00/0.99  --res_lit_sel                           adaptive
% 2.00/0.99  --res_lit_sel_side                      none
% 2.00/0.99  --res_ordering                          kbo
% 2.00/0.99  --res_to_prop_solver                    active
% 2.00/0.99  --res_prop_simpl_new                    false
% 2.00/0.99  --res_prop_simpl_given                  true
% 2.00/0.99  --res_passive_queue_type                priority_queues
% 2.00/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.00/0.99  --res_passive_queues_freq               [15;5]
% 2.00/0.99  --res_forward_subs                      full
% 2.00/0.99  --res_backward_subs                     full
% 2.00/0.99  --res_forward_subs_resolution           true
% 2.00/0.99  --res_backward_subs_resolution          true
% 2.00/0.99  --res_orphan_elimination                true
% 2.00/0.99  --res_time_limit                        2.
% 2.00/0.99  --res_out_proof                         true
% 2.00/0.99  
% 2.00/0.99  ------ Superposition Options
% 2.00/0.99  
% 2.00/0.99  --superposition_flag                    true
% 2.00/0.99  --sup_passive_queue_type                priority_queues
% 2.00/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.00/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.00/0.99  --demod_completeness_check              fast
% 2.00/0.99  --demod_use_ground                      true
% 2.00/0.99  --sup_to_prop_solver                    passive
% 2.00/0.99  --sup_prop_simpl_new                    true
% 2.00/0.99  --sup_prop_simpl_given                  true
% 2.00/0.99  --sup_fun_splitting                     false
% 2.00/0.99  --sup_smt_interval                      50000
% 2.00/0.99  
% 2.00/0.99  ------ Superposition Simplification Setup
% 2.00/0.99  
% 2.00/0.99  --sup_indices_passive                   []
% 2.00/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.00/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.00/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.00/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.00/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.00/0.99  --sup_full_bw                           [BwDemod]
% 2.00/0.99  --sup_immed_triv                        [TrivRules]
% 2.00/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.00/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.00/0.99  --sup_immed_bw_main                     []
% 2.00/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.00/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.00/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.00/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.00/0.99  
% 2.00/0.99  ------ Combination Options
% 2.00/0.99  
% 2.00/0.99  --comb_res_mult                         3
% 2.00/0.99  --comb_sup_mult                         2
% 2.00/0.99  --comb_inst_mult                        10
% 2.00/0.99  
% 2.00/0.99  ------ Debug Options
% 2.00/0.99  
% 2.00/0.99  --dbg_backtrace                         false
% 2.00/0.99  --dbg_dump_prop_clauses                 false
% 2.00/0.99  --dbg_dump_prop_clauses_file            -
% 2.00/0.99  --dbg_out_stat                          false
% 2.00/0.99  ------ Parsing...
% 2.00/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.00/0.99  
% 2.00/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 2.00/0.99  
% 2.00/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.00/0.99  ------ Proving...
% 2.00/0.99  ------ Problem Properties 
% 2.00/0.99  
% 2.00/0.99  
% 2.00/0.99  clauses                                 19
% 2.00/0.99  conjectures                             5
% 2.00/0.99  EPR                                     3
% 2.00/0.99  Horn                                    13
% 2.00/0.99  unary                                   2
% 2.00/0.99  binary                                  6
% 2.00/0.99  lits                                    54
% 2.00/0.99  lits eq                                 0
% 2.00/0.99  fd_pure                                 0
% 2.00/0.99  fd_pseudo                               0
% 2.00/0.99  fd_cond                                 0
% 2.00/0.99  fd_pseudo_cond                          0
% 2.00/0.99  AC symbols                              0
% 2.00/0.99  
% 2.00/0.99  ------ Schedule dynamic 5 is on 
% 2.00/0.99  
% 2.00/0.99  ------ no equalities: superposition off 
% 2.00/0.99  
% 2.00/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.00/0.99  
% 2.00/0.99  
% 2.00/0.99  ------ 
% 2.00/0.99  Current options:
% 2.00/0.99  ------ 
% 2.00/0.99  
% 2.00/0.99  ------ Input Options
% 2.00/0.99  
% 2.00/0.99  --out_options                           all
% 2.00/0.99  --tptp_safe_out                         true
% 2.00/0.99  --problem_path                          ""
% 2.00/0.99  --include_path                          ""
% 2.00/0.99  --clausifier                            res/vclausify_rel
% 2.00/0.99  --clausifier_options                    --mode clausify
% 2.00/0.99  --stdin                                 false
% 2.00/0.99  --stats_out                             all
% 2.00/0.99  
% 2.00/0.99  ------ General Options
% 2.00/0.99  
% 2.00/0.99  --fof                                   false
% 2.00/0.99  --time_out_real                         305.
% 2.00/0.99  --time_out_virtual                      -1.
% 2.00/0.99  --symbol_type_check                     false
% 2.00/0.99  --clausify_out                          false
% 2.00/0.99  --sig_cnt_out                           false
% 2.00/0.99  --trig_cnt_out                          false
% 2.00/0.99  --trig_cnt_out_tolerance                1.
% 2.00/0.99  --trig_cnt_out_sk_spl                   false
% 2.00/0.99  --abstr_cl_out                          false
% 2.00/0.99  
% 2.00/0.99  ------ Global Options
% 2.00/0.99  
% 2.00/0.99  --schedule                              default
% 2.00/0.99  --add_important_lit                     false
% 2.00/0.99  --prop_solver_per_cl                    1000
% 2.00/0.99  --min_unsat_core                        false
% 2.00/0.99  --soft_assumptions                      false
% 2.00/0.99  --soft_lemma_size                       3
% 2.00/0.99  --prop_impl_unit_size                   0
% 2.00/0.99  --prop_impl_unit                        []
% 2.00/0.99  --share_sel_clauses                     true
% 2.00/0.99  --reset_solvers                         false
% 2.00/0.99  --bc_imp_inh                            [conj_cone]
% 2.00/0.99  --conj_cone_tolerance                   3.
% 2.00/0.99  --extra_neg_conj                        none
% 2.00/0.99  --large_theory_mode                     true
% 2.00/0.99  --prolific_symb_bound                   200
% 2.00/0.99  --lt_threshold                          2000
% 2.00/0.99  --clause_weak_htbl                      true
% 2.00/0.99  --gc_record_bc_elim                     false
% 2.00/0.99  
% 2.00/0.99  ------ Preprocessing Options
% 2.00/0.99  
% 2.00/0.99  --preprocessing_flag                    true
% 2.00/0.99  --time_out_prep_mult                    0.1
% 2.00/0.99  --splitting_mode                        input
% 2.00/0.99  --splitting_grd                         true
% 2.00/0.99  --splitting_cvd                         false
% 2.00/0.99  --splitting_cvd_svl                     false
% 2.00/0.99  --splitting_nvd                         32
% 2.00/0.99  --sub_typing                            true
% 2.00/0.99  --prep_gs_sim                           true
% 2.00/0.99  --prep_unflatten                        true
% 2.00/0.99  --prep_res_sim                          true
% 2.00/0.99  --prep_upred                            true
% 2.00/0.99  --prep_sem_filter                       exhaustive
% 2.00/0.99  --prep_sem_filter_out                   false
% 2.00/0.99  --pred_elim                             true
% 2.00/0.99  --res_sim_input                         true
% 2.00/0.99  --eq_ax_congr_red                       true
% 2.00/0.99  --pure_diseq_elim                       true
% 2.00/0.99  --brand_transform                       false
% 2.00/0.99  --non_eq_to_eq                          false
% 2.00/0.99  --prep_def_merge                        true
% 2.00/0.99  --prep_def_merge_prop_impl              false
% 2.00/0.99  --prep_def_merge_mbd                    true
% 2.00/0.99  --prep_def_merge_tr_red                 false
% 2.00/0.99  --prep_def_merge_tr_cl                  false
% 2.00/0.99  --smt_preprocessing                     true
% 2.00/0.99  --smt_ac_axioms                         fast
% 2.00/0.99  --preprocessed_out                      false
% 2.00/0.99  --preprocessed_stats                    false
% 2.00/0.99  
% 2.00/0.99  ------ Abstraction refinement Options
% 2.00/0.99  
% 2.00/0.99  --abstr_ref                             []
% 2.00/0.99  --abstr_ref_prep                        false
% 2.00/0.99  --abstr_ref_until_sat                   false
% 2.00/0.99  --abstr_ref_sig_restrict                funpre
% 2.00/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.00/0.99  --abstr_ref_under                       []
% 2.00/0.99  
% 2.00/0.99  ------ SAT Options
% 2.00/0.99  
% 2.00/0.99  --sat_mode                              false
% 2.00/0.99  --sat_fm_restart_options                ""
% 2.00/0.99  --sat_gr_def                            false
% 2.00/0.99  --sat_epr_types                         true
% 2.00/0.99  --sat_non_cyclic_types                  false
% 2.00/0.99  --sat_finite_models                     false
% 2.00/0.99  --sat_fm_lemmas                         false
% 2.00/0.99  --sat_fm_prep                           false
% 2.00/0.99  --sat_fm_uc_incr                        true
% 2.00/0.99  --sat_out_model                         small
% 2.00/0.99  --sat_out_clauses                       false
% 2.00/0.99  
% 2.00/0.99  ------ QBF Options
% 2.00/0.99  
% 2.00/0.99  --qbf_mode                              false
% 2.00/0.99  --qbf_elim_univ                         false
% 2.00/0.99  --qbf_dom_inst                          none
% 2.00/0.99  --qbf_dom_pre_inst                      false
% 2.00/0.99  --qbf_sk_in                             false
% 2.00/0.99  --qbf_pred_elim                         true
% 2.00/0.99  --qbf_split                             512
% 2.00/0.99  
% 2.00/0.99  ------ BMC1 Options
% 2.00/0.99  
% 2.00/0.99  --bmc1_incremental                      false
% 2.00/0.99  --bmc1_axioms                           reachable_all
% 2.00/0.99  --bmc1_min_bound                        0
% 2.00/0.99  --bmc1_max_bound                        -1
% 2.00/0.99  --bmc1_max_bound_default                -1
% 2.00/0.99  --bmc1_symbol_reachability              true
% 2.00/0.99  --bmc1_property_lemmas                  false
% 2.00/0.99  --bmc1_k_induction                      false
% 2.00/0.99  --bmc1_non_equiv_states                 false
% 2.00/0.99  --bmc1_deadlock                         false
% 2.00/0.99  --bmc1_ucm                              false
% 2.00/0.99  --bmc1_add_unsat_core                   none
% 2.00/0.99  --bmc1_unsat_core_children              false
% 2.00/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.00/0.99  --bmc1_out_stat                         full
% 2.00/0.99  --bmc1_ground_init                      false
% 2.00/0.99  --bmc1_pre_inst_next_state              false
% 2.00/0.99  --bmc1_pre_inst_state                   false
% 2.00/0.99  --bmc1_pre_inst_reach_state             false
% 2.00/0.99  --bmc1_out_unsat_core                   false
% 2.00/0.99  --bmc1_aig_witness_out                  false
% 2.00/0.99  --bmc1_verbose                          false
% 2.00/0.99  --bmc1_dump_clauses_tptp                false
% 2.00/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.00/0.99  --bmc1_dump_file                        -
% 2.00/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.00/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.00/0.99  --bmc1_ucm_extend_mode                  1
% 2.00/0.99  --bmc1_ucm_init_mode                    2
% 2.00/0.99  --bmc1_ucm_cone_mode                    none
% 2.00/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.00/0.99  --bmc1_ucm_relax_model                  4
% 2.00/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.00/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.00/0.99  --bmc1_ucm_layered_model                none
% 2.00/0.99  --bmc1_ucm_max_lemma_size               10
% 2.00/0.99  
% 2.00/0.99  ------ AIG Options
% 2.00/0.99  
% 2.00/0.99  --aig_mode                              false
% 2.00/0.99  
% 2.00/0.99  ------ Instantiation Options
% 2.00/0.99  
% 2.00/0.99  --instantiation_flag                    true
% 2.00/0.99  --inst_sos_flag                         false
% 2.00/0.99  --inst_sos_phase                        true
% 2.00/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.00/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.00/0.99  --inst_lit_sel_side                     none
% 2.00/0.99  --inst_solver_per_active                1400
% 2.00/0.99  --inst_solver_calls_frac                1.
% 2.00/0.99  --inst_passive_queue_type               priority_queues
% 2.00/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.00/0.99  --inst_passive_queues_freq              [25;2]
% 2.00/0.99  --inst_dismatching                      true
% 2.00/0.99  --inst_eager_unprocessed_to_passive     true
% 2.00/0.99  --inst_prop_sim_given                   true
% 2.00/0.99  --inst_prop_sim_new                     false
% 2.00/0.99  --inst_subs_new                         false
% 2.00/0.99  --inst_eq_res_simp                      false
% 2.00/0.99  --inst_subs_given                       false
% 2.00/0.99  --inst_orphan_elimination               true
% 2.00/0.99  --inst_learning_loop_flag               true
% 2.00/0.99  --inst_learning_start                   3000
% 2.00/0.99  --inst_learning_factor                  2
% 2.00/0.99  --inst_start_prop_sim_after_learn       3
% 2.00/0.99  --inst_sel_renew                        solver
% 2.00/0.99  --inst_lit_activity_flag                true
% 2.00/0.99  --inst_restr_to_given                   false
% 2.00/0.99  --inst_activity_threshold               500
% 2.00/0.99  --inst_out_proof                        true
% 2.00/0.99  
% 2.00/0.99  ------ Resolution Options
% 2.00/0.99  
% 2.00/0.99  --resolution_flag                       false
% 2.00/0.99  --res_lit_sel                           adaptive
% 2.00/0.99  --res_lit_sel_side                      none
% 2.00/0.99  --res_ordering                          kbo
% 2.00/0.99  --res_to_prop_solver                    active
% 2.00/0.99  --res_prop_simpl_new                    false
% 2.00/0.99  --res_prop_simpl_given                  true
% 2.00/0.99  --res_passive_queue_type                priority_queues
% 2.00/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.00/0.99  --res_passive_queues_freq               [15;5]
% 2.00/0.99  --res_forward_subs                      full
% 2.00/0.99  --res_backward_subs                     full
% 2.00/0.99  --res_forward_subs_resolution           true
% 2.00/0.99  --res_backward_subs_resolution          true
% 2.00/0.99  --res_orphan_elimination                true
% 2.00/0.99  --res_time_limit                        2.
% 2.00/0.99  --res_out_proof                         true
% 2.00/0.99  
% 2.00/0.99  ------ Superposition Options
% 2.00/0.99  
% 2.00/0.99  --superposition_flag                    false
% 2.00/0.99  --sup_passive_queue_type                priority_queues
% 2.00/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.00/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.00/0.99  --demod_completeness_check              fast
% 2.00/0.99  --demod_use_ground                      true
% 2.00/0.99  --sup_to_prop_solver                    passive
% 2.00/0.99  --sup_prop_simpl_new                    true
% 2.00/0.99  --sup_prop_simpl_given                  true
% 2.00/0.99  --sup_fun_splitting                     false
% 2.00/0.99  --sup_smt_interval                      50000
% 2.00/0.99  
% 2.00/0.99  ------ Superposition Simplification Setup
% 2.00/0.99  
% 2.00/0.99  --sup_indices_passive                   []
% 2.00/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.00/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.00/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.00/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.00/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.00/0.99  --sup_full_bw                           [BwDemod]
% 2.00/0.99  --sup_immed_triv                        [TrivRules]
% 2.00/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.00/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.00/0.99  --sup_immed_bw_main                     []
% 2.00/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.00/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.00/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.00/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.00/0.99  
% 2.00/0.99  ------ Combination Options
% 2.00/0.99  
% 2.00/0.99  --comb_res_mult                         3
% 2.00/0.99  --comb_sup_mult                         2
% 2.00/0.99  --comb_inst_mult                        10
% 2.00/0.99  
% 2.00/0.99  ------ Debug Options
% 2.00/0.99  
% 2.00/0.99  --dbg_backtrace                         false
% 2.00/0.99  --dbg_dump_prop_clauses                 false
% 2.00/0.99  --dbg_dump_prop_clauses_file            -
% 2.00/0.99  --dbg_out_stat                          false
% 2.00/0.99  
% 2.00/0.99  
% 2.00/0.99  
% 2.00/0.99  
% 2.00/0.99  ------ Proving...
% 2.00/0.99  
% 2.00/0.99  
% 2.00/0.99  % SZS status Theorem for theBenchmark.p
% 2.00/0.99  
% 2.00/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.00/0.99  
% 2.00/0.99  fof(f7,axiom,(
% 2.00/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 2.00/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.00/0.99  
% 2.00/0.99  fof(f21,plain,(
% 2.00/0.99    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.00/0.99    inference(ennf_transformation,[],[f7])).
% 2.00/0.99  
% 2.00/0.99  fof(f22,plain,(
% 2.00/0.99    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.00/0.99    inference(flattening,[],[f21])).
% 2.00/0.99  
% 2.00/0.99  fof(f32,plain,(
% 2.00/0.99    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.00/0.99    inference(nnf_transformation,[],[f22])).
% 2.00/0.99  
% 2.00/0.99  fof(f51,plain,(
% 2.00/0.99    ( ! [X2,X0,X1] : (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.00/0.99    inference(cnf_transformation,[],[f32])).
% 2.00/0.99  
% 2.00/0.99  fof(f10,conjecture,(
% 2.00/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 2.00/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.00/0.99  
% 2.00/0.99  fof(f11,negated_conjecture,(
% 2.00/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 2.00/0.99    inference(negated_conjecture,[],[f10])).
% 2.00/0.99  
% 2.00/0.99  fof(f27,plain,(
% 2.00/0.99    ? [X0] : (? [X1] : (? [X2] : ((m1_connsp_2(X2,X0,X1) <~> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.00/0.99    inference(ennf_transformation,[],[f11])).
% 2.00/0.99  
% 2.00/0.99  fof(f28,plain,(
% 2.00/0.99    ? [X0] : (? [X1] : (? [X2] : ((m1_connsp_2(X2,X0,X1) <~> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.00/0.99    inference(flattening,[],[f27])).
% 2.00/0.99  
% 2.00/0.99  fof(f33,plain,(
% 2.00/0.99    ? [X0] : (? [X1] : (? [X2] : (((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1)) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | m1_connsp_2(X2,X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.00/0.99    inference(nnf_transformation,[],[f28])).
% 2.00/0.99  
% 2.00/0.99  fof(f34,plain,(
% 2.00/0.99    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1)) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.00/0.99    inference(flattening,[],[f33])).
% 2.00/0.99  
% 2.00/0.99  fof(f35,plain,(
% 2.00/0.99    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1)) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.00/0.99    inference(rectify,[],[f34])).
% 2.00/0.99  
% 2.00/0.99  fof(f39,plain,(
% 2.00/0.99    ( ! [X2,X0,X1] : (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) => (r2_hidden(X1,sK4) & r1_tarski(sK4,X2) & v3_pre_topc(sK4,X0) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.00/0.99    introduced(choice_axiom,[])).
% 2.00/0.99  
% 2.00/0.99  fof(f38,plain,(
% 2.00/0.99    ( ! [X0,X1] : (? [X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1)) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,sK3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(sK3,X0,X1)) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,sK3) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | m1_connsp_2(sK3,X0,X1)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.00/0.99    introduced(choice_axiom,[])).
% 2.00/0.99  
% 2.00/0.99  fof(f37,plain,(
% 2.00/0.99    ( ! [X0] : (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1)) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : ((! [X3] : (~r2_hidden(sK2,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,sK2)) & (? [X4] : (r2_hidden(sK2,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | m1_connsp_2(X2,X0,sK2)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK2,u1_struct_0(X0)))) )),
% 2.00/0.99    introduced(choice_axiom,[])).
% 2.00/0.99  
% 2.00/0.99  fof(f36,plain,(
% 2.00/0.99    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1)) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) | ~m1_connsp_2(X2,sK1,X1)) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,sK1) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))) | m1_connsp_2(X2,sK1,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X1,u1_struct_0(sK1))) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 2.00/0.99    introduced(choice_axiom,[])).
% 2.00/0.99  
% 2.00/0.99  fof(f40,plain,(
% 2.00/0.99    (((! [X3] : (~r2_hidden(sK2,X3) | ~r1_tarski(X3,sK3) | ~v3_pre_topc(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) | ~m1_connsp_2(sK3,sK1,sK2)) & ((r2_hidden(sK2,sK4) & r1_tarski(sK4,sK3) & v3_pre_topc(sK4,sK1) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))) | m1_connsp_2(sK3,sK1,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK2,u1_struct_0(sK1))) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 2.00/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f35,f39,f38,f37,f36])).
% 2.00/0.99  
% 2.00/0.99  fof(f54,plain,(
% 2.00/0.99    ~v2_struct_0(sK1)),
% 2.00/0.99    inference(cnf_transformation,[],[f40])).
% 2.00/0.99  
% 2.00/0.99  fof(f55,plain,(
% 2.00/0.99    v2_pre_topc(sK1)),
% 2.00/0.99    inference(cnf_transformation,[],[f40])).
% 2.00/0.99  
% 2.00/0.99  fof(f56,plain,(
% 2.00/0.99    l1_pre_topc(sK1)),
% 2.00/0.99    inference(cnf_transformation,[],[f40])).
% 2.00/0.99  
% 2.00/0.99  fof(f9,axiom,(
% 2.00/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (m1_connsp_2(X1,X0,X2) => r2_hidden(X2,X1)))))),
% 2.00/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.00/0.99  
% 2.00/0.99  fof(f25,plain,(
% 2.00/0.99    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.00/0.99    inference(ennf_transformation,[],[f9])).
% 2.00/0.99  
% 2.00/0.99  fof(f26,plain,(
% 2.00/0.99    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.00/0.99    inference(flattening,[],[f25])).
% 2.00/0.99  
% 2.00/0.99  fof(f53,plain,(
% 2.00/0.99    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.00/0.99    inference(cnf_transformation,[],[f26])).
% 2.00/0.99  
% 2.00/0.99  fof(f8,axiom,(
% 2.00/0.99    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.00/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.00/0.99  
% 2.00/0.99  fof(f23,plain,(
% 2.00/0.99    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.00/0.99    inference(ennf_transformation,[],[f8])).
% 2.00/0.99  
% 2.00/0.99  fof(f24,plain,(
% 2.00/0.99    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.00/0.99    inference(flattening,[],[f23])).
% 2.00/0.99  
% 2.00/0.99  fof(f52,plain,(
% 2.00/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.00/0.99    inference(cnf_transformation,[],[f24])).
% 2.00/0.99  
% 2.00/0.99  fof(f1,axiom,(
% 2.00/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 2.00/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.00/0.99  
% 2.00/0.99  fof(f12,plain,(
% 2.00/0.99    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.00/0.99    inference(ennf_transformation,[],[f1])).
% 2.00/0.99  
% 2.00/0.99  fof(f41,plain,(
% 2.00/0.99    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.00/0.99    inference(cnf_transformation,[],[f12])).
% 2.00/0.99  
% 2.00/0.99  fof(f3,axiom,(
% 2.00/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.00/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.00/0.99  
% 2.00/0.99  fof(f31,plain,(
% 2.00/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.00/0.99    inference(nnf_transformation,[],[f3])).
% 2.00/0.99  
% 2.00/0.99  fof(f46,plain,(
% 2.00/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.00/0.99    inference(cnf_transformation,[],[f31])).
% 2.00/0.99  
% 2.00/0.99  fof(f63,plain,(
% 2.00/0.99    ( ! [X3] : (~r2_hidden(sK2,X3) | ~r1_tarski(X3,sK3) | ~v3_pre_topc(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_connsp_2(sK3,sK1,sK2)) )),
% 2.00/0.99    inference(cnf_transformation,[],[f40])).
% 2.00/0.99  
% 2.00/0.99  fof(f5,axiom,(
% 2.00/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 2.00/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.00/0.99  
% 2.00/0.99  fof(f17,plain,(
% 2.00/0.99    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.00/0.99    inference(ennf_transformation,[],[f5])).
% 2.00/0.99  
% 2.00/0.99  fof(f18,plain,(
% 2.00/0.99    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.00/0.99    inference(flattening,[],[f17])).
% 2.00/0.99  
% 2.00/0.99  fof(f48,plain,(
% 2.00/0.99    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.00/0.99    inference(cnf_transformation,[],[f18])).
% 2.00/0.99  
% 2.00/0.99  fof(f4,axiom,(
% 2.00/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.00/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.00/0.99  
% 2.00/0.99  fof(f15,plain,(
% 2.00/0.99    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.00/0.99    inference(ennf_transformation,[],[f4])).
% 2.00/0.99  
% 2.00/0.99  fof(f16,plain,(
% 2.00/0.99    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.00/0.99    inference(flattening,[],[f15])).
% 2.00/0.99  
% 2.00/0.99  fof(f47,plain,(
% 2.00/0.99    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.00/0.99    inference(cnf_transformation,[],[f16])).
% 2.00/0.99  
% 2.00/0.99  fof(f2,axiom,(
% 2.00/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) => r2_hidden(X3,X2))) => r1_tarski(X1,X2))))),
% 2.00/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.00/0.99  
% 2.00/0.99  fof(f13,plain,(
% 2.00/0.99    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) | ? [X3] : ((~r2_hidden(X3,X2) & r2_hidden(X3,X1)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.00/0.99    inference(ennf_transformation,[],[f2])).
% 2.00/0.99  
% 2.00/0.99  fof(f14,plain,(
% 2.00/0.99    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | ? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.00/0.99    inference(flattening,[],[f13])).
% 2.00/0.99  
% 2.00/0.99  fof(f29,plain,(
% 2.00/0.99    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) => (~r2_hidden(sK0(X0,X1,X2),X2) & r2_hidden(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),X0)))),
% 2.00/0.99    introduced(choice_axiom,[])).
% 2.00/0.99  
% 2.00/0.99  fof(f30,plain,(
% 2.00/0.99    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | (~r2_hidden(sK0(X0,X1,X2),X2) & r2_hidden(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.00/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f29])).
% 2.00/0.99  
% 2.00/0.99  fof(f44,plain,(
% 2.00/0.99    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r2_hidden(sK0(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.00/0.99    inference(cnf_transformation,[],[f30])).
% 2.00/0.99  
% 2.00/0.99  fof(f42,plain,(
% 2.00/0.99    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | m1_subset_1(sK0(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.00/0.99    inference(cnf_transformation,[],[f30])).
% 2.00/0.99  
% 2.00/0.99  fof(f43,plain,(
% 2.00/0.99    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | r2_hidden(sK0(X0,X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.00/0.99    inference(cnf_transformation,[],[f30])).
% 2.00/0.99  
% 2.00/0.99  fof(f6,axiom,(
% 2.00/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 2.00/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.00/0.99  
% 2.00/0.99  fof(f19,plain,(
% 2.00/0.99    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.00/0.99    inference(ennf_transformation,[],[f6])).
% 2.00/0.99  
% 2.00/0.99  fof(f20,plain,(
% 2.00/0.99    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.00/0.99    inference(flattening,[],[f19])).
% 2.00/0.99  
% 2.00/0.99  fof(f49,plain,(
% 2.00/0.99    ( ! [X2,X0,X1] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.00/0.99    inference(cnf_transformation,[],[f20])).
% 2.00/0.99  
% 2.00/0.99  fof(f60,plain,(
% 2.00/0.99    v3_pre_topc(sK4,sK1) | m1_connsp_2(sK3,sK1,sK2)),
% 2.00/0.99    inference(cnf_transformation,[],[f40])).
% 2.00/0.99  
% 2.00/0.99  fof(f59,plain,(
% 2.00/0.99    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) | m1_connsp_2(sK3,sK1,sK2)),
% 2.00/0.99    inference(cnf_transformation,[],[f40])).
% 2.00/0.99  
% 2.00/0.99  fof(f50,plain,(
% 2.00/0.99    ( ! [X2,X0,X1] : (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.00/0.99    inference(cnf_transformation,[],[f32])).
% 2.00/0.99  
% 2.00/0.99  fof(f62,plain,(
% 2.00/0.99    r2_hidden(sK2,sK4) | m1_connsp_2(sK3,sK1,sK2)),
% 2.00/0.99    inference(cnf_transformation,[],[f40])).
% 2.00/0.99  
% 2.00/0.99  fof(f57,plain,(
% 2.00/0.99    m1_subset_1(sK2,u1_struct_0(sK1))),
% 2.00/0.99    inference(cnf_transformation,[],[f40])).
% 2.00/0.99  
% 2.00/0.99  fof(f61,plain,(
% 2.00/0.99    r1_tarski(sK4,sK3) | m1_connsp_2(sK3,sK1,sK2)),
% 2.00/0.99    inference(cnf_transformation,[],[f40])).
% 2.00/0.99  
% 2.00/0.99  fof(f58,plain,(
% 2.00/0.99    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 2.00/0.99    inference(cnf_transformation,[],[f40])).
% 2.00/0.99  
% 2.00/0.99  cnf(c_9,plain,
% 2.00/0.99      ( m1_connsp_2(X0,X1,X2)
% 2.00/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.00/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.00/0.99      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 2.00/0.99      | v2_struct_0(X1)
% 2.00/0.99      | ~ v2_pre_topc(X1)
% 2.00/0.99      | ~ l1_pre_topc(X1) ),
% 2.00/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.00/0.99  
% 2.00/0.99  cnf(c_22,negated_conjecture,
% 2.00/0.99      ( ~ v2_struct_0(sK1) ),
% 2.00/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.00/0.99  
% 2.00/0.99  cnf(c_358,plain,
% 2.00/0.99      ( m1_connsp_2(X0,sK1,X1)
% 2.00/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.00/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.00/0.99      | ~ r2_hidden(X1,k1_tops_1(sK1,X0))
% 2.00/0.99      | ~ v2_pre_topc(sK1)
% 2.00/0.99      | ~ l1_pre_topc(sK1) ),
% 2.00/0.99      inference(resolution,[status(thm)],[c_9,c_22]) ).
% 2.00/0.99  
% 2.00/0.99  cnf(c_21,negated_conjecture,
% 2.00/0.99      ( v2_pre_topc(sK1) ),
% 2.00/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.00/0.99  
% 2.00/0.99  cnf(c_20,negated_conjecture,
% 2.00/0.99      ( l1_pre_topc(sK1) ),
% 2.00/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.00/0.99  
% 2.00/0.99  cnf(c_362,plain,
% 2.00/0.99      ( m1_connsp_2(X0,sK1,X1)
% 2.00/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.00/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.00/0.99      | ~ r2_hidden(X1,k1_tops_1(sK1,X0)) ),
% 2.00/0.99      inference(global_propositional_subsumption,
% 2.00/0.99                [status(thm)],
% 2.00/0.99                [c_358,c_21,c_20]) ).
% 2.00/0.99  
% 2.00/0.99  cnf(c_1265,plain,
% 2.00/0.99      ( m1_connsp_2(X0_44,sK1,X1_44)
% 2.00/0.99      | ~ m1_subset_1(X1_44,u1_struct_0(sK1))
% 2.00/0.99      | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.00/0.99      | ~ r2_hidden(X1_44,k1_tops_1(sK1,X0_44)) ),
% 2.00/0.99      inference(subtyping,[status(esa)],[c_362]) ).
% 2.00/0.99  
% 2.00/0.99  cnf(c_1392,plain,
% 2.00/0.99      ( m1_connsp_2(sK3,sK1,X0_44)
% 2.00/0.99      | ~ m1_subset_1(X0_44,u1_struct_0(sK1))
% 2.00/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.00/0.99      | ~ r2_hidden(X0_44,k1_tops_1(sK1,sK3)) ),
% 2.00/0.99      inference(instantiation,[status(thm)],[c_1265]) ).
% 2.00/0.99  
% 2.00/0.99  cnf(c_3262,plain,
% 2.00/0.99      ( m1_connsp_2(sK3,sK1,sK0(u1_struct_0(sK1),k1_tops_1(sK1,k1_tops_1(sK1,sK3)),sK3))
% 2.00/0.99      | ~ m1_subset_1(sK0(u1_struct_0(sK1),k1_tops_1(sK1,k1_tops_1(sK1,sK3)),sK3),u1_struct_0(sK1))
% 2.00/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.00/0.99      | ~ r2_hidden(sK0(u1_struct_0(sK1),k1_tops_1(sK1,k1_tops_1(sK1,sK3)),sK3),k1_tops_1(sK1,sK3)) ),
% 2.00/0.99      inference(instantiation,[status(thm)],[c_1392]) ).
% 2.00/0.99  
% 2.00/0.99  cnf(c_12,plain,
% 2.00/0.99      ( ~ m1_connsp_2(X0,X1,X2)
% 2.00/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.00/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.00/0.99      | r2_hidden(X2,X0)
% 2.00/0.99      | v2_struct_0(X1)
% 2.00/0.99      | ~ v2_pre_topc(X1)
% 2.00/0.99      | ~ l1_pre_topc(X1) ),
% 2.00/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.00/0.99  
% 2.00/0.99  cnf(c_11,plain,
% 2.00/0.99      ( ~ m1_connsp_2(X0,X1,X2)
% 2.00/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.00/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.00/0.99      | v2_struct_0(X1)
% 2.00/0.99      | ~ v2_pre_topc(X1)
% 2.00/0.99      | ~ l1_pre_topc(X1) ),
% 2.00/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.00/0.99  
% 2.00/0.99  cnf(c_123,plain,
% 2.00/0.99      ( ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.00/0.99      | ~ m1_connsp_2(X0,X1,X2)
% 2.00/0.99      | r2_hidden(X2,X0)
% 2.00/0.99      | v2_struct_0(X1)
% 2.00/0.99      | ~ v2_pre_topc(X1)
% 2.00/0.99      | ~ l1_pre_topc(X1) ),
% 2.00/0.99      inference(global_propositional_subsumption,
% 2.00/0.99                [status(thm)],
% 2.00/0.99                [c_12,c_11]) ).
% 2.00/0.99  
% 2.00/0.99  cnf(c_124,plain,
% 2.00/0.99      ( ~ m1_connsp_2(X0,X1,X2)
% 2.00/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.00/0.99      | r2_hidden(X2,X0)
% 2.00/0.99      | v2_struct_0(X1)
% 2.00/0.99      | ~ v2_pre_topc(X1)
% 2.00/0.99      | ~ l1_pre_topc(X1) ),
% 2.00/0.99      inference(renaming,[status(thm)],[c_123]) ).
% 2.00/0.99  
% 2.00/0.99  cnf(c_318,plain,
% 2.00/0.99      ( ~ m1_connsp_2(X0,sK1,X1)
% 2.00/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.00/0.99      | r2_hidden(X1,X0)
% 2.00/0.99      | ~ v2_pre_topc(sK1)
% 2.00/0.99      | ~ l1_pre_topc(sK1) ),
% 2.00/0.99      inference(resolution,[status(thm)],[c_124,c_22]) ).
% 2.00/0.99  
% 2.00/0.99  cnf(c_322,plain,
% 2.00/0.99      ( ~ m1_connsp_2(X0,sK1,X1)
% 2.00/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.00/0.99      | r2_hidden(X1,X0) ),
% 2.00/0.99      inference(global_propositional_subsumption,
% 2.00/0.99                [status(thm)],
% 2.00/0.99                [c_318,c_21,c_20]) ).
% 2.00/0.99  
% 2.00/0.99  cnf(c_1267,plain,
% 2.00/0.99      ( ~ m1_connsp_2(X0_44,sK1,X1_44)
% 2.00/0.99      | ~ m1_subset_1(X1_44,u1_struct_0(sK1))
% 2.00/0.99      | r2_hidden(X1_44,X0_44) ),
% 2.00/0.99      inference(subtyping,[status(esa)],[c_322]) ).
% 2.00/0.99  
% 2.00/0.99  cnf(c_1714,plain,
% 2.00/0.99      ( ~ m1_connsp_2(sK3,sK1,X0_44)
% 2.00/0.99      | ~ m1_subset_1(X0_44,u1_struct_0(sK1))
% 2.00/0.99      | r2_hidden(X0_44,sK3) ),
% 2.00/0.99      inference(instantiation,[status(thm)],[c_1267]) ).
% 2.00/0.99  
% 2.00/0.99  cnf(c_2510,plain,
% 2.00/0.99      ( ~ m1_connsp_2(sK3,sK1,sK0(u1_struct_0(sK1),k1_tops_1(sK1,k1_tops_1(sK1,sK3)),sK3))
% 2.00/0.99      | ~ m1_subset_1(sK0(u1_struct_0(sK1),k1_tops_1(sK1,k1_tops_1(sK1,sK3)),sK3),u1_struct_0(sK1))
% 2.00/0.99      | r2_hidden(sK0(u1_struct_0(sK1),k1_tops_1(sK1,k1_tops_1(sK1,sK3)),sK3),sK3) ),
% 2.00/0.99      inference(instantiation,[status(thm)],[c_1714]) ).
% 2.00/0.99  
% 2.00/0.99  cnf(c_2363,plain,
% 2.00/0.99      ( ~ m1_connsp_2(k1_tops_1(sK1,sK3),sK1,sK0(u1_struct_0(sK1),k1_tops_1(sK1,k1_tops_1(sK1,sK3)),sK3))
% 2.00/0.99      | ~ m1_subset_1(sK0(u1_struct_0(sK1),k1_tops_1(sK1,k1_tops_1(sK1,sK3)),sK3),u1_struct_0(sK1))
% 2.00/0.99      | r2_hidden(sK0(u1_struct_0(sK1),k1_tops_1(sK1,k1_tops_1(sK1,sK3)),sK3),k1_tops_1(sK1,sK3)) ),
% 2.00/0.99      inference(instantiation,[status(thm)],[c_1267]) ).
% 2.00/0.99  
% 2.00/0.99  cnf(c_0,plain,
% 2.00/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.00/0.99      | ~ r2_hidden(X2,X0)
% 2.00/0.99      | r2_hidden(X2,X1) ),
% 2.00/0.99      inference(cnf_transformation,[],[f41]) ).
% 2.00/0.99  
% 2.00/0.99  cnf(c_4,plain,
% 2.00/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.00/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.00/0.99  
% 2.00/0.99  cnf(c_178,plain,
% 2.00/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.00/0.99      inference(prop_impl,[status(thm)],[c_4]) ).
% 2.00/0.99  
% 2.00/0.99  cnf(c_226,plain,
% 2.00/0.99      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 2.00/0.99      inference(bin_hyper_res,[status(thm)],[c_0,c_178]) ).
% 2.00/0.99  
% 2.00/0.99  cnf(c_1269,plain,
% 2.00/0.99      ( ~ r1_tarski(X0_44,X1_44)
% 2.00/0.99      | ~ r2_hidden(X2_44,X0_44)
% 2.00/0.99      | r2_hidden(X2_44,X1_44) ),
% 2.00/0.99      inference(subtyping,[status(esa)],[c_226]) ).
% 2.00/0.99  
% 2.00/0.99  cnf(c_2329,plain,
% 2.00/0.99      ( ~ r1_tarski(k1_tops_1(sK1,sK3),k1_tops_1(sK1,k1_tops_1(sK1,sK3)))
% 2.00/0.99      | r2_hidden(X0_44,k1_tops_1(sK1,k1_tops_1(sK1,sK3)))
% 2.00/0.99      | ~ r2_hidden(X0_44,k1_tops_1(sK1,sK3)) ),
% 2.00/0.99      inference(instantiation,[status(thm)],[c_1269]) ).
% 2.00/0.99  
% 2.00/0.99  cnf(c_2334,plain,
% 2.00/0.99      ( ~ r1_tarski(k1_tops_1(sK1,sK3),k1_tops_1(sK1,k1_tops_1(sK1,sK3)))
% 2.00/0.99      | r2_hidden(sK2,k1_tops_1(sK1,k1_tops_1(sK1,sK3)))
% 2.00/0.99      | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
% 2.00/0.99      inference(instantiation,[status(thm)],[c_2329]) ).
% 2.00/0.99  
% 2.00/0.99  cnf(c_2130,plain,
% 2.00/0.99      ( ~ r1_tarski(sK4,k1_tops_1(sK1,sK3))
% 2.00/0.99      | r2_hidden(X0_44,k1_tops_1(sK1,sK3))
% 2.00/0.99      | ~ r2_hidden(X0_44,sK4) ),
% 2.00/0.99      inference(instantiation,[status(thm)],[c_1269]) ).
% 2.00/0.99  
% 2.00/0.99  cnf(c_2135,plain,
% 2.00/0.99      ( ~ r1_tarski(sK4,k1_tops_1(sK1,sK3))
% 2.00/0.99      | r2_hidden(sK2,k1_tops_1(sK1,sK3))
% 2.00/0.99      | ~ r2_hidden(sK2,sK4) ),
% 2.00/0.99      inference(instantiation,[status(thm)],[c_2130]) ).
% 2.00/0.99  
% 2.00/0.99  cnf(c_13,negated_conjecture,
% 2.00/0.99      ( ~ m1_connsp_2(sK3,sK1,sK2)
% 2.00/0.99      | ~ v3_pre_topc(X0,sK1)
% 2.00/0.99      | ~ r1_tarski(X0,sK3)
% 2.00/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.00/0.99      | ~ r2_hidden(sK2,X0) ),
% 2.00/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.00/0.99  
% 2.00/0.99  cnf(c_7,plain,
% 2.00/0.99      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 2.00/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.00/0.99      | ~ v2_pre_topc(X0)
% 2.00/0.99      | ~ l1_pre_topc(X0) ),
% 2.00/0.99      inference(cnf_transformation,[],[f48]) ).
% 2.00/0.99  
% 2.00/0.99  cnf(c_398,plain,
% 2.00/0.99      ( v3_pre_topc(k1_tops_1(sK1,X0),sK1)
% 2.00/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.00/0.99      | ~ l1_pre_topc(sK1) ),
% 2.00/0.99      inference(resolution,[status(thm)],[c_7,c_21]) ).
% 2.00/0.99  
% 2.00/0.99  cnf(c_402,plain,
% 2.00/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.00/0.99      | v3_pre_topc(k1_tops_1(sK1,X0),sK1) ),
% 2.00/0.99      inference(global_propositional_subsumption,
% 2.00/0.99                [status(thm)],
% 2.00/0.99                [c_398,c_20]) ).
% 2.00/0.99  
% 2.00/0.99  cnf(c_403,plain,
% 2.00/0.99      ( v3_pre_topc(k1_tops_1(sK1,X0),sK1)
% 2.00/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.00/0.99      inference(renaming,[status(thm)],[c_402]) ).
% 2.00/0.99  
% 2.00/0.99  cnf(c_505,plain,
% 2.00/0.99      ( ~ m1_connsp_2(sK3,sK1,sK2)
% 2.00/0.99      | ~ r1_tarski(k1_tops_1(sK1,X0),sK3)
% 2.00/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.00/0.99      | ~ m1_subset_1(k1_tops_1(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.00/0.99      | ~ r2_hidden(sK2,k1_tops_1(sK1,X0)) ),
% 2.00/0.99      inference(resolution,[status(thm)],[c_13,c_403]) ).
% 2.00/0.99  
% 2.00/0.99  cnf(c_6,plain,
% 2.00/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.00/0.99      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.00/0.99      | ~ l1_pre_topc(X1) ),
% 2.00/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.00/0.99  
% 2.00/0.99  cnf(c_438,plain,
% 2.00/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.00/0.99      | m1_subset_1(k1_tops_1(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.00/0.99      inference(resolution,[status(thm)],[c_6,c_20]) ).
% 2.00/0.99  
% 2.00/0.99  cnf(c_509,plain,
% 2.00/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.00/0.99      | ~ r1_tarski(k1_tops_1(sK1,X0),sK3)
% 2.00/0.99      | ~ m1_connsp_2(sK3,sK1,sK2)
% 2.00/0.99      | ~ r2_hidden(sK2,k1_tops_1(sK1,X0)) ),
% 2.00/0.99      inference(global_propositional_subsumption,
% 2.00/0.99                [status(thm)],
% 2.00/0.99                [c_505,c_438]) ).
% 2.00/0.99  
% 2.00/0.99  cnf(c_510,plain,
% 2.00/0.99      ( ~ m1_connsp_2(sK3,sK1,sK2)
% 2.00/0.99      | ~ r1_tarski(k1_tops_1(sK1,X0),sK3)
% 2.00/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.00/0.99      | ~ r2_hidden(sK2,k1_tops_1(sK1,X0)) ),
% 2.00/0.99      inference(renaming,[status(thm)],[c_509]) ).
% 2.00/0.99  
% 2.00/0.99  cnf(c_1261,plain,
% 2.00/0.99      ( ~ m1_connsp_2(sK3,sK1,sK2)
% 2.00/0.99      | ~ r1_tarski(k1_tops_1(sK1,X0_44),sK3)
% 2.00/0.99      | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.00/0.99      | ~ r2_hidden(sK2,k1_tops_1(sK1,X0_44)) ),
% 2.00/0.99      inference(subtyping,[status(esa)],[c_510]) ).
% 2.00/0.99  
% 2.00/0.99  cnf(c_1936,plain,
% 2.00/0.99      ( ~ m1_connsp_2(sK3,sK1,sK2)
% 2.00/0.99      | ~ r1_tarski(k1_tops_1(sK1,k1_tops_1(sK1,sK3)),sK3)
% 2.00/0.99      | ~ m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.00/0.99      | ~ r2_hidden(sK2,k1_tops_1(sK1,k1_tops_1(sK1,sK3))) ),
% 2.00/0.99      inference(instantiation,[status(thm)],[c_1261]) ).
% 2.00/0.99  
% 2.00/0.99  cnf(c_1429,plain,
% 2.00/0.99      ( m1_connsp_2(k1_tops_1(sK1,sK3),sK1,X0_44)
% 2.00/0.99      | ~ m1_subset_1(X0_44,u1_struct_0(sK1))
% 2.00/0.99      | ~ m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.00/0.99      | ~ r2_hidden(X0_44,k1_tops_1(sK1,k1_tops_1(sK1,sK3))) ),
% 2.00/0.99      inference(instantiation,[status(thm)],[c_1265]) ).
% 2.00/0.99  
% 2.00/0.99  cnf(c_1933,plain,
% 2.00/0.99      ( m1_connsp_2(k1_tops_1(sK1,sK3),sK1,sK0(u1_struct_0(sK1),k1_tops_1(sK1,k1_tops_1(sK1,sK3)),sK3))
% 2.00/0.99      | ~ m1_subset_1(sK0(u1_struct_0(sK1),k1_tops_1(sK1,k1_tops_1(sK1,sK3)),sK3),u1_struct_0(sK1))
% 2.00/0.99      | ~ m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.00/0.99      | ~ r2_hidden(sK0(u1_struct_0(sK1),k1_tops_1(sK1,k1_tops_1(sK1,sK3)),sK3),k1_tops_1(sK1,k1_tops_1(sK1,sK3))) ),
% 2.00/0.99      inference(instantiation,[status(thm)],[c_1429]) ).
% 2.00/0.99  
% 2.00/0.99  cnf(c_1,plain,
% 2.00/0.99      ( r1_tarski(X0,X1)
% 2.00/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(X2))
% 2.00/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 2.00/0.99      | ~ r2_hidden(sK0(X2,X0,X1),X1) ),
% 2.00/0.99      inference(cnf_transformation,[],[f44]) ).
% 2.00/0.99  
% 2.00/0.99  cnf(c_1279,plain,
% 2.00/0.99      ( r1_tarski(X0_44,X1_44)
% 2.00/0.99      | ~ m1_subset_1(X0_44,k1_zfmisc_1(X2_44))
% 2.00/0.99      | ~ m1_subset_1(X1_44,k1_zfmisc_1(X2_44))
% 2.00/0.99      | ~ r2_hidden(sK0(X2_44,X0_44,X1_44),X1_44) ),
% 2.00/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 2.00/0.99  
% 2.00/0.99  cnf(c_1588,plain,
% 2.00/0.99      ( r1_tarski(k1_tops_1(sK1,k1_tops_1(sK1,sK3)),X0_44)
% 2.00/0.99      | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.00/0.99      | ~ m1_subset_1(k1_tops_1(sK1,k1_tops_1(sK1,sK3)),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.00/0.99      | ~ r2_hidden(sK0(u1_struct_0(sK1),k1_tops_1(sK1,k1_tops_1(sK1,sK3)),X0_44),X0_44) ),
% 2.00/0.99      inference(instantiation,[status(thm)],[c_1279]) ).
% 2.00/0.99  
% 2.00/0.99  cnf(c_1905,plain,
% 2.00/0.99      ( r1_tarski(k1_tops_1(sK1,k1_tops_1(sK1,sK3)),sK3)
% 2.00/0.99      | ~ m1_subset_1(k1_tops_1(sK1,k1_tops_1(sK1,sK3)),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.00/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.00/0.99      | ~ r2_hidden(sK0(u1_struct_0(sK1),k1_tops_1(sK1,k1_tops_1(sK1,sK3)),sK3),sK3) ),
% 2.00/0.99      inference(instantiation,[status(thm)],[c_1588]) ).
% 2.00/0.99  
% 2.00/0.99  cnf(c_3,plain,
% 2.00/0.99      ( r1_tarski(X0,X1)
% 2.00/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(X2))
% 2.00/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 2.00/0.99      | m1_subset_1(sK0(X2,X0,X1),X2) ),
% 2.00/0.99      inference(cnf_transformation,[],[f42]) ).
% 2.00/0.99  
% 2.00/0.99  cnf(c_1277,plain,
% 2.00/0.99      ( r1_tarski(X0_44,X1_44)
% 2.00/0.99      | ~ m1_subset_1(X0_44,k1_zfmisc_1(X2_44))
% 2.00/0.99      | ~ m1_subset_1(X1_44,k1_zfmisc_1(X2_44))
% 2.00/0.99      | m1_subset_1(sK0(X2_44,X0_44,X1_44),X2_44) ),
% 2.00/0.99      inference(subtyping,[status(esa)],[c_3]) ).
% 2.00/0.99  
% 2.00/0.99  cnf(c_1590,plain,
% 2.00/0.99      ( r1_tarski(k1_tops_1(sK1,k1_tops_1(sK1,sK3)),X0_44)
% 2.00/0.99      | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.00/0.99      | m1_subset_1(sK0(u1_struct_0(sK1),k1_tops_1(sK1,k1_tops_1(sK1,sK3)),X0_44),u1_struct_0(sK1))
% 2.00/0.99      | ~ m1_subset_1(k1_tops_1(sK1,k1_tops_1(sK1,sK3)),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.00/0.99      inference(instantiation,[status(thm)],[c_1277]) ).
% 2.00/0.99  
% 2.00/0.99  cnf(c_1893,plain,
% 2.00/0.99      ( r1_tarski(k1_tops_1(sK1,k1_tops_1(sK1,sK3)),sK3)
% 2.00/0.99      | m1_subset_1(sK0(u1_struct_0(sK1),k1_tops_1(sK1,k1_tops_1(sK1,sK3)),sK3),u1_struct_0(sK1))
% 2.00/0.99      | ~ m1_subset_1(k1_tops_1(sK1,k1_tops_1(sK1,sK3)),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.00/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.00/0.99      inference(instantiation,[status(thm)],[c_1590]) ).
% 2.00/0.99  
% 2.00/0.99  cnf(c_2,plain,
% 2.00/0.99      ( r1_tarski(X0,X1)
% 2.00/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(X2))
% 2.00/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 2.00/0.99      | r2_hidden(sK0(X2,X0,X1),X0) ),
% 2.00/0.99      inference(cnf_transformation,[],[f43]) ).
% 2.00/0.99  
% 2.00/0.99  cnf(c_1278,plain,
% 2.00/0.99      ( r1_tarski(X0_44,X1_44)
% 2.00/0.99      | ~ m1_subset_1(X0_44,k1_zfmisc_1(X2_44))
% 2.00/0.99      | ~ m1_subset_1(X1_44,k1_zfmisc_1(X2_44))
% 2.00/0.99      | r2_hidden(sK0(X2_44,X0_44,X1_44),X0_44) ),
% 2.00/0.99      inference(subtyping,[status(esa)],[c_2]) ).
% 2.00/0.99  
% 2.00/0.99  cnf(c_1589,plain,
% 2.00/0.99      ( r1_tarski(k1_tops_1(sK1,k1_tops_1(sK1,sK3)),X0_44)
% 2.00/0.99      | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.00/0.99      | ~ m1_subset_1(k1_tops_1(sK1,k1_tops_1(sK1,sK3)),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.00/0.99      | r2_hidden(sK0(u1_struct_0(sK1),k1_tops_1(sK1,k1_tops_1(sK1,sK3)),X0_44),k1_tops_1(sK1,k1_tops_1(sK1,sK3))) ),
% 2.00/0.99      inference(instantiation,[status(thm)],[c_1278]) ).
% 2.00/0.99  
% 2.00/0.99  cnf(c_1881,plain,
% 2.00/0.99      ( r1_tarski(k1_tops_1(sK1,k1_tops_1(sK1,sK3)),sK3)
% 2.00/0.99      | ~ m1_subset_1(k1_tops_1(sK1,k1_tops_1(sK1,sK3)),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.00/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.00/0.99      | r2_hidden(sK0(u1_struct_0(sK1),k1_tops_1(sK1,k1_tops_1(sK1,sK3)),sK3),k1_tops_1(sK1,k1_tops_1(sK1,sK3))) ),
% 2.00/0.99      inference(instantiation,[status(thm)],[c_1589]) ).
% 2.00/0.99  
% 2.00/0.99  cnf(c_1444,plain,
% 2.00/0.99      ( r1_tarski(k1_tops_1(sK1,sK3),X0_44)
% 2.00/0.99      | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.00/0.99      | ~ m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.00/0.99      | ~ r2_hidden(sK0(u1_struct_0(sK1),k1_tops_1(sK1,sK3),X0_44),X0_44) ),
% 2.00/0.99      inference(instantiation,[status(thm)],[c_1279]) ).
% 2.00/0.99  
% 2.00/0.99  cnf(c_1835,plain,
% 2.00/0.99      ( r1_tarski(k1_tops_1(sK1,sK3),k1_tops_1(sK1,sK3))
% 2.00/0.99      | ~ m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.00/0.99      | ~ r2_hidden(sK0(u1_struct_0(sK1),k1_tops_1(sK1,sK3),k1_tops_1(sK1,sK3)),k1_tops_1(sK1,sK3)) ),
% 2.00/0.99      inference(instantiation,[status(thm)],[c_1444]) ).
% 2.00/0.99  
% 2.00/0.99  cnf(c_8,plain,
% 2.00/0.99      ( ~ v3_pre_topc(X0,X1)
% 2.00/0.99      | ~ r1_tarski(X0,X2)
% 2.00/0.99      | r1_tarski(X0,k1_tops_1(X1,X2))
% 2.00/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.00/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.00/0.99      | ~ l1_pre_topc(X1) ),
% 2.00/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.00/0.99  
% 2.00/0.99  cnf(c_418,plain,
% 2.00/0.99      ( ~ v3_pre_topc(X0,sK1)
% 2.00/0.99      | ~ r1_tarski(X0,X1)
% 2.00/0.99      | r1_tarski(X0,k1_tops_1(sK1,X1))
% 2.00/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.00/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.00/0.99      inference(resolution,[status(thm)],[c_8,c_20]) ).
% 2.00/0.99  
% 2.00/0.99  cnf(c_482,plain,
% 2.00/0.99      ( ~ r1_tarski(k1_tops_1(sK1,X0),X1)
% 2.00/0.99      | r1_tarski(k1_tops_1(sK1,X0),k1_tops_1(sK1,X1))
% 2.00/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.00/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.00/0.99      | ~ m1_subset_1(k1_tops_1(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.00/0.99      inference(resolution,[status(thm)],[c_418,c_403]) ).
% 2.00/0.99  
% 2.00/0.99  cnf(c_486,plain,
% 2.00/0.99      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.00/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.00/0.99      | r1_tarski(k1_tops_1(sK1,X0),k1_tops_1(sK1,X1))
% 2.00/0.99      | ~ r1_tarski(k1_tops_1(sK1,X0),X1) ),
% 2.00/0.99      inference(global_propositional_subsumption,
% 2.00/0.99                [status(thm)],
% 2.00/0.99                [c_482,c_438]) ).
% 2.00/0.99  
% 2.00/0.99  cnf(c_487,plain,
% 2.00/0.99      ( ~ r1_tarski(k1_tops_1(sK1,X0),X1)
% 2.00/0.99      | r1_tarski(k1_tops_1(sK1,X0),k1_tops_1(sK1,X1))
% 2.00/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.00/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.00/0.99      inference(renaming,[status(thm)],[c_486]) ).
% 2.00/0.99  
% 2.00/0.99  cnf(c_1262,plain,
% 2.00/0.99      ( ~ r1_tarski(k1_tops_1(sK1,X0_44),X1_44)
% 2.00/0.99      | r1_tarski(k1_tops_1(sK1,X0_44),k1_tops_1(sK1,X1_44))
% 2.00/0.99      | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.00/0.99      | ~ m1_subset_1(X1_44,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.00/0.99      inference(subtyping,[status(esa)],[c_487]) ).
% 2.00/0.99  
% 2.00/0.99  cnf(c_1397,plain,
% 2.00/0.99      ( ~ r1_tarski(k1_tops_1(sK1,sK3),X0_44)
% 2.00/0.99      | r1_tarski(k1_tops_1(sK1,sK3),k1_tops_1(sK1,X0_44))
% 2.00/0.99      | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.00/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.00/0.99      inference(instantiation,[status(thm)],[c_1262]) ).
% 2.00/0.99  
% 2.00/0.99  cnf(c_1803,plain,
% 2.00/0.99      ( r1_tarski(k1_tops_1(sK1,sK3),k1_tops_1(sK1,k1_tops_1(sK1,sK3)))
% 2.00/0.99      | ~ r1_tarski(k1_tops_1(sK1,sK3),k1_tops_1(sK1,sK3))
% 2.00/0.99      | ~ m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.00/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.00/0.99      inference(instantiation,[status(thm)],[c_1397]) ).
% 2.00/0.99  
% 2.00/0.99  cnf(c_1445,plain,
% 2.00/0.99      ( r1_tarski(k1_tops_1(sK1,sK3),X0_44)
% 2.00/0.99      | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.00/0.99      | ~ m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.00/0.99      | r2_hidden(sK0(u1_struct_0(sK1),k1_tops_1(sK1,sK3),X0_44),k1_tops_1(sK1,sK3)) ),
% 2.00/0.99      inference(instantiation,[status(thm)],[c_1278]) ).
% 2.00/0.99  
% 2.00/0.99  cnf(c_1640,plain,
% 2.00/0.99      ( r1_tarski(k1_tops_1(sK1,sK3),k1_tops_1(sK1,sK3))
% 2.00/0.99      | ~ m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.00/0.99      | r2_hidden(sK0(u1_struct_0(sK1),k1_tops_1(sK1,sK3),k1_tops_1(sK1,sK3)),k1_tops_1(sK1,sK3)) ),
% 2.00/0.99      inference(instantiation,[status(thm)],[c_1445]) ).
% 2.00/0.99  
% 2.00/0.99  cnf(c_16,negated_conjecture,
% 2.00/0.99      ( m1_connsp_2(sK3,sK1,sK2) | v3_pre_topc(sK4,sK1) ),
% 2.00/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.00/0.99  
% 2.00/0.99  cnf(c_458,plain,
% 2.00/0.99      ( m1_connsp_2(sK3,sK1,sK2)
% 2.00/0.99      | ~ r1_tarski(sK4,X0)
% 2.00/0.99      | r1_tarski(sK4,k1_tops_1(sK1,X0))
% 2.00/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.00/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.00/0.99      inference(resolution,[status(thm)],[c_418,c_16]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_17,negated_conjecture,
% 2.00/1.00      ( m1_connsp_2(sK3,sK1,sK2)
% 2.00/1.00      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.00/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_462,plain,
% 2.00/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.00/1.00      | r1_tarski(sK4,k1_tops_1(sK1,X0))
% 2.00/1.00      | ~ r1_tarski(sK4,X0)
% 2.00/1.00      | m1_connsp_2(sK3,sK1,sK2) ),
% 2.00/1.00      inference(global_propositional_subsumption,
% 2.00/1.00                [status(thm)],
% 2.00/1.00                [c_458,c_17]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_463,plain,
% 2.00/1.00      ( m1_connsp_2(sK3,sK1,sK2)
% 2.00/1.00      | ~ r1_tarski(sK4,X0)
% 2.00/1.00      | r1_tarski(sK4,k1_tops_1(sK1,X0))
% 2.00/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.00/1.00      inference(renaming,[status(thm)],[c_462]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_1263,plain,
% 2.00/1.00      ( m1_connsp_2(sK3,sK1,sK2)
% 2.00/1.00      | ~ r1_tarski(sK4,X0_44)
% 2.00/1.00      | r1_tarski(sK4,k1_tops_1(sK1,X0_44))
% 2.00/1.00      | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.00/1.00      inference(subtyping,[status(esa)],[c_463]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_1551,plain,
% 2.00/1.00      ( m1_connsp_2(sK3,sK1,sK2)
% 2.00/1.00      | r1_tarski(sK4,k1_tops_1(sK1,sK3))
% 2.00/1.00      | ~ r1_tarski(sK4,sK3)
% 2.00/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.00/1.00      inference(instantiation,[status(thm)],[c_1263]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_1264,plain,
% 2.00/1.00      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.00/1.00      | m1_subset_1(k1_tops_1(sK1,X0_44),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.00/1.00      inference(subtyping,[status(esa)],[c_438]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_1430,plain,
% 2.00/1.00      ( m1_subset_1(k1_tops_1(sK1,k1_tops_1(sK1,sK3)),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.00/1.00      | ~ m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.00/1.00      inference(instantiation,[status(thm)],[c_1264]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_1394,plain,
% 2.00/1.00      ( m1_connsp_2(sK3,sK1,sK2)
% 2.00/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.00/1.00      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 2.00/1.00      | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
% 2.00/1.00      inference(instantiation,[status(thm)],[c_1392]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_10,plain,
% 2.00/1.00      ( ~ m1_connsp_2(X0,X1,X2)
% 2.00/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.00/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.00/1.00      | r2_hidden(X2,k1_tops_1(X1,X0))
% 2.00/1.00      | v2_struct_0(X1)
% 2.00/1.00      | ~ v2_pre_topc(X1)
% 2.00/1.00      | ~ l1_pre_topc(X1) ),
% 2.00/1.00      inference(cnf_transformation,[],[f50]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_131,plain,
% 2.00/1.00      ( ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.00/1.00      | ~ m1_connsp_2(X0,X1,X2)
% 2.00/1.00      | r2_hidden(X2,k1_tops_1(X1,X0))
% 2.00/1.00      | v2_struct_0(X1)
% 2.00/1.00      | ~ v2_pre_topc(X1)
% 2.00/1.00      | ~ l1_pre_topc(X1) ),
% 2.00/1.00      inference(global_propositional_subsumption,
% 2.00/1.00                [status(thm)],
% 2.00/1.00                [c_10,c_11]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_132,plain,
% 2.00/1.00      ( ~ m1_connsp_2(X0,X1,X2)
% 2.00/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.00/1.00      | r2_hidden(X2,k1_tops_1(X1,X0))
% 2.00/1.00      | v2_struct_0(X1)
% 2.00/1.00      | ~ v2_pre_topc(X1)
% 2.00/1.00      | ~ l1_pre_topc(X1) ),
% 2.00/1.00      inference(renaming,[status(thm)],[c_131]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_298,plain,
% 2.00/1.00      ( ~ m1_connsp_2(X0,sK1,X1)
% 2.00/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.00/1.00      | r2_hidden(X1,k1_tops_1(sK1,X0))
% 2.00/1.00      | ~ v2_pre_topc(sK1)
% 2.00/1.00      | ~ l1_pre_topc(sK1) ),
% 2.00/1.00      inference(resolution,[status(thm)],[c_132,c_22]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_302,plain,
% 2.00/1.00      ( ~ m1_connsp_2(X0,sK1,X1)
% 2.00/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.00/1.00      | r2_hidden(X1,k1_tops_1(sK1,X0)) ),
% 2.00/1.00      inference(global_propositional_subsumption,
% 2.00/1.00                [status(thm)],
% 2.00/1.00                [c_298,c_21,c_20]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_1268,plain,
% 2.00/1.00      ( ~ m1_connsp_2(X0_44,sK1,X1_44)
% 2.00/1.00      | ~ m1_subset_1(X1_44,u1_struct_0(sK1))
% 2.00/1.00      | r2_hidden(X1_44,k1_tops_1(sK1,X0_44)) ),
% 2.00/1.00      inference(subtyping,[status(esa)],[c_302]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_1389,plain,
% 2.00/1.00      ( ~ m1_connsp_2(sK3,sK1,sK2)
% 2.00/1.00      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 2.00/1.00      | r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
% 2.00/1.00      inference(instantiation,[status(thm)],[c_1268]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_1382,plain,
% 2.00/1.00      ( m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.00/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.00/1.00      inference(instantiation,[status(thm)],[c_1264]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_14,negated_conjecture,
% 2.00/1.00      ( m1_connsp_2(sK3,sK1,sK2) | r2_hidden(sK2,sK4) ),
% 2.00/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_751,plain,
% 2.00/1.00      ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 2.00/1.00      | r2_hidden(sK2,k1_tops_1(sK1,sK3))
% 2.00/1.00      | r2_hidden(sK2,sK4) ),
% 2.00/1.00      inference(resolution,[status(thm)],[c_14,c_302]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_19,negated_conjecture,
% 2.00/1.00      ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 2.00/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_753,plain,
% 2.00/1.00      ( r2_hidden(sK2,k1_tops_1(sK1,sK3)) | r2_hidden(sK2,sK4) ),
% 2.00/1.00      inference(global_propositional_subsumption,
% 2.00/1.00                [status(thm)],
% 2.00/1.00                [c_751,c_19]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_15,negated_conjecture,
% 2.00/1.00      ( m1_connsp_2(sK3,sK1,sK2) | r1_tarski(sK4,sK3) ),
% 2.00/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_724,plain,
% 2.00/1.00      ( r1_tarski(sK4,sK3)
% 2.00/1.00      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 2.00/1.00      | r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
% 2.00/1.00      inference(resolution,[status(thm)],[c_15,c_302]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_726,plain,
% 2.00/1.00      ( r1_tarski(sK4,sK3) | r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
% 2.00/1.00      inference(global_propositional_subsumption,
% 2.00/1.00                [status(thm)],
% 2.00/1.00                [c_724,c_19]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_18,negated_conjecture,
% 2.00/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.00/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(contradiction,plain,
% 2.00/1.00      ( $false ),
% 2.00/1.00      inference(minisat,
% 2.00/1.00                [status(thm)],
% 2.00/1.00                [c_3262,c_2510,c_2363,c_2334,c_2135,c_1936,c_1933,c_1905,
% 2.00/1.00                 c_1893,c_1881,c_1835,c_1803,c_1640,c_1551,c_1430,c_1394,
% 2.00/1.00                 c_1389,c_1382,c_753,c_726,c_18,c_19]) ).
% 2.00/1.00  
% 2.00/1.00  
% 2.00/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.00/1.00  
% 2.00/1.00  ------                               Statistics
% 2.00/1.00  
% 2.00/1.00  ------ General
% 2.00/1.00  
% 2.00/1.00  abstr_ref_over_cycles:                  0
% 2.00/1.00  abstr_ref_under_cycles:                 0
% 2.00/1.00  gc_basic_clause_elim:                   0
% 2.00/1.00  forced_gc_time:                         0
% 2.00/1.00  parsing_time:                           0.01
% 2.00/1.00  unif_index_cands_time:                  0.
% 2.00/1.00  unif_index_add_time:                    0.
% 2.00/1.00  orderings_time:                         0.
% 2.00/1.00  out_proof_time:                         0.02
% 2.00/1.00  total_time:                             0.103
% 2.00/1.00  num_of_symbols:                         46
% 2.00/1.00  num_of_terms:                           2692
% 2.00/1.00  
% 2.00/1.00  ------ Preprocessing
% 2.00/1.00  
% 2.00/1.00  num_of_splits:                          0
% 2.00/1.00  num_of_split_atoms:                     0
% 2.00/1.00  num_of_reused_defs:                     0
% 2.00/1.00  num_eq_ax_congr_red:                    0
% 2.00/1.00  num_of_sem_filtered_clauses:            0
% 2.00/1.00  num_of_subtypes:                        2
% 2.00/1.00  monotx_restored_types:                  0
% 2.00/1.00  sat_num_of_epr_types:                   0
% 2.00/1.00  sat_num_of_non_cyclic_types:            0
% 2.00/1.00  sat_guarded_non_collapsed_types:        0
% 2.00/1.00  num_pure_diseq_elim:                    0
% 2.00/1.00  simp_replaced_by:                       0
% 2.00/1.00  res_preprocessed:                       42
% 2.00/1.00  prep_upred:                             0
% 2.00/1.00  prep_unflattend:                        0
% 2.00/1.00  smt_new_axioms:                         0
% 2.00/1.00  pred_elim_cands:                        4
% 2.00/1.00  pred_elim:                              4
% 2.00/1.00  pred_elim_cl:                           4
% 2.00/1.00  pred_elim_cycles:                       6
% 2.00/1.00  merged_defs:                            4
% 2.00/1.00  merged_defs_ncl:                        0
% 2.00/1.00  bin_hyper_res:                          5
% 2.00/1.00  prep_cycles:                            2
% 2.00/1.00  pred_elim_time:                         0.009
% 2.00/1.00  splitting_time:                         0.
% 2.00/1.00  sem_filter_time:                        0.
% 2.00/1.00  monotx_time:                            0.
% 2.00/1.00  subtype_inf_time:                       0.
% 2.00/1.00  
% 2.00/1.00  ------ Problem properties
% 2.00/1.00  
% 2.00/1.00  clauses:                                19
% 2.00/1.00  conjectures:                            5
% 2.00/1.00  epr:                                    3
% 2.00/1.00  horn:                                   13
% 2.00/1.00  ground:                                 5
% 2.00/1.00  unary:                                  2
% 2.00/1.00  binary:                                 6
% 2.00/1.00  lits:                                   54
% 2.00/1.00  lits_eq:                                0
% 2.00/1.00  fd_pure:                                0
% 2.00/1.00  fd_pseudo:                              0
% 2.00/1.00  fd_cond:                                0
% 2.00/1.00  fd_pseudo_cond:                         0
% 2.00/1.00  ac_symbols:                             0
% 2.00/1.00  
% 2.00/1.00  ------ Propositional Solver
% 2.00/1.00  
% 2.00/1.00  prop_solver_calls:                      18
% 2.00/1.00  prop_fast_solver_calls:                 505
% 2.00/1.00  smt_solver_calls:                       0
% 2.00/1.00  smt_fast_solver_calls:                  0
% 2.00/1.00  prop_num_of_clauses:                    1264
% 2.00/1.00  prop_preprocess_simplified:             3156
% 2.00/1.00  prop_fo_subsumed:                       34
% 2.00/1.00  prop_solver_time:                       0.
% 2.00/1.00  smt_solver_time:                        0.
% 2.00/1.00  smt_fast_solver_time:                   0.
% 2.00/1.00  prop_fast_solver_time:                  0.
% 2.00/1.00  prop_unsat_core_time:                   0.
% 2.00/1.00  
% 2.00/1.00  ------ QBF
% 2.00/1.00  
% 2.00/1.00  qbf_q_res:                              0
% 2.00/1.00  qbf_num_tautologies:                    0
% 2.00/1.00  qbf_prep_cycles:                        0
% 2.00/1.00  
% 2.00/1.00  ------ BMC1
% 2.00/1.00  
% 2.00/1.00  bmc1_current_bound:                     -1
% 2.00/1.00  bmc1_last_solved_bound:                 -1
% 2.00/1.00  bmc1_unsat_core_size:                   -1
% 2.00/1.00  bmc1_unsat_core_parents_size:           -1
% 2.00/1.00  bmc1_merge_next_fun:                    0
% 2.00/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.00/1.00  
% 2.00/1.00  ------ Instantiation
% 2.00/1.00  
% 2.00/1.00  inst_num_of_clauses:                    414
% 2.00/1.00  inst_num_in_passive:                    118
% 2.00/1.00  inst_num_in_active:                     233
% 2.00/1.00  inst_num_in_unprocessed:                62
% 2.00/1.00  inst_num_of_loops:                      311
% 2.00/1.00  inst_num_of_learning_restarts:          0
% 2.00/1.00  inst_num_moves_active_passive:          75
% 2.00/1.00  inst_lit_activity:                      0
% 2.00/1.00  inst_lit_activity_moves:                0
% 2.00/1.00  inst_num_tautologies:                   0
% 2.00/1.00  inst_num_prop_implied:                  0
% 2.00/1.00  inst_num_existing_simplified:           0
% 2.00/1.00  inst_num_eq_res_simplified:             0
% 2.00/1.00  inst_num_child_elim:                    0
% 2.00/1.00  inst_num_of_dismatching_blockings:      0
% 2.00/1.00  inst_num_of_non_proper_insts:           330
% 2.00/1.00  inst_num_of_duplicates:                 0
% 2.00/1.00  inst_inst_num_from_inst_to_res:         0
% 2.00/1.00  inst_dismatching_checking_time:         0.
% 2.00/1.00  
% 2.00/1.00  ------ Resolution
% 2.00/1.00  
% 2.00/1.00  res_num_of_clauses:                     0
% 2.00/1.00  res_num_in_passive:                     0
% 2.00/1.00  res_num_in_active:                      0
% 2.00/1.00  res_num_of_loops:                       44
% 2.00/1.00  res_forward_subset_subsumed:            22
% 2.00/1.00  res_backward_subset_subsumed:           0
% 2.00/1.00  res_forward_subsumed:                   0
% 2.00/1.00  res_backward_subsumed:                  0
% 2.00/1.00  res_forward_subsumption_resolution:     0
% 2.00/1.00  res_backward_subsumption_resolution:    0
% 2.00/1.00  res_clause_to_clause_subsumption:       142
% 2.00/1.00  res_orphan_elimination:                 0
% 2.00/1.00  res_tautology_del:                      31
% 2.00/1.00  res_num_eq_res_simplified:              0
% 2.00/1.00  res_num_sel_changes:                    0
% 2.00/1.00  res_moves_from_active_to_pass:          0
% 2.00/1.00  
% 2.00/1.00  ------ Superposition
% 2.00/1.00  
% 2.00/1.00  sup_time_total:                         0.
% 2.00/1.00  sup_time_generating:                    0.
% 2.00/1.00  sup_time_sim_full:                      0.
% 2.00/1.00  sup_time_sim_immed:                     0.
% 2.00/1.00  
% 2.00/1.00  sup_num_of_clauses:                     0
% 2.00/1.00  sup_num_in_active:                      0
% 2.00/1.00  sup_num_in_passive:                     0
% 2.00/1.00  sup_num_of_loops:                       0
% 2.00/1.00  sup_fw_superposition:                   0
% 2.00/1.00  sup_bw_superposition:                   0
% 2.00/1.00  sup_immediate_simplified:               0
% 2.00/1.00  sup_given_eliminated:                   0
% 2.00/1.00  comparisons_done:                       0
% 2.00/1.00  comparisons_avoided:                    0
% 2.00/1.00  
% 2.00/1.00  ------ Simplifications
% 2.00/1.00  
% 2.00/1.00  
% 2.00/1.00  sim_fw_subset_subsumed:                 0
% 2.00/1.00  sim_bw_subset_subsumed:                 0
% 2.00/1.00  sim_fw_subsumed:                        0
% 2.00/1.00  sim_bw_subsumed:                        0
% 2.00/1.00  sim_fw_subsumption_res:                 0
% 2.00/1.00  sim_bw_subsumption_res:                 0
% 2.00/1.00  sim_tautology_del:                      0
% 2.00/1.00  sim_eq_tautology_del:                   0
% 2.00/1.00  sim_eq_res_simp:                        0
% 2.00/1.00  sim_fw_demodulated:                     0
% 2.00/1.00  sim_bw_demodulated:                     0
% 2.00/1.00  sim_light_normalised:                   0
% 2.00/1.00  sim_joinable_taut:                      0
% 2.00/1.00  sim_joinable_simp:                      0
% 2.00/1.00  sim_ac_normalised:                      0
% 2.00/1.00  sim_smt_subsumption:                    0
% 2.00/1.00  
%------------------------------------------------------------------------------
