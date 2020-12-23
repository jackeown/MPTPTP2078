%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:16:46 EST 2020

% Result     : Theorem 1.21s
% Output     : CNFRefutation 1.21s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 926 expanded)
%              Number of clauses        :   81 ( 249 expanded)
%              Number of leaves         :   13 ( 296 expanded)
%              Depth                    :   21
%              Number of atoms          :  480 (5397 expanded)
%              Number of equality atoms :  125 ( 867 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v1_tops_2(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
                   => ( X1 = X3
                     => v1_tops_2(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ! [X2] :
                ( m1_pre_topc(X2,X0)
               => ( v1_tops_2(X1,X0)
                 => ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
                     => ( X1 = X3
                       => v1_tops_2(X3,X2) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v1_tops_2(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
              & v1_tops_2(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v1_tops_2(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
              & v1_tops_2(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f29,plain,(
    ! [X2,X1] :
      ( ? [X3] :
          ( ~ v1_tops_2(X3,X2)
          & X1 = X3
          & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
     => ( ~ v1_tops_2(sK5,X2)
        & sK5 = X1
        & m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ v1_tops_2(X3,X2)
              & X1 = X3
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
          & v1_tops_2(X1,X0)
          & m1_pre_topc(X2,X0) )
     => ( ? [X3] :
            ( ~ v1_tops_2(X3,sK4)
            & X1 = X3
            & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) )
        & v1_tops_2(X1,X0)
        & m1_pre_topc(sK4,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v1_tops_2(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
              & v1_tops_2(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ v1_tops_2(X3,X2)
                & sK3 = X3
                & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
            & v1_tops_2(sK3,X0)
            & m1_pre_topc(X2,X0) )
        & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ v1_tops_2(X3,X2)
                    & X1 = X3
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
                & v1_tops_2(X1,X0)
                & m1_pre_topc(X2,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v1_tops_2(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
              & v1_tops_2(X1,sK2)
              & m1_pre_topc(X2,sK2) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) )
      & l1_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ~ v1_tops_2(sK5,sK4)
    & sK3 = sK5
    & m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    & v1_tops_2(sK3,sK2)
    & m1_pre_topc(sK4,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    & l1_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f16,f29,f28,f27,f26])).

fof(f48,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) ),
    inference(cnf_transformation,[],[f30])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ? [X2] :
                  ( ~ v3_pre_topc(X2,X0)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v3_pre_topc(X2,X0)
                  | ~ r2_hidden(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ? [X2] :
                  ( ~ v3_pre_topc(X2,X0)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f22])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v3_pre_topc(X2,X0)
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK1(X0,X1),X0)
        & r2_hidden(sK1(X0,X1),X1)
        & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ( ~ v3_pre_topc(sK1(X0,X1),X0)
                & r2_hidden(sK1(X0,X1),X1)
                & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f23,f24])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,X0)
      | r2_hidden(sK1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f38,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f46,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f44,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f50,plain,(
    ~ v1_tops_2(sK5,sK4) ),
    inference(cnf_transformation,[],[f30])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f17])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK0(X0,X1),X0)
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( r1_tarski(sK0(X0,X1),X0)
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK0(X0,X1),X0)
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( r1_tarski(sK0(X0,X1),X0)
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).

fof(f31,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f52,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f31])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,X0)
      | m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v3_pre_topc(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( X1 = X3
                     => v3_pre_topc(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v3_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v3_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X3,X2)
      | X1 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f53,plain,(
    ! [X2,X0,X3] :
      ( v3_pre_topc(X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f43])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,X0)
      | ~ v3_pre_topc(sK1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f45,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f30])).

fof(f49,plain,(
    sK3 = sK5 ),
    inference(cnf_transformation,[],[f30])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( v3_pre_topc(X3,X0)
      | ~ r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f47,plain,(
    v1_tops_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1390,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_9,plain,
    ( v1_tops_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | r2_hidden(sK1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_17,negated_conjecture,
    ( m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_261,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK2 != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_17])).

cnf(c_262,plain,
    ( ~ l1_pre_topc(sK2)
    | l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_261])).

cnf(c_19,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_264,plain,
    ( l1_pre_topc(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_262,c_19])).

cnf(c_420,plain,
    ( v1_tops_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | r2_hidden(sK1(X1,X0),X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_264])).

cnf(c_421,plain,
    ( v1_tops_2(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | r2_hidden(sK1(sK4,X0),X0) ),
    inference(unflattening,[status(thm)],[c_420])).

cnf(c_1378,plain,
    ( v1_tops_2(X0,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top
    | r2_hidden(sK1(sK4,X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_421])).

cnf(c_1794,plain,
    ( v1_tops_2(sK5,sK4) = iProver_top
    | r2_hidden(sK1(sK4,sK5),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1390,c_1378])).

cnf(c_24,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_13,negated_conjecture,
    ( ~ v1_tops_2(sK5,sK4) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_638,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | r2_hidden(sK1(sK4,X0),X0)
    | sK4 != sK4
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_421])).

cnf(c_639,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | r2_hidden(sK1(sK4,sK5),sK5) ),
    inference(unflattening,[status(thm)],[c_638])).

cnf(c_640,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top
    | r2_hidden(sK1(sK4,sK5),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_639])).

cnf(c_2282,plain,
    ( r2_hidden(sK1(sK4,sK5),sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1794,c_24,c_640])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_5,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_145,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_5])).

cnf(c_146,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_145])).

cnf(c_189,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_4,c_146])).

cnf(c_1387,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_189])).

cnf(c_2647,plain,
    ( r2_hidden(sK1(sK4,sK5),X0) = iProver_top
    | r1_tarski(sK5,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2282,c_1387])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1394,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2676,plain,
    ( r1_tarski(sK1(sK4,sK5),X0) = iProver_top
    | r1_tarski(sK5,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2647,c_1394])).

cnf(c_10,plain,
    ( v1_tops_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | m1_subset_1(sK1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_405,plain,
    ( v1_tops_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | m1_subset_1(sK1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_264])).

cnf(c_406,plain,
    ( v1_tops_2(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | m1_subset_1(sK1(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(unflattening,[status(thm)],[c_405])).

cnf(c_1379,plain,
    ( v1_tops_2(X0,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top
    | m1_subset_1(sK1(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_406])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1392,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2435,plain,
    ( v1_tops_2(X0,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top
    | r1_tarski(sK1(sK4,X0),u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1379,c_1392])).

cnf(c_4051,plain,
    ( v1_tops_2(sK5,sK4) = iProver_top
    | r1_tarski(sK1(sK4,sK5),u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1390,c_2435])).

cnf(c_649,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | m1_subset_1(sK1(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | sK4 != sK4
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_406])).

cnf(c_650,plain,
    ( m1_subset_1(sK1(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) ),
    inference(unflattening,[status(thm)],[c_649])).

cnf(c_651,plain,
    ( m1_subset_1(sK1(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_650])).

cnf(c_1599,plain,
    ( ~ m1_subset_1(sK1(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_tarski(sK1(sK4,sK5),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1600,plain,
    ( m1_subset_1(sK1(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(sK1(sK4,sK5),u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1599])).

cnf(c_4067,plain,
    ( r1_tarski(sK1(sK4,sK5),u1_struct_0(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4051,c_24,c_651,c_1600])).

cnf(c_1393,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_12,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v3_pre_topc(X0,X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_272,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v3_pre_topc(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X1)
    | sK2 != X1
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_17])).

cnf(c_273,plain,
    ( ~ v3_pre_topc(X0,sK2)
    | v3_pre_topc(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_272])).

cnf(c_277,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v3_pre_topc(X0,sK4)
    | ~ v3_pre_topc(X0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_273,c_19])).

cnf(c_278,plain,
    ( ~ v3_pre_topc(X0,sK2)
    | v3_pre_topc(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(renaming,[status(thm)],[c_277])).

cnf(c_1386,plain,
    ( v3_pre_topc(X0,sK2) != iProver_top
    | v3_pre_topc(X0,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_278])).

cnf(c_1924,plain,
    ( v3_pre_topc(X0,sK2) != iProver_top
    | v3_pre_topc(X0,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1393,c_1386])).

cnf(c_2870,plain,
    ( v3_pre_topc(X0,sK2) != iProver_top
    | v3_pre_topc(X0,sK4) = iProver_top
    | r1_tarski(X0,u1_struct_0(sK2)) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1393,c_1924])).

cnf(c_4072,plain,
    ( v3_pre_topc(sK1(sK4,sK5),sK2) != iProver_top
    | v3_pre_topc(sK1(sK4,sK5),sK4) = iProver_top
    | r1_tarski(sK1(sK4,sK5),u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4067,c_2870])).

cnf(c_8,plain,
    ( ~ v3_pre_topc(sK1(X0,X1),X0)
    | v1_tops_2(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_318,plain,
    ( ~ v3_pre_topc(sK1(X0,X1),X0)
    | v1_tops_2(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_264])).

cnf(c_319,plain,
    ( ~ v3_pre_topc(sK1(sK4,X0),sK4)
    | v1_tops_2(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) ),
    inference(unflattening,[status(thm)],[c_318])).

cnf(c_660,plain,
    ( ~ v3_pre_topc(sK1(sK4,X0),sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | sK4 != sK4
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_319])).

cnf(c_661,plain,
    ( ~ v3_pre_topc(sK1(sK4,sK5),sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) ),
    inference(unflattening,[status(thm)],[c_660])).

cnf(c_662,plain,
    ( v3_pre_topc(sK1(sK4,sK5),sK4) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_661])).

cnf(c_1567,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | r1_tarski(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1568,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top
    | r1_tarski(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1567])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1388,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_14,negated_conjecture,
    ( sK3 = sK5 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1405,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1388,c_14])).

cnf(c_1800,plain,
    ( r1_tarski(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1405,c_1392])).

cnf(c_11,plain,
    ( v3_pre_topc(X0,X1)
    | ~ v1_tops_2(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ r2_hidden(X0,X2)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_333,plain,
    ( v3_pre_topc(X0,X1)
    | ~ v1_tops_2(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ r2_hidden(X0,X2)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_19])).

cnf(c_334,plain,
    ( v3_pre_topc(X0,sK2)
    | ~ v1_tops_2(X1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ r2_hidden(X0,X1) ),
    inference(unflattening,[status(thm)],[c_333])).

cnf(c_1383,plain,
    ( v3_pre_topc(X0,sK2) = iProver_top
    | v1_tops_2(X1,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_334])).

cnf(c_1703,plain,
    ( v3_pre_topc(X0,sK2) = iProver_top
    | v1_tops_2(sK5,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1405,c_1383])).

cnf(c_16,negated_conjecture,
    ( v1_tops_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1389,plain,
    ( v1_tops_2(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1400,plain,
    ( v1_tops_2(sK5,sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1389,c_14])).

cnf(c_2149,plain,
    ( v3_pre_topc(X0,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1703,c_1400])).

cnf(c_2158,plain,
    ( v3_pre_topc(X0,sK2) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1393,c_2149])).

cnf(c_3255,plain,
    ( v3_pre_topc(sK1(sK4,sK5),sK2) = iProver_top
    | r2_hidden(sK1(sK4,sK5),sK5) != iProver_top
    | r1_tarski(sK5,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2676,c_2158])).

cnf(c_3923,plain,
    ( v3_pre_topc(sK1(sK4,sK5),sK2) != iProver_top
    | v3_pre_topc(sK1(sK4,sK5),sK4) = iProver_top
    | r1_tarski(sK1(sK4,sK5),u1_struct_0(sK2)) != iProver_top
    | r1_tarski(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2676,c_2870])).

cnf(c_4250,plain,
    ( r1_tarski(sK1(sK4,sK5),u1_struct_0(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4072,c_24,c_640,c_662,c_1568,c_1800,c_3255,c_3923])).

cnf(c_4255,plain,
    ( r1_tarski(sK5,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2676,c_4250])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4255,c_1800])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:05:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 1.21/1.04  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.21/1.04  
% 1.21/1.04  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.21/1.04  
% 1.21/1.04  ------  iProver source info
% 1.21/1.04  
% 1.21/1.04  git: date: 2020-06-30 10:37:57 +0100
% 1.21/1.04  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.21/1.04  git: non_committed_changes: false
% 1.21/1.04  git: last_make_outside_of_git: false
% 1.21/1.04  
% 1.21/1.04  ------ 
% 1.21/1.04  
% 1.21/1.04  ------ Input Options
% 1.21/1.04  
% 1.21/1.04  --out_options                           all
% 1.21/1.04  --tptp_safe_out                         true
% 1.21/1.04  --problem_path                          ""
% 1.21/1.04  --include_path                          ""
% 1.21/1.04  --clausifier                            res/vclausify_rel
% 1.21/1.04  --clausifier_options                    --mode clausify
% 1.21/1.04  --stdin                                 false
% 1.21/1.04  --stats_out                             all
% 1.21/1.04  
% 1.21/1.04  ------ General Options
% 1.21/1.04  
% 1.21/1.04  --fof                                   false
% 1.21/1.04  --time_out_real                         305.
% 1.21/1.04  --time_out_virtual                      -1.
% 1.21/1.04  --symbol_type_check                     false
% 1.21/1.04  --clausify_out                          false
% 1.21/1.04  --sig_cnt_out                           false
% 1.21/1.04  --trig_cnt_out                          false
% 1.21/1.04  --trig_cnt_out_tolerance                1.
% 1.21/1.04  --trig_cnt_out_sk_spl                   false
% 1.21/1.04  --abstr_cl_out                          false
% 1.21/1.04  
% 1.21/1.04  ------ Global Options
% 1.21/1.04  
% 1.21/1.04  --schedule                              default
% 1.21/1.04  --add_important_lit                     false
% 1.21/1.04  --prop_solver_per_cl                    1000
% 1.21/1.04  --min_unsat_core                        false
% 1.21/1.04  --soft_assumptions                      false
% 1.21/1.04  --soft_lemma_size                       3
% 1.21/1.04  --prop_impl_unit_size                   0
% 1.21/1.04  --prop_impl_unit                        []
% 1.21/1.04  --share_sel_clauses                     true
% 1.21/1.04  --reset_solvers                         false
% 1.21/1.04  --bc_imp_inh                            [conj_cone]
% 1.21/1.04  --conj_cone_tolerance                   3.
% 1.21/1.04  --extra_neg_conj                        none
% 1.21/1.04  --large_theory_mode                     true
% 1.21/1.04  --prolific_symb_bound                   200
% 1.21/1.04  --lt_threshold                          2000
% 1.21/1.04  --clause_weak_htbl                      true
% 1.21/1.04  --gc_record_bc_elim                     false
% 1.21/1.05  
% 1.21/1.05  ------ Preprocessing Options
% 1.21/1.05  
% 1.21/1.05  --preprocessing_flag                    true
% 1.21/1.05  --time_out_prep_mult                    0.1
% 1.21/1.05  --splitting_mode                        input
% 1.21/1.05  --splitting_grd                         true
% 1.21/1.05  --splitting_cvd                         false
% 1.21/1.05  --splitting_cvd_svl                     false
% 1.21/1.05  --splitting_nvd                         32
% 1.21/1.05  --sub_typing                            true
% 1.21/1.05  --prep_gs_sim                           true
% 1.21/1.05  --prep_unflatten                        true
% 1.21/1.05  --prep_res_sim                          true
% 1.21/1.05  --prep_upred                            true
% 1.21/1.05  --prep_sem_filter                       exhaustive
% 1.21/1.05  --prep_sem_filter_out                   false
% 1.21/1.05  --pred_elim                             true
% 1.21/1.05  --res_sim_input                         true
% 1.21/1.05  --eq_ax_congr_red                       true
% 1.21/1.05  --pure_diseq_elim                       true
% 1.21/1.05  --brand_transform                       false
% 1.21/1.05  --non_eq_to_eq                          false
% 1.21/1.05  --prep_def_merge                        true
% 1.21/1.05  --prep_def_merge_prop_impl              false
% 1.21/1.05  --prep_def_merge_mbd                    true
% 1.21/1.05  --prep_def_merge_tr_red                 false
% 1.21/1.05  --prep_def_merge_tr_cl                  false
% 1.21/1.05  --smt_preprocessing                     true
% 1.21/1.05  --smt_ac_axioms                         fast
% 1.21/1.05  --preprocessed_out                      false
% 1.21/1.05  --preprocessed_stats                    false
% 1.21/1.05  
% 1.21/1.05  ------ Abstraction refinement Options
% 1.21/1.05  
% 1.21/1.05  --abstr_ref                             []
% 1.21/1.05  --abstr_ref_prep                        false
% 1.21/1.05  --abstr_ref_until_sat                   false
% 1.21/1.05  --abstr_ref_sig_restrict                funpre
% 1.21/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 1.21/1.05  --abstr_ref_under                       []
% 1.21/1.05  
% 1.21/1.05  ------ SAT Options
% 1.21/1.05  
% 1.21/1.05  --sat_mode                              false
% 1.21/1.05  --sat_fm_restart_options                ""
% 1.21/1.05  --sat_gr_def                            false
% 1.21/1.05  --sat_epr_types                         true
% 1.21/1.05  --sat_non_cyclic_types                  false
% 1.21/1.05  --sat_finite_models                     false
% 1.21/1.05  --sat_fm_lemmas                         false
% 1.21/1.05  --sat_fm_prep                           false
% 1.21/1.05  --sat_fm_uc_incr                        true
% 1.21/1.05  --sat_out_model                         small
% 1.21/1.05  --sat_out_clauses                       false
% 1.21/1.05  
% 1.21/1.05  ------ QBF Options
% 1.21/1.05  
% 1.21/1.05  --qbf_mode                              false
% 1.21/1.05  --qbf_elim_univ                         false
% 1.21/1.05  --qbf_dom_inst                          none
% 1.21/1.05  --qbf_dom_pre_inst                      false
% 1.21/1.05  --qbf_sk_in                             false
% 1.21/1.05  --qbf_pred_elim                         true
% 1.21/1.05  --qbf_split                             512
% 1.21/1.05  
% 1.21/1.05  ------ BMC1 Options
% 1.21/1.05  
% 1.21/1.05  --bmc1_incremental                      false
% 1.21/1.05  --bmc1_axioms                           reachable_all
% 1.21/1.05  --bmc1_min_bound                        0
% 1.21/1.05  --bmc1_max_bound                        -1
% 1.21/1.05  --bmc1_max_bound_default                -1
% 1.21/1.05  --bmc1_symbol_reachability              true
% 1.21/1.05  --bmc1_property_lemmas                  false
% 1.21/1.05  --bmc1_k_induction                      false
% 1.21/1.05  --bmc1_non_equiv_states                 false
% 1.21/1.05  --bmc1_deadlock                         false
% 1.21/1.05  --bmc1_ucm                              false
% 1.21/1.05  --bmc1_add_unsat_core                   none
% 1.21/1.05  --bmc1_unsat_core_children              false
% 1.21/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 1.21/1.05  --bmc1_out_stat                         full
% 1.21/1.05  --bmc1_ground_init                      false
% 1.21/1.05  --bmc1_pre_inst_next_state              false
% 1.21/1.05  --bmc1_pre_inst_state                   false
% 1.21/1.05  --bmc1_pre_inst_reach_state             false
% 1.21/1.05  --bmc1_out_unsat_core                   false
% 1.21/1.05  --bmc1_aig_witness_out                  false
% 1.21/1.05  --bmc1_verbose                          false
% 1.21/1.05  --bmc1_dump_clauses_tptp                false
% 1.21/1.05  --bmc1_dump_unsat_core_tptp             false
% 1.21/1.05  --bmc1_dump_file                        -
% 1.21/1.05  --bmc1_ucm_expand_uc_limit              128
% 1.21/1.05  --bmc1_ucm_n_expand_iterations          6
% 1.21/1.05  --bmc1_ucm_extend_mode                  1
% 1.21/1.05  --bmc1_ucm_init_mode                    2
% 1.21/1.05  --bmc1_ucm_cone_mode                    none
% 1.21/1.05  --bmc1_ucm_reduced_relation_type        0
% 1.21/1.05  --bmc1_ucm_relax_model                  4
% 1.21/1.05  --bmc1_ucm_full_tr_after_sat            true
% 1.21/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 1.21/1.05  --bmc1_ucm_layered_model                none
% 1.21/1.05  --bmc1_ucm_max_lemma_size               10
% 1.21/1.05  
% 1.21/1.05  ------ AIG Options
% 1.21/1.05  
% 1.21/1.05  --aig_mode                              false
% 1.21/1.05  
% 1.21/1.05  ------ Instantiation Options
% 1.21/1.05  
% 1.21/1.05  --instantiation_flag                    true
% 1.21/1.05  --inst_sos_flag                         false
% 1.21/1.05  --inst_sos_phase                        true
% 1.21/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.21/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.21/1.05  --inst_lit_sel_side                     num_symb
% 1.21/1.05  --inst_solver_per_active                1400
% 1.21/1.05  --inst_solver_calls_frac                1.
% 1.21/1.05  --inst_passive_queue_type               priority_queues
% 1.21/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.21/1.05  --inst_passive_queues_freq              [25;2]
% 1.21/1.05  --inst_dismatching                      true
% 1.21/1.05  --inst_eager_unprocessed_to_passive     true
% 1.21/1.05  --inst_prop_sim_given                   true
% 1.21/1.05  --inst_prop_sim_new                     false
% 1.21/1.05  --inst_subs_new                         false
% 1.21/1.05  --inst_eq_res_simp                      false
% 1.21/1.05  --inst_subs_given                       false
% 1.21/1.05  --inst_orphan_elimination               true
% 1.21/1.05  --inst_learning_loop_flag               true
% 1.21/1.05  --inst_learning_start                   3000
% 1.21/1.05  --inst_learning_factor                  2
% 1.21/1.05  --inst_start_prop_sim_after_learn       3
% 1.21/1.05  --inst_sel_renew                        solver
% 1.21/1.05  --inst_lit_activity_flag                true
% 1.21/1.05  --inst_restr_to_given                   false
% 1.21/1.05  --inst_activity_threshold               500
% 1.21/1.05  --inst_out_proof                        true
% 1.21/1.05  
% 1.21/1.05  ------ Resolution Options
% 1.21/1.05  
% 1.21/1.05  --resolution_flag                       true
% 1.21/1.05  --res_lit_sel                           adaptive
% 1.21/1.05  --res_lit_sel_side                      none
% 1.21/1.05  --res_ordering                          kbo
% 1.21/1.05  --res_to_prop_solver                    active
% 1.21/1.05  --res_prop_simpl_new                    false
% 1.21/1.05  --res_prop_simpl_given                  true
% 1.21/1.05  --res_passive_queue_type                priority_queues
% 1.21/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.21/1.05  --res_passive_queues_freq               [15;5]
% 1.21/1.05  --res_forward_subs                      full
% 1.21/1.05  --res_backward_subs                     full
% 1.21/1.05  --res_forward_subs_resolution           true
% 1.21/1.05  --res_backward_subs_resolution          true
% 1.21/1.05  --res_orphan_elimination                true
% 1.21/1.05  --res_time_limit                        2.
% 1.21/1.05  --res_out_proof                         true
% 1.21/1.05  
% 1.21/1.05  ------ Superposition Options
% 1.21/1.05  
% 1.21/1.05  --superposition_flag                    true
% 1.21/1.05  --sup_passive_queue_type                priority_queues
% 1.21/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.21/1.05  --sup_passive_queues_freq               [8;1;4]
% 1.21/1.05  --demod_completeness_check              fast
% 1.21/1.05  --demod_use_ground                      true
% 1.21/1.05  --sup_to_prop_solver                    passive
% 1.21/1.05  --sup_prop_simpl_new                    true
% 1.21/1.05  --sup_prop_simpl_given                  true
% 1.21/1.05  --sup_fun_splitting                     false
% 1.21/1.05  --sup_smt_interval                      50000
% 1.21/1.05  
% 1.21/1.05  ------ Superposition Simplification Setup
% 1.21/1.05  
% 1.21/1.05  --sup_indices_passive                   []
% 1.21/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.21/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.21/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.21/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 1.21/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.21/1.05  --sup_full_bw                           [BwDemod]
% 1.21/1.05  --sup_immed_triv                        [TrivRules]
% 1.21/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.21/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.21/1.05  --sup_immed_bw_main                     []
% 1.21/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.21/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 1.21/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.21/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.21/1.05  
% 1.21/1.05  ------ Combination Options
% 1.21/1.05  
% 1.21/1.05  --comb_res_mult                         3
% 1.21/1.05  --comb_sup_mult                         2
% 1.21/1.05  --comb_inst_mult                        10
% 1.21/1.05  
% 1.21/1.05  ------ Debug Options
% 1.21/1.05  
% 1.21/1.05  --dbg_backtrace                         false
% 1.21/1.05  --dbg_dump_prop_clauses                 false
% 1.21/1.05  --dbg_dump_prop_clauses_file            -
% 1.21/1.05  --dbg_out_stat                          false
% 1.21/1.05  ------ Parsing...
% 1.21/1.05  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.21/1.05  
% 1.21/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 1.21/1.05  
% 1.21/1.05  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.21/1.05  
% 1.21/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.21/1.05  ------ Proving...
% 1.21/1.05  ------ Problem Properties 
% 1.21/1.05  
% 1.21/1.05  
% 1.21/1.05  clauses                                 21
% 1.21/1.05  conjectures                             5
% 1.21/1.05  EPR                                     4
% 1.21/1.05  Horn                                    16
% 1.21/1.05  unary                                   5
% 1.21/1.05  binary                                  4
% 1.21/1.05  lits                                    54
% 1.21/1.05  lits eq                                 3
% 1.21/1.05  fd_pure                                 0
% 1.21/1.05  fd_pseudo                               0
% 1.21/1.05  fd_cond                                 0
% 1.21/1.05  fd_pseudo_cond                          2
% 1.21/1.05  AC symbols                              0
% 1.21/1.05  
% 1.21/1.05  ------ Schedule dynamic 5 is on 
% 1.21/1.05  
% 1.21/1.05  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.21/1.05  
% 1.21/1.05  
% 1.21/1.05  ------ 
% 1.21/1.05  Current options:
% 1.21/1.05  ------ 
% 1.21/1.05  
% 1.21/1.05  ------ Input Options
% 1.21/1.05  
% 1.21/1.05  --out_options                           all
% 1.21/1.05  --tptp_safe_out                         true
% 1.21/1.05  --problem_path                          ""
% 1.21/1.05  --include_path                          ""
% 1.21/1.05  --clausifier                            res/vclausify_rel
% 1.21/1.05  --clausifier_options                    --mode clausify
% 1.21/1.05  --stdin                                 false
% 1.21/1.05  --stats_out                             all
% 1.21/1.05  
% 1.21/1.05  ------ General Options
% 1.21/1.05  
% 1.21/1.05  --fof                                   false
% 1.21/1.05  --time_out_real                         305.
% 1.21/1.05  --time_out_virtual                      -1.
% 1.21/1.05  --symbol_type_check                     false
% 1.21/1.05  --clausify_out                          false
% 1.21/1.05  --sig_cnt_out                           false
% 1.21/1.05  --trig_cnt_out                          false
% 1.21/1.05  --trig_cnt_out_tolerance                1.
% 1.21/1.05  --trig_cnt_out_sk_spl                   false
% 1.21/1.05  --abstr_cl_out                          false
% 1.21/1.05  
% 1.21/1.05  ------ Global Options
% 1.21/1.05  
% 1.21/1.05  --schedule                              default
% 1.21/1.05  --add_important_lit                     false
% 1.21/1.05  --prop_solver_per_cl                    1000
% 1.21/1.05  --min_unsat_core                        false
% 1.21/1.05  --soft_assumptions                      false
% 1.21/1.05  --soft_lemma_size                       3
% 1.21/1.05  --prop_impl_unit_size                   0
% 1.21/1.05  --prop_impl_unit                        []
% 1.21/1.05  --share_sel_clauses                     true
% 1.21/1.05  --reset_solvers                         false
% 1.21/1.05  --bc_imp_inh                            [conj_cone]
% 1.21/1.05  --conj_cone_tolerance                   3.
% 1.21/1.05  --extra_neg_conj                        none
% 1.21/1.05  --large_theory_mode                     true
% 1.21/1.05  --prolific_symb_bound                   200
% 1.21/1.05  --lt_threshold                          2000
% 1.21/1.05  --clause_weak_htbl                      true
% 1.21/1.05  --gc_record_bc_elim                     false
% 1.21/1.05  
% 1.21/1.05  ------ Preprocessing Options
% 1.21/1.05  
% 1.21/1.05  --preprocessing_flag                    true
% 1.21/1.05  --time_out_prep_mult                    0.1
% 1.21/1.05  --splitting_mode                        input
% 1.21/1.05  --splitting_grd                         true
% 1.21/1.05  --splitting_cvd                         false
% 1.21/1.05  --splitting_cvd_svl                     false
% 1.21/1.05  --splitting_nvd                         32
% 1.21/1.05  --sub_typing                            true
% 1.21/1.05  --prep_gs_sim                           true
% 1.21/1.05  --prep_unflatten                        true
% 1.21/1.05  --prep_res_sim                          true
% 1.21/1.05  --prep_upred                            true
% 1.21/1.05  --prep_sem_filter                       exhaustive
% 1.21/1.05  --prep_sem_filter_out                   false
% 1.21/1.05  --pred_elim                             true
% 1.21/1.05  --res_sim_input                         true
% 1.21/1.05  --eq_ax_congr_red                       true
% 1.21/1.05  --pure_diseq_elim                       true
% 1.21/1.05  --brand_transform                       false
% 1.21/1.05  --non_eq_to_eq                          false
% 1.21/1.05  --prep_def_merge                        true
% 1.21/1.05  --prep_def_merge_prop_impl              false
% 1.21/1.05  --prep_def_merge_mbd                    true
% 1.21/1.05  --prep_def_merge_tr_red                 false
% 1.21/1.05  --prep_def_merge_tr_cl                  false
% 1.21/1.05  --smt_preprocessing                     true
% 1.21/1.05  --smt_ac_axioms                         fast
% 1.21/1.05  --preprocessed_out                      false
% 1.21/1.05  --preprocessed_stats                    false
% 1.21/1.05  
% 1.21/1.05  ------ Abstraction refinement Options
% 1.21/1.05  
% 1.21/1.05  --abstr_ref                             []
% 1.21/1.05  --abstr_ref_prep                        false
% 1.21/1.05  --abstr_ref_until_sat                   false
% 1.21/1.05  --abstr_ref_sig_restrict                funpre
% 1.21/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 1.21/1.05  --abstr_ref_under                       []
% 1.21/1.05  
% 1.21/1.05  ------ SAT Options
% 1.21/1.05  
% 1.21/1.05  --sat_mode                              false
% 1.21/1.05  --sat_fm_restart_options                ""
% 1.21/1.05  --sat_gr_def                            false
% 1.21/1.05  --sat_epr_types                         true
% 1.21/1.05  --sat_non_cyclic_types                  false
% 1.21/1.05  --sat_finite_models                     false
% 1.21/1.05  --sat_fm_lemmas                         false
% 1.21/1.05  --sat_fm_prep                           false
% 1.21/1.05  --sat_fm_uc_incr                        true
% 1.21/1.05  --sat_out_model                         small
% 1.21/1.05  --sat_out_clauses                       false
% 1.21/1.05  
% 1.21/1.05  ------ QBF Options
% 1.21/1.05  
% 1.21/1.05  --qbf_mode                              false
% 1.21/1.05  --qbf_elim_univ                         false
% 1.21/1.05  --qbf_dom_inst                          none
% 1.21/1.05  --qbf_dom_pre_inst                      false
% 1.21/1.05  --qbf_sk_in                             false
% 1.21/1.05  --qbf_pred_elim                         true
% 1.21/1.05  --qbf_split                             512
% 1.21/1.05  
% 1.21/1.05  ------ BMC1 Options
% 1.21/1.05  
% 1.21/1.05  --bmc1_incremental                      false
% 1.21/1.05  --bmc1_axioms                           reachable_all
% 1.21/1.05  --bmc1_min_bound                        0
% 1.21/1.05  --bmc1_max_bound                        -1
% 1.21/1.05  --bmc1_max_bound_default                -1
% 1.21/1.05  --bmc1_symbol_reachability              true
% 1.21/1.05  --bmc1_property_lemmas                  false
% 1.21/1.05  --bmc1_k_induction                      false
% 1.21/1.05  --bmc1_non_equiv_states                 false
% 1.21/1.05  --bmc1_deadlock                         false
% 1.21/1.05  --bmc1_ucm                              false
% 1.21/1.05  --bmc1_add_unsat_core                   none
% 1.21/1.05  --bmc1_unsat_core_children              false
% 1.21/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 1.21/1.05  --bmc1_out_stat                         full
% 1.21/1.05  --bmc1_ground_init                      false
% 1.21/1.05  --bmc1_pre_inst_next_state              false
% 1.21/1.05  --bmc1_pre_inst_state                   false
% 1.21/1.05  --bmc1_pre_inst_reach_state             false
% 1.21/1.05  --bmc1_out_unsat_core                   false
% 1.21/1.05  --bmc1_aig_witness_out                  false
% 1.21/1.05  --bmc1_verbose                          false
% 1.21/1.05  --bmc1_dump_clauses_tptp                false
% 1.21/1.05  --bmc1_dump_unsat_core_tptp             false
% 1.21/1.05  --bmc1_dump_file                        -
% 1.21/1.05  --bmc1_ucm_expand_uc_limit              128
% 1.21/1.05  --bmc1_ucm_n_expand_iterations          6
% 1.21/1.05  --bmc1_ucm_extend_mode                  1
% 1.21/1.05  --bmc1_ucm_init_mode                    2
% 1.21/1.05  --bmc1_ucm_cone_mode                    none
% 1.21/1.05  --bmc1_ucm_reduced_relation_type        0
% 1.21/1.05  --bmc1_ucm_relax_model                  4
% 1.21/1.05  --bmc1_ucm_full_tr_after_sat            true
% 1.21/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 1.21/1.05  --bmc1_ucm_layered_model                none
% 1.21/1.05  --bmc1_ucm_max_lemma_size               10
% 1.21/1.05  
% 1.21/1.05  ------ AIG Options
% 1.21/1.05  
% 1.21/1.05  --aig_mode                              false
% 1.21/1.05  
% 1.21/1.05  ------ Instantiation Options
% 1.21/1.05  
% 1.21/1.05  --instantiation_flag                    true
% 1.21/1.05  --inst_sos_flag                         false
% 1.21/1.05  --inst_sos_phase                        true
% 1.21/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.21/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.21/1.05  --inst_lit_sel_side                     none
% 1.21/1.05  --inst_solver_per_active                1400
% 1.21/1.05  --inst_solver_calls_frac                1.
% 1.21/1.05  --inst_passive_queue_type               priority_queues
% 1.21/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.21/1.05  --inst_passive_queues_freq              [25;2]
% 1.21/1.05  --inst_dismatching                      true
% 1.21/1.05  --inst_eager_unprocessed_to_passive     true
% 1.21/1.05  --inst_prop_sim_given                   true
% 1.21/1.05  --inst_prop_sim_new                     false
% 1.21/1.05  --inst_subs_new                         false
% 1.21/1.05  --inst_eq_res_simp                      false
% 1.21/1.05  --inst_subs_given                       false
% 1.21/1.05  --inst_orphan_elimination               true
% 1.21/1.05  --inst_learning_loop_flag               true
% 1.21/1.05  --inst_learning_start                   3000
% 1.21/1.05  --inst_learning_factor                  2
% 1.21/1.05  --inst_start_prop_sim_after_learn       3
% 1.21/1.05  --inst_sel_renew                        solver
% 1.21/1.05  --inst_lit_activity_flag                true
% 1.21/1.05  --inst_restr_to_given                   false
% 1.21/1.05  --inst_activity_threshold               500
% 1.21/1.05  --inst_out_proof                        true
% 1.21/1.05  
% 1.21/1.05  ------ Resolution Options
% 1.21/1.05  
% 1.21/1.05  --resolution_flag                       false
% 1.21/1.05  --res_lit_sel                           adaptive
% 1.21/1.05  --res_lit_sel_side                      none
% 1.21/1.05  --res_ordering                          kbo
% 1.21/1.05  --res_to_prop_solver                    active
% 1.21/1.05  --res_prop_simpl_new                    false
% 1.21/1.05  --res_prop_simpl_given                  true
% 1.21/1.05  --res_passive_queue_type                priority_queues
% 1.21/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.21/1.05  --res_passive_queues_freq               [15;5]
% 1.21/1.05  --res_forward_subs                      full
% 1.21/1.05  --res_backward_subs                     full
% 1.21/1.05  --res_forward_subs_resolution           true
% 1.21/1.05  --res_backward_subs_resolution          true
% 1.21/1.05  --res_orphan_elimination                true
% 1.21/1.05  --res_time_limit                        2.
% 1.21/1.05  --res_out_proof                         true
% 1.21/1.05  
% 1.21/1.05  ------ Superposition Options
% 1.21/1.05  
% 1.21/1.05  --superposition_flag                    true
% 1.21/1.05  --sup_passive_queue_type                priority_queues
% 1.21/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.21/1.05  --sup_passive_queues_freq               [8;1;4]
% 1.21/1.05  --demod_completeness_check              fast
% 1.21/1.05  --demod_use_ground                      true
% 1.21/1.05  --sup_to_prop_solver                    passive
% 1.21/1.05  --sup_prop_simpl_new                    true
% 1.21/1.05  --sup_prop_simpl_given                  true
% 1.21/1.05  --sup_fun_splitting                     false
% 1.21/1.05  --sup_smt_interval                      50000
% 1.21/1.05  
% 1.21/1.05  ------ Superposition Simplification Setup
% 1.21/1.05  
% 1.21/1.05  --sup_indices_passive                   []
% 1.21/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.21/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.21/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.21/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 1.21/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.21/1.05  --sup_full_bw                           [BwDemod]
% 1.21/1.05  --sup_immed_triv                        [TrivRules]
% 1.21/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.21/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.21/1.05  --sup_immed_bw_main                     []
% 1.21/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.21/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 1.21/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.21/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.21/1.05  
% 1.21/1.05  ------ Combination Options
% 1.21/1.05  
% 1.21/1.05  --comb_res_mult                         3
% 1.21/1.05  --comb_sup_mult                         2
% 1.21/1.05  --comb_inst_mult                        10
% 1.21/1.05  
% 1.21/1.05  ------ Debug Options
% 1.21/1.05  
% 1.21/1.05  --dbg_backtrace                         false
% 1.21/1.05  --dbg_dump_prop_clauses                 false
% 1.21/1.05  --dbg_dump_prop_clauses_file            -
% 1.21/1.05  --dbg_out_stat                          false
% 1.21/1.05  
% 1.21/1.05  
% 1.21/1.05  
% 1.21/1.05  
% 1.21/1.05  ------ Proving...
% 1.21/1.05  
% 1.21/1.05  
% 1.21/1.05  % SZS status Theorem for theBenchmark.p
% 1.21/1.05  
% 1.21/1.05  % SZS output start CNFRefutation for theBenchmark.p
% 1.21/1.05  
% 1.21/1.05  fof(f7,conjecture,(
% 1.21/1.05    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_pre_topc(X2,X0) => (v1_tops_2(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) => (X1 = X3 => v1_tops_2(X3,X2)))))))),
% 1.21/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.21/1.05  
% 1.21/1.05  fof(f8,negated_conjecture,(
% 1.21/1.05    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_pre_topc(X2,X0) => (v1_tops_2(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) => (X1 = X3 => v1_tops_2(X3,X2)))))))),
% 1.21/1.05    inference(negated_conjecture,[],[f7])).
% 1.21/1.05  
% 1.21/1.05  fof(f15,plain,(
% 1.21/1.05    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : ((~v1_tops_2(X3,X2) & X1 = X3) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))) & v1_tops_2(X1,X0)) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 1.21/1.05    inference(ennf_transformation,[],[f8])).
% 1.21/1.05  
% 1.21/1.05  fof(f16,plain,(
% 1.21/1.05    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v1_tops_2(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))) & v1_tops_2(X1,X0) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 1.21/1.05    inference(flattening,[],[f15])).
% 1.21/1.05  
% 1.21/1.05  fof(f29,plain,(
% 1.21/1.05    ( ! [X2,X1] : (? [X3] : (~v1_tops_2(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))) => (~v1_tops_2(sK5,X2) & sK5 = X1 & m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))))) )),
% 1.21/1.05    introduced(choice_axiom,[])).
% 1.21/1.05  
% 1.21/1.05  fof(f28,plain,(
% 1.21/1.05    ( ! [X0,X1] : (? [X2] : (? [X3] : (~v1_tops_2(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))) & v1_tops_2(X1,X0) & m1_pre_topc(X2,X0)) => (? [X3] : (~v1_tops_2(X3,sK4) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))) & v1_tops_2(X1,X0) & m1_pre_topc(sK4,X0))) )),
% 1.21/1.05    introduced(choice_axiom,[])).
% 1.21/1.05  
% 1.21/1.05  fof(f27,plain,(
% 1.21/1.05    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~v1_tops_2(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))) & v1_tops_2(X1,X0) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (? [X2] : (? [X3] : (~v1_tops_2(X3,X2) & sK3 = X3 & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))) & v1_tops_2(sK3,X0) & m1_pre_topc(X2,X0)) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) )),
% 1.21/1.05    introduced(choice_axiom,[])).
% 1.21/1.05  
% 1.21/1.05  fof(f26,plain,(
% 1.21/1.05    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v1_tops_2(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))) & v1_tops_2(X1,X0) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : (~v1_tops_2(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))) & v1_tops_2(X1,sK2) & m1_pre_topc(X2,sK2)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))) & l1_pre_topc(sK2))),
% 1.21/1.05    introduced(choice_axiom,[])).
% 1.21/1.05  
% 1.21/1.05  fof(f30,plain,(
% 1.21/1.05    (((~v1_tops_2(sK5,sK4) & sK3 = sK5 & m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))) & v1_tops_2(sK3,sK2) & m1_pre_topc(sK4,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))) & l1_pre_topc(sK2)),
% 1.21/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f16,f29,f28,f27,f26])).
% 1.21/1.05  
% 1.21/1.05  fof(f48,plain,(
% 1.21/1.05    m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))),
% 1.21/1.05    inference(cnf_transformation,[],[f30])).
% 1.21/1.05  
% 1.21/1.05  fof(f5,axiom,(
% 1.21/1.05    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,X1) => v3_pre_topc(X2,X0))))))),
% 1.21/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.21/1.05  
% 1.21/1.05  fof(f11,plain,(
% 1.21/1.05    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> ! [X2] : ((v3_pre_topc(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 1.21/1.05    inference(ennf_transformation,[],[f5])).
% 1.21/1.05  
% 1.21/1.05  fof(f12,plain,(
% 1.21/1.05    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> ! [X2] : (v3_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 1.21/1.05    inference(flattening,[],[f11])).
% 1.21/1.05  
% 1.21/1.05  fof(f22,plain,(
% 1.21/1.05    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 1.21/1.05    inference(nnf_transformation,[],[f12])).
% 1.21/1.05  
% 1.21/1.05  fof(f23,plain,(
% 1.21/1.05    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 1.21/1.05    inference(rectify,[],[f22])).
% 1.21/1.05  
% 1.21/1.05  fof(f24,plain,(
% 1.21/1.05    ! [X1,X0] : (? [X2] : (~v3_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK1(X0,X1),X0) & r2_hidden(sK1(X0,X1),X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.21/1.05    introduced(choice_axiom,[])).
% 1.21/1.05  
% 1.21/1.05  fof(f25,plain,(
% 1.21/1.05    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | (~v3_pre_topc(sK1(X0,X1),X0) & r2_hidden(sK1(X0,X1),X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 1.21/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f23,f24])).
% 1.21/1.05  
% 1.21/1.05  fof(f41,plain,(
% 1.21/1.05    ( ! [X0,X1] : (v1_tops_2(X1,X0) | r2_hidden(sK1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 1.21/1.05    inference(cnf_transformation,[],[f25])).
% 1.21/1.05  
% 1.21/1.05  fof(f4,axiom,(
% 1.21/1.05    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.21/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.21/1.05  
% 1.21/1.05  fof(f10,plain,(
% 1.21/1.05    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.21/1.05    inference(ennf_transformation,[],[f4])).
% 1.21/1.05  
% 1.21/1.05  fof(f38,plain,(
% 1.21/1.05    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.21/1.05    inference(cnf_transformation,[],[f10])).
% 1.21/1.05  
% 1.21/1.05  fof(f46,plain,(
% 1.21/1.05    m1_pre_topc(sK4,sK2)),
% 1.21/1.05    inference(cnf_transformation,[],[f30])).
% 1.21/1.05  
% 1.21/1.05  fof(f44,plain,(
% 1.21/1.05    l1_pre_topc(sK2)),
% 1.21/1.05    inference(cnf_transformation,[],[f30])).
% 1.21/1.05  
% 1.21/1.05  fof(f50,plain,(
% 1.21/1.05    ~v1_tops_2(sK5,sK4)),
% 1.21/1.05    inference(cnf_transformation,[],[f30])).
% 1.21/1.05  
% 1.21/1.05  fof(f2,axiom,(
% 1.21/1.05    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.21/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.21/1.05  
% 1.21/1.05  fof(f9,plain,(
% 1.21/1.05    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.21/1.05    inference(ennf_transformation,[],[f2])).
% 1.21/1.05  
% 1.21/1.05  fof(f35,plain,(
% 1.21/1.05    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.21/1.05    inference(cnf_transformation,[],[f9])).
% 1.21/1.05  
% 1.21/1.05  fof(f3,axiom,(
% 1.21/1.05    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.21/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.21/1.05  
% 1.21/1.05  fof(f21,plain,(
% 1.21/1.05    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.21/1.05    inference(nnf_transformation,[],[f3])).
% 1.21/1.05  
% 1.21/1.05  fof(f37,plain,(
% 1.21/1.05    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.21/1.05    inference(cnf_transformation,[],[f21])).
% 1.21/1.05  
% 1.21/1.05  fof(f1,axiom,(
% 1.21/1.05    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.21/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.21/1.05  
% 1.21/1.05  fof(f17,plain,(
% 1.21/1.05    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.21/1.05    inference(nnf_transformation,[],[f1])).
% 1.21/1.05  
% 1.21/1.05  fof(f18,plain,(
% 1.21/1.05    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.21/1.05    inference(rectify,[],[f17])).
% 1.21/1.05  
% 1.21/1.05  fof(f19,plain,(
% 1.21/1.05    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 1.21/1.05    introduced(choice_axiom,[])).
% 1.21/1.05  
% 1.21/1.05  fof(f20,plain,(
% 1.21/1.05    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.21/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).
% 1.21/1.05  
% 1.21/1.05  fof(f31,plain,(
% 1.21/1.05    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.21/1.05    inference(cnf_transformation,[],[f20])).
% 1.21/1.05  
% 1.21/1.05  fof(f52,plain,(
% 1.21/1.05    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 1.21/1.05    inference(equality_resolution,[],[f31])).
% 1.21/1.05  
% 1.21/1.05  fof(f40,plain,(
% 1.21/1.05    ( ! [X0,X1] : (v1_tops_2(X1,X0) | m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 1.21/1.05    inference(cnf_transformation,[],[f25])).
% 1.21/1.05  
% 1.21/1.05  fof(f36,plain,(
% 1.21/1.05    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.21/1.05    inference(cnf_transformation,[],[f21])).
% 1.21/1.05  
% 1.21/1.05  fof(f6,axiom,(
% 1.21/1.05    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v3_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v3_pre_topc(X3,X2)))))))),
% 1.21/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.21/1.05  
% 1.21/1.05  fof(f13,plain,(
% 1.21/1.05    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((v3_pre_topc(X3,X2) | X1 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v3_pre_topc(X1,X0)) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.21/1.05    inference(ennf_transformation,[],[f6])).
% 1.21/1.05  
% 1.21/1.05  fof(f14,plain,(
% 1.21/1.05    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v3_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v3_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.21/1.05    inference(flattening,[],[f13])).
% 1.21/1.05  
% 1.21/1.05  fof(f43,plain,(
% 1.21/1.05    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~v3_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.21/1.05    inference(cnf_transformation,[],[f14])).
% 1.21/1.05  
% 1.21/1.05  fof(f53,plain,(
% 1.21/1.05    ( ! [X2,X0,X3] : (v3_pre_topc(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~v3_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.21/1.05    inference(equality_resolution,[],[f43])).
% 1.21/1.05  
% 1.21/1.05  fof(f42,plain,(
% 1.21/1.05    ( ! [X0,X1] : (v1_tops_2(X1,X0) | ~v3_pre_topc(sK1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 1.21/1.05    inference(cnf_transformation,[],[f25])).
% 1.21/1.05  
% 1.21/1.05  fof(f45,plain,(
% 1.21/1.05    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))),
% 1.21/1.05    inference(cnf_transformation,[],[f30])).
% 1.21/1.05  
% 1.21/1.05  fof(f49,plain,(
% 1.21/1.05    sK3 = sK5),
% 1.21/1.05    inference(cnf_transformation,[],[f30])).
% 1.21/1.05  
% 1.21/1.05  fof(f39,plain,(
% 1.21/1.05    ( ! [X0,X3,X1] : (v3_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 1.21/1.05    inference(cnf_transformation,[],[f25])).
% 1.21/1.05  
% 1.21/1.05  fof(f47,plain,(
% 1.21/1.05    v1_tops_2(sK3,sK2)),
% 1.21/1.05    inference(cnf_transformation,[],[f30])).
% 1.21/1.05  
% 1.21/1.05  cnf(c_15,negated_conjecture,
% 1.21/1.05      ( m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) ),
% 1.21/1.05      inference(cnf_transformation,[],[f48]) ).
% 1.21/1.05  
% 1.21/1.05  cnf(c_1390,plain,
% 1.21/1.05      ( m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) = iProver_top ),
% 1.21/1.05      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 1.21/1.05  
% 1.21/1.05  cnf(c_9,plain,
% 1.21/1.05      ( v1_tops_2(X0,X1)
% 1.21/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 1.21/1.05      | r2_hidden(sK1(X1,X0),X0)
% 1.21/1.05      | ~ l1_pre_topc(X1) ),
% 1.21/1.05      inference(cnf_transformation,[],[f41]) ).
% 1.21/1.05  
% 1.21/1.05  cnf(c_7,plain,
% 1.21/1.05      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 1.21/1.05      inference(cnf_transformation,[],[f38]) ).
% 1.21/1.05  
% 1.21/1.05  cnf(c_17,negated_conjecture,
% 1.21/1.05      ( m1_pre_topc(sK4,sK2) ),
% 1.21/1.05      inference(cnf_transformation,[],[f46]) ).
% 1.21/1.05  
% 1.21/1.05  cnf(c_261,plain,
% 1.21/1.05      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | sK2 != X0 | sK4 != X1 ),
% 1.21/1.05      inference(resolution_lifted,[status(thm)],[c_7,c_17]) ).
% 1.21/1.05  
% 1.21/1.05  cnf(c_262,plain,
% 1.21/1.05      ( ~ l1_pre_topc(sK2) | l1_pre_topc(sK4) ),
% 1.21/1.05      inference(unflattening,[status(thm)],[c_261]) ).
% 1.21/1.05  
% 1.21/1.05  cnf(c_19,negated_conjecture,
% 1.21/1.05      ( l1_pre_topc(sK2) ),
% 1.21/1.05      inference(cnf_transformation,[],[f44]) ).
% 1.21/1.05  
% 1.21/1.05  cnf(c_264,plain,
% 1.21/1.05      ( l1_pre_topc(sK4) ),
% 1.21/1.05      inference(global_propositional_subsumption,
% 1.21/1.05                [status(thm)],
% 1.21/1.05                [c_262,c_19]) ).
% 1.21/1.05  
% 1.21/1.05  cnf(c_420,plain,
% 1.21/1.05      ( v1_tops_2(X0,X1)
% 1.21/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 1.21/1.05      | r2_hidden(sK1(X1,X0),X0)
% 1.21/1.05      | sK4 != X1 ),
% 1.21/1.05      inference(resolution_lifted,[status(thm)],[c_9,c_264]) ).
% 1.21/1.05  
% 1.21/1.05  cnf(c_421,plain,
% 1.21/1.05      ( v1_tops_2(X0,sK4)
% 1.21/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 1.21/1.05      | r2_hidden(sK1(sK4,X0),X0) ),
% 1.21/1.05      inference(unflattening,[status(thm)],[c_420]) ).
% 1.21/1.05  
% 1.21/1.05  cnf(c_1378,plain,
% 1.21/1.05      ( v1_tops_2(X0,sK4) = iProver_top
% 1.21/1.05      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top
% 1.21/1.05      | r2_hidden(sK1(sK4,X0),X0) = iProver_top ),
% 1.21/1.05      inference(predicate_to_equality,[status(thm)],[c_421]) ).
% 1.21/1.05  
% 1.21/1.05  cnf(c_1794,plain,
% 1.21/1.05      ( v1_tops_2(sK5,sK4) = iProver_top
% 1.21/1.05      | r2_hidden(sK1(sK4,sK5),sK5) = iProver_top ),
% 1.21/1.05      inference(superposition,[status(thm)],[c_1390,c_1378]) ).
% 1.21/1.05  
% 1.21/1.05  cnf(c_24,plain,
% 1.21/1.05      ( m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) = iProver_top ),
% 1.21/1.05      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 1.21/1.05  
% 1.21/1.05  cnf(c_13,negated_conjecture,
% 1.21/1.05      ( ~ v1_tops_2(sK5,sK4) ),
% 1.21/1.05      inference(cnf_transformation,[],[f50]) ).
% 1.21/1.05  
% 1.21/1.05  cnf(c_638,plain,
% 1.21/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 1.21/1.05      | r2_hidden(sK1(sK4,X0),X0)
% 1.21/1.05      | sK4 != sK4
% 1.21/1.05      | sK5 != X0 ),
% 1.21/1.05      inference(resolution_lifted,[status(thm)],[c_13,c_421]) ).
% 1.21/1.05  
% 1.21/1.05  cnf(c_639,plain,
% 1.21/1.05      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 1.21/1.05      | r2_hidden(sK1(sK4,sK5),sK5) ),
% 1.21/1.05      inference(unflattening,[status(thm)],[c_638]) ).
% 1.21/1.05  
% 1.21/1.05  cnf(c_640,plain,
% 1.21/1.05      ( m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top
% 1.21/1.05      | r2_hidden(sK1(sK4,sK5),sK5) = iProver_top ),
% 1.21/1.05      inference(predicate_to_equality,[status(thm)],[c_639]) ).
% 1.21/1.05  
% 1.21/1.05  cnf(c_2282,plain,
% 1.21/1.05      ( r2_hidden(sK1(sK4,sK5),sK5) = iProver_top ),
% 1.21/1.05      inference(global_propositional_subsumption,
% 1.21/1.05                [status(thm)],
% 1.21/1.05                [c_1794,c_24,c_640]) ).
% 1.21/1.05  
% 1.21/1.05  cnf(c_4,plain,
% 1.21/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.21/1.05      | ~ r2_hidden(X2,X0)
% 1.21/1.05      | r2_hidden(X2,X1) ),
% 1.21/1.05      inference(cnf_transformation,[],[f35]) ).
% 1.21/1.05  
% 1.21/1.05  cnf(c_5,plain,
% 1.21/1.05      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 1.21/1.05      inference(cnf_transformation,[],[f37]) ).
% 1.21/1.05  
% 1.21/1.05  cnf(c_145,plain,
% 1.21/1.05      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 1.21/1.05      inference(prop_impl,[status(thm)],[c_5]) ).
% 1.21/1.05  
% 1.21/1.05  cnf(c_146,plain,
% 1.21/1.05      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 1.21/1.05      inference(renaming,[status(thm)],[c_145]) ).
% 1.21/1.05  
% 1.21/1.05  cnf(c_189,plain,
% 1.21/1.05      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 1.21/1.05      inference(bin_hyper_res,[status(thm)],[c_4,c_146]) ).
% 1.21/1.05  
% 1.21/1.05  cnf(c_1387,plain,
% 1.21/1.05      ( r2_hidden(X0,X1) != iProver_top
% 1.21/1.05      | r2_hidden(X0,X2) = iProver_top
% 1.21/1.05      | r1_tarski(X1,X2) != iProver_top ),
% 1.21/1.05      inference(predicate_to_equality,[status(thm)],[c_189]) ).
% 1.21/1.05  
% 1.21/1.05  cnf(c_2647,plain,
% 1.21/1.05      ( r2_hidden(sK1(sK4,sK5),X0) = iProver_top
% 1.21/1.05      | r1_tarski(sK5,X0) != iProver_top ),
% 1.21/1.05      inference(superposition,[status(thm)],[c_2282,c_1387]) ).
% 1.21/1.05  
% 1.21/1.05  cnf(c_3,plain,
% 1.21/1.05      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 1.21/1.05      inference(cnf_transformation,[],[f52]) ).
% 1.21/1.05  
% 1.21/1.05  cnf(c_1394,plain,
% 1.21/1.05      ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
% 1.21/1.05      | r1_tarski(X0,X1) = iProver_top ),
% 1.21/1.05      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 1.21/1.05  
% 1.21/1.05  cnf(c_2676,plain,
% 1.21/1.05      ( r1_tarski(sK1(sK4,sK5),X0) = iProver_top
% 1.21/1.05      | r1_tarski(sK5,k1_zfmisc_1(X0)) != iProver_top ),
% 1.21/1.05      inference(superposition,[status(thm)],[c_2647,c_1394]) ).
% 1.21/1.05  
% 1.21/1.05  cnf(c_10,plain,
% 1.21/1.05      ( v1_tops_2(X0,X1)
% 1.21/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 1.21/1.05      | m1_subset_1(sK1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.21/1.05      | ~ l1_pre_topc(X1) ),
% 1.21/1.05      inference(cnf_transformation,[],[f40]) ).
% 1.21/1.05  
% 1.21/1.05  cnf(c_405,plain,
% 1.21/1.05      ( v1_tops_2(X0,X1)
% 1.21/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 1.21/1.05      | m1_subset_1(sK1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.21/1.05      | sK4 != X1 ),
% 1.21/1.05      inference(resolution_lifted,[status(thm)],[c_10,c_264]) ).
% 1.21/1.05  
% 1.21/1.05  cnf(c_406,plain,
% 1.21/1.05      ( v1_tops_2(X0,sK4)
% 1.21/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 1.21/1.05      | m1_subset_1(sK1(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4))) ),
% 1.21/1.05      inference(unflattening,[status(thm)],[c_405]) ).
% 1.21/1.05  
% 1.21/1.05  cnf(c_1379,plain,
% 1.21/1.05      ( v1_tops_2(X0,sK4) = iProver_top
% 1.21/1.05      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top
% 1.21/1.05      | m1_subset_1(sK1(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 1.21/1.05      inference(predicate_to_equality,[status(thm)],[c_406]) ).
% 1.21/1.05  
% 1.21/1.05  cnf(c_6,plain,
% 1.21/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 1.21/1.05      inference(cnf_transformation,[],[f36]) ).
% 1.21/1.05  
% 1.21/1.05  cnf(c_1392,plain,
% 1.21/1.05      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 1.21/1.05      | r1_tarski(X0,X1) = iProver_top ),
% 1.21/1.05      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 1.21/1.05  
% 1.21/1.05  cnf(c_2435,plain,
% 1.21/1.05      ( v1_tops_2(X0,sK4) = iProver_top
% 1.21/1.05      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top
% 1.21/1.05      | r1_tarski(sK1(sK4,X0),u1_struct_0(sK4)) = iProver_top ),
% 1.21/1.05      inference(superposition,[status(thm)],[c_1379,c_1392]) ).
% 1.21/1.05  
% 1.21/1.05  cnf(c_4051,plain,
% 1.21/1.05      ( v1_tops_2(sK5,sK4) = iProver_top
% 1.21/1.05      | r1_tarski(sK1(sK4,sK5),u1_struct_0(sK4)) = iProver_top ),
% 1.21/1.05      inference(superposition,[status(thm)],[c_1390,c_2435]) ).
% 1.21/1.05  
% 1.21/1.05  cnf(c_649,plain,
% 1.21/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 1.21/1.05      | m1_subset_1(sK1(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
% 1.21/1.05      | sK4 != sK4
% 1.21/1.05      | sK5 != X0 ),
% 1.21/1.05      inference(resolution_lifted,[status(thm)],[c_13,c_406]) ).
% 1.21/1.05  
% 1.21/1.05  cnf(c_650,plain,
% 1.21/1.05      ( m1_subset_1(sK1(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK4)))
% 1.21/1.05      | ~ m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) ),
% 1.21/1.05      inference(unflattening,[status(thm)],[c_649]) ).
% 1.21/1.05  
% 1.21/1.05  cnf(c_651,plain,
% 1.21/1.05      ( m1_subset_1(sK1(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 1.21/1.05      | m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top ),
% 1.21/1.05      inference(predicate_to_equality,[status(thm)],[c_650]) ).
% 1.21/1.05  
% 1.21/1.05  cnf(c_1599,plain,
% 1.21/1.05      ( ~ m1_subset_1(sK1(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK4)))
% 1.21/1.05      | r1_tarski(sK1(sK4,sK5),u1_struct_0(sK4)) ),
% 1.21/1.05      inference(instantiation,[status(thm)],[c_6]) ).
% 1.21/1.05  
% 1.21/1.05  cnf(c_1600,plain,
% 1.21/1.05      ( m1_subset_1(sK1(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 1.21/1.05      | r1_tarski(sK1(sK4,sK5),u1_struct_0(sK4)) = iProver_top ),
% 1.21/1.05      inference(predicate_to_equality,[status(thm)],[c_1599]) ).
% 1.21/1.05  
% 1.21/1.05  cnf(c_4067,plain,
% 1.21/1.05      ( r1_tarski(sK1(sK4,sK5),u1_struct_0(sK4)) = iProver_top ),
% 1.21/1.05      inference(global_propositional_subsumption,
% 1.21/1.05                [status(thm)],
% 1.21/1.05                [c_4051,c_24,c_651,c_1600]) ).
% 1.21/1.05  
% 1.21/1.05  cnf(c_1393,plain,
% 1.21/1.05      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 1.21/1.05      | r1_tarski(X0,X1) != iProver_top ),
% 1.21/1.05      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 1.21/1.05  
% 1.21/1.05  cnf(c_12,plain,
% 1.21/1.05      ( ~ v3_pre_topc(X0,X1)
% 1.21/1.05      | v3_pre_topc(X0,X2)
% 1.21/1.05      | ~ m1_pre_topc(X2,X1)
% 1.21/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.21/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 1.21/1.05      | ~ l1_pre_topc(X1) ),
% 1.21/1.05      inference(cnf_transformation,[],[f53]) ).
% 1.21/1.05  
% 1.21/1.05  cnf(c_272,plain,
% 1.21/1.05      ( ~ v3_pre_topc(X0,X1)
% 1.21/1.05      | v3_pre_topc(X0,X2)
% 1.21/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.21/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 1.21/1.05      | ~ l1_pre_topc(X1)
% 1.21/1.05      | sK2 != X1
% 1.21/1.05      | sK4 != X2 ),
% 1.21/1.05      inference(resolution_lifted,[status(thm)],[c_12,c_17]) ).
% 1.21/1.05  
% 1.21/1.05  cnf(c_273,plain,
% 1.21/1.05      ( ~ v3_pre_topc(X0,sK2)
% 1.21/1.05      | v3_pre_topc(X0,sK4)
% 1.21/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.21/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.21/1.05      | ~ l1_pre_topc(sK2) ),
% 1.21/1.05      inference(unflattening,[status(thm)],[c_272]) ).
% 1.21/1.05  
% 1.21/1.05  cnf(c_277,plain,
% 1.21/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.21/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.21/1.05      | v3_pre_topc(X0,sK4)
% 1.21/1.05      | ~ v3_pre_topc(X0,sK2) ),
% 1.21/1.05      inference(global_propositional_subsumption,
% 1.21/1.05                [status(thm)],
% 1.21/1.05                [c_273,c_19]) ).
% 1.21/1.05  
% 1.21/1.05  cnf(c_278,plain,
% 1.21/1.05      ( ~ v3_pre_topc(X0,sK2)
% 1.21/1.05      | v3_pre_topc(X0,sK4)
% 1.21/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.21/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 1.21/1.05      inference(renaming,[status(thm)],[c_277]) ).
% 1.21/1.05  
% 1.21/1.05  cnf(c_1386,plain,
% 1.21/1.05      ( v3_pre_topc(X0,sK2) != iProver_top
% 1.21/1.05      | v3_pre_topc(X0,sK4) = iProver_top
% 1.21/1.05      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.21/1.05      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 1.21/1.05      inference(predicate_to_equality,[status(thm)],[c_278]) ).
% 1.21/1.05  
% 1.21/1.05  cnf(c_1924,plain,
% 1.21/1.05      ( v3_pre_topc(X0,sK2) != iProver_top
% 1.21/1.05      | v3_pre_topc(X0,sK4) = iProver_top
% 1.21/1.05      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 1.21/1.05      | r1_tarski(X0,u1_struct_0(sK2)) != iProver_top ),
% 1.21/1.05      inference(superposition,[status(thm)],[c_1393,c_1386]) ).
% 1.21/1.05  
% 1.21/1.05  cnf(c_2870,plain,
% 1.21/1.05      ( v3_pre_topc(X0,sK2) != iProver_top
% 1.21/1.05      | v3_pre_topc(X0,sK4) = iProver_top
% 1.21/1.05      | r1_tarski(X0,u1_struct_0(sK2)) != iProver_top
% 1.21/1.05      | r1_tarski(X0,u1_struct_0(sK4)) != iProver_top ),
% 1.21/1.05      inference(superposition,[status(thm)],[c_1393,c_1924]) ).
% 1.21/1.05  
% 1.21/1.05  cnf(c_4072,plain,
% 1.21/1.05      ( v3_pre_topc(sK1(sK4,sK5),sK2) != iProver_top
% 1.21/1.05      | v3_pre_topc(sK1(sK4,sK5),sK4) = iProver_top
% 1.21/1.05      | r1_tarski(sK1(sK4,sK5),u1_struct_0(sK2)) != iProver_top ),
% 1.21/1.05      inference(superposition,[status(thm)],[c_4067,c_2870]) ).
% 1.21/1.05  
% 1.21/1.05  cnf(c_8,plain,
% 1.21/1.05      ( ~ v3_pre_topc(sK1(X0,X1),X0)
% 1.21/1.05      | v1_tops_2(X1,X0)
% 1.21/1.05      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 1.21/1.05      | ~ l1_pre_topc(X0) ),
% 1.21/1.05      inference(cnf_transformation,[],[f42]) ).
% 1.21/1.05  
% 1.21/1.05  cnf(c_318,plain,
% 1.21/1.05      ( ~ v3_pre_topc(sK1(X0,X1),X0)
% 1.21/1.05      | v1_tops_2(X1,X0)
% 1.21/1.05      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 1.21/1.05      | sK4 != X0 ),
% 1.21/1.05      inference(resolution_lifted,[status(thm)],[c_8,c_264]) ).
% 1.21/1.05  
% 1.21/1.05  cnf(c_319,plain,
% 1.21/1.05      ( ~ v3_pre_topc(sK1(sK4,X0),sK4)
% 1.21/1.05      | v1_tops_2(X0,sK4)
% 1.21/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) ),
% 1.21/1.05      inference(unflattening,[status(thm)],[c_318]) ).
% 1.21/1.05  
% 1.21/1.05  cnf(c_660,plain,
% 1.21/1.05      ( ~ v3_pre_topc(sK1(sK4,X0),sK4)
% 1.21/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 1.21/1.05      | sK4 != sK4
% 1.21/1.05      | sK5 != X0 ),
% 1.21/1.05      inference(resolution_lifted,[status(thm)],[c_13,c_319]) ).
% 1.21/1.05  
% 1.21/1.05  cnf(c_661,plain,
% 1.21/1.05      ( ~ v3_pre_topc(sK1(sK4,sK5),sK4)
% 1.21/1.05      | ~ m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) ),
% 1.21/1.05      inference(unflattening,[status(thm)],[c_660]) ).
% 1.21/1.05  
% 1.21/1.05  cnf(c_662,plain,
% 1.21/1.05      ( v3_pre_topc(sK1(sK4,sK5),sK4) != iProver_top
% 1.21/1.05      | m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top ),
% 1.21/1.05      inference(predicate_to_equality,[status(thm)],[c_661]) ).
% 1.21/1.05  
% 1.21/1.05  cnf(c_1567,plain,
% 1.21/1.05      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 1.21/1.05      | r1_tarski(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 1.21/1.05      inference(instantiation,[status(thm)],[c_6]) ).
% 1.21/1.05  
% 1.21/1.05  cnf(c_1568,plain,
% 1.21/1.05      ( m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top
% 1.21/1.05      | r1_tarski(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 1.21/1.05      inference(predicate_to_equality,[status(thm)],[c_1567]) ).
% 1.21/1.05  
% 1.21/1.05  cnf(c_18,negated_conjecture,
% 1.21/1.05      ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
% 1.21/1.05      inference(cnf_transformation,[],[f45]) ).
% 1.21/1.05  
% 1.21/1.05  cnf(c_1388,plain,
% 1.21/1.05      ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top ),
% 1.21/1.05      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 1.21/1.05  
% 1.21/1.05  cnf(c_14,negated_conjecture,
% 1.21/1.05      ( sK3 = sK5 ),
% 1.21/1.05      inference(cnf_transformation,[],[f49]) ).
% 1.21/1.05  
% 1.21/1.05  cnf(c_1405,plain,
% 1.21/1.05      ( m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top ),
% 1.21/1.05      inference(light_normalisation,[status(thm)],[c_1388,c_14]) ).
% 1.21/1.05  
% 1.21/1.05  cnf(c_1800,plain,
% 1.21/1.05      ( r1_tarski(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 1.21/1.05      inference(superposition,[status(thm)],[c_1405,c_1392]) ).
% 1.21/1.05  
% 1.21/1.05  cnf(c_11,plain,
% 1.21/1.05      ( v3_pre_topc(X0,X1)
% 1.21/1.05      | ~ v1_tops_2(X2,X1)
% 1.21/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.21/1.05      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 1.21/1.05      | ~ r2_hidden(X0,X2)
% 1.21/1.05      | ~ l1_pre_topc(X1) ),
% 1.21/1.05      inference(cnf_transformation,[],[f39]) ).
% 1.21/1.05  
% 1.21/1.05  cnf(c_333,plain,
% 1.21/1.05      ( v3_pre_topc(X0,X1)
% 1.21/1.05      | ~ v1_tops_2(X2,X1)
% 1.21/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.21/1.05      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 1.21/1.05      | ~ r2_hidden(X0,X2)
% 1.21/1.05      | sK2 != X1 ),
% 1.21/1.05      inference(resolution_lifted,[status(thm)],[c_11,c_19]) ).
% 1.21/1.05  
% 1.21/1.05  cnf(c_334,plain,
% 1.21/1.05      ( v3_pre_topc(X0,sK2)
% 1.21/1.05      | ~ v1_tops_2(X1,sK2)
% 1.21/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.21/1.05      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 1.21/1.05      | ~ r2_hidden(X0,X1) ),
% 1.21/1.05      inference(unflattening,[status(thm)],[c_333]) ).
% 1.21/1.05  
% 1.21/1.05  cnf(c_1383,plain,
% 1.21/1.05      ( v3_pre_topc(X0,sK2) = iProver_top
% 1.21/1.05      | v1_tops_2(X1,sK2) != iProver_top
% 1.21/1.05      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.21/1.05      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
% 1.21/1.05      | r2_hidden(X0,X1) != iProver_top ),
% 1.21/1.05      inference(predicate_to_equality,[status(thm)],[c_334]) ).
% 1.21/1.05  
% 1.21/1.05  cnf(c_1703,plain,
% 1.21/1.05      ( v3_pre_topc(X0,sK2) = iProver_top
% 1.21/1.05      | v1_tops_2(sK5,sK2) != iProver_top
% 1.21/1.05      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.21/1.05      | r2_hidden(X0,sK5) != iProver_top ),
% 1.21/1.05      inference(superposition,[status(thm)],[c_1405,c_1383]) ).
% 1.21/1.05  
% 1.21/1.05  cnf(c_16,negated_conjecture,
% 1.21/1.05      ( v1_tops_2(sK3,sK2) ),
% 1.21/1.05      inference(cnf_transformation,[],[f47]) ).
% 1.21/1.05  
% 1.21/1.05  cnf(c_1389,plain,
% 1.21/1.05      ( v1_tops_2(sK3,sK2) = iProver_top ),
% 1.21/1.05      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 1.21/1.05  
% 1.21/1.05  cnf(c_1400,plain,
% 1.21/1.05      ( v1_tops_2(sK5,sK2) = iProver_top ),
% 1.21/1.05      inference(light_normalisation,[status(thm)],[c_1389,c_14]) ).
% 1.21/1.05  
% 1.21/1.05  cnf(c_2149,plain,
% 1.21/1.05      ( v3_pre_topc(X0,sK2) = iProver_top
% 1.21/1.05      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.21/1.05      | r2_hidden(X0,sK5) != iProver_top ),
% 1.21/1.05      inference(global_propositional_subsumption,
% 1.21/1.05                [status(thm)],
% 1.21/1.05                [c_1703,c_1400]) ).
% 1.21/1.05  
% 1.21/1.05  cnf(c_2158,plain,
% 1.21/1.05      ( v3_pre_topc(X0,sK2) = iProver_top
% 1.21/1.05      | r2_hidden(X0,sK5) != iProver_top
% 1.21/1.05      | r1_tarski(X0,u1_struct_0(sK2)) != iProver_top ),
% 1.21/1.05      inference(superposition,[status(thm)],[c_1393,c_2149]) ).
% 1.21/1.05  
% 1.21/1.05  cnf(c_3255,plain,
% 1.21/1.05      ( v3_pre_topc(sK1(sK4,sK5),sK2) = iProver_top
% 1.21/1.05      | r2_hidden(sK1(sK4,sK5),sK5) != iProver_top
% 1.21/1.05      | r1_tarski(sK5,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 1.21/1.05      inference(superposition,[status(thm)],[c_2676,c_2158]) ).
% 1.21/1.05  
% 1.21/1.05  cnf(c_3923,plain,
% 1.21/1.05      ( v3_pre_topc(sK1(sK4,sK5),sK2) != iProver_top
% 1.21/1.05      | v3_pre_topc(sK1(sK4,sK5),sK4) = iProver_top
% 1.21/1.05      | r1_tarski(sK1(sK4,sK5),u1_struct_0(sK2)) != iProver_top
% 1.21/1.05      | r1_tarski(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 1.21/1.05      inference(superposition,[status(thm)],[c_2676,c_2870]) ).
% 1.21/1.05  
% 1.21/1.05  cnf(c_4250,plain,
% 1.21/1.05      ( r1_tarski(sK1(sK4,sK5),u1_struct_0(sK2)) != iProver_top ),
% 1.21/1.05      inference(global_propositional_subsumption,
% 1.21/1.05                [status(thm)],
% 1.21/1.05                [c_4072,c_24,c_640,c_662,c_1568,c_1800,c_3255,c_3923]) ).
% 1.21/1.05  
% 1.21/1.05  cnf(c_4255,plain,
% 1.21/1.05      ( r1_tarski(sK5,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 1.21/1.05      inference(superposition,[status(thm)],[c_2676,c_4250]) ).
% 1.21/1.05  
% 1.21/1.05  cnf(contradiction,plain,
% 1.21/1.05      ( $false ),
% 1.21/1.05      inference(minisat,[status(thm)],[c_4255,c_1800]) ).
% 1.21/1.05  
% 1.21/1.05  
% 1.21/1.05  % SZS output end CNFRefutation for theBenchmark.p
% 1.21/1.05  
% 1.21/1.05  ------                               Statistics
% 1.21/1.05  
% 1.21/1.05  ------ General
% 1.21/1.05  
% 1.21/1.05  abstr_ref_over_cycles:                  0
% 1.21/1.05  abstr_ref_under_cycles:                 0
% 1.21/1.05  gc_basic_clause_elim:                   0
% 1.21/1.05  forced_gc_time:                         0
% 1.21/1.05  parsing_time:                           0.007
% 1.21/1.05  unif_index_cands_time:                  0.
% 1.21/1.05  unif_index_add_time:                    0.
% 1.21/1.05  orderings_time:                         0.
% 1.21/1.05  out_proof_time:                         0.049
% 1.21/1.05  total_time:                             0.191
% 1.21/1.05  num_of_symbols:                         46
% 1.21/1.05  num_of_terms:                           2687
% 1.21/1.05  
% 1.21/1.05  ------ Preprocessing
% 1.21/1.05  
% 1.21/1.05  num_of_splits:                          0
% 1.21/1.05  num_of_split_atoms:                     0
% 1.21/1.05  num_of_reused_defs:                     0
% 1.21/1.05  num_eq_ax_congr_red:                    10
% 1.21/1.05  num_of_sem_filtered_clauses:            1
% 1.21/1.05  num_of_subtypes:                        0
% 1.21/1.05  monotx_restored_types:                  0
% 1.21/1.05  sat_num_of_epr_types:                   0
% 1.21/1.05  sat_num_of_non_cyclic_types:            0
% 1.21/1.05  sat_guarded_non_collapsed_types:        0
% 1.21/1.05  num_pure_diseq_elim:                    0
% 1.21/1.05  simp_replaced_by:                       0
% 1.21/1.05  res_preprocessed:                       83
% 1.21/1.05  prep_upred:                             0
% 1.21/1.05  prep_unflattend:                        46
% 1.21/1.05  smt_new_axioms:                         0
% 1.21/1.05  pred_elim_cands:                        7
% 1.21/1.05  pred_elim:                              2
% 1.21/1.05  pred_elim_cl:                           -1
% 1.21/1.05  pred_elim_cycles:                       4
% 1.21/1.05  merged_defs:                            12
% 1.21/1.05  merged_defs_ncl:                        0
% 1.21/1.05  bin_hyper_res:                          13
% 1.21/1.05  prep_cycles:                            3
% 1.21/1.05  pred_elim_time:                         0.011
% 1.21/1.05  splitting_time:                         0.
% 1.21/1.05  sem_filter_time:                        0.
% 1.21/1.05  monotx_time:                            0.
% 1.21/1.05  subtype_inf_time:                       0.
% 1.21/1.05  
% 1.21/1.05  ------ Problem properties
% 1.21/1.05  
% 1.21/1.05  clauses:                                21
% 1.21/1.05  conjectures:                            5
% 1.21/1.05  epr:                                    4
% 1.21/1.05  horn:                                   16
% 1.21/1.05  ground:                                 5
% 1.21/1.05  unary:                                  5
% 1.21/1.05  binary:                                 4
% 1.21/1.05  lits:                                   54
% 1.21/1.05  lits_eq:                                3
% 1.21/1.05  fd_pure:                                0
% 1.21/1.05  fd_pseudo:                              0
% 1.21/1.05  fd_cond:                                0
% 1.21/1.05  fd_pseudo_cond:                         2
% 1.21/1.05  ac_symbols:                             0
% 1.21/1.05  
% 1.21/1.05  ------ Propositional Solver
% 1.21/1.05  
% 1.21/1.05  prop_solver_calls:                      23
% 1.21/1.05  prop_fast_solver_calls:                 712
% 1.21/1.05  smt_solver_calls:                       0
% 1.21/1.05  smt_fast_solver_calls:                  0
% 1.21/1.05  prop_num_of_clauses:                    1334
% 1.21/1.05  prop_preprocess_simplified:             3934
% 1.21/1.05  prop_fo_subsumed:                       17
% 1.21/1.05  prop_solver_time:                       0.
% 1.21/1.05  smt_solver_time:                        0.
% 1.21/1.05  smt_fast_solver_time:                   0.
% 1.21/1.05  prop_fast_solver_time:                  0.
% 1.21/1.05  prop_unsat_core_time:                   0.
% 1.21/1.05  
% 1.21/1.05  ------ QBF
% 1.21/1.05  
% 1.21/1.05  qbf_q_res:                              0
% 1.21/1.05  qbf_num_tautologies:                    0
% 1.21/1.05  qbf_prep_cycles:                        0
% 1.21/1.05  
% 1.21/1.05  ------ BMC1
% 1.21/1.05  
% 1.21/1.05  bmc1_current_bound:                     -1
% 1.21/1.05  bmc1_last_solved_bound:                 -1
% 1.21/1.05  bmc1_unsat_core_size:                   -1
% 1.21/1.05  bmc1_unsat_core_parents_size:           -1
% 1.21/1.05  bmc1_merge_next_fun:                    0
% 1.21/1.05  bmc1_unsat_core_clauses_time:           0.
% 1.21/1.05  
% 1.21/1.05  ------ Instantiation
% 1.21/1.05  
% 1.21/1.05  inst_num_of_clauses:                    349
% 1.21/1.05  inst_num_in_passive:                    68
% 1.21/1.05  inst_num_in_active:                     211
% 1.21/1.05  inst_num_in_unprocessed:                70
% 1.21/1.05  inst_num_of_loops:                      260
% 1.21/1.05  inst_num_of_learning_restarts:          0
% 1.21/1.05  inst_num_moves_active_passive:          45
% 1.21/1.05  inst_lit_activity:                      0
% 1.21/1.05  inst_lit_activity_moves:                0
% 1.21/1.05  inst_num_tautologies:                   0
% 1.21/1.05  inst_num_prop_implied:                  0
% 1.21/1.05  inst_num_existing_simplified:           0
% 1.21/1.05  inst_num_eq_res_simplified:             0
% 1.21/1.05  inst_num_child_elim:                    0
% 1.21/1.05  inst_num_of_dismatching_blockings:      45
% 1.21/1.05  inst_num_of_non_proper_insts:           333
% 1.21/1.05  inst_num_of_duplicates:                 0
% 1.21/1.05  inst_inst_num_from_inst_to_res:         0
% 1.21/1.05  inst_dismatching_checking_time:         0.
% 1.21/1.05  
% 1.21/1.05  ------ Resolution
% 1.21/1.05  
% 1.21/1.05  res_num_of_clauses:                     0
% 1.21/1.05  res_num_in_passive:                     0
% 1.21/1.05  res_num_in_active:                      0
% 1.21/1.05  res_num_of_loops:                       86
% 1.21/1.05  res_forward_subset_subsumed:            57
% 1.21/1.05  res_backward_subset_subsumed:           0
% 1.21/1.05  res_forward_subsumed:                   0
% 1.21/1.05  res_backward_subsumed:                  0
% 1.21/1.05  res_forward_subsumption_resolution:     0
% 1.21/1.05  res_backward_subsumption_resolution:    0
% 1.21/1.05  res_clause_to_clause_subsumption:       145
% 1.21/1.05  res_orphan_elimination:                 0
% 1.21/1.05  res_tautology_del:                      60
% 1.21/1.05  res_num_eq_res_simplified:              0
% 1.21/1.05  res_num_sel_changes:                    0
% 1.21/1.05  res_moves_from_active_to_pass:          0
% 1.21/1.05  
% 1.21/1.05  ------ Superposition
% 1.21/1.05  
% 1.21/1.05  sup_time_total:                         0.
% 1.21/1.05  sup_time_generating:                    0.
% 1.21/1.05  sup_time_sim_full:                      0.
% 1.21/1.05  sup_time_sim_immed:                     0.
% 1.21/1.05  
% 1.21/1.05  sup_num_of_clauses:                     78
% 1.21/1.05  sup_num_in_active:                      52
% 1.21/1.05  sup_num_in_passive:                     26
% 1.21/1.05  sup_num_of_loops:                       51
% 1.21/1.05  sup_fw_superposition:                   48
% 1.21/1.05  sup_bw_superposition:                   26
% 1.21/1.05  sup_immediate_simplified:               9
% 1.21/1.05  sup_given_eliminated:                   0
% 1.21/1.05  comparisons_done:                       0
% 1.21/1.05  comparisons_avoided:                    0
% 1.21/1.05  
% 1.21/1.05  ------ Simplifications
% 1.21/1.05  
% 1.21/1.05  
% 1.21/1.05  sim_fw_subset_subsumed:                 7
% 1.21/1.05  sim_bw_subset_subsumed:                 1
% 1.21/1.05  sim_fw_subsumed:                        2
% 1.21/1.05  sim_bw_subsumed:                        0
% 1.21/1.05  sim_fw_subsumption_res:                 0
% 1.21/1.05  sim_bw_subsumption_res:                 0
% 1.21/1.05  sim_tautology_del:                      5
% 1.21/1.05  sim_eq_tautology_del:                   1
% 1.21/1.05  sim_eq_res_simp:                        0
% 1.21/1.05  sim_fw_demodulated:                     0
% 1.21/1.05  sim_bw_demodulated:                     0
% 1.21/1.05  sim_light_normalised:                   2
% 1.21/1.05  sim_joinable_taut:                      0
% 1.21/1.05  sim_joinable_simp:                      0
% 1.21/1.05  sim_ac_normalised:                      0
% 1.21/1.05  sim_smt_subsumption:                    0
% 1.21/1.05  
%------------------------------------------------------------------------------
