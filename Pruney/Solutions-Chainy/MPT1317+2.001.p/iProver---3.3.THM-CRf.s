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
% DateTime   : Thu Dec  3 12:16:47 EST 2020

% Result     : Theorem 0.90s
% Output     : CNFRefutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 325 expanded)
%              Number of clauses        :   60 (  79 expanded)
%              Number of leaves         :   16 ( 110 expanded)
%              Depth                    :   14
%              Number of atoms          :  463 (2000 expanded)
%              Number of equality atoms :   56 ( 283 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v4_pre_topc(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( X1 = X3
                     => v4_pre_topc(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v4_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v4_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( v4_pre_topc(X3,X2)
      | X1 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f59,plain,(
    ! [X2,X0,X3] :
      ( v4_pre_topc(X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v4_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f7,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v2_tops_2(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
                   => ( X1 = X3
                     => v2_tops_2(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ! [X2] :
                ( m1_pre_topc(X2,X0)
               => ( v2_tops_2(X1,X0)
                 => ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
                     => ( X1 = X3
                       => v2_tops_2(X3,X2) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_tops_2(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
              & v2_tops_2(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_tops_2(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
              & v2_tops_2(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f33,plain,(
    ! [X2,X1] :
      ( ? [X3] :
          ( ~ v2_tops_2(X3,X2)
          & X1 = X3
          & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
     => ( ~ v2_tops_2(sK6,X2)
        & sK6 = X1
        & m1_subset_1(sK6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ v2_tops_2(X3,X2)
              & X1 = X3
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
          & v2_tops_2(X1,X0)
          & m1_pre_topc(X2,X0) )
     => ( ? [X3] :
            ( ~ v2_tops_2(X3,sK5)
            & X1 = X3
            & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) )
        & v2_tops_2(X1,X0)
        & m1_pre_topc(sK5,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_tops_2(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
              & v2_tops_2(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ v2_tops_2(X3,X2)
                & sK4 = X3
                & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
            & v2_tops_2(sK4,X0)
            & m1_pre_topc(X2,X0) )
        & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ v2_tops_2(X3,X2)
                    & X1 = X3
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
                & v2_tops_2(X1,X0)
                & m1_pre_topc(X2,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_tops_2(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
              & v2_tops_2(X1,sK3)
              & m1_pre_topc(X2,sK3) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) )
      & l1_pre_topc(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ~ v2_tops_2(sK6,sK5)
    & sK4 = sK6
    & m1_subset_1(sK6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    & v2_tops_2(sK4,sK3)
    & m1_pre_topc(sK5,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    & l1_pre_topc(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f16,f33,f32,f31,f30])).

fof(f52,plain,(
    m1_pre_topc(sK5,sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f50,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK1(X0,X1),X0)
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( r1_tarski(sK1(X0,X1),X0)
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK1(X0,X1),X0)
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( r1_tarski(sK1(X0,X1),X0)
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f23])).

fof(f38,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f58,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f38])).

fof(f3,axiom,(
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
    inference(nnf_transformation,[],[f3])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v4_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( v4_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( v4_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_2(X1,X0)
              | ? [X2] :
                  ( ~ v4_pre_topc(X2,X0)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v4_pre_topc(X2,X0)
                  | ~ r2_hidden(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_2(X1,X0)
              | ? [X2] :
                  ( ~ v4_pre_topc(X2,X0)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v4_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v4_pre_topc(X2,X0)
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v4_pre_topc(sK2(X0,X1),X0)
        & r2_hidden(sK2(X0,X1),X1)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_2(X1,X0)
              | ( ~ v4_pre_topc(sK2(X0,X1),X0)
                & r2_hidden(sK2(X0,X1),X1)
                & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v4_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f27,f28])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( v4_pre_topc(X3,X0)
      | ~ r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f17])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).

fof(f35,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f51,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f34])).

fof(f55,plain,(
    sK4 = sK6 ),
    inference(cnf_transformation,[],[f34])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f56,plain,(
    ~ v2_tops_2(sK6,sK5) ),
    inference(cnf_transformation,[],[f34])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v2_tops_2(X1,X0)
      | ~ v4_pre_topc(sK2(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f44,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v2_tops_2(X1,X0)
      | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v2_tops_2(X1,X0)
      | r2_hidden(sK2(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f54,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) ),
    inference(cnf_transformation,[],[f34])).

fof(f53,plain,(
    v2_tops_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_14,plain,
    ( ~ v4_pre_topc(X0,X1)
    | v4_pre_topc(X0,X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_19,negated_conjecture,
    ( m1_pre_topc(sK5,sK3) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_298,plain,
    ( ~ v4_pre_topc(X0,X1)
    | v4_pre_topc(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X1)
    | sK3 != X1
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_19])).

cnf(c_299,plain,
    ( ~ v4_pre_topc(X0,sK3)
    | v4_pre_topc(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_298])).

cnf(c_21,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_303,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v4_pre_topc(X0,sK5)
    | ~ v4_pre_topc(X0,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_299,c_21])).

cnf(c_304,plain,
    ( ~ v4_pre_topc(X0,sK3)
    | v4_pre_topc(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(renaming,[status(thm)],[c_303])).

cnf(c_2480,plain,
    ( ~ v4_pre_topc(sK2(sK5,X0),sK3)
    | v4_pre_topc(sK2(sK5,X0),sK5)
    | ~ m1_subset_1(sK2(sK5,X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK2(sK5,X0),k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(instantiation,[status(thm)],[c_304])).

cnf(c_3649,plain,
    ( ~ v4_pre_topc(sK2(sK5,sK6),sK3)
    | v4_pre_topc(sK2(sK5,sK6),sK5)
    | ~ m1_subset_1(sK2(sK5,sK6),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK2(sK5,sK6),k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(instantiation,[status(thm)],[c_2480])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2219,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | r1_tarski(X0,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_3332,plain,
    ( ~ r2_hidden(sK2(sK5,sK6),k1_zfmisc_1(u1_struct_0(sK3)))
    | r1_tarski(sK2(sK5,sK6),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_2219])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1991,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(X0,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2617,plain,
    ( m1_subset_1(sK2(sK5,sK6),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(sK2(sK5,sK6),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1991])).

cnf(c_13,plain,
    ( v4_pre_topc(X0,X1)
    | ~ v2_tops_2(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ r2_hidden(X0,X2)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_359,plain,
    ( v4_pre_topc(X0,X1)
    | ~ v2_tops_2(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ r2_hidden(X0,X2)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_21])).

cnf(c_360,plain,
    ( v4_pre_topc(X0,sK3)
    | ~ v2_tops_2(X1,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | ~ r2_hidden(X0,X1) ),
    inference(unflattening,[status(thm)],[c_359])).

cnf(c_1751,plain,
    ( v4_pre_topc(X0,sK3)
    | ~ v2_tops_2(sK4,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | ~ r2_hidden(X0,sK4) ),
    inference(instantiation,[status(thm)],[c_360])).

cnf(c_2383,plain,
    ( v4_pre_topc(sK2(sK5,sK6),sK3)
    | ~ v2_tops_2(sK4,sK3)
    | ~ m1_subset_1(sK2(sK5,sK6),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | ~ r2_hidden(sK2(sK5,sK6),sK4) ),
    inference(instantiation,[status(thm)],[c_1751])).

cnf(c_1016,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2251,plain,
    ( sK2(sK5,sK6) = sK2(sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_1016])).

cnf(c_1019,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1808,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK2(sK5,sK6),sK6)
    | X0 != sK2(sK5,sK6)
    | X1 != sK6 ),
    inference(instantiation,[status(thm)],[c_1019])).

cnf(c_1996,plain,
    ( r2_hidden(X0,sK4)
    | ~ r2_hidden(sK2(sK5,sK6),sK6)
    | X0 != sK2(sK5,sK6)
    | sK4 != sK6 ),
    inference(instantiation,[status(thm)],[c_1808])).

cnf(c_2250,plain,
    ( r2_hidden(sK2(sK5,sK6),sK4)
    | ~ r2_hidden(sK2(sK5,sK6),sK6)
    | sK2(sK5,sK6) != sK2(sK5,sK6)
    | sK4 != sK6 ),
    inference(instantiation,[status(thm)],[c_1996])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1807,plain,
    ( r2_hidden(sK2(sK5,sK6),X0)
    | ~ r2_hidden(sK2(sK5,sK6),sK6)
    | ~ r1_tarski(sK6,X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2036,plain,
    ( r2_hidden(sK2(sK5,sK6),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(sK2(sK5,sK6),sK6)
    | ~ r1_tarski(sK6,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_1807])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1569,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_16,negated_conjecture,
    ( sK4 = sK6 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1589,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1569,c_16])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1573,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2013,plain,
    ( r1_tarski(sK6,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1589,c_1573])).

cnf(c_2019,plain,
    ( r1_tarski(sK6,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2013])).

cnf(c_15,negated_conjecture,
    ( ~ v2_tops_2(sK6,sK5) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_10,plain,
    ( ~ v4_pre_topc(sK2(X0,X1),X0)
    | v2_tops_2(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_9,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_287,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK3 != X0
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_19])).

cnf(c_288,plain,
    ( ~ l1_pre_topc(sK3)
    | l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_287])).

cnf(c_290,plain,
    ( l1_pre_topc(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_288,c_21])).

cnf(c_344,plain,
    ( ~ v4_pre_topc(sK2(X0,X1),X0)
    | v2_tops_2(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_290])).

cnf(c_345,plain,
    ( ~ v4_pre_topc(sK2(sK5,X0),sK5)
    | v2_tops_2(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) ),
    inference(unflattening,[status(thm)],[c_344])).

cnf(c_806,plain,
    ( ~ v4_pre_topc(sK2(sK5,X0),sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | sK5 != sK5
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_345])).

cnf(c_807,plain,
    ( ~ v4_pre_topc(sK2(sK5,sK6),sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) ),
    inference(unflattening,[status(thm)],[c_806])).

cnf(c_12,plain,
    ( v2_tops_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | m1_subset_1(sK2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_431,plain,
    ( v2_tops_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | m1_subset_1(sK2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_290])).

cnf(c_432,plain,
    ( v2_tops_2(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | m1_subset_1(sK2(sK5,X0),k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(unflattening,[status(thm)],[c_431])).

cnf(c_795,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | m1_subset_1(sK2(sK5,X0),k1_zfmisc_1(u1_struct_0(sK5)))
    | sK5 != sK5
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_432])).

cnf(c_796,plain,
    ( m1_subset_1(sK2(sK5,sK6),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) ),
    inference(unflattening,[status(thm)],[c_795])).

cnf(c_11,plain,
    ( v2_tops_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | r2_hidden(sK2(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_446,plain,
    ( v2_tops_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | r2_hidden(sK2(X1,X0),X0)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_290])).

cnf(c_447,plain,
    ( v2_tops_2(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | r2_hidden(sK2(sK5,X0),X0) ),
    inference(unflattening,[status(thm)],[c_446])).

cnf(c_784,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | r2_hidden(sK2(sK5,X0),X0)
    | sK5 != sK5
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_447])).

cnf(c_785,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | r2_hidden(sK2(sK5,sK6),sK6) ),
    inference(unflattening,[status(thm)],[c_784])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_18,negated_conjecture,
    ( v2_tops_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f53])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3649,c_3332,c_2617,c_2383,c_2251,c_2250,c_2036,c_2019,c_807,c_796,c_785,c_16,c_17,c_18,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:36:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 0.90/1.04  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.90/1.04  
% 0.90/1.04  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.90/1.04  
% 0.90/1.04  ------  iProver source info
% 0.90/1.04  
% 0.90/1.04  git: date: 2020-06-30 10:37:57 +0100
% 0.90/1.04  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.90/1.04  git: non_committed_changes: false
% 0.90/1.04  git: last_make_outside_of_git: false
% 0.90/1.04  
% 0.90/1.04  ------ 
% 0.90/1.04  
% 0.90/1.04  ------ Input Options
% 0.90/1.04  
% 0.90/1.04  --out_options                           all
% 0.90/1.04  --tptp_safe_out                         true
% 0.90/1.04  --problem_path                          ""
% 0.90/1.04  --include_path                          ""
% 0.90/1.04  --clausifier                            res/vclausify_rel
% 0.90/1.04  --clausifier_options                    --mode clausify
% 0.90/1.04  --stdin                                 false
% 0.90/1.04  --stats_out                             all
% 0.90/1.04  
% 0.90/1.04  ------ General Options
% 0.90/1.04  
% 0.90/1.04  --fof                                   false
% 0.90/1.04  --time_out_real                         305.
% 0.90/1.04  --time_out_virtual                      -1.
% 0.90/1.04  --symbol_type_check                     false
% 0.90/1.04  --clausify_out                          false
% 0.90/1.04  --sig_cnt_out                           false
% 0.90/1.04  --trig_cnt_out                          false
% 0.90/1.04  --trig_cnt_out_tolerance                1.
% 0.90/1.04  --trig_cnt_out_sk_spl                   false
% 0.90/1.04  --abstr_cl_out                          false
% 0.90/1.04  
% 0.90/1.04  ------ Global Options
% 0.90/1.04  
% 0.90/1.04  --schedule                              default
% 0.90/1.04  --add_important_lit                     false
% 0.90/1.04  --prop_solver_per_cl                    1000
% 0.90/1.04  --min_unsat_core                        false
% 0.90/1.04  --soft_assumptions                      false
% 0.90/1.04  --soft_lemma_size                       3
% 0.90/1.04  --prop_impl_unit_size                   0
% 0.90/1.04  --prop_impl_unit                        []
% 0.90/1.04  --share_sel_clauses                     true
% 0.90/1.04  --reset_solvers                         false
% 0.90/1.04  --bc_imp_inh                            [conj_cone]
% 0.90/1.04  --conj_cone_tolerance                   3.
% 0.90/1.04  --extra_neg_conj                        none
% 0.90/1.04  --large_theory_mode                     true
% 0.90/1.04  --prolific_symb_bound                   200
% 0.90/1.04  --lt_threshold                          2000
% 0.90/1.04  --clause_weak_htbl                      true
% 0.90/1.04  --gc_record_bc_elim                     false
% 0.90/1.04  
% 0.90/1.04  ------ Preprocessing Options
% 0.90/1.04  
% 0.90/1.04  --preprocessing_flag                    true
% 0.90/1.04  --time_out_prep_mult                    0.1
% 0.90/1.04  --splitting_mode                        input
% 0.90/1.04  --splitting_grd                         true
% 0.90/1.04  --splitting_cvd                         false
% 0.90/1.04  --splitting_cvd_svl                     false
% 0.90/1.04  --splitting_nvd                         32
% 0.90/1.04  --sub_typing                            true
% 0.90/1.04  --prep_gs_sim                           true
% 0.90/1.04  --prep_unflatten                        true
% 0.90/1.04  --prep_res_sim                          true
% 0.90/1.04  --prep_upred                            true
% 0.90/1.04  --prep_sem_filter                       exhaustive
% 0.90/1.04  --prep_sem_filter_out                   false
% 0.90/1.04  --pred_elim                             true
% 0.90/1.04  --res_sim_input                         true
% 0.90/1.04  --eq_ax_congr_red                       true
% 0.90/1.04  --pure_diseq_elim                       true
% 0.90/1.04  --brand_transform                       false
% 0.90/1.04  --non_eq_to_eq                          false
% 0.90/1.04  --prep_def_merge                        true
% 0.90/1.04  --prep_def_merge_prop_impl              false
% 0.90/1.04  --prep_def_merge_mbd                    true
% 0.90/1.04  --prep_def_merge_tr_red                 false
% 0.90/1.04  --prep_def_merge_tr_cl                  false
% 0.90/1.04  --smt_preprocessing                     true
% 0.90/1.04  --smt_ac_axioms                         fast
% 0.90/1.04  --preprocessed_out                      false
% 0.90/1.04  --preprocessed_stats                    false
% 0.90/1.04  
% 0.90/1.04  ------ Abstraction refinement Options
% 0.90/1.04  
% 0.90/1.04  --abstr_ref                             []
% 0.90/1.04  --abstr_ref_prep                        false
% 0.90/1.04  --abstr_ref_until_sat                   false
% 0.90/1.04  --abstr_ref_sig_restrict                funpre
% 0.90/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 0.90/1.04  --abstr_ref_under                       []
% 0.90/1.04  
% 0.90/1.04  ------ SAT Options
% 0.90/1.04  
% 0.90/1.04  --sat_mode                              false
% 0.90/1.04  --sat_fm_restart_options                ""
% 0.90/1.04  --sat_gr_def                            false
% 0.90/1.04  --sat_epr_types                         true
% 0.90/1.04  --sat_non_cyclic_types                  false
% 0.90/1.04  --sat_finite_models                     false
% 0.90/1.04  --sat_fm_lemmas                         false
% 0.90/1.04  --sat_fm_prep                           false
% 0.90/1.04  --sat_fm_uc_incr                        true
% 0.90/1.04  --sat_out_model                         small
% 0.90/1.04  --sat_out_clauses                       false
% 0.90/1.04  
% 0.90/1.04  ------ QBF Options
% 0.90/1.04  
% 0.90/1.04  --qbf_mode                              false
% 0.90/1.04  --qbf_elim_univ                         false
% 0.90/1.04  --qbf_dom_inst                          none
% 0.90/1.04  --qbf_dom_pre_inst                      false
% 0.90/1.04  --qbf_sk_in                             false
% 0.90/1.04  --qbf_pred_elim                         true
% 0.90/1.04  --qbf_split                             512
% 0.90/1.04  
% 0.90/1.04  ------ BMC1 Options
% 0.90/1.04  
% 0.90/1.04  --bmc1_incremental                      false
% 0.90/1.04  --bmc1_axioms                           reachable_all
% 0.90/1.04  --bmc1_min_bound                        0
% 0.90/1.04  --bmc1_max_bound                        -1
% 0.90/1.04  --bmc1_max_bound_default                -1
% 0.90/1.04  --bmc1_symbol_reachability              true
% 0.90/1.04  --bmc1_property_lemmas                  false
% 0.90/1.04  --bmc1_k_induction                      false
% 0.90/1.04  --bmc1_non_equiv_states                 false
% 0.90/1.04  --bmc1_deadlock                         false
% 0.90/1.04  --bmc1_ucm                              false
% 0.90/1.04  --bmc1_add_unsat_core                   none
% 0.90/1.04  --bmc1_unsat_core_children              false
% 0.90/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 0.90/1.04  --bmc1_out_stat                         full
% 0.90/1.04  --bmc1_ground_init                      false
% 0.90/1.04  --bmc1_pre_inst_next_state              false
% 0.90/1.04  --bmc1_pre_inst_state                   false
% 0.90/1.04  --bmc1_pre_inst_reach_state             false
% 0.90/1.04  --bmc1_out_unsat_core                   false
% 0.90/1.04  --bmc1_aig_witness_out                  false
% 0.90/1.04  --bmc1_verbose                          false
% 0.90/1.04  --bmc1_dump_clauses_tptp                false
% 0.90/1.04  --bmc1_dump_unsat_core_tptp             false
% 0.90/1.04  --bmc1_dump_file                        -
% 0.90/1.04  --bmc1_ucm_expand_uc_limit              128
% 0.90/1.04  --bmc1_ucm_n_expand_iterations          6
% 0.90/1.04  --bmc1_ucm_extend_mode                  1
% 0.90/1.04  --bmc1_ucm_init_mode                    2
% 0.90/1.04  --bmc1_ucm_cone_mode                    none
% 0.90/1.04  --bmc1_ucm_reduced_relation_type        0
% 0.90/1.04  --bmc1_ucm_relax_model                  4
% 0.90/1.04  --bmc1_ucm_full_tr_after_sat            true
% 0.90/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 0.90/1.04  --bmc1_ucm_layered_model                none
% 0.90/1.04  --bmc1_ucm_max_lemma_size               10
% 0.90/1.04  
% 0.90/1.04  ------ AIG Options
% 0.90/1.04  
% 0.90/1.04  --aig_mode                              false
% 0.90/1.04  
% 0.90/1.04  ------ Instantiation Options
% 0.90/1.04  
% 0.90/1.04  --instantiation_flag                    true
% 0.90/1.04  --inst_sos_flag                         false
% 0.90/1.04  --inst_sos_phase                        true
% 0.90/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.90/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.90/1.04  --inst_lit_sel_side                     num_symb
% 0.90/1.04  --inst_solver_per_active                1400
% 0.90/1.04  --inst_solver_calls_frac                1.
% 0.90/1.04  --inst_passive_queue_type               priority_queues
% 0.90/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.90/1.04  --inst_passive_queues_freq              [25;2]
% 0.90/1.04  --inst_dismatching                      true
% 0.90/1.04  --inst_eager_unprocessed_to_passive     true
% 0.90/1.04  --inst_prop_sim_given                   true
% 0.90/1.04  --inst_prop_sim_new                     false
% 0.90/1.04  --inst_subs_new                         false
% 0.90/1.04  --inst_eq_res_simp                      false
% 0.90/1.04  --inst_subs_given                       false
% 0.90/1.04  --inst_orphan_elimination               true
% 0.90/1.04  --inst_learning_loop_flag               true
% 0.90/1.04  --inst_learning_start                   3000
% 0.90/1.04  --inst_learning_factor                  2
% 0.90/1.04  --inst_start_prop_sim_after_learn       3
% 0.90/1.04  --inst_sel_renew                        solver
% 0.90/1.04  --inst_lit_activity_flag                true
% 0.90/1.04  --inst_restr_to_given                   false
% 0.90/1.04  --inst_activity_threshold               500
% 0.90/1.04  --inst_out_proof                        true
% 0.90/1.04  
% 0.90/1.04  ------ Resolution Options
% 0.90/1.04  
% 0.90/1.04  --resolution_flag                       true
% 0.90/1.04  --res_lit_sel                           adaptive
% 0.90/1.04  --res_lit_sel_side                      none
% 0.90/1.04  --res_ordering                          kbo
% 0.90/1.04  --res_to_prop_solver                    active
% 0.90/1.04  --res_prop_simpl_new                    false
% 0.90/1.04  --res_prop_simpl_given                  true
% 0.90/1.04  --res_passive_queue_type                priority_queues
% 0.90/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.90/1.04  --res_passive_queues_freq               [15;5]
% 0.90/1.04  --res_forward_subs                      full
% 0.90/1.04  --res_backward_subs                     full
% 0.90/1.04  --res_forward_subs_resolution           true
% 0.90/1.04  --res_backward_subs_resolution          true
% 0.90/1.04  --res_orphan_elimination                true
% 0.90/1.04  --res_time_limit                        2.
% 0.90/1.04  --res_out_proof                         true
% 0.90/1.04  
% 0.90/1.04  ------ Superposition Options
% 0.90/1.04  
% 0.90/1.04  --superposition_flag                    true
% 0.90/1.04  --sup_passive_queue_type                priority_queues
% 0.90/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.90/1.04  --sup_passive_queues_freq               [8;1;4]
% 0.90/1.04  --demod_completeness_check              fast
% 0.90/1.04  --demod_use_ground                      true
% 0.90/1.04  --sup_to_prop_solver                    passive
% 0.90/1.04  --sup_prop_simpl_new                    true
% 0.90/1.04  --sup_prop_simpl_given                  true
% 0.90/1.04  --sup_fun_splitting                     false
% 0.90/1.04  --sup_smt_interval                      50000
% 0.90/1.04  
% 0.90/1.04  ------ Superposition Simplification Setup
% 0.90/1.04  
% 0.90/1.04  --sup_indices_passive                   []
% 0.90/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.90/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.90/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.90/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 0.90/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.90/1.04  --sup_full_bw                           [BwDemod]
% 0.90/1.04  --sup_immed_triv                        [TrivRules]
% 0.90/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.90/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.90/1.04  --sup_immed_bw_main                     []
% 0.90/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.90/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 0.90/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.90/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.90/1.04  
% 0.90/1.04  ------ Combination Options
% 0.90/1.04  
% 0.90/1.04  --comb_res_mult                         3
% 0.90/1.04  --comb_sup_mult                         2
% 0.90/1.04  --comb_inst_mult                        10
% 0.90/1.04  
% 0.90/1.04  ------ Debug Options
% 0.90/1.04  
% 0.90/1.04  --dbg_backtrace                         false
% 0.90/1.04  --dbg_dump_prop_clauses                 false
% 0.90/1.04  --dbg_dump_prop_clauses_file            -
% 0.90/1.04  --dbg_out_stat                          false
% 0.90/1.04  ------ Parsing...
% 0.90/1.04  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.90/1.04  
% 0.90/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 0.90/1.04  
% 0.90/1.04  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.90/1.04  
% 0.90/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.90/1.04  ------ Proving...
% 0.90/1.04  ------ Problem Properties 
% 0.90/1.04  
% 0.90/1.04  
% 0.90/1.04  clauses                                 23
% 0.90/1.04  conjectures                             5
% 0.90/1.04  EPR                                     4
% 0.90/1.04  Horn                                    17
% 0.90/1.04  unary                                   5
% 0.90/1.04  binary                                  6
% 0.90/1.04  lits                                    58
% 0.90/1.04  lits eq                                 3
% 0.90/1.04  fd_pure                                 0
% 0.90/1.04  fd_pseudo                               0
% 0.90/1.04  fd_cond                                 0
% 0.90/1.04  fd_pseudo_cond                          2
% 0.90/1.04  AC symbols                              0
% 0.90/1.04  
% 0.90/1.04  ------ Schedule dynamic 5 is on 
% 0.90/1.04  
% 0.90/1.04  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.90/1.04  
% 0.90/1.04  
% 0.90/1.04  ------ 
% 0.90/1.04  Current options:
% 0.90/1.04  ------ 
% 0.90/1.04  
% 0.90/1.04  ------ Input Options
% 0.90/1.04  
% 0.90/1.04  --out_options                           all
% 0.90/1.04  --tptp_safe_out                         true
% 0.90/1.04  --problem_path                          ""
% 0.90/1.04  --include_path                          ""
% 0.90/1.04  --clausifier                            res/vclausify_rel
% 0.90/1.04  --clausifier_options                    --mode clausify
% 0.90/1.04  --stdin                                 false
% 0.90/1.04  --stats_out                             all
% 0.90/1.04  
% 0.90/1.04  ------ General Options
% 0.90/1.04  
% 0.90/1.04  --fof                                   false
% 0.90/1.04  --time_out_real                         305.
% 0.90/1.04  --time_out_virtual                      -1.
% 0.90/1.04  --symbol_type_check                     false
% 0.90/1.04  --clausify_out                          false
% 0.90/1.04  --sig_cnt_out                           false
% 0.90/1.04  --trig_cnt_out                          false
% 0.90/1.04  --trig_cnt_out_tolerance                1.
% 0.90/1.04  --trig_cnt_out_sk_spl                   false
% 0.90/1.04  --abstr_cl_out                          false
% 0.90/1.04  
% 0.90/1.04  ------ Global Options
% 0.90/1.04  
% 0.90/1.04  --schedule                              default
% 0.90/1.04  --add_important_lit                     false
% 0.90/1.04  --prop_solver_per_cl                    1000
% 0.90/1.04  --min_unsat_core                        false
% 0.90/1.04  --soft_assumptions                      false
% 0.90/1.04  --soft_lemma_size                       3
% 0.90/1.04  --prop_impl_unit_size                   0
% 0.90/1.04  --prop_impl_unit                        []
% 0.90/1.04  --share_sel_clauses                     true
% 0.90/1.04  --reset_solvers                         false
% 0.90/1.04  --bc_imp_inh                            [conj_cone]
% 0.90/1.04  --conj_cone_tolerance                   3.
% 0.90/1.04  --extra_neg_conj                        none
% 0.90/1.04  --large_theory_mode                     true
% 0.90/1.04  --prolific_symb_bound                   200
% 0.90/1.04  --lt_threshold                          2000
% 0.90/1.04  --clause_weak_htbl                      true
% 0.90/1.04  --gc_record_bc_elim                     false
% 0.90/1.04  
% 0.90/1.04  ------ Preprocessing Options
% 0.90/1.04  
% 0.90/1.04  --preprocessing_flag                    true
% 0.90/1.04  --time_out_prep_mult                    0.1
% 0.90/1.04  --splitting_mode                        input
% 0.90/1.04  --splitting_grd                         true
% 0.90/1.04  --splitting_cvd                         false
% 0.90/1.04  --splitting_cvd_svl                     false
% 0.90/1.04  --splitting_nvd                         32
% 0.90/1.04  --sub_typing                            true
% 0.90/1.04  --prep_gs_sim                           true
% 0.90/1.04  --prep_unflatten                        true
% 0.90/1.04  --prep_res_sim                          true
% 0.90/1.04  --prep_upred                            true
% 0.90/1.04  --prep_sem_filter                       exhaustive
% 0.90/1.04  --prep_sem_filter_out                   false
% 0.90/1.04  --pred_elim                             true
% 0.90/1.04  --res_sim_input                         true
% 0.90/1.04  --eq_ax_congr_red                       true
% 0.90/1.04  --pure_diseq_elim                       true
% 0.90/1.04  --brand_transform                       false
% 0.90/1.04  --non_eq_to_eq                          false
% 0.90/1.04  --prep_def_merge                        true
% 0.90/1.04  --prep_def_merge_prop_impl              false
% 0.90/1.04  --prep_def_merge_mbd                    true
% 0.90/1.04  --prep_def_merge_tr_red                 false
% 0.90/1.04  --prep_def_merge_tr_cl                  false
% 0.90/1.04  --smt_preprocessing                     true
% 0.90/1.04  --smt_ac_axioms                         fast
% 0.90/1.04  --preprocessed_out                      false
% 0.90/1.04  --preprocessed_stats                    false
% 0.90/1.04  
% 0.90/1.04  ------ Abstraction refinement Options
% 0.90/1.04  
% 0.90/1.04  --abstr_ref                             []
% 0.90/1.04  --abstr_ref_prep                        false
% 0.90/1.04  --abstr_ref_until_sat                   false
% 0.90/1.04  --abstr_ref_sig_restrict                funpre
% 0.90/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 0.90/1.04  --abstr_ref_under                       []
% 0.90/1.04  
% 0.90/1.04  ------ SAT Options
% 0.90/1.04  
% 0.90/1.04  --sat_mode                              false
% 0.90/1.04  --sat_fm_restart_options                ""
% 0.90/1.04  --sat_gr_def                            false
% 0.90/1.04  --sat_epr_types                         true
% 0.90/1.04  --sat_non_cyclic_types                  false
% 0.90/1.04  --sat_finite_models                     false
% 0.90/1.04  --sat_fm_lemmas                         false
% 0.90/1.04  --sat_fm_prep                           false
% 0.90/1.04  --sat_fm_uc_incr                        true
% 0.90/1.04  --sat_out_model                         small
% 0.90/1.04  --sat_out_clauses                       false
% 0.90/1.04  
% 0.90/1.04  ------ QBF Options
% 0.90/1.04  
% 0.90/1.04  --qbf_mode                              false
% 0.90/1.04  --qbf_elim_univ                         false
% 0.90/1.04  --qbf_dom_inst                          none
% 0.90/1.04  --qbf_dom_pre_inst                      false
% 0.90/1.04  --qbf_sk_in                             false
% 0.90/1.04  --qbf_pred_elim                         true
% 0.90/1.04  --qbf_split                             512
% 0.90/1.04  
% 0.90/1.04  ------ BMC1 Options
% 0.90/1.04  
% 0.90/1.04  --bmc1_incremental                      false
% 0.90/1.04  --bmc1_axioms                           reachable_all
% 0.90/1.04  --bmc1_min_bound                        0
% 0.90/1.04  --bmc1_max_bound                        -1
% 0.90/1.04  --bmc1_max_bound_default                -1
% 0.90/1.04  --bmc1_symbol_reachability              true
% 0.90/1.04  --bmc1_property_lemmas                  false
% 0.90/1.04  --bmc1_k_induction                      false
% 0.90/1.04  --bmc1_non_equiv_states                 false
% 0.90/1.04  --bmc1_deadlock                         false
% 0.90/1.04  --bmc1_ucm                              false
% 0.90/1.04  --bmc1_add_unsat_core                   none
% 0.90/1.04  --bmc1_unsat_core_children              false
% 0.90/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 0.90/1.04  --bmc1_out_stat                         full
% 0.90/1.04  --bmc1_ground_init                      false
% 0.90/1.04  --bmc1_pre_inst_next_state              false
% 0.90/1.04  --bmc1_pre_inst_state                   false
% 0.90/1.04  --bmc1_pre_inst_reach_state             false
% 0.90/1.04  --bmc1_out_unsat_core                   false
% 0.90/1.04  --bmc1_aig_witness_out                  false
% 0.90/1.04  --bmc1_verbose                          false
% 0.90/1.04  --bmc1_dump_clauses_tptp                false
% 0.90/1.04  --bmc1_dump_unsat_core_tptp             false
% 0.90/1.04  --bmc1_dump_file                        -
% 0.90/1.04  --bmc1_ucm_expand_uc_limit              128
% 0.90/1.04  --bmc1_ucm_n_expand_iterations          6
% 0.90/1.04  --bmc1_ucm_extend_mode                  1
% 0.90/1.04  --bmc1_ucm_init_mode                    2
% 0.90/1.04  --bmc1_ucm_cone_mode                    none
% 0.90/1.04  --bmc1_ucm_reduced_relation_type        0
% 0.90/1.04  --bmc1_ucm_relax_model                  4
% 0.90/1.04  --bmc1_ucm_full_tr_after_sat            true
% 0.90/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 0.90/1.04  --bmc1_ucm_layered_model                none
% 0.90/1.04  --bmc1_ucm_max_lemma_size               10
% 0.90/1.04  
% 0.90/1.04  ------ AIG Options
% 0.90/1.04  
% 0.90/1.04  --aig_mode                              false
% 0.90/1.04  
% 0.90/1.04  ------ Instantiation Options
% 0.90/1.04  
% 0.90/1.04  --instantiation_flag                    true
% 0.90/1.04  --inst_sos_flag                         false
% 0.90/1.04  --inst_sos_phase                        true
% 0.90/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.90/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.90/1.04  --inst_lit_sel_side                     none
% 0.90/1.04  --inst_solver_per_active                1400
% 0.90/1.04  --inst_solver_calls_frac                1.
% 0.90/1.04  --inst_passive_queue_type               priority_queues
% 0.90/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.90/1.04  --inst_passive_queues_freq              [25;2]
% 0.90/1.04  --inst_dismatching                      true
% 0.90/1.04  --inst_eager_unprocessed_to_passive     true
% 0.90/1.04  --inst_prop_sim_given                   true
% 0.90/1.04  --inst_prop_sim_new                     false
% 0.90/1.04  --inst_subs_new                         false
% 0.90/1.04  --inst_eq_res_simp                      false
% 0.90/1.04  --inst_subs_given                       false
% 0.90/1.04  --inst_orphan_elimination               true
% 0.90/1.04  --inst_learning_loop_flag               true
% 0.90/1.04  --inst_learning_start                   3000
% 0.90/1.04  --inst_learning_factor                  2
% 0.90/1.04  --inst_start_prop_sim_after_learn       3
% 0.90/1.04  --inst_sel_renew                        solver
% 0.90/1.04  --inst_lit_activity_flag                true
% 0.90/1.04  --inst_restr_to_given                   false
% 0.90/1.04  --inst_activity_threshold               500
% 0.90/1.04  --inst_out_proof                        true
% 0.90/1.04  
% 0.90/1.04  ------ Resolution Options
% 0.90/1.04  
% 0.90/1.04  --resolution_flag                       false
% 0.90/1.04  --res_lit_sel                           adaptive
% 0.90/1.04  --res_lit_sel_side                      none
% 0.90/1.04  --res_ordering                          kbo
% 0.90/1.04  --res_to_prop_solver                    active
% 0.90/1.04  --res_prop_simpl_new                    false
% 0.90/1.04  --res_prop_simpl_given                  true
% 0.90/1.04  --res_passive_queue_type                priority_queues
% 0.90/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.90/1.04  --res_passive_queues_freq               [15;5]
% 0.90/1.04  --res_forward_subs                      full
% 0.90/1.04  --res_backward_subs                     full
% 0.90/1.04  --res_forward_subs_resolution           true
% 0.90/1.04  --res_backward_subs_resolution          true
% 0.90/1.04  --res_orphan_elimination                true
% 0.90/1.04  --res_time_limit                        2.
% 0.90/1.04  --res_out_proof                         true
% 0.90/1.04  
% 0.90/1.04  ------ Superposition Options
% 0.90/1.04  
% 0.90/1.04  --superposition_flag                    true
% 0.90/1.04  --sup_passive_queue_type                priority_queues
% 0.90/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.90/1.04  --sup_passive_queues_freq               [8;1;4]
% 0.90/1.04  --demod_completeness_check              fast
% 0.90/1.04  --demod_use_ground                      true
% 0.90/1.04  --sup_to_prop_solver                    passive
% 0.90/1.04  --sup_prop_simpl_new                    true
% 0.90/1.04  --sup_prop_simpl_given                  true
% 0.90/1.04  --sup_fun_splitting                     false
% 0.90/1.04  --sup_smt_interval                      50000
% 0.90/1.04  
% 0.90/1.04  ------ Superposition Simplification Setup
% 0.90/1.04  
% 0.90/1.04  --sup_indices_passive                   []
% 0.90/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.90/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.90/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.90/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 0.90/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.90/1.04  --sup_full_bw                           [BwDemod]
% 0.90/1.04  --sup_immed_triv                        [TrivRules]
% 0.90/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.90/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.90/1.04  --sup_immed_bw_main                     []
% 0.90/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.90/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 0.90/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.90/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.90/1.04  
% 0.90/1.04  ------ Combination Options
% 0.90/1.04  
% 0.90/1.04  --comb_res_mult                         3
% 0.90/1.04  --comb_sup_mult                         2
% 0.90/1.04  --comb_inst_mult                        10
% 0.90/1.04  
% 0.90/1.04  ------ Debug Options
% 0.90/1.04  
% 0.90/1.04  --dbg_backtrace                         false
% 0.90/1.04  --dbg_dump_prop_clauses                 false
% 0.90/1.04  --dbg_dump_prop_clauses_file            -
% 0.90/1.04  --dbg_out_stat                          false
% 0.90/1.04  
% 0.90/1.04  
% 0.90/1.04  
% 0.90/1.04  
% 0.90/1.04  ------ Proving...
% 0.90/1.04  
% 0.90/1.04  
% 0.90/1.04  % SZS status Theorem for theBenchmark.p
% 0.90/1.04  
% 0.90/1.04  % SZS output start CNFRefutation for theBenchmark.p
% 0.90/1.04  
% 0.90/1.04  fof(f6,axiom,(
% 0.90/1.04    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v4_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v4_pre_topc(X3,X2)))))))),
% 0.90/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.90/1.04  
% 0.90/1.04  fof(f13,plain,(
% 0.90/1.04    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((v4_pre_topc(X3,X2) | X1 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v4_pre_topc(X1,X0)) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.90/1.04    inference(ennf_transformation,[],[f6])).
% 0.90/1.04  
% 0.90/1.04  fof(f14,plain,(
% 0.90/1.04    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v4_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v4_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.90/1.04    inference(flattening,[],[f13])).
% 0.90/1.04  
% 0.90/1.04  fof(f49,plain,(
% 0.90/1.04    ( ! [X2,X0,X3,X1] : (v4_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~v4_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.90/1.04    inference(cnf_transformation,[],[f14])).
% 0.90/1.04  
% 0.90/1.04  fof(f59,plain,(
% 0.90/1.04    ( ! [X2,X0,X3] : (v4_pre_topc(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~v4_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.90/1.04    inference(equality_resolution,[],[f49])).
% 0.90/1.04  
% 0.90/1.04  fof(f7,conjecture,(
% 0.90/1.04    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_pre_topc(X2,X0) => (v2_tops_2(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) => (X1 = X3 => v2_tops_2(X3,X2)))))))),
% 0.90/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.90/1.04  
% 0.90/1.04  fof(f8,negated_conjecture,(
% 0.90/1.04    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_pre_topc(X2,X0) => (v2_tops_2(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) => (X1 = X3 => v2_tops_2(X3,X2)))))))),
% 0.90/1.04    inference(negated_conjecture,[],[f7])).
% 0.90/1.04  
% 0.90/1.04  fof(f15,plain,(
% 0.90/1.04    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : ((~v2_tops_2(X3,X2) & X1 = X3) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))) & v2_tops_2(X1,X0)) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.90/1.04    inference(ennf_transformation,[],[f8])).
% 0.90/1.04  
% 0.90/1.04  fof(f16,plain,(
% 0.90/1.04    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v2_tops_2(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))) & v2_tops_2(X1,X0) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.90/1.04    inference(flattening,[],[f15])).
% 0.90/1.04  
% 0.90/1.04  fof(f33,plain,(
% 0.90/1.04    ( ! [X2,X1] : (? [X3] : (~v2_tops_2(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))) => (~v2_tops_2(sK6,X2) & sK6 = X1 & m1_subset_1(sK6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))))) )),
% 0.90/1.04    introduced(choice_axiom,[])).
% 0.90/1.04  
% 0.90/1.04  fof(f32,plain,(
% 0.90/1.04    ( ! [X0,X1] : (? [X2] : (? [X3] : (~v2_tops_2(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))) & v2_tops_2(X1,X0) & m1_pre_topc(X2,X0)) => (? [X3] : (~v2_tops_2(X3,sK5) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))) & v2_tops_2(X1,X0) & m1_pre_topc(sK5,X0))) )),
% 0.90/1.04    introduced(choice_axiom,[])).
% 0.90/1.04  
% 0.90/1.04  fof(f31,plain,(
% 0.90/1.04    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~v2_tops_2(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))) & v2_tops_2(X1,X0) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (? [X2] : (? [X3] : (~v2_tops_2(X3,X2) & sK4 = X3 & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))) & v2_tops_2(sK4,X0) & m1_pre_topc(X2,X0)) & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) )),
% 0.90/1.04    introduced(choice_axiom,[])).
% 0.90/1.04  
% 0.90/1.04  fof(f30,plain,(
% 0.90/1.04    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v2_tops_2(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))) & v2_tops_2(X1,X0) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : (~v2_tops_2(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))) & v2_tops_2(X1,sK3) & m1_pre_topc(X2,sK3)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))) & l1_pre_topc(sK3))),
% 0.90/1.04    introduced(choice_axiom,[])).
% 0.90/1.04  
% 0.90/1.04  fof(f34,plain,(
% 0.90/1.04    (((~v2_tops_2(sK6,sK5) & sK4 = sK6 & m1_subset_1(sK6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))) & v2_tops_2(sK4,sK3) & m1_pre_topc(sK5,sK3)) & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))) & l1_pre_topc(sK3)),
% 0.90/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f16,f33,f32,f31,f30])).
% 0.90/1.04  
% 0.90/1.04  fof(f52,plain,(
% 0.90/1.04    m1_pre_topc(sK5,sK3)),
% 0.90/1.04    inference(cnf_transformation,[],[f34])).
% 0.90/1.04  
% 0.90/1.04  fof(f50,plain,(
% 0.90/1.04    l1_pre_topc(sK3)),
% 0.90/1.04    inference(cnf_transformation,[],[f34])).
% 0.90/1.04  
% 0.90/1.04  fof(f2,axiom,(
% 0.90/1.04    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.90/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.90/1.04  
% 0.90/1.04  fof(f21,plain,(
% 0.90/1.04    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.90/1.04    inference(nnf_transformation,[],[f2])).
% 0.90/1.04  
% 0.90/1.04  fof(f22,plain,(
% 0.90/1.04    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.90/1.04    inference(rectify,[],[f21])).
% 0.90/1.04  
% 0.90/1.04  fof(f23,plain,(
% 0.90/1.04    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK1(X0,X1),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r1_tarski(sK1(X0,X1),X0) | r2_hidden(sK1(X0,X1),X1))))),
% 0.90/1.04    introduced(choice_axiom,[])).
% 0.90/1.04  
% 0.90/1.04  fof(f24,plain,(
% 0.90/1.04    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK1(X0,X1),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r1_tarski(sK1(X0,X1),X0) | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.90/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f23])).
% 0.90/1.04  
% 0.90/1.04  fof(f38,plain,(
% 0.90/1.04    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.90/1.04    inference(cnf_transformation,[],[f24])).
% 0.90/1.04  
% 0.90/1.04  fof(f58,plain,(
% 0.90/1.04    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 0.90/1.04    inference(equality_resolution,[],[f38])).
% 0.90/1.04  
% 0.90/1.04  fof(f3,axiom,(
% 0.90/1.04    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.90/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.90/1.04  
% 0.90/1.04  fof(f25,plain,(
% 0.90/1.04    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.90/1.04    inference(nnf_transformation,[],[f3])).
% 0.90/1.04  
% 0.90/1.04  fof(f43,plain,(
% 0.90/1.04    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.90/1.04    inference(cnf_transformation,[],[f25])).
% 0.90/1.04  
% 0.90/1.04  fof(f5,axiom,(
% 0.90/1.04    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v2_tops_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,X1) => v4_pre_topc(X2,X0))))))),
% 0.90/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.90/1.04  
% 0.90/1.04  fof(f11,plain,(
% 0.90/1.04    ! [X0] : (! [X1] : ((v2_tops_2(X1,X0) <=> ! [X2] : ((v4_pre_topc(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.90/1.04    inference(ennf_transformation,[],[f5])).
% 0.90/1.04  
% 0.90/1.04  fof(f12,plain,(
% 0.90/1.04    ! [X0] : (! [X1] : ((v2_tops_2(X1,X0) <=> ! [X2] : (v4_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.90/1.04    inference(flattening,[],[f11])).
% 0.90/1.04  
% 0.90/1.04  fof(f26,plain,(
% 0.90/1.04    ! [X0] : (! [X1] : (((v2_tops_2(X1,X0) | ? [X2] : (~v4_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v4_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.90/1.04    inference(nnf_transformation,[],[f12])).
% 0.90/1.04  
% 0.90/1.04  fof(f27,plain,(
% 0.90/1.04    ! [X0] : (! [X1] : (((v2_tops_2(X1,X0) | ? [X2] : (~v4_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v4_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.90/1.04    inference(rectify,[],[f26])).
% 0.90/1.04  
% 0.90/1.04  fof(f28,plain,(
% 0.90/1.04    ! [X1,X0] : (? [X2] : (~v4_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v4_pre_topc(sK2(X0,X1),X0) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.90/1.04    introduced(choice_axiom,[])).
% 0.90/1.04  
% 0.90/1.04  fof(f29,plain,(
% 0.90/1.04    ! [X0] : (! [X1] : (((v2_tops_2(X1,X0) | (~v4_pre_topc(sK2(X0,X1),X0) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v4_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.90/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f27,f28])).
% 0.90/1.04  
% 0.90/1.04  fof(f45,plain,(
% 0.90/1.04    ( ! [X0,X3,X1] : (v4_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.90/1.04    inference(cnf_transformation,[],[f29])).
% 0.90/1.04  
% 0.90/1.04  fof(f1,axiom,(
% 0.90/1.04    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.90/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.90/1.04  
% 0.90/1.04  fof(f9,plain,(
% 0.90/1.04    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.90/1.04    inference(ennf_transformation,[],[f1])).
% 0.90/1.04  
% 0.90/1.04  fof(f17,plain,(
% 0.90/1.04    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.90/1.04    inference(nnf_transformation,[],[f9])).
% 0.90/1.04  
% 0.90/1.04  fof(f18,plain,(
% 0.90/1.04    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.90/1.04    inference(rectify,[],[f17])).
% 0.90/1.04  
% 0.90/1.04  fof(f19,plain,(
% 0.90/1.04    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 0.90/1.04    introduced(choice_axiom,[])).
% 0.90/1.04  
% 0.90/1.04  fof(f20,plain,(
% 0.90/1.04    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.90/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).
% 0.90/1.04  
% 0.90/1.04  fof(f35,plain,(
% 0.90/1.04    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.90/1.04    inference(cnf_transformation,[],[f20])).
% 0.90/1.04  
% 0.90/1.04  fof(f51,plain,(
% 0.90/1.04    m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))),
% 0.90/1.04    inference(cnf_transformation,[],[f34])).
% 0.90/1.04  
% 0.90/1.04  fof(f55,plain,(
% 0.90/1.04    sK4 = sK6),
% 0.90/1.04    inference(cnf_transformation,[],[f34])).
% 0.90/1.04  
% 0.90/1.04  fof(f42,plain,(
% 0.90/1.04    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.90/1.04    inference(cnf_transformation,[],[f25])).
% 0.90/1.04  
% 0.90/1.04  fof(f56,plain,(
% 0.90/1.04    ~v2_tops_2(sK6,sK5)),
% 0.90/1.04    inference(cnf_transformation,[],[f34])).
% 0.90/1.04  
% 0.90/1.04  fof(f48,plain,(
% 0.90/1.04    ( ! [X0,X1] : (v2_tops_2(X1,X0) | ~v4_pre_topc(sK2(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.90/1.04    inference(cnf_transformation,[],[f29])).
% 0.90/1.04  
% 0.90/1.04  fof(f4,axiom,(
% 0.90/1.04    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.90/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.90/1.04  
% 0.90/1.04  fof(f10,plain,(
% 0.90/1.04    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.90/1.04    inference(ennf_transformation,[],[f4])).
% 0.90/1.04  
% 0.90/1.04  fof(f44,plain,(
% 0.90/1.04    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.90/1.04    inference(cnf_transformation,[],[f10])).
% 0.90/1.04  
% 0.90/1.04  fof(f46,plain,(
% 0.90/1.04    ( ! [X0,X1] : (v2_tops_2(X1,X0) | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.90/1.04    inference(cnf_transformation,[],[f29])).
% 0.90/1.04  
% 0.90/1.04  fof(f47,plain,(
% 0.90/1.04    ( ! [X0,X1] : (v2_tops_2(X1,X0) | r2_hidden(sK2(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.90/1.04    inference(cnf_transformation,[],[f29])).
% 0.90/1.04  
% 0.90/1.04  fof(f54,plain,(
% 0.90/1.04    m1_subset_1(sK6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))),
% 0.90/1.04    inference(cnf_transformation,[],[f34])).
% 0.90/1.04  
% 0.90/1.04  fof(f53,plain,(
% 0.90/1.04    v2_tops_2(sK4,sK3)),
% 0.90/1.04    inference(cnf_transformation,[],[f34])).
% 0.90/1.04  
% 0.90/1.04  cnf(c_14,plain,
% 0.90/1.04      ( ~ v4_pre_topc(X0,X1)
% 0.90/1.04      | v4_pre_topc(X0,X2)
% 0.90/1.04      | ~ m1_pre_topc(X2,X1)
% 0.90/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.90/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 0.90/1.04      | ~ l1_pre_topc(X1) ),
% 0.90/1.04      inference(cnf_transformation,[],[f59]) ).
% 0.90/1.04  
% 0.90/1.04  cnf(c_19,negated_conjecture,
% 0.90/1.04      ( m1_pre_topc(sK5,sK3) ),
% 0.90/1.04      inference(cnf_transformation,[],[f52]) ).
% 0.90/1.04  
% 0.90/1.04  cnf(c_298,plain,
% 0.90/1.04      ( ~ v4_pre_topc(X0,X1)
% 0.90/1.04      | v4_pre_topc(X0,X2)
% 0.90/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.90/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 0.90/1.04      | ~ l1_pre_topc(X1)
% 0.90/1.04      | sK3 != X1
% 0.90/1.04      | sK5 != X2 ),
% 0.90/1.04      inference(resolution_lifted,[status(thm)],[c_14,c_19]) ).
% 0.90/1.04  
% 0.90/1.04  cnf(c_299,plain,
% 0.90/1.04      ( ~ v4_pre_topc(X0,sK3)
% 0.90/1.04      | v4_pre_topc(X0,sK5)
% 0.90/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 0.90/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 0.90/1.04      | ~ l1_pre_topc(sK3) ),
% 0.90/1.04      inference(unflattening,[status(thm)],[c_298]) ).
% 0.90/1.04  
% 0.90/1.04  cnf(c_21,negated_conjecture,
% 0.90/1.04      ( l1_pre_topc(sK3) ),
% 0.90/1.04      inference(cnf_transformation,[],[f50]) ).
% 0.90/1.04  
% 0.90/1.04  cnf(c_303,plain,
% 0.90/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 0.90/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 0.90/1.04      | v4_pre_topc(X0,sK5)
% 0.90/1.04      | ~ v4_pre_topc(X0,sK3) ),
% 0.90/1.04      inference(global_propositional_subsumption,
% 0.90/1.04                [status(thm)],
% 0.90/1.04                [c_299,c_21]) ).
% 0.90/1.04  
% 0.90/1.04  cnf(c_304,plain,
% 0.90/1.04      ( ~ v4_pre_topc(X0,sK3)
% 0.90/1.04      | v4_pre_topc(X0,sK5)
% 0.90/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 0.90/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) ),
% 0.90/1.04      inference(renaming,[status(thm)],[c_303]) ).
% 0.90/1.04  
% 0.90/1.04  cnf(c_2480,plain,
% 0.90/1.04      ( ~ v4_pre_topc(sK2(sK5,X0),sK3)
% 0.90/1.04      | v4_pre_topc(sK2(sK5,X0),sK5)
% 0.90/1.04      | ~ m1_subset_1(sK2(sK5,X0),k1_zfmisc_1(u1_struct_0(sK3)))
% 0.90/1.04      | ~ m1_subset_1(sK2(sK5,X0),k1_zfmisc_1(u1_struct_0(sK5))) ),
% 0.90/1.04      inference(instantiation,[status(thm)],[c_304]) ).
% 0.90/1.04  
% 0.90/1.04  cnf(c_3649,plain,
% 0.90/1.04      ( ~ v4_pre_topc(sK2(sK5,sK6),sK3)
% 0.90/1.04      | v4_pre_topc(sK2(sK5,sK6),sK5)
% 0.90/1.04      | ~ m1_subset_1(sK2(sK5,sK6),k1_zfmisc_1(u1_struct_0(sK3)))
% 0.90/1.04      | ~ m1_subset_1(sK2(sK5,sK6),k1_zfmisc_1(u1_struct_0(sK5))) ),
% 0.90/1.04      inference(instantiation,[status(thm)],[c_2480]) ).
% 0.90/1.04  
% 0.90/1.04  cnf(c_6,plain,
% 0.90/1.04      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 0.90/1.04      inference(cnf_transformation,[],[f58]) ).
% 0.90/1.04  
% 0.90/1.04  cnf(c_2219,plain,
% 0.90/1.04      ( ~ r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 0.90/1.04      | r1_tarski(X0,u1_struct_0(sK3)) ),
% 0.90/1.04      inference(instantiation,[status(thm)],[c_6]) ).
% 0.90/1.04  
% 0.90/1.04  cnf(c_3332,plain,
% 0.90/1.04      ( ~ r2_hidden(sK2(sK5,sK6),k1_zfmisc_1(u1_struct_0(sK3)))
% 0.90/1.04      | r1_tarski(sK2(sK5,sK6),u1_struct_0(sK3)) ),
% 0.90/1.04      inference(instantiation,[status(thm)],[c_2219]) ).
% 0.90/1.04  
% 0.90/1.04  cnf(c_7,plain,
% 0.90/1.04      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 0.90/1.04      inference(cnf_transformation,[],[f43]) ).
% 0.90/1.04  
% 0.90/1.04  cnf(c_1991,plain,
% 0.90/1.04      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 0.90/1.04      | ~ r1_tarski(X0,u1_struct_0(sK3)) ),
% 0.90/1.04      inference(instantiation,[status(thm)],[c_7]) ).
% 0.90/1.04  
% 0.90/1.04  cnf(c_2617,plain,
% 0.90/1.04      ( m1_subset_1(sK2(sK5,sK6),k1_zfmisc_1(u1_struct_0(sK3)))
% 0.90/1.04      | ~ r1_tarski(sK2(sK5,sK6),u1_struct_0(sK3)) ),
% 0.90/1.04      inference(instantiation,[status(thm)],[c_1991]) ).
% 0.90/1.04  
% 0.90/1.04  cnf(c_13,plain,
% 0.90/1.04      ( v4_pre_topc(X0,X1)
% 0.90/1.04      | ~ v2_tops_2(X2,X1)
% 0.90/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.90/1.04      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 0.90/1.04      | ~ r2_hidden(X0,X2)
% 0.90/1.04      | ~ l1_pre_topc(X1) ),
% 0.90/1.04      inference(cnf_transformation,[],[f45]) ).
% 0.90/1.04  
% 0.90/1.04  cnf(c_359,plain,
% 0.90/1.04      ( v4_pre_topc(X0,X1)
% 0.90/1.04      | ~ v2_tops_2(X2,X1)
% 0.90/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.90/1.04      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 0.90/1.04      | ~ r2_hidden(X0,X2)
% 0.90/1.04      | sK3 != X1 ),
% 0.90/1.04      inference(resolution_lifted,[status(thm)],[c_13,c_21]) ).
% 0.90/1.04  
% 0.90/1.04  cnf(c_360,plain,
% 0.90/1.04      ( v4_pre_topc(X0,sK3)
% 0.90/1.04      | ~ v2_tops_2(X1,sK3)
% 0.90/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 0.90/1.04      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
% 0.90/1.04      | ~ r2_hidden(X0,X1) ),
% 0.90/1.04      inference(unflattening,[status(thm)],[c_359]) ).
% 0.90/1.04  
% 0.90/1.04  cnf(c_1751,plain,
% 0.90/1.04      ( v4_pre_topc(X0,sK3)
% 0.90/1.04      | ~ v2_tops_2(sK4,sK3)
% 0.90/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 0.90/1.04      | ~ m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
% 0.90/1.04      | ~ r2_hidden(X0,sK4) ),
% 0.90/1.04      inference(instantiation,[status(thm)],[c_360]) ).
% 0.90/1.04  
% 0.90/1.04  cnf(c_2383,plain,
% 0.90/1.04      ( v4_pre_topc(sK2(sK5,sK6),sK3)
% 0.90/1.04      | ~ v2_tops_2(sK4,sK3)
% 0.90/1.04      | ~ m1_subset_1(sK2(sK5,sK6),k1_zfmisc_1(u1_struct_0(sK3)))
% 0.90/1.04      | ~ m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
% 0.90/1.04      | ~ r2_hidden(sK2(sK5,sK6),sK4) ),
% 0.90/1.04      inference(instantiation,[status(thm)],[c_1751]) ).
% 0.90/1.04  
% 0.90/1.04  cnf(c_1016,plain,( X0 = X0 ),theory(equality) ).
% 0.90/1.04  
% 0.90/1.04  cnf(c_2251,plain,
% 0.90/1.04      ( sK2(sK5,sK6) = sK2(sK5,sK6) ),
% 0.90/1.04      inference(instantiation,[status(thm)],[c_1016]) ).
% 0.90/1.04  
% 0.90/1.04  cnf(c_1019,plain,
% 0.90/1.04      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 0.90/1.04      theory(equality) ).
% 0.90/1.04  
% 0.90/1.04  cnf(c_1808,plain,
% 0.90/1.04      ( r2_hidden(X0,X1)
% 0.90/1.04      | ~ r2_hidden(sK2(sK5,sK6),sK6)
% 0.90/1.04      | X0 != sK2(sK5,sK6)
% 0.90/1.04      | X1 != sK6 ),
% 0.90/1.04      inference(instantiation,[status(thm)],[c_1019]) ).
% 0.90/1.04  
% 0.90/1.04  cnf(c_1996,plain,
% 0.90/1.04      ( r2_hidden(X0,sK4)
% 0.90/1.04      | ~ r2_hidden(sK2(sK5,sK6),sK6)
% 0.90/1.04      | X0 != sK2(sK5,sK6)
% 0.90/1.04      | sK4 != sK6 ),
% 0.90/1.04      inference(instantiation,[status(thm)],[c_1808]) ).
% 0.90/1.04  
% 0.90/1.04  cnf(c_2250,plain,
% 0.90/1.04      ( r2_hidden(sK2(sK5,sK6),sK4)
% 0.90/1.04      | ~ r2_hidden(sK2(sK5,sK6),sK6)
% 0.90/1.04      | sK2(sK5,sK6) != sK2(sK5,sK6)
% 0.90/1.04      | sK4 != sK6 ),
% 0.90/1.04      inference(instantiation,[status(thm)],[c_1996]) ).
% 0.90/1.04  
% 0.90/1.04  cnf(c_2,plain,
% 0.90/1.04      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 0.90/1.04      inference(cnf_transformation,[],[f35]) ).
% 0.90/1.04  
% 0.90/1.04  cnf(c_1807,plain,
% 0.90/1.04      ( r2_hidden(sK2(sK5,sK6),X0)
% 0.90/1.04      | ~ r2_hidden(sK2(sK5,sK6),sK6)
% 0.90/1.04      | ~ r1_tarski(sK6,X0) ),
% 0.90/1.04      inference(instantiation,[status(thm)],[c_2]) ).
% 0.90/1.04  
% 0.90/1.04  cnf(c_2036,plain,
% 0.90/1.04      ( r2_hidden(sK2(sK5,sK6),k1_zfmisc_1(u1_struct_0(sK3)))
% 0.90/1.04      | ~ r2_hidden(sK2(sK5,sK6),sK6)
% 0.90/1.04      | ~ r1_tarski(sK6,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 0.90/1.04      inference(instantiation,[status(thm)],[c_1807]) ).
% 0.90/1.04  
% 0.90/1.04  cnf(c_20,negated_conjecture,
% 0.90/1.04      ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) ),
% 0.90/1.04      inference(cnf_transformation,[],[f51]) ).
% 0.90/1.04  
% 0.90/1.04  cnf(c_1569,plain,
% 0.90/1.04      ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) = iProver_top ),
% 0.90/1.04      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 0.90/1.04  
% 0.90/1.04  cnf(c_16,negated_conjecture,
% 0.90/1.04      ( sK4 = sK6 ),
% 0.90/1.04      inference(cnf_transformation,[],[f55]) ).
% 0.90/1.04  
% 0.90/1.04  cnf(c_1589,plain,
% 0.90/1.04      ( m1_subset_1(sK6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) = iProver_top ),
% 0.90/1.04      inference(light_normalisation,[status(thm)],[c_1569,c_16]) ).
% 0.90/1.04  
% 0.90/1.04  cnf(c_8,plain,
% 0.90/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 0.90/1.04      inference(cnf_transformation,[],[f42]) ).
% 0.90/1.04  
% 0.90/1.04  cnf(c_1573,plain,
% 0.90/1.04      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 0.90/1.04      | r1_tarski(X0,X1) = iProver_top ),
% 0.90/1.04      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 0.90/1.04  
% 0.90/1.04  cnf(c_2013,plain,
% 0.90/1.04      ( r1_tarski(sK6,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 0.90/1.04      inference(superposition,[status(thm)],[c_1589,c_1573]) ).
% 0.90/1.04  
% 0.90/1.04  cnf(c_2019,plain,
% 0.90/1.04      ( r1_tarski(sK6,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 0.90/1.04      inference(predicate_to_equality_rev,[status(thm)],[c_2013]) ).
% 0.90/1.04  
% 0.90/1.04  cnf(c_15,negated_conjecture,
% 0.90/1.04      ( ~ v2_tops_2(sK6,sK5) ),
% 0.90/1.04      inference(cnf_transformation,[],[f56]) ).
% 0.90/1.04  
% 0.90/1.04  cnf(c_10,plain,
% 0.90/1.04      ( ~ v4_pre_topc(sK2(X0,X1),X0)
% 0.90/1.04      | v2_tops_2(X1,X0)
% 0.90/1.04      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 0.90/1.04      | ~ l1_pre_topc(X0) ),
% 0.90/1.04      inference(cnf_transformation,[],[f48]) ).
% 0.90/1.04  
% 0.90/1.04  cnf(c_9,plain,
% 0.90/1.04      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 0.90/1.04      inference(cnf_transformation,[],[f44]) ).
% 0.90/1.04  
% 0.90/1.04  cnf(c_287,plain,
% 0.90/1.04      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | sK3 != X0 | sK5 != X1 ),
% 0.90/1.04      inference(resolution_lifted,[status(thm)],[c_9,c_19]) ).
% 0.90/1.04  
% 0.90/1.04  cnf(c_288,plain,
% 0.90/1.04      ( ~ l1_pre_topc(sK3) | l1_pre_topc(sK5) ),
% 0.90/1.04      inference(unflattening,[status(thm)],[c_287]) ).
% 0.90/1.04  
% 0.90/1.04  cnf(c_290,plain,
% 0.90/1.04      ( l1_pre_topc(sK5) ),
% 0.90/1.04      inference(global_propositional_subsumption,
% 0.90/1.04                [status(thm)],
% 0.90/1.04                [c_288,c_21]) ).
% 0.90/1.04  
% 0.90/1.04  cnf(c_344,plain,
% 0.90/1.04      ( ~ v4_pre_topc(sK2(X0,X1),X0)
% 0.90/1.04      | v2_tops_2(X1,X0)
% 0.90/1.04      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 0.90/1.04      | sK5 != X0 ),
% 0.90/1.04      inference(resolution_lifted,[status(thm)],[c_10,c_290]) ).
% 0.90/1.04  
% 0.90/1.04  cnf(c_345,plain,
% 0.90/1.04      ( ~ v4_pre_topc(sK2(sK5,X0),sK5)
% 0.90/1.04      | v2_tops_2(X0,sK5)
% 0.90/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) ),
% 0.90/1.04      inference(unflattening,[status(thm)],[c_344]) ).
% 0.90/1.04  
% 0.90/1.04  cnf(c_806,plain,
% 0.90/1.04      ( ~ v4_pre_topc(sK2(sK5,X0),sK5)
% 0.90/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
% 0.90/1.04      | sK5 != sK5
% 0.90/1.04      | sK6 != X0 ),
% 0.90/1.04      inference(resolution_lifted,[status(thm)],[c_15,c_345]) ).
% 0.90/1.04  
% 0.90/1.04  cnf(c_807,plain,
% 0.90/1.04      ( ~ v4_pre_topc(sK2(sK5,sK6),sK5)
% 0.90/1.04      | ~ m1_subset_1(sK6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) ),
% 0.90/1.04      inference(unflattening,[status(thm)],[c_806]) ).
% 0.90/1.04  
% 0.90/1.04  cnf(c_12,plain,
% 0.90/1.04      ( v2_tops_2(X0,X1)
% 0.90/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 0.90/1.04      | m1_subset_1(sK2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 0.90/1.04      | ~ l1_pre_topc(X1) ),
% 0.90/1.04      inference(cnf_transformation,[],[f46]) ).
% 0.90/1.04  
% 0.90/1.04  cnf(c_431,plain,
% 0.90/1.04      ( v2_tops_2(X0,X1)
% 0.90/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 0.90/1.04      | m1_subset_1(sK2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 0.90/1.04      | sK5 != X1 ),
% 0.90/1.04      inference(resolution_lifted,[status(thm)],[c_12,c_290]) ).
% 0.90/1.04  
% 0.90/1.04  cnf(c_432,plain,
% 0.90/1.04      ( v2_tops_2(X0,sK5)
% 0.90/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
% 0.90/1.04      | m1_subset_1(sK2(sK5,X0),k1_zfmisc_1(u1_struct_0(sK5))) ),
% 0.90/1.04      inference(unflattening,[status(thm)],[c_431]) ).
% 0.90/1.04  
% 0.90/1.04  cnf(c_795,plain,
% 0.90/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
% 0.90/1.04      | m1_subset_1(sK2(sK5,X0),k1_zfmisc_1(u1_struct_0(sK5)))
% 0.90/1.04      | sK5 != sK5
% 0.90/1.04      | sK6 != X0 ),
% 0.90/1.04      inference(resolution_lifted,[status(thm)],[c_15,c_432]) ).
% 0.90/1.04  
% 0.90/1.04  cnf(c_796,plain,
% 0.90/1.04      ( m1_subset_1(sK2(sK5,sK6),k1_zfmisc_1(u1_struct_0(sK5)))
% 0.90/1.04      | ~ m1_subset_1(sK6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) ),
% 0.90/1.04      inference(unflattening,[status(thm)],[c_795]) ).
% 0.90/1.04  
% 0.90/1.04  cnf(c_11,plain,
% 0.90/1.04      ( v2_tops_2(X0,X1)
% 0.90/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 0.90/1.04      | r2_hidden(sK2(X1,X0),X0)
% 0.90/1.04      | ~ l1_pre_topc(X1) ),
% 0.90/1.04      inference(cnf_transformation,[],[f47]) ).
% 0.90/1.04  
% 0.90/1.04  cnf(c_446,plain,
% 0.90/1.04      ( v2_tops_2(X0,X1)
% 0.90/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 0.90/1.04      | r2_hidden(sK2(X1,X0),X0)
% 0.90/1.04      | sK5 != X1 ),
% 0.90/1.04      inference(resolution_lifted,[status(thm)],[c_11,c_290]) ).
% 0.90/1.04  
% 0.90/1.04  cnf(c_447,plain,
% 0.90/1.04      ( v2_tops_2(X0,sK5)
% 0.90/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
% 0.90/1.04      | r2_hidden(sK2(sK5,X0),X0) ),
% 0.90/1.04      inference(unflattening,[status(thm)],[c_446]) ).
% 0.90/1.04  
% 0.90/1.04  cnf(c_784,plain,
% 0.90/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
% 0.90/1.04      | r2_hidden(sK2(sK5,X0),X0)
% 0.90/1.04      | sK5 != sK5
% 0.90/1.04      | sK6 != X0 ),
% 0.90/1.04      inference(resolution_lifted,[status(thm)],[c_15,c_447]) ).
% 0.90/1.04  
% 0.90/1.04  cnf(c_785,plain,
% 0.90/1.04      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
% 0.90/1.04      | r2_hidden(sK2(sK5,sK6),sK6) ),
% 0.90/1.04      inference(unflattening,[status(thm)],[c_784]) ).
% 0.90/1.04  
% 0.90/1.04  cnf(c_17,negated_conjecture,
% 0.90/1.04      ( m1_subset_1(sK6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) ),
% 0.90/1.04      inference(cnf_transformation,[],[f54]) ).
% 0.90/1.04  
% 0.90/1.04  cnf(c_18,negated_conjecture,
% 0.90/1.04      ( v2_tops_2(sK4,sK3) ),
% 0.90/1.04      inference(cnf_transformation,[],[f53]) ).
% 0.90/1.04  
% 0.90/1.04  cnf(contradiction,plain,
% 0.90/1.04      ( $false ),
% 0.90/1.04      inference(minisat,
% 0.90/1.04                [status(thm)],
% 0.90/1.04                [c_3649,c_3332,c_2617,c_2383,c_2251,c_2250,c_2036,c_2019,
% 0.90/1.04                 c_807,c_796,c_785,c_16,c_17,c_18,c_20]) ).
% 0.90/1.04  
% 0.90/1.04  
% 0.90/1.04  % SZS output end CNFRefutation for theBenchmark.p
% 0.90/1.04  
% 0.90/1.04  ------                               Statistics
% 0.90/1.04  
% 0.90/1.04  ------ General
% 0.90/1.04  
% 0.90/1.04  abstr_ref_over_cycles:                  0
% 0.90/1.04  abstr_ref_under_cycles:                 0
% 0.90/1.04  gc_basic_clause_elim:                   0
% 0.90/1.04  forced_gc_time:                         0
% 0.90/1.04  parsing_time:                           0.019
% 0.90/1.04  unif_index_cands_time:                  0.
% 0.90/1.04  unif_index_add_time:                    0.
% 0.90/1.04  orderings_time:                         0.
% 0.90/1.04  out_proof_time:                         0.008
% 0.90/1.04  total_time:                             0.132
% 0.90/1.04  num_of_symbols:                         47
% 0.90/1.04  num_of_terms:                           2456
% 0.90/1.04  
% 0.90/1.04  ------ Preprocessing
% 0.90/1.04  
% 0.90/1.04  num_of_splits:                          0
% 0.90/1.04  num_of_split_atoms:                     0
% 0.90/1.04  num_of_reused_defs:                     0
% 0.90/1.04  num_eq_ax_congr_red:                    14
% 0.90/1.04  num_of_sem_filtered_clauses:            1
% 0.90/1.04  num_of_subtypes:                        0
% 0.90/1.04  monotx_restored_types:                  0
% 0.90/1.04  sat_num_of_epr_types:                   0
% 0.90/1.04  sat_num_of_non_cyclic_types:            0
% 0.90/1.04  sat_guarded_non_collapsed_types:        0
% 0.90/1.04  num_pure_diseq_elim:                    0
% 0.90/1.04  simp_replaced_by:                       0
% 0.90/1.04  res_preprocessed:                       89
% 0.90/1.04  prep_upred:                             0
% 0.90/1.04  prep_unflattend:                        54
% 0.90/1.04  smt_new_axioms:                         0
% 0.90/1.04  pred_elim_cands:                        7
% 0.90/1.04  pred_elim:                              2
% 0.90/1.04  pred_elim_cl:                           -1
% 0.90/1.04  pred_elim_cycles:                       4
% 0.90/1.04  merged_defs:                            12
% 0.90/1.04  merged_defs_ncl:                        0
% 0.90/1.04  bin_hyper_res:                          12
% 0.90/1.04  prep_cycles:                            3
% 0.90/1.04  pred_elim_time:                         0.016
% 0.90/1.04  splitting_time:                         0.
% 0.90/1.04  sem_filter_time:                        0.
% 0.90/1.04  monotx_time:                            0.
% 0.90/1.04  subtype_inf_time:                       0.
% 0.90/1.04  
% 0.90/1.04  ------ Problem properties
% 0.90/1.04  
% 0.90/1.04  clauses:                                23
% 0.90/1.04  conjectures:                            5
% 0.90/1.04  epr:                                    4
% 0.90/1.04  horn:                                   17
% 0.90/1.04  ground:                                 5
% 0.90/1.04  unary:                                  5
% 0.90/1.04  binary:                                 6
% 0.90/1.04  lits:                                   58
% 0.90/1.04  lits_eq:                                3
% 0.90/1.04  fd_pure:                                0
% 0.90/1.04  fd_pseudo:                              0
% 0.90/1.04  fd_cond:                                0
% 0.90/1.04  fd_pseudo_cond:                         2
% 0.90/1.04  ac_symbols:                             0
% 0.90/1.04  
% 0.90/1.04  ------ Propositional Solver
% 0.90/1.04  
% 0.90/1.04  prop_solver_calls:                      24
% 0.90/1.04  prop_fast_solver_calls:                 696
% 0.90/1.04  smt_solver_calls:                       0
% 0.90/1.04  smt_fast_solver_calls:                  0
% 0.90/1.04  prop_num_of_clauses:                    1147
% 0.90/1.04  prop_preprocess_simplified:             4129
% 0.90/1.04  prop_fo_subsumed:                       10
% 0.90/1.04  prop_solver_time:                       0.
% 0.90/1.04  smt_solver_time:                        0.
% 0.90/1.04  smt_fast_solver_time:                   0.
% 0.90/1.04  prop_fast_solver_time:                  0.
% 0.90/1.04  prop_unsat_core_time:                   0.
% 0.90/1.04  
% 0.90/1.04  ------ QBF
% 0.90/1.04  
% 0.90/1.04  qbf_q_res:                              0
% 0.90/1.04  qbf_num_tautologies:                    0
% 0.90/1.04  qbf_prep_cycles:                        0
% 0.90/1.04  
% 0.90/1.04  ------ BMC1
% 0.90/1.04  
% 0.90/1.04  bmc1_current_bound:                     -1
% 0.90/1.04  bmc1_last_solved_bound:                 -1
% 0.90/1.04  bmc1_unsat_core_size:                   -1
% 0.90/1.04  bmc1_unsat_core_parents_size:           -1
% 0.90/1.04  bmc1_merge_next_fun:                    0
% 0.90/1.04  bmc1_unsat_core_clauses_time:           0.
% 0.90/1.04  
% 0.90/1.04  ------ Instantiation
% 0.90/1.04  
% 0.90/1.04  inst_num_of_clauses:                    288
% 0.90/1.04  inst_num_in_passive:                    133
% 0.90/1.04  inst_num_in_active:                     154
% 0.90/1.04  inst_num_in_unprocessed:                0
% 0.90/1.04  inst_num_of_loops:                      196
% 0.90/1.04  inst_num_of_learning_restarts:          0
% 0.90/1.04  inst_num_moves_active_passive:          38
% 0.90/1.04  inst_lit_activity:                      0
% 0.90/1.04  inst_lit_activity_moves:                0
% 0.90/1.04  inst_num_tautologies:                   0
% 0.90/1.04  inst_num_prop_implied:                  0
% 0.90/1.04  inst_num_existing_simplified:           0
% 0.90/1.04  inst_num_eq_res_simplified:             0
% 0.90/1.04  inst_num_child_elim:                    0
% 0.90/1.04  inst_num_of_dismatching_blockings:      58
% 0.90/1.04  inst_num_of_non_proper_insts:           212
% 0.90/1.04  inst_num_of_duplicates:                 0
% 0.90/1.04  inst_inst_num_from_inst_to_res:         0
% 0.90/1.04  inst_dismatching_checking_time:         0.
% 0.90/1.04  
% 0.90/1.04  ------ Resolution
% 0.90/1.04  
% 0.90/1.04  res_num_of_clauses:                     0
% 0.90/1.04  res_num_in_passive:                     0
% 0.90/1.04  res_num_in_active:                      0
% 0.90/1.04  res_num_of_loops:                       92
% 0.90/1.04  res_forward_subset_subsumed:            23
% 0.90/1.04  res_backward_subset_subsumed:           0
% 0.90/1.04  res_forward_subsumed:                   0
% 0.90/1.04  res_backward_subsumed:                  0
% 0.90/1.04  res_forward_subsumption_resolution:     0
% 0.90/1.04  res_backward_subsumption_resolution:    0
% 0.90/1.04  res_clause_to_clause_subsumption:       137
% 0.90/1.04  res_orphan_elimination:                 0
% 0.90/1.04  res_tautology_del:                      37
% 0.90/1.04  res_num_eq_res_simplified:              0
% 0.90/1.04  res_num_sel_changes:                    0
% 0.90/1.04  res_moves_from_active_to_pass:          0
% 0.90/1.04  
% 0.90/1.04  ------ Superposition
% 0.90/1.04  
% 0.90/1.04  sup_time_total:                         0.
% 0.90/1.04  sup_time_generating:                    0.
% 0.90/1.04  sup_time_sim_full:                      0.
% 0.90/1.04  sup_time_sim_immed:                     0.
% 0.90/1.04  
% 0.90/1.04  sup_num_of_clauses:                     64
% 0.90/1.04  sup_num_in_active:                      38
% 0.90/1.04  sup_num_in_passive:                     26
% 0.90/1.04  sup_num_of_loops:                       38
% 0.90/1.04  sup_fw_superposition:                   27
% 0.90/1.04  sup_bw_superposition:                   22
% 0.90/1.04  sup_immediate_simplified:               5
% 0.90/1.04  sup_given_eliminated:                   0
% 0.90/1.04  comparisons_done:                       0
% 0.90/1.04  comparisons_avoided:                    0
% 0.90/1.04  
% 0.90/1.04  ------ Simplifications
% 0.90/1.04  
% 0.90/1.04  
% 0.90/1.04  sim_fw_subset_subsumed:                 4
% 0.90/1.04  sim_bw_subset_subsumed:                 0
% 0.90/1.04  sim_fw_subsumed:                        1
% 0.90/1.04  sim_bw_subsumed:                        0
% 0.90/1.04  sim_fw_subsumption_res:                 0
% 0.90/1.04  sim_bw_subsumption_res:                 0
% 0.90/1.04  sim_tautology_del:                      3
% 0.90/1.04  sim_eq_tautology_del:                   0
% 0.90/1.04  sim_eq_res_simp:                        0
% 0.90/1.04  sim_fw_demodulated:                     0
% 0.90/1.04  sim_bw_demodulated:                     0
% 0.90/1.04  sim_light_normalised:                   2
% 0.90/1.04  sim_joinable_taut:                      0
% 0.90/1.04  sim_joinable_simp:                      0
% 0.90/1.04  sim_ac_normalised:                      0
% 0.90/1.04  sim_smt_subsumption:                    0
% 0.90/1.04  
%------------------------------------------------------------------------------
