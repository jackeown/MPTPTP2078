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
% DateTime   : Thu Dec  3 12:15:52 EST 2020

% Result     : Theorem 3.23s
% Output     : CNFRefutation 3.23s
% Verified   : 
% Statistics : Number of formulae       :  191 (20010 expanded)
%              Number of clauses        :  133 (5407 expanded)
%              Number of leaves         :   13 (6614 expanded)
%              Depth                    :   37
%              Number of atoms          :  698 (177375 expanded)
%              Number of equality atoms :  239 (8852 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( v5_tops_1(X2,X0)
                     => ( v4_tops_1(X2,X0)
                        & v4_pre_topc(X2,X0) ) )
                    & ( ( v4_tops_1(X3,X1)
                        & v4_pre_topc(X3,X1) )
                     => v5_tops_1(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( ( v5_tops_1(X2,X0)
                       => ( v4_tops_1(X2,X0)
                          & v4_pre_topc(X2,X0) ) )
                      & ( ( v4_tops_1(X3,X1)
                          & v4_pre_topc(X3,X1) )
                       => v5_tops_1(X3,X1) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ v4_tops_1(X2,X0)
                        | ~ v4_pre_topc(X2,X0) )
                      & v5_tops_1(X2,X0) )
                    | ( ~ v5_tops_1(X3,X1)
                      & v4_tops_1(X3,X1)
                      & v4_pre_topc(X3,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ v4_tops_1(X2,X0)
                        | ~ v4_pre_topc(X2,X0) )
                      & v5_tops_1(X2,X0) )
                    | ( ~ v5_tops_1(X3,X1)
                      & v4_tops_1(X3,X1)
                      & v4_pre_topc(X3,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ( ( ~ v4_tops_1(X2,X0)
                | ~ v4_pre_topc(X2,X0) )
              & v5_tops_1(X2,X0) )
            | ( ~ v5_tops_1(X3,X1)
              & v4_tops_1(X3,X1)
              & v4_pre_topc(X3,X1) ) )
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ( ( ( ~ v4_tops_1(X2,X0)
              | ~ v4_pre_topc(X2,X0) )
            & v5_tops_1(X2,X0) )
          | ( ~ v5_tops_1(sK3,X1)
            & v4_tops_1(sK3,X1)
            & v4_pre_topc(sK3,X1) ) )
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ( ( ( ~ v4_tops_1(X2,X0)
                    | ~ v4_pre_topc(X2,X0) )
                  & v5_tops_1(X2,X0) )
                | ( ~ v5_tops_1(X3,X1)
                  & v4_tops_1(X3,X1)
                  & v4_pre_topc(X3,X1) ) )
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X3] :
            ( ( ( ( ~ v4_tops_1(sK2,X0)
                  | ~ v4_pre_topc(sK2,X0) )
                & v5_tops_1(sK2,X0) )
              | ( ~ v5_tops_1(X3,X1)
                & v4_tops_1(X3,X1)
                & v4_pre_topc(X3,X1) ) )
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ v4_tops_1(X2,X0)
                        | ~ v4_pre_topc(X2,X0) )
                      & v5_tops_1(X2,X0) )
                    | ( ~ v5_tops_1(X3,X1)
                      & v4_tops_1(X3,X1)
                      & v4_pre_topc(X3,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ( ( ( ~ v4_tops_1(X2,X0)
                      | ~ v4_pre_topc(X2,X0) )
                    & v5_tops_1(X2,X0) )
                  | ( ~ v5_tops_1(X3,sK1)
                    & v4_tops_1(X3,sK1)
                    & v4_pre_topc(X3,sK1) ) )
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ( ( ~ v4_tops_1(X2,X0)
                          | ~ v4_pre_topc(X2,X0) )
                        & v5_tops_1(X2,X0) )
                      | ( ~ v5_tops_1(X3,X1)
                        & v4_tops_1(X3,X1)
                        & v4_pre_topc(X3,X1) ) )
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ v4_tops_1(X2,sK0)
                        | ~ v4_pre_topc(X2,sK0) )
                      & v5_tops_1(X2,sK0) )
                    | ( ~ v5_tops_1(X3,X1)
                      & v4_tops_1(X3,X1)
                      & v4_pre_topc(X3,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ( ( ( ~ v4_tops_1(sK2,sK0)
          | ~ v4_pre_topc(sK2,sK0) )
        & v5_tops_1(sK2,sK0) )
      | ( ~ v5_tops_1(sK3,sK1)
        & v4_tops_1(sK3,sK1)
        & v4_pre_topc(sK3,sK1) ) )
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f32,f31,f30,f29])).

fof(f54,plain,
    ( v5_tops_1(sK2,sK0)
    | v4_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f51,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f33])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_tops_1(X1,X0)
              | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1 )
            & ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
              | ~ v5_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
      | ~ v5_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f49,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f53,plain,
    ( v5_tops_1(sK2,sK0)
    | v4_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f52,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f33])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f50,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f6,axiom,(
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
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f56,plain,
    ( ~ v4_tops_1(sK2,sK0)
    | ~ v4_pre_topc(sK2,sK0)
    | v4_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f48,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f24])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f60,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f34])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_tops_1(X1,X0)
          <=> ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_tops_1(X1,X0)
          <=> ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_tops_1(X1,X0)
              | ~ r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              | ~ r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
            & ( ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
                & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
              | ~ v4_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_tops_1(X1,X0)
              | ~ r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              | ~ r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
            & ( ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
                & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
              | ~ v4_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)
      | ~ v4_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X2,X1)
                  & v4_pre_topc(X1,X0) )
               => r1_tarski(k2_pre_topc(X0,X2),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X2),X1)
              | ~ r1_tarski(X2,X1)
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X2),X1)
              | ~ r1_tarski(X2,X1)
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_pre_topc(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
      | ~ v4_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f36,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f55,plain,
    ( v5_tops_1(sK2,sK0)
    | ~ v5_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v5_tops_1(X1,X0)
      | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v4_tops_1(X1,X0)
      | ~ r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
      | ~ r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f57,plain,
    ( ~ v4_tops_1(sK2,sK0)
    | ~ v4_pre_topc(sK2,sK0)
    | v4_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f58,plain,
    ( ~ v4_tops_1(sK2,sK0)
    | ~ v4_pre_topc(sK2,sK0)
    | ~ v5_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_18,negated_conjecture,
    ( v5_tops_1(sK2,sK0)
    | v4_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1207,plain,
    ( v5_tops_1(sK2,sK0) = iProver_top
    | v4_tops_1(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1204,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_10,plain,
    ( ~ v5_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k1_tops_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_23,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_481,plain,
    ( ~ v5_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,k1_tops_1(X1,X0)) = X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_23])).

cnf(c_482,plain,
    ( ~ v5_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k1_tops_1(sK0,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_481])).

cnf(c_1190,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,X0)) = X0
    | v5_tops_1(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_482])).

cnf(c_2291,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = sK2
    | v5_tops_1(sK2,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1204,c_1190])).

cnf(c_2339,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = sK2
    | v4_tops_1(sK3,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1207,c_2291])).

cnf(c_19,negated_conjecture,
    ( v5_tops_1(sK2,sK0)
    | v4_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1206,plain,
    ( v5_tops_1(sK2,sK0) = iProver_top
    | v4_pre_topc(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2340,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = sK2
    | v4_pre_topc(sK3,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1206,c_2291])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1205,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_5,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_22,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_421,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,X0) = X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_22])).

cnf(c_422,plain,
    ( ~ v4_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_421])).

cnf(c_1194,plain,
    ( k2_pre_topc(sK1,X0) = X0
    | v4_pre_topc(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_422])).

cnf(c_2154,plain,
    ( k2_pre_topc(sK1,sK3) = sK3
    | v4_pre_topc(sK3,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1205,c_1194])).

cnf(c_2637,plain,
    ( k2_pre_topc(sK1,sK3) = sK3
    | k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_2340,c_2154])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_469,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_23])).

cnf(c_470,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_469])).

cnf(c_1191,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_470])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_574,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_23])).

cnf(c_575,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,k2_pre_topc(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_574])).

cnf(c_1184,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_575])).

cnf(c_1880,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),k2_pre_topc(sK0,k1_tops_1(sK0,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1191,c_1184])).

cnf(c_3342,plain,
    ( k2_pre_topc(sK1,sK3) = sK3
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK2),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2637,c_1880])).

cnf(c_28,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_16,negated_conjecture,
    ( ~ v4_tops_1(sK2,sK0)
    | v4_pre_topc(sK3,sK1)
    | ~ v4_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_33,plain,
    ( v4_tops_1(sK2,sK0) != iProver_top
    | v4_pre_topc(sK3,sK1) = iProver_top
    | v4_pre_topc(sK2,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_24,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_282,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_24])).

cnf(c_283,plain,
    ( v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_282])).

cnf(c_287,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(X0,sK0)
    | k2_pre_topc(sK0,X0) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_283,c_23])).

cnf(c_288,plain,
    ( v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X0) != X0 ),
    inference(renaming,[status(thm)],[c_287])).

cnf(c_1462,plain,
    ( v4_pre_topc(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,sK2) != sK2 ),
    inference(instantiation,[status(thm)],[c_288])).

cnf(c_1463,plain,
    ( k2_pre_topc(sK0,sK2) != sK2
    | v4_pre_topc(sK2,sK0) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1462])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_3128,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_3131,plain,
    ( r1_tarski(sK2,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3128])).

cnf(c_12,plain,
    ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_264,plain,
    ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_24])).

cnf(c_265,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_264])).

cnf(c_269,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(k2_pre_topc(sK0,X0),sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_265,c_23])).

cnf(c_270,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(renaming,[status(thm)],[c_269])).

cnf(c_1203,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,X0),sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_270])).

cnf(c_1879,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,k1_tops_1(sK0,X0)),sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1191,c_1203])).

cnf(c_3282,plain,
    ( k2_pre_topc(sK1,sK3) = sK3
    | v4_pre_topc(sK2,sK0) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2637,c_1879])).

cnf(c_5006,plain,
    ( v4_pre_topc(sK2,sK0) = iProver_top
    | k2_pre_topc(sK1,sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3282,c_28])).

cnf(c_5007,plain,
    ( k2_pre_topc(sK1,sK3) = sK3
    | v4_pre_topc(sK2,sK0) = iProver_top ),
    inference(renaming,[status(thm)],[c_5006])).

cnf(c_559,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,X0) = X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_23])).

cnf(c_560,plain,
    ( ~ v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_559])).

cnf(c_1185,plain,
    ( k2_pre_topc(sK0,X0) = X0
    | v4_pre_topc(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_560])).

cnf(c_1990,plain,
    ( k2_pre_topc(sK0,sK2) = sK2
    | v4_pre_topc(sK2,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1204,c_1185])).

cnf(c_5012,plain,
    ( k2_pre_topc(sK1,sK3) = sK3
    | k2_pre_topc(sK0,sK2) = sK2 ),
    inference(superposition,[status(thm)],[c_5007,c_1990])).

cnf(c_8,plain,
    ( ~ v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_373,plain,
    ( ~ v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_22])).

cnf(c_374,plain,
    ( ~ v4_tops_1(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,X0)),X0) ),
    inference(unflattening,[status(thm)],[c_373])).

cnf(c_1197,plain,
    ( v4_tops_1(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,X0)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_374])).

cnf(c_5096,plain,
    ( k2_pre_topc(sK0,sK2) = sK2
    | v4_tops_1(sK3,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(k1_tops_1(sK1,sK3),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_5012,c_1197])).

cnf(c_29,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_5387,plain,
    ( v4_tops_1(sK3,sK1) != iProver_top
    | k2_pre_topc(sK0,sK2) = sK2
    | r1_tarski(k1_tops_1(sK1,sK3),sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5096,c_29])).

cnf(c_5388,plain,
    ( k2_pre_topc(sK0,sK2) = sK2
    | v4_tops_1(sK3,sK1) != iProver_top
    | r1_tarski(k1_tops_1(sK1,sK3),sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_5387])).

cnf(c_331,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_22])).

cnf(c_332,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k1_tops_1(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_331])).

cnf(c_1200,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k1_tops_1(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_332])).

cnf(c_13,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | r1_tarski(k2_pre_topc(X1,X2),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_310,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | r1_tarski(k2_pre_topc(X1,X2),X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_22])).

cnf(c_311,plain,
    ( ~ v4_pre_topc(X0,sK1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X1,X0)
    | r1_tarski(k2_pre_topc(sK1,X1),X0) ),
    inference(unflattening,[status(thm)],[c_310])).

cnf(c_1201,plain,
    ( v4_pre_topc(X0,sK1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(k2_pre_topc(sK1,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_311])).

cnf(c_3004,plain,
    ( v4_pre_topc(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(k1_tops_1(sK1,X1),X0) != iProver_top
    | r1_tarski(k2_pre_topc(sK1,k1_tops_1(sK1,X1)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1200,c_1201])).

cnf(c_7,plain,
    ( ~ v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_388,plain,
    ( ~ v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_22])).

cnf(c_389,plain,
    ( ~ v4_tops_1(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(X0,k2_pre_topc(sK1,k1_tops_1(sK1,X0))) ),
    inference(unflattening,[status(thm)],[c_388])).

cnf(c_1196,plain,
    ( v4_tops_1(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK1,k1_tops_1(sK1,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_389])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1213,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2756,plain,
    ( k2_pre_topc(sK1,k1_tops_1(sK1,X0)) = X0
    | v4_tops_1(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(k2_pre_topc(sK1,k1_tops_1(sK1,X0)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1196,c_1213])).

cnf(c_4096,plain,
    ( k2_pre_topc(sK1,k1_tops_1(sK1,X0)) = X0
    | v4_tops_1(X0,sK1) != iProver_top
    | v4_pre_topc(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(k1_tops_1(sK1,X0),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3004,c_2756])).

cnf(c_4359,plain,
    ( k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) = sK3
    | v4_tops_1(sK3,sK1) != iProver_top
    | v4_pre_topc(sK3,sK1) != iProver_top
    | r1_tarski(k1_tops_1(sK1,sK3),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1205,c_4096])).

cnf(c_5395,plain,
    ( k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) = sK3
    | k2_pre_topc(sK0,sK2) = sK2
    | v4_tops_1(sK3,sK1) != iProver_top
    | v4_pre_topc(sK3,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5388,c_4359])).

cnf(c_5419,plain,
    ( k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) = sK3
    | k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = sK2
    | k2_pre_topc(sK0,sK2) = sK2
    | v4_pre_topc(sK3,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2339,c_5395])).

cnf(c_17,negated_conjecture,
    ( ~ v5_tops_1(sK3,sK1)
    | v5_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_32,plain,
    ( v5_tops_1(sK3,sK1) != iProver_top
    | v5_tops_1(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_9,plain,
    ( v5_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k1_tops_1(X1,X0)) != X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_358,plain,
    ( v5_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,k1_tops_1(X1,X0)) != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_22])).

cnf(c_359,plain,
    ( v5_tops_1(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,k1_tops_1(sK1,X0)) != X0 ),
    inference(unflattening,[status(thm)],[c_358])).

cnf(c_1465,plain,
    ( v5_tops_1(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) != sK3 ),
    inference(instantiation,[status(thm)],[c_359])).

cnf(c_1466,plain,
    ( k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) != sK3
    | v5_tops_1(sK3,sK1) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1465])).

cnf(c_5518,plain,
    ( k2_pre_topc(sK0,sK2) = sK2
    | k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5419,c_29,c_32,c_1466,c_2291,c_2339,c_2340,c_4359,c_5096])).

cnf(c_5519,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = sK2
    | k2_pre_topc(sK0,sK2) = sK2 ),
    inference(renaming,[status(thm)],[c_5518])).

cnf(c_496,plain,
    ( v5_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,k1_tops_1(X1,X0)) != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_23])).

cnf(c_497,plain,
    ( v5_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k1_tops_1(sK0,X0)) != X0 ),
    inference(unflattening,[status(thm)],[c_496])).

cnf(c_1189,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,X0)) != X0
    | v5_tops_1(X0,sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_497])).

cnf(c_5536,plain,
    ( k2_pre_topc(sK0,sK2) = sK2
    | v5_tops_1(sK2,sK0) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5519,c_1189])).

cnf(c_2002,plain,
    ( ~ v4_pre_topc(sK2,sK0)
    | k2_pre_topc(sK0,sK2) = sK2 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1990])).

cnf(c_5533,plain,
    ( k2_pre_topc(sK0,sK2) = sK2
    | v4_pre_topc(sK2,sK0) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5519,c_1879])).

cnf(c_5653,plain,
    ( v4_pre_topc(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,sK2) = sK2 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5533])).

cnf(c_5656,plain,
    ( k2_pre_topc(sK0,sK2) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5536,c_21,c_2002,c_5653])).

cnf(c_6,plain,
    ( v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
    | ~ r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_541,plain,
    ( v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
    | ~ r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_23])).

cnf(c_542,plain,
    ( v4_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,X0)))
    | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X0) ),
    inference(unflattening,[status(thm)],[c_541])).

cnf(c_1186,plain,
    ( v4_tops_1(X0,sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,X0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_542])).

cnf(c_5678,plain,
    ( v4_tops_1(sK2,sK0) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK2),sK2) != iProver_top
    | r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5656,c_1186])).

cnf(c_6042,plain,
    ( v4_tops_1(sK2,sK0) = iProver_top
    | r1_tarski(k1_tops_1(sK0,sK2),sK2) != iProver_top
    | r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5678,c_28])).

cnf(c_6051,plain,
    ( k2_pre_topc(sK1,sK3) = sK3
    | v4_tops_1(sK2,sK0) = iProver_top
    | r1_tarski(k1_tops_1(sK0,sK2),sK2) != iProver_top
    | r1_tarski(sK2,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2637,c_6042])).

cnf(c_6065,plain,
    ( k2_pre_topc(sK1,sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3342,c_21,c_28,c_33,c_1463,c_2002,c_2154,c_3131,c_5653,c_6051])).

cnf(c_6099,plain,
    ( v4_tops_1(sK3,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(k1_tops_1(sK1,sK3),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_6065,c_1197])).

cnf(c_6187,plain,
    ( v4_tops_1(sK3,sK1) != iProver_top
    | r1_tarski(k1_tops_1(sK1,sK3),sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6099,c_29])).

cnf(c_6194,plain,
    ( k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) = sK3
    | v4_tops_1(sK3,sK1) != iProver_top
    | v4_pre_topc(sK3,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_6187,c_4359])).

cnf(c_6279,plain,
    ( k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) = sK3
    | k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = sK2
    | v4_pre_topc(sK3,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2339,c_6194])).

cnf(c_6346,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6279,c_29,c_32,c_1466,c_2291,c_2339,c_2340,c_4359,c_6099])).

cnf(c_6361,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK2),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_6346,c_1880])).

cnf(c_6349,plain,
    ( v4_tops_1(sK2,sK0) = iProver_top
    | r1_tarski(k1_tops_1(sK0,sK2),sK2) != iProver_top
    | r1_tarski(sK2,sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6346,c_6042])).

cnf(c_511,plain,
    ( ~ v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_23])).

cnf(c_512,plain,
    ( ~ v4_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X0) ),
    inference(unflattening,[status(thm)],[c_511])).

cnf(c_1188,plain,
    ( v4_tops_1(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_512])).

cnf(c_5676,plain,
    ( v4_tops_1(sK2,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK2),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_5656,c_1188])).

cnf(c_5830,plain,
    ( v4_tops_1(sK2,sK0) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK2),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5676,c_28])).

cnf(c_5836,plain,
    ( k1_tops_1(sK0,sK2) = sK2
    | v4_tops_1(sK2,sK0) != iProver_top
    | r1_tarski(sK2,k1_tops_1(sK0,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5830,c_1213])).

cnf(c_15,negated_conjecture,
    ( v4_tops_1(sK3,sK1)
    | ~ v4_tops_1(sK2,sK0)
    | ~ v4_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_34,plain,
    ( v4_tops_1(sK3,sK1) = iProver_top
    | v4_tops_1(sK2,sK0) != iProver_top
    | v4_pre_topc(sK2,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_14,negated_conjecture,
    ( ~ v5_tops_1(sK3,sK1)
    | ~ v4_tops_1(sK2,sK0)
    | ~ v4_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_35,plain,
    ( v5_tops_1(sK3,sK1) != iProver_top
    | v4_tops_1(sK2,sK0) != iProver_top
    | v4_pre_topc(sK2,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_6172,plain,
    ( v4_tops_1(sK2,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5836,c_21,c_28,c_29,c_33,c_34,c_35,c_1463,c_1466,c_2002,c_4359,c_5653,c_6099])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6361,c_6349,c_6172,c_3131,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:32:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  % Running in FOF mode
% 3.23/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.23/1.00  
% 3.23/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.23/1.00  
% 3.23/1.00  ------  iProver source info
% 3.23/1.00  
% 3.23/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.23/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.23/1.00  git: non_committed_changes: false
% 3.23/1.00  git: last_make_outside_of_git: false
% 3.23/1.00  
% 3.23/1.00  ------ 
% 3.23/1.00  
% 3.23/1.00  ------ Input Options
% 3.23/1.00  
% 3.23/1.00  --out_options                           all
% 3.23/1.00  --tptp_safe_out                         true
% 3.23/1.00  --problem_path                          ""
% 3.23/1.00  --include_path                          ""
% 3.23/1.00  --clausifier                            res/vclausify_rel
% 3.23/1.00  --clausifier_options                    --mode clausify
% 3.23/1.00  --stdin                                 false
% 3.23/1.00  --stats_out                             all
% 3.23/1.00  
% 3.23/1.00  ------ General Options
% 3.23/1.00  
% 3.23/1.00  --fof                                   false
% 3.23/1.00  --time_out_real                         305.
% 3.23/1.00  --time_out_virtual                      -1.
% 3.23/1.00  --symbol_type_check                     false
% 3.23/1.00  --clausify_out                          false
% 3.23/1.00  --sig_cnt_out                           false
% 3.23/1.00  --trig_cnt_out                          false
% 3.23/1.00  --trig_cnt_out_tolerance                1.
% 3.23/1.00  --trig_cnt_out_sk_spl                   false
% 3.23/1.00  --abstr_cl_out                          false
% 3.23/1.00  
% 3.23/1.00  ------ Global Options
% 3.23/1.00  
% 3.23/1.00  --schedule                              default
% 3.23/1.00  --add_important_lit                     false
% 3.23/1.00  --prop_solver_per_cl                    1000
% 3.23/1.00  --min_unsat_core                        false
% 3.23/1.00  --soft_assumptions                      false
% 3.23/1.00  --soft_lemma_size                       3
% 3.23/1.00  --prop_impl_unit_size                   0
% 3.23/1.00  --prop_impl_unit                        []
% 3.23/1.00  --share_sel_clauses                     true
% 3.23/1.00  --reset_solvers                         false
% 3.23/1.00  --bc_imp_inh                            [conj_cone]
% 3.23/1.00  --conj_cone_tolerance                   3.
% 3.23/1.00  --extra_neg_conj                        none
% 3.23/1.00  --large_theory_mode                     true
% 3.23/1.00  --prolific_symb_bound                   200
% 3.23/1.00  --lt_threshold                          2000
% 3.23/1.00  --clause_weak_htbl                      true
% 3.23/1.00  --gc_record_bc_elim                     false
% 3.23/1.00  
% 3.23/1.00  ------ Preprocessing Options
% 3.23/1.00  
% 3.23/1.00  --preprocessing_flag                    true
% 3.23/1.00  --time_out_prep_mult                    0.1
% 3.23/1.00  --splitting_mode                        input
% 3.23/1.00  --splitting_grd                         true
% 3.23/1.00  --splitting_cvd                         false
% 3.23/1.00  --splitting_cvd_svl                     false
% 3.23/1.00  --splitting_nvd                         32
% 3.23/1.00  --sub_typing                            true
% 3.23/1.00  --prep_gs_sim                           true
% 3.23/1.00  --prep_unflatten                        true
% 3.23/1.00  --prep_res_sim                          true
% 3.23/1.00  --prep_upred                            true
% 3.23/1.00  --prep_sem_filter                       exhaustive
% 3.23/1.00  --prep_sem_filter_out                   false
% 3.23/1.00  --pred_elim                             true
% 3.23/1.00  --res_sim_input                         true
% 3.23/1.00  --eq_ax_congr_red                       true
% 3.23/1.00  --pure_diseq_elim                       true
% 3.23/1.00  --brand_transform                       false
% 3.23/1.00  --non_eq_to_eq                          false
% 3.23/1.00  --prep_def_merge                        true
% 3.23/1.00  --prep_def_merge_prop_impl              false
% 3.23/1.00  --prep_def_merge_mbd                    true
% 3.23/1.00  --prep_def_merge_tr_red                 false
% 3.23/1.00  --prep_def_merge_tr_cl                  false
% 3.23/1.00  --smt_preprocessing                     true
% 3.23/1.00  --smt_ac_axioms                         fast
% 3.23/1.00  --preprocessed_out                      false
% 3.23/1.00  --preprocessed_stats                    false
% 3.23/1.00  
% 3.23/1.00  ------ Abstraction refinement Options
% 3.23/1.00  
% 3.23/1.00  --abstr_ref                             []
% 3.23/1.00  --abstr_ref_prep                        false
% 3.23/1.00  --abstr_ref_until_sat                   false
% 3.23/1.00  --abstr_ref_sig_restrict                funpre
% 3.23/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.23/1.00  --abstr_ref_under                       []
% 3.23/1.00  
% 3.23/1.00  ------ SAT Options
% 3.23/1.00  
% 3.23/1.00  --sat_mode                              false
% 3.23/1.00  --sat_fm_restart_options                ""
% 3.23/1.00  --sat_gr_def                            false
% 3.23/1.00  --sat_epr_types                         true
% 3.23/1.00  --sat_non_cyclic_types                  false
% 3.23/1.00  --sat_finite_models                     false
% 3.23/1.00  --sat_fm_lemmas                         false
% 3.23/1.00  --sat_fm_prep                           false
% 3.23/1.00  --sat_fm_uc_incr                        true
% 3.23/1.00  --sat_out_model                         small
% 3.23/1.00  --sat_out_clauses                       false
% 3.23/1.00  
% 3.23/1.00  ------ QBF Options
% 3.23/1.00  
% 3.23/1.00  --qbf_mode                              false
% 3.23/1.00  --qbf_elim_univ                         false
% 3.23/1.00  --qbf_dom_inst                          none
% 3.23/1.00  --qbf_dom_pre_inst                      false
% 3.23/1.00  --qbf_sk_in                             false
% 3.23/1.00  --qbf_pred_elim                         true
% 3.23/1.00  --qbf_split                             512
% 3.23/1.00  
% 3.23/1.00  ------ BMC1 Options
% 3.23/1.00  
% 3.23/1.00  --bmc1_incremental                      false
% 3.23/1.00  --bmc1_axioms                           reachable_all
% 3.23/1.00  --bmc1_min_bound                        0
% 3.23/1.00  --bmc1_max_bound                        -1
% 3.23/1.00  --bmc1_max_bound_default                -1
% 3.23/1.00  --bmc1_symbol_reachability              true
% 3.23/1.00  --bmc1_property_lemmas                  false
% 3.23/1.00  --bmc1_k_induction                      false
% 3.23/1.00  --bmc1_non_equiv_states                 false
% 3.23/1.00  --bmc1_deadlock                         false
% 3.23/1.00  --bmc1_ucm                              false
% 3.23/1.00  --bmc1_add_unsat_core                   none
% 3.23/1.00  --bmc1_unsat_core_children              false
% 3.23/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.23/1.00  --bmc1_out_stat                         full
% 3.23/1.00  --bmc1_ground_init                      false
% 3.23/1.00  --bmc1_pre_inst_next_state              false
% 3.23/1.00  --bmc1_pre_inst_state                   false
% 3.23/1.00  --bmc1_pre_inst_reach_state             false
% 3.23/1.00  --bmc1_out_unsat_core                   false
% 3.23/1.00  --bmc1_aig_witness_out                  false
% 3.23/1.00  --bmc1_verbose                          false
% 3.23/1.00  --bmc1_dump_clauses_tptp                false
% 3.23/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.23/1.00  --bmc1_dump_file                        -
% 3.23/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.23/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.23/1.00  --bmc1_ucm_extend_mode                  1
% 3.23/1.00  --bmc1_ucm_init_mode                    2
% 3.23/1.00  --bmc1_ucm_cone_mode                    none
% 3.23/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.23/1.00  --bmc1_ucm_relax_model                  4
% 3.23/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.23/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.23/1.00  --bmc1_ucm_layered_model                none
% 3.23/1.00  --bmc1_ucm_max_lemma_size               10
% 3.23/1.00  
% 3.23/1.00  ------ AIG Options
% 3.23/1.00  
% 3.23/1.00  --aig_mode                              false
% 3.23/1.00  
% 3.23/1.00  ------ Instantiation Options
% 3.23/1.00  
% 3.23/1.00  --instantiation_flag                    true
% 3.23/1.00  --inst_sos_flag                         false
% 3.23/1.00  --inst_sos_phase                        true
% 3.23/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.23/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.23/1.00  --inst_lit_sel_side                     num_symb
% 3.23/1.00  --inst_solver_per_active                1400
% 3.23/1.00  --inst_solver_calls_frac                1.
% 3.23/1.00  --inst_passive_queue_type               priority_queues
% 3.23/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.23/1.00  --inst_passive_queues_freq              [25;2]
% 3.23/1.00  --inst_dismatching                      true
% 3.23/1.00  --inst_eager_unprocessed_to_passive     true
% 3.23/1.00  --inst_prop_sim_given                   true
% 3.23/1.00  --inst_prop_sim_new                     false
% 3.23/1.00  --inst_subs_new                         false
% 3.23/1.00  --inst_eq_res_simp                      false
% 3.23/1.00  --inst_subs_given                       false
% 3.23/1.00  --inst_orphan_elimination               true
% 3.23/1.00  --inst_learning_loop_flag               true
% 3.23/1.00  --inst_learning_start                   3000
% 3.23/1.00  --inst_learning_factor                  2
% 3.23/1.00  --inst_start_prop_sim_after_learn       3
% 3.23/1.00  --inst_sel_renew                        solver
% 3.23/1.00  --inst_lit_activity_flag                true
% 3.23/1.00  --inst_restr_to_given                   false
% 3.23/1.00  --inst_activity_threshold               500
% 3.23/1.00  --inst_out_proof                        true
% 3.23/1.00  
% 3.23/1.00  ------ Resolution Options
% 3.23/1.00  
% 3.23/1.00  --resolution_flag                       true
% 3.23/1.00  --res_lit_sel                           adaptive
% 3.23/1.00  --res_lit_sel_side                      none
% 3.23/1.00  --res_ordering                          kbo
% 3.23/1.00  --res_to_prop_solver                    active
% 3.23/1.00  --res_prop_simpl_new                    false
% 3.23/1.00  --res_prop_simpl_given                  true
% 3.23/1.00  --res_passive_queue_type                priority_queues
% 3.23/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.23/1.00  --res_passive_queues_freq               [15;5]
% 3.23/1.00  --res_forward_subs                      full
% 3.23/1.00  --res_backward_subs                     full
% 3.23/1.00  --res_forward_subs_resolution           true
% 3.23/1.00  --res_backward_subs_resolution          true
% 3.23/1.00  --res_orphan_elimination                true
% 3.23/1.00  --res_time_limit                        2.
% 3.23/1.00  --res_out_proof                         true
% 3.23/1.00  
% 3.23/1.00  ------ Superposition Options
% 3.23/1.00  
% 3.23/1.00  --superposition_flag                    true
% 3.23/1.00  --sup_passive_queue_type                priority_queues
% 3.23/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.23/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.23/1.00  --demod_completeness_check              fast
% 3.23/1.00  --demod_use_ground                      true
% 3.23/1.00  --sup_to_prop_solver                    passive
% 3.23/1.00  --sup_prop_simpl_new                    true
% 3.23/1.00  --sup_prop_simpl_given                  true
% 3.23/1.00  --sup_fun_splitting                     false
% 3.23/1.00  --sup_smt_interval                      50000
% 3.23/1.00  
% 3.23/1.00  ------ Superposition Simplification Setup
% 3.23/1.00  
% 3.23/1.00  --sup_indices_passive                   []
% 3.23/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.23/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.23/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.23/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.23/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.23/1.00  --sup_full_bw                           [BwDemod]
% 3.23/1.00  --sup_immed_triv                        [TrivRules]
% 3.23/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.23/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.23/1.00  --sup_immed_bw_main                     []
% 3.23/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.23/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.23/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.23/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.23/1.00  
% 3.23/1.00  ------ Combination Options
% 3.23/1.00  
% 3.23/1.00  --comb_res_mult                         3
% 3.23/1.00  --comb_sup_mult                         2
% 3.23/1.00  --comb_inst_mult                        10
% 3.23/1.00  
% 3.23/1.00  ------ Debug Options
% 3.23/1.00  
% 3.23/1.00  --dbg_backtrace                         false
% 3.23/1.00  --dbg_dump_prop_clauses                 false
% 3.23/1.00  --dbg_dump_prop_clauses_file            -
% 3.23/1.00  --dbg_out_stat                          false
% 3.23/1.00  ------ Parsing...
% 3.23/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.23/1.00  
% 3.23/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 3.23/1.00  
% 3.23/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.23/1.00  
% 3.23/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.23/1.00  ------ Proving...
% 3.23/1.00  ------ Problem Properties 
% 3.23/1.00  
% 3.23/1.00  
% 3.23/1.00  clauses                                 30
% 3.23/1.00  conjectures                             8
% 3.23/1.00  EPR                                     8
% 3.23/1.00  Horn                                    28
% 3.23/1.00  unary                                   3
% 3.23/1.00  binary                                  8
% 3.23/1.00  lits                                    82
% 3.23/1.00  lits eq                                 8
% 3.23/1.00  fd_pure                                 0
% 3.23/1.00  fd_pseudo                               0
% 3.23/1.00  fd_cond                                 0
% 3.23/1.00  fd_pseudo_cond                          1
% 3.23/1.00  AC symbols                              0
% 3.23/1.00  
% 3.23/1.00  ------ Schedule dynamic 5 is on 
% 3.23/1.00  
% 3.23/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.23/1.00  
% 3.23/1.00  
% 3.23/1.00  ------ 
% 3.23/1.00  Current options:
% 3.23/1.00  ------ 
% 3.23/1.00  
% 3.23/1.00  ------ Input Options
% 3.23/1.00  
% 3.23/1.00  --out_options                           all
% 3.23/1.00  --tptp_safe_out                         true
% 3.23/1.00  --problem_path                          ""
% 3.23/1.00  --include_path                          ""
% 3.23/1.00  --clausifier                            res/vclausify_rel
% 3.23/1.00  --clausifier_options                    --mode clausify
% 3.23/1.00  --stdin                                 false
% 3.23/1.00  --stats_out                             all
% 3.23/1.00  
% 3.23/1.00  ------ General Options
% 3.23/1.00  
% 3.23/1.00  --fof                                   false
% 3.23/1.00  --time_out_real                         305.
% 3.23/1.00  --time_out_virtual                      -1.
% 3.23/1.00  --symbol_type_check                     false
% 3.23/1.00  --clausify_out                          false
% 3.23/1.00  --sig_cnt_out                           false
% 3.23/1.00  --trig_cnt_out                          false
% 3.23/1.00  --trig_cnt_out_tolerance                1.
% 3.23/1.00  --trig_cnt_out_sk_spl                   false
% 3.23/1.00  --abstr_cl_out                          false
% 3.23/1.00  
% 3.23/1.00  ------ Global Options
% 3.23/1.00  
% 3.23/1.00  --schedule                              default
% 3.23/1.00  --add_important_lit                     false
% 3.23/1.00  --prop_solver_per_cl                    1000
% 3.23/1.00  --min_unsat_core                        false
% 3.23/1.00  --soft_assumptions                      false
% 3.23/1.00  --soft_lemma_size                       3
% 3.23/1.00  --prop_impl_unit_size                   0
% 3.23/1.00  --prop_impl_unit                        []
% 3.23/1.00  --share_sel_clauses                     true
% 3.23/1.00  --reset_solvers                         false
% 3.23/1.00  --bc_imp_inh                            [conj_cone]
% 3.23/1.00  --conj_cone_tolerance                   3.
% 3.23/1.00  --extra_neg_conj                        none
% 3.23/1.00  --large_theory_mode                     true
% 3.23/1.00  --prolific_symb_bound                   200
% 3.23/1.00  --lt_threshold                          2000
% 3.23/1.00  --clause_weak_htbl                      true
% 3.23/1.00  --gc_record_bc_elim                     false
% 3.23/1.00  
% 3.23/1.00  ------ Preprocessing Options
% 3.23/1.00  
% 3.23/1.00  --preprocessing_flag                    true
% 3.23/1.00  --time_out_prep_mult                    0.1
% 3.23/1.00  --splitting_mode                        input
% 3.23/1.00  --splitting_grd                         true
% 3.23/1.00  --splitting_cvd                         false
% 3.23/1.00  --splitting_cvd_svl                     false
% 3.23/1.00  --splitting_nvd                         32
% 3.23/1.00  --sub_typing                            true
% 3.23/1.00  --prep_gs_sim                           true
% 3.23/1.00  --prep_unflatten                        true
% 3.23/1.00  --prep_res_sim                          true
% 3.23/1.00  --prep_upred                            true
% 3.23/1.00  --prep_sem_filter                       exhaustive
% 3.23/1.00  --prep_sem_filter_out                   false
% 3.23/1.00  --pred_elim                             true
% 3.23/1.00  --res_sim_input                         true
% 3.23/1.00  --eq_ax_congr_red                       true
% 3.23/1.00  --pure_diseq_elim                       true
% 3.23/1.00  --brand_transform                       false
% 3.23/1.00  --non_eq_to_eq                          false
% 3.23/1.00  --prep_def_merge                        true
% 3.23/1.00  --prep_def_merge_prop_impl              false
% 3.23/1.00  --prep_def_merge_mbd                    true
% 3.23/1.00  --prep_def_merge_tr_red                 false
% 3.23/1.00  --prep_def_merge_tr_cl                  false
% 3.23/1.00  --smt_preprocessing                     true
% 3.23/1.00  --smt_ac_axioms                         fast
% 3.23/1.00  --preprocessed_out                      false
% 3.23/1.00  --preprocessed_stats                    false
% 3.23/1.00  
% 3.23/1.00  ------ Abstraction refinement Options
% 3.23/1.00  
% 3.23/1.00  --abstr_ref                             []
% 3.23/1.00  --abstr_ref_prep                        false
% 3.23/1.00  --abstr_ref_until_sat                   false
% 3.23/1.00  --abstr_ref_sig_restrict                funpre
% 3.23/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.23/1.00  --abstr_ref_under                       []
% 3.23/1.00  
% 3.23/1.00  ------ SAT Options
% 3.23/1.00  
% 3.23/1.00  --sat_mode                              false
% 3.23/1.00  --sat_fm_restart_options                ""
% 3.23/1.00  --sat_gr_def                            false
% 3.23/1.00  --sat_epr_types                         true
% 3.23/1.00  --sat_non_cyclic_types                  false
% 3.23/1.00  --sat_finite_models                     false
% 3.23/1.00  --sat_fm_lemmas                         false
% 3.23/1.00  --sat_fm_prep                           false
% 3.23/1.00  --sat_fm_uc_incr                        true
% 3.23/1.00  --sat_out_model                         small
% 3.23/1.00  --sat_out_clauses                       false
% 3.23/1.00  
% 3.23/1.00  ------ QBF Options
% 3.23/1.00  
% 3.23/1.00  --qbf_mode                              false
% 3.23/1.00  --qbf_elim_univ                         false
% 3.23/1.00  --qbf_dom_inst                          none
% 3.23/1.00  --qbf_dom_pre_inst                      false
% 3.23/1.00  --qbf_sk_in                             false
% 3.23/1.00  --qbf_pred_elim                         true
% 3.23/1.00  --qbf_split                             512
% 3.23/1.00  
% 3.23/1.00  ------ BMC1 Options
% 3.23/1.00  
% 3.23/1.00  --bmc1_incremental                      false
% 3.23/1.00  --bmc1_axioms                           reachable_all
% 3.23/1.00  --bmc1_min_bound                        0
% 3.23/1.00  --bmc1_max_bound                        -1
% 3.23/1.00  --bmc1_max_bound_default                -1
% 3.23/1.00  --bmc1_symbol_reachability              true
% 3.23/1.00  --bmc1_property_lemmas                  false
% 3.23/1.00  --bmc1_k_induction                      false
% 3.23/1.00  --bmc1_non_equiv_states                 false
% 3.23/1.00  --bmc1_deadlock                         false
% 3.23/1.00  --bmc1_ucm                              false
% 3.23/1.00  --bmc1_add_unsat_core                   none
% 3.23/1.00  --bmc1_unsat_core_children              false
% 3.23/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.23/1.00  --bmc1_out_stat                         full
% 3.23/1.00  --bmc1_ground_init                      false
% 3.23/1.00  --bmc1_pre_inst_next_state              false
% 3.23/1.00  --bmc1_pre_inst_state                   false
% 3.23/1.00  --bmc1_pre_inst_reach_state             false
% 3.23/1.00  --bmc1_out_unsat_core                   false
% 3.23/1.00  --bmc1_aig_witness_out                  false
% 3.23/1.00  --bmc1_verbose                          false
% 3.23/1.00  --bmc1_dump_clauses_tptp                false
% 3.23/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.23/1.00  --bmc1_dump_file                        -
% 3.23/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.23/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.23/1.00  --bmc1_ucm_extend_mode                  1
% 3.23/1.00  --bmc1_ucm_init_mode                    2
% 3.23/1.00  --bmc1_ucm_cone_mode                    none
% 3.23/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.23/1.00  --bmc1_ucm_relax_model                  4
% 3.23/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.23/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.23/1.00  --bmc1_ucm_layered_model                none
% 3.23/1.00  --bmc1_ucm_max_lemma_size               10
% 3.23/1.00  
% 3.23/1.00  ------ AIG Options
% 3.23/1.00  
% 3.23/1.00  --aig_mode                              false
% 3.23/1.00  
% 3.23/1.00  ------ Instantiation Options
% 3.23/1.00  
% 3.23/1.00  --instantiation_flag                    true
% 3.23/1.00  --inst_sos_flag                         false
% 3.23/1.00  --inst_sos_phase                        true
% 3.23/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.23/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.23/1.00  --inst_lit_sel_side                     none
% 3.23/1.00  --inst_solver_per_active                1400
% 3.23/1.00  --inst_solver_calls_frac                1.
% 3.23/1.00  --inst_passive_queue_type               priority_queues
% 3.23/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.23/1.00  --inst_passive_queues_freq              [25;2]
% 3.23/1.00  --inst_dismatching                      true
% 3.23/1.00  --inst_eager_unprocessed_to_passive     true
% 3.23/1.00  --inst_prop_sim_given                   true
% 3.23/1.00  --inst_prop_sim_new                     false
% 3.23/1.00  --inst_subs_new                         false
% 3.23/1.00  --inst_eq_res_simp                      false
% 3.23/1.00  --inst_subs_given                       false
% 3.23/1.00  --inst_orphan_elimination               true
% 3.23/1.00  --inst_learning_loop_flag               true
% 3.23/1.00  --inst_learning_start                   3000
% 3.23/1.00  --inst_learning_factor                  2
% 3.23/1.00  --inst_start_prop_sim_after_learn       3
% 3.23/1.00  --inst_sel_renew                        solver
% 3.23/1.00  --inst_lit_activity_flag                true
% 3.23/1.00  --inst_restr_to_given                   false
% 3.23/1.00  --inst_activity_threshold               500
% 3.23/1.00  --inst_out_proof                        true
% 3.23/1.00  
% 3.23/1.00  ------ Resolution Options
% 3.23/1.00  
% 3.23/1.00  --resolution_flag                       false
% 3.23/1.00  --res_lit_sel                           adaptive
% 3.23/1.00  --res_lit_sel_side                      none
% 3.23/1.00  --res_ordering                          kbo
% 3.23/1.00  --res_to_prop_solver                    active
% 3.23/1.00  --res_prop_simpl_new                    false
% 3.23/1.00  --res_prop_simpl_given                  true
% 3.23/1.00  --res_passive_queue_type                priority_queues
% 3.23/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.23/1.00  --res_passive_queues_freq               [15;5]
% 3.23/1.00  --res_forward_subs                      full
% 3.23/1.00  --res_backward_subs                     full
% 3.23/1.00  --res_forward_subs_resolution           true
% 3.23/1.00  --res_backward_subs_resolution          true
% 3.23/1.00  --res_orphan_elimination                true
% 3.23/1.00  --res_time_limit                        2.
% 3.23/1.00  --res_out_proof                         true
% 3.23/1.00  
% 3.23/1.00  ------ Superposition Options
% 3.23/1.00  
% 3.23/1.00  --superposition_flag                    true
% 3.23/1.00  --sup_passive_queue_type                priority_queues
% 3.23/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.23/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.23/1.00  --demod_completeness_check              fast
% 3.23/1.00  --demod_use_ground                      true
% 3.23/1.00  --sup_to_prop_solver                    passive
% 3.23/1.00  --sup_prop_simpl_new                    true
% 3.23/1.00  --sup_prop_simpl_given                  true
% 3.23/1.00  --sup_fun_splitting                     false
% 3.23/1.00  --sup_smt_interval                      50000
% 3.23/1.00  
% 3.23/1.00  ------ Superposition Simplification Setup
% 3.23/1.00  
% 3.23/1.00  --sup_indices_passive                   []
% 3.23/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.23/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.23/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.23/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.23/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.23/1.00  --sup_full_bw                           [BwDemod]
% 3.23/1.00  --sup_immed_triv                        [TrivRules]
% 3.23/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.23/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.23/1.00  --sup_immed_bw_main                     []
% 3.23/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.23/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.23/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.23/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.23/1.00  
% 3.23/1.00  ------ Combination Options
% 3.23/1.00  
% 3.23/1.00  --comb_res_mult                         3
% 3.23/1.00  --comb_sup_mult                         2
% 3.23/1.00  --comb_inst_mult                        10
% 3.23/1.00  
% 3.23/1.00  ------ Debug Options
% 3.23/1.00  
% 3.23/1.00  --dbg_backtrace                         false
% 3.23/1.00  --dbg_dump_prop_clauses                 false
% 3.23/1.00  --dbg_dump_prop_clauses_file            -
% 3.23/1.00  --dbg_out_stat                          false
% 3.23/1.00  
% 3.23/1.00  
% 3.23/1.00  
% 3.23/1.00  
% 3.23/1.00  ------ Proving...
% 3.23/1.00  
% 3.23/1.00  
% 3.23/1.00  % SZS status Theorem for theBenchmark.p
% 3.23/1.00  
% 3.23/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.23/1.00  
% 3.23/1.00  fof(f9,conjecture,(
% 3.23/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v5_tops_1(X2,X0) => (v4_tops_1(X2,X0) & v4_pre_topc(X2,X0))) & ((v4_tops_1(X3,X1) & v4_pre_topc(X3,X1)) => v5_tops_1(X3,X1)))))))),
% 3.23/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/1.00  
% 3.23/1.00  fof(f10,negated_conjecture,(
% 3.23/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v5_tops_1(X2,X0) => (v4_tops_1(X2,X0) & v4_pre_topc(X2,X0))) & ((v4_tops_1(X3,X1) & v4_pre_topc(X3,X1)) => v5_tops_1(X3,X1)))))))),
% 3.23/1.00    inference(negated_conjecture,[],[f9])).
% 3.23/1.00  
% 3.23/1.00  fof(f22,plain,(
% 3.23/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v4_pre_topc(X2,X0)) & v5_tops_1(X2,X0)) | (~v5_tops_1(X3,X1) & (v4_tops_1(X3,X1) & v4_pre_topc(X3,X1)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.23/1.00    inference(ennf_transformation,[],[f10])).
% 3.23/1.00  
% 3.23/1.00  fof(f23,plain,(
% 3.23/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v4_pre_topc(X2,X0)) & v5_tops_1(X2,X0)) | (~v5_tops_1(X3,X1) & v4_tops_1(X3,X1) & v4_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.23/1.00    inference(flattening,[],[f22])).
% 3.23/1.00  
% 3.23/1.00  fof(f32,plain,(
% 3.23/1.00    ( ! [X2,X0,X1] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v4_pre_topc(X2,X0)) & v5_tops_1(X2,X0)) | (~v5_tops_1(X3,X1) & v4_tops_1(X3,X1) & v4_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => ((((~v4_tops_1(X2,X0) | ~v4_pre_topc(X2,X0)) & v5_tops_1(X2,X0)) | (~v5_tops_1(sK3,X1) & v4_tops_1(sK3,X1) & v4_pre_topc(sK3,X1))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X1))))) )),
% 3.23/1.00    introduced(choice_axiom,[])).
% 3.23/1.00  
% 3.23/1.00  fof(f31,plain,(
% 3.23/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v4_pre_topc(X2,X0)) & v5_tops_1(X2,X0)) | (~v5_tops_1(X3,X1) & v4_tops_1(X3,X1) & v4_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X3] : ((((~v4_tops_1(sK2,X0) | ~v4_pre_topc(sK2,X0)) & v5_tops_1(sK2,X0)) | (~v5_tops_1(X3,X1) & v4_tops_1(X3,X1) & v4_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.23/1.00    introduced(choice_axiom,[])).
% 3.23/1.00  
% 3.23/1.00  fof(f30,plain,(
% 3.23/1.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v4_pre_topc(X2,X0)) & v5_tops_1(X2,X0)) | (~v5_tops_1(X3,X1) & v4_tops_1(X3,X1) & v4_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) => (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v4_pre_topc(X2,X0)) & v5_tops_1(X2,X0)) | (~v5_tops_1(X3,sK1) & v4_tops_1(X3,sK1) & v4_pre_topc(X3,sK1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(sK1))) )),
% 3.23/1.00    introduced(choice_axiom,[])).
% 3.23/1.00  
% 3.23/1.00  fof(f29,plain,(
% 3.23/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v4_pre_topc(X2,X0)) & v5_tops_1(X2,X0)) | (~v5_tops_1(X3,X1) & v4_tops_1(X3,X1) & v4_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,sK0) | ~v4_pre_topc(X2,sK0)) & v5_tops_1(X2,sK0)) | (~v5_tops_1(X3,X1) & v4_tops_1(X3,X1) & v4_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 3.23/1.00    introduced(choice_axiom,[])).
% 3.23/1.00  
% 3.23/1.00  fof(f33,plain,(
% 3.23/1.00    ((((((~v4_tops_1(sK2,sK0) | ~v4_pre_topc(sK2,sK0)) & v5_tops_1(sK2,sK0)) | (~v5_tops_1(sK3,sK1) & v4_tops_1(sK3,sK1) & v4_pre_topc(sK3,sK1))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 3.23/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f32,f31,f30,f29])).
% 3.23/1.00  
% 3.23/1.00  fof(f54,plain,(
% 3.23/1.00    v5_tops_1(sK2,sK0) | v4_tops_1(sK3,sK1)),
% 3.23/1.00    inference(cnf_transformation,[],[f33])).
% 3.23/1.00  
% 3.23/1.00  fof(f51,plain,(
% 3.23/1.00    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.23/1.00    inference(cnf_transformation,[],[f33])).
% 3.23/1.00  
% 3.23/1.00  fof(f5,axiom,(
% 3.23/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1)))),
% 3.23/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/1.00  
% 3.23/1.00  fof(f15,plain,(
% 3.23/1.00    ! [X0] : (! [X1] : ((v5_tops_1(X1,X0) <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.23/1.00    inference(ennf_transformation,[],[f5])).
% 3.23/1.00  
% 3.23/1.00  fof(f28,plain,(
% 3.23/1.00    ! [X0] : (! [X1] : (((v5_tops_1(X1,X0) | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1) & (k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 | ~v5_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.23/1.00    inference(nnf_transformation,[],[f15])).
% 3.23/1.00  
% 3.23/1.00  fof(f43,plain,(
% 3.23/1.00    ( ! [X0,X1] : (k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 | ~v5_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.23/1.00    inference(cnf_transformation,[],[f28])).
% 3.23/1.00  
% 3.23/1.00  fof(f49,plain,(
% 3.23/1.00    l1_pre_topc(sK0)),
% 3.23/1.00    inference(cnf_transformation,[],[f33])).
% 3.23/1.00  
% 3.23/1.00  fof(f53,plain,(
% 3.23/1.00    v5_tops_1(sK2,sK0) | v4_pre_topc(sK3,sK1)),
% 3.23/1.00    inference(cnf_transformation,[],[f33])).
% 3.23/1.00  
% 3.23/1.00  fof(f52,plain,(
% 3.23/1.00    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 3.23/1.00    inference(cnf_transformation,[],[f33])).
% 3.23/1.00  
% 3.23/1.00  fof(f3,axiom,(
% 3.23/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 3.23/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/1.00  
% 3.23/1.00  fof(f12,plain,(
% 3.23/1.00    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.23/1.00    inference(ennf_transformation,[],[f3])).
% 3.23/1.00  
% 3.23/1.00  fof(f13,plain,(
% 3.23/1.00    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.23/1.00    inference(flattening,[],[f12])).
% 3.23/1.00  
% 3.23/1.00  fof(f38,plain,(
% 3.23/1.00    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.23/1.00    inference(cnf_transformation,[],[f13])).
% 3.23/1.00  
% 3.23/1.00  fof(f50,plain,(
% 3.23/1.00    l1_pre_topc(sK1)),
% 3.23/1.00    inference(cnf_transformation,[],[f33])).
% 3.23/1.00  
% 3.23/1.00  fof(f6,axiom,(
% 3.23/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.23/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/1.00  
% 3.23/1.00  fof(f16,plain,(
% 3.23/1.00    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.23/1.00    inference(ennf_transformation,[],[f6])).
% 3.23/1.00  
% 3.23/1.00  fof(f17,plain,(
% 3.23/1.00    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.23/1.00    inference(flattening,[],[f16])).
% 3.23/1.00  
% 3.23/1.00  fof(f45,plain,(
% 3.23/1.00    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.23/1.00    inference(cnf_transformation,[],[f17])).
% 3.23/1.00  
% 3.23/1.00  fof(f2,axiom,(
% 3.23/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 3.23/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/1.00  
% 3.23/1.00  fof(f11,plain,(
% 3.23/1.00    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.23/1.00    inference(ennf_transformation,[],[f2])).
% 3.23/1.00  
% 3.23/1.00  fof(f37,plain,(
% 3.23/1.00    ( ! [X0,X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.23/1.00    inference(cnf_transformation,[],[f11])).
% 3.23/1.00  
% 3.23/1.00  fof(f56,plain,(
% 3.23/1.00    ~v4_tops_1(sK2,sK0) | ~v4_pre_topc(sK2,sK0) | v4_pre_topc(sK3,sK1)),
% 3.23/1.00    inference(cnf_transformation,[],[f33])).
% 3.23/1.00  
% 3.23/1.00  fof(f39,plain,(
% 3.23/1.00    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.23/1.00    inference(cnf_transformation,[],[f13])).
% 3.23/1.00  
% 3.23/1.00  fof(f48,plain,(
% 3.23/1.00    v2_pre_topc(sK0)),
% 3.23/1.00    inference(cnf_transformation,[],[f33])).
% 3.23/1.00  
% 3.23/1.00  fof(f1,axiom,(
% 3.23/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.23/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/1.00  
% 3.23/1.00  fof(f24,plain,(
% 3.23/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.23/1.00    inference(nnf_transformation,[],[f1])).
% 3.23/1.00  
% 3.23/1.00  fof(f25,plain,(
% 3.23/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.23/1.00    inference(flattening,[],[f24])).
% 3.23/1.00  
% 3.23/1.00  fof(f34,plain,(
% 3.23/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.23/1.00    inference(cnf_transformation,[],[f25])).
% 3.23/1.00  
% 3.23/1.00  fof(f60,plain,(
% 3.23/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.23/1.00    inference(equality_resolution,[],[f34])).
% 3.23/1.00  
% 3.23/1.00  fof(f7,axiom,(
% 3.23/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 3.23/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/1.00  
% 3.23/1.00  fof(f18,plain,(
% 3.23/1.00    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.23/1.00    inference(ennf_transformation,[],[f7])).
% 3.23/1.00  
% 3.23/1.00  fof(f19,plain,(
% 3.23/1.00    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.23/1.00    inference(flattening,[],[f18])).
% 3.23/1.00  
% 3.23/1.00  fof(f46,plain,(
% 3.23/1.00    ( ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.23/1.00    inference(cnf_transformation,[],[f19])).
% 3.23/1.00  
% 3.23/1.00  fof(f4,axiom,(
% 3.23/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)))))),
% 3.23/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/1.00  
% 3.23/1.00  fof(f14,plain,(
% 3.23/1.00    ! [X0] : (! [X1] : ((v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.23/1.00    inference(ennf_transformation,[],[f4])).
% 3.23/1.00  
% 3.23/1.00  fof(f26,plain,(
% 3.23/1.00    ! [X0] : (! [X1] : (((v4_tops_1(X1,X0) | (~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1))) & ((r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) | ~v4_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.23/1.00    inference(nnf_transformation,[],[f14])).
% 3.23/1.00  
% 3.23/1.00  fof(f27,plain,(
% 3.23/1.00    ! [X0] : (! [X1] : (((v4_tops_1(X1,X0) | ~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) & ((r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) | ~v4_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.23/1.00    inference(flattening,[],[f26])).
% 3.23/1.00  
% 3.23/1.00  fof(f40,plain,(
% 3.23/1.00    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) | ~v4_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.23/1.00    inference(cnf_transformation,[],[f27])).
% 3.23/1.00  
% 3.23/1.00  fof(f8,axiom,(
% 3.23/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X2,X1) & v4_pre_topc(X1,X0)) => r1_tarski(k2_pre_topc(X0,X2),X1)))))),
% 3.23/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/1.00  
% 3.23/1.00  fof(f20,plain,(
% 3.23/1.00    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k2_pre_topc(X0,X2),X1) | (~r1_tarski(X2,X1) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.23/1.00    inference(ennf_transformation,[],[f8])).
% 3.23/1.00  
% 3.23/1.00  fof(f21,plain,(
% 3.23/1.00    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k2_pre_topc(X0,X2),X1) | ~r1_tarski(X2,X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.23/1.00    inference(flattening,[],[f20])).
% 3.23/1.00  
% 3.23/1.00  fof(f47,plain,(
% 3.23/1.00    ( ! [X2,X0,X1] : (r1_tarski(k2_pre_topc(X0,X2),X1) | ~r1_tarski(X2,X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.23/1.00    inference(cnf_transformation,[],[f21])).
% 3.23/1.00  
% 3.23/1.00  fof(f41,plain,(
% 3.23/1.00    ( ! [X0,X1] : (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~v4_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.23/1.00    inference(cnf_transformation,[],[f27])).
% 3.23/1.00  
% 3.23/1.00  fof(f36,plain,(
% 3.23/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.23/1.00    inference(cnf_transformation,[],[f25])).
% 3.23/1.00  
% 3.23/1.00  fof(f55,plain,(
% 3.23/1.00    v5_tops_1(sK2,sK0) | ~v5_tops_1(sK3,sK1)),
% 3.23/1.00    inference(cnf_transformation,[],[f33])).
% 3.23/1.00  
% 3.23/1.00  fof(f44,plain,(
% 3.23/1.00    ( ! [X0,X1] : (v5_tops_1(X1,X0) | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.23/1.00    inference(cnf_transformation,[],[f28])).
% 3.23/1.00  
% 3.23/1.00  fof(f42,plain,(
% 3.23/1.00    ( ! [X0,X1] : (v4_tops_1(X1,X0) | ~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.23/1.00    inference(cnf_transformation,[],[f27])).
% 3.23/1.00  
% 3.23/1.00  fof(f57,plain,(
% 3.23/1.00    ~v4_tops_1(sK2,sK0) | ~v4_pre_topc(sK2,sK0) | v4_tops_1(sK3,sK1)),
% 3.23/1.00    inference(cnf_transformation,[],[f33])).
% 3.23/1.00  
% 3.23/1.00  fof(f58,plain,(
% 3.23/1.00    ~v4_tops_1(sK2,sK0) | ~v4_pre_topc(sK2,sK0) | ~v5_tops_1(sK3,sK1)),
% 3.23/1.00    inference(cnf_transformation,[],[f33])).
% 3.23/1.00  
% 3.23/1.00  cnf(c_18,negated_conjecture,
% 3.23/1.00      ( v5_tops_1(sK2,sK0) | v4_tops_1(sK3,sK1) ),
% 3.23/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1207,plain,
% 3.23/1.00      ( v5_tops_1(sK2,sK0) = iProver_top
% 3.23/1.00      | v4_tops_1(sK3,sK1) = iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_21,negated_conjecture,
% 3.23/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.23/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1204,plain,
% 3.23/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_10,plain,
% 3.23/1.00      ( ~ v5_tops_1(X0,X1)
% 3.23/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.23/1.00      | ~ l1_pre_topc(X1)
% 3.23/1.00      | k2_pre_topc(X1,k1_tops_1(X1,X0)) = X0 ),
% 3.23/1.00      inference(cnf_transformation,[],[f43]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_23,negated_conjecture,
% 3.23/1.00      ( l1_pre_topc(sK0) ),
% 3.23/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_481,plain,
% 3.23/1.00      ( ~ v5_tops_1(X0,X1)
% 3.23/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.23/1.00      | k2_pre_topc(X1,k1_tops_1(X1,X0)) = X0
% 3.23/1.00      | sK0 != X1 ),
% 3.23/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_23]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_482,plain,
% 3.23/1.00      ( ~ v5_tops_1(X0,sK0)
% 3.23/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.23/1.00      | k2_pre_topc(sK0,k1_tops_1(sK0,X0)) = X0 ),
% 3.23/1.00      inference(unflattening,[status(thm)],[c_481]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1190,plain,
% 3.23/1.00      ( k2_pre_topc(sK0,k1_tops_1(sK0,X0)) = X0
% 3.23/1.00      | v5_tops_1(X0,sK0) != iProver_top
% 3.23/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_482]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_2291,plain,
% 3.23/1.00      ( k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = sK2
% 3.23/1.00      | v5_tops_1(sK2,sK0) != iProver_top ),
% 3.23/1.00      inference(superposition,[status(thm)],[c_1204,c_1190]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_2339,plain,
% 3.23/1.00      ( k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = sK2
% 3.23/1.00      | v4_tops_1(sK3,sK1) = iProver_top ),
% 3.23/1.00      inference(superposition,[status(thm)],[c_1207,c_2291]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_19,negated_conjecture,
% 3.23/1.00      ( v5_tops_1(sK2,sK0) | v4_pre_topc(sK3,sK1) ),
% 3.23/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1206,plain,
% 3.23/1.00      ( v5_tops_1(sK2,sK0) = iProver_top
% 3.23/1.00      | v4_pre_topc(sK3,sK1) = iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_2340,plain,
% 3.23/1.00      ( k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = sK2
% 3.23/1.00      | v4_pre_topc(sK3,sK1) = iProver_top ),
% 3.23/1.00      inference(superposition,[status(thm)],[c_1206,c_2291]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_20,negated_conjecture,
% 3.23/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 3.23/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1205,plain,
% 3.23/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_5,plain,
% 3.23/1.00      ( ~ v4_pre_topc(X0,X1)
% 3.23/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.23/1.00      | ~ l1_pre_topc(X1)
% 3.23/1.00      | k2_pre_topc(X1,X0) = X0 ),
% 3.23/1.00      inference(cnf_transformation,[],[f38]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_22,negated_conjecture,
% 3.23/1.00      ( l1_pre_topc(sK1) ),
% 3.23/1.00      inference(cnf_transformation,[],[f50]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_421,plain,
% 3.23/1.00      ( ~ v4_pre_topc(X0,X1)
% 3.23/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.23/1.00      | k2_pre_topc(X1,X0) = X0
% 3.23/1.00      | sK1 != X1 ),
% 3.23/1.00      inference(resolution_lifted,[status(thm)],[c_5,c_22]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_422,plain,
% 3.23/1.00      ( ~ v4_pre_topc(X0,sK1)
% 3.23/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.23/1.00      | k2_pre_topc(sK1,X0) = X0 ),
% 3.23/1.00      inference(unflattening,[status(thm)],[c_421]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1194,plain,
% 3.23/1.00      ( k2_pre_topc(sK1,X0) = X0
% 3.23/1.00      | v4_pre_topc(X0,sK1) != iProver_top
% 3.23/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_422]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_2154,plain,
% 3.23/1.00      ( k2_pre_topc(sK1,sK3) = sK3
% 3.23/1.00      | v4_pre_topc(sK3,sK1) != iProver_top ),
% 3.23/1.00      inference(superposition,[status(thm)],[c_1205,c_1194]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_2637,plain,
% 3.23/1.00      ( k2_pre_topc(sK1,sK3) = sK3
% 3.23/1.00      | k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = sK2 ),
% 3.23/1.00      inference(superposition,[status(thm)],[c_2340,c_2154]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_11,plain,
% 3.23/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.23/1.00      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.23/1.00      | ~ l1_pre_topc(X1) ),
% 3.23/1.00      inference(cnf_transformation,[],[f45]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_469,plain,
% 3.23/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.23/1.00      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.23/1.00      | sK0 != X1 ),
% 3.23/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_23]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_470,plain,
% 3.23/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.23/1.00      | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.23/1.00      inference(unflattening,[status(thm)],[c_469]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1191,plain,
% 3.23/1.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.23/1.00      | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_470]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_3,plain,
% 3.23/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.23/1.00      | r1_tarski(X0,k2_pre_topc(X1,X0))
% 3.23/1.00      | ~ l1_pre_topc(X1) ),
% 3.23/1.00      inference(cnf_transformation,[],[f37]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_574,plain,
% 3.23/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.23/1.00      | r1_tarski(X0,k2_pre_topc(X1,X0))
% 3.23/1.00      | sK0 != X1 ),
% 3.23/1.00      inference(resolution_lifted,[status(thm)],[c_3,c_23]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_575,plain,
% 3.23/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.23/1.00      | r1_tarski(X0,k2_pre_topc(sK0,X0)) ),
% 3.23/1.00      inference(unflattening,[status(thm)],[c_574]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1184,plain,
% 3.23/1.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.23/1.00      | r1_tarski(X0,k2_pre_topc(sK0,X0)) = iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_575]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1880,plain,
% 3.23/1.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.23/1.00      | r1_tarski(k1_tops_1(sK0,X0),k2_pre_topc(sK0,k1_tops_1(sK0,X0))) = iProver_top ),
% 3.23/1.00      inference(superposition,[status(thm)],[c_1191,c_1184]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_3342,plain,
% 3.23/1.00      ( k2_pre_topc(sK1,sK3) = sK3
% 3.23/1.00      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.23/1.00      | r1_tarski(k1_tops_1(sK0,sK2),sK2) = iProver_top ),
% 3.23/1.00      inference(superposition,[status(thm)],[c_2637,c_1880]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_28,plain,
% 3.23/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_16,negated_conjecture,
% 3.23/1.00      ( ~ v4_tops_1(sK2,sK0)
% 3.23/1.00      | v4_pre_topc(sK3,sK1)
% 3.23/1.00      | ~ v4_pre_topc(sK2,sK0) ),
% 3.23/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_33,plain,
% 3.23/1.00      ( v4_tops_1(sK2,sK0) != iProver_top
% 3.23/1.00      | v4_pre_topc(sK3,sK1) = iProver_top
% 3.23/1.00      | v4_pre_topc(sK2,sK0) != iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_4,plain,
% 3.23/1.00      ( v4_pre_topc(X0,X1)
% 3.23/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.23/1.00      | ~ v2_pre_topc(X1)
% 3.23/1.00      | ~ l1_pre_topc(X1)
% 3.23/1.00      | k2_pre_topc(X1,X0) != X0 ),
% 3.23/1.00      inference(cnf_transformation,[],[f39]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_24,negated_conjecture,
% 3.23/1.00      ( v2_pre_topc(sK0) ),
% 3.23/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_282,plain,
% 3.23/1.00      ( v4_pre_topc(X0,X1)
% 3.23/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.23/1.00      | ~ l1_pre_topc(X1)
% 3.23/1.00      | k2_pre_topc(X1,X0) != X0
% 3.23/1.00      | sK0 != X1 ),
% 3.23/1.00      inference(resolution_lifted,[status(thm)],[c_4,c_24]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_283,plain,
% 3.23/1.00      ( v4_pre_topc(X0,sK0)
% 3.23/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.23/1.00      | ~ l1_pre_topc(sK0)
% 3.23/1.00      | k2_pre_topc(sK0,X0) != X0 ),
% 3.23/1.00      inference(unflattening,[status(thm)],[c_282]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_287,plain,
% 3.23/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.23/1.00      | v4_pre_topc(X0,sK0)
% 3.23/1.00      | k2_pre_topc(sK0,X0) != X0 ),
% 3.23/1.00      inference(global_propositional_subsumption,
% 3.23/1.00                [status(thm)],
% 3.23/1.00                [c_283,c_23]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_288,plain,
% 3.23/1.00      ( v4_pre_topc(X0,sK0)
% 3.23/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.23/1.00      | k2_pre_topc(sK0,X0) != X0 ),
% 3.23/1.00      inference(renaming,[status(thm)],[c_287]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1462,plain,
% 3.23/1.00      ( v4_pre_topc(sK2,sK0)
% 3.23/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.23/1.00      | k2_pre_topc(sK0,sK2) != sK2 ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_288]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1463,plain,
% 3.23/1.00      ( k2_pre_topc(sK0,sK2) != sK2
% 3.23/1.00      | v4_pre_topc(sK2,sK0) = iProver_top
% 3.23/1.00      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_1462]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_2,plain,
% 3.23/1.00      ( r1_tarski(X0,X0) ),
% 3.23/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_3128,plain,
% 3.23/1.00      ( r1_tarski(sK2,sK2) ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_3131,plain,
% 3.23/1.00      ( r1_tarski(sK2,sK2) = iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_3128]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_12,plain,
% 3.23/1.00      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
% 3.23/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.23/1.00      | ~ v2_pre_topc(X0)
% 3.23/1.00      | ~ l1_pre_topc(X0) ),
% 3.23/1.00      inference(cnf_transformation,[],[f46]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_264,plain,
% 3.23/1.00      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
% 3.23/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.23/1.00      | ~ l1_pre_topc(X0)
% 3.23/1.00      | sK0 != X0 ),
% 3.23/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_24]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_265,plain,
% 3.23/1.00      ( v4_pre_topc(k2_pre_topc(sK0,X0),sK0)
% 3.23/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.23/1.00      | ~ l1_pre_topc(sK0) ),
% 3.23/1.00      inference(unflattening,[status(thm)],[c_264]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_269,plain,
% 3.23/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.23/1.00      | v4_pre_topc(k2_pre_topc(sK0,X0),sK0) ),
% 3.23/1.00      inference(global_propositional_subsumption,
% 3.23/1.00                [status(thm)],
% 3.23/1.00                [c_265,c_23]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_270,plain,
% 3.23/1.00      ( v4_pre_topc(k2_pre_topc(sK0,X0),sK0)
% 3.23/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.23/1.00      inference(renaming,[status(thm)],[c_269]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1203,plain,
% 3.23/1.00      ( v4_pre_topc(k2_pre_topc(sK0,X0),sK0) = iProver_top
% 3.23/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_270]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1879,plain,
% 3.23/1.00      ( v4_pre_topc(k2_pre_topc(sK0,k1_tops_1(sK0,X0)),sK0) = iProver_top
% 3.23/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.23/1.00      inference(superposition,[status(thm)],[c_1191,c_1203]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_3282,plain,
% 3.23/1.00      ( k2_pre_topc(sK1,sK3) = sK3
% 3.23/1.00      | v4_pre_topc(sK2,sK0) = iProver_top
% 3.23/1.00      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.23/1.00      inference(superposition,[status(thm)],[c_2637,c_1879]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_5006,plain,
% 3.23/1.00      ( v4_pre_topc(sK2,sK0) = iProver_top | k2_pre_topc(sK1,sK3) = sK3 ),
% 3.23/1.00      inference(global_propositional_subsumption,
% 3.23/1.00                [status(thm)],
% 3.23/1.00                [c_3282,c_28]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_5007,plain,
% 3.23/1.00      ( k2_pre_topc(sK1,sK3) = sK3 | v4_pre_topc(sK2,sK0) = iProver_top ),
% 3.23/1.00      inference(renaming,[status(thm)],[c_5006]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_559,plain,
% 3.23/1.00      ( ~ v4_pre_topc(X0,X1)
% 3.23/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.23/1.00      | k2_pre_topc(X1,X0) = X0
% 3.23/1.00      | sK0 != X1 ),
% 3.23/1.00      inference(resolution_lifted,[status(thm)],[c_5,c_23]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_560,plain,
% 3.23/1.00      ( ~ v4_pre_topc(X0,sK0)
% 3.23/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.23/1.00      | k2_pre_topc(sK0,X0) = X0 ),
% 3.23/1.00      inference(unflattening,[status(thm)],[c_559]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1185,plain,
% 3.23/1.00      ( k2_pre_topc(sK0,X0) = X0
% 3.23/1.00      | v4_pre_topc(X0,sK0) != iProver_top
% 3.23/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_560]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1990,plain,
% 3.23/1.00      ( k2_pre_topc(sK0,sK2) = sK2
% 3.23/1.00      | v4_pre_topc(sK2,sK0) != iProver_top ),
% 3.23/1.00      inference(superposition,[status(thm)],[c_1204,c_1185]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_5012,plain,
% 3.23/1.00      ( k2_pre_topc(sK1,sK3) = sK3 | k2_pre_topc(sK0,sK2) = sK2 ),
% 3.23/1.00      inference(superposition,[status(thm)],[c_5007,c_1990]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_8,plain,
% 3.23/1.00      ( ~ v4_tops_1(X0,X1)
% 3.23/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.23/1.00      | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
% 3.23/1.00      | ~ l1_pre_topc(X1) ),
% 3.23/1.00      inference(cnf_transformation,[],[f40]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_373,plain,
% 3.23/1.00      ( ~ v4_tops_1(X0,X1)
% 3.23/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.23/1.00      | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
% 3.23/1.00      | sK1 != X1 ),
% 3.23/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_22]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_374,plain,
% 3.23/1.00      ( ~ v4_tops_1(X0,sK1)
% 3.23/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.23/1.00      | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,X0)),X0) ),
% 3.23/1.00      inference(unflattening,[status(thm)],[c_373]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1197,plain,
% 3.23/1.00      ( v4_tops_1(X0,sK1) != iProver_top
% 3.23/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.23/1.00      | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,X0)),X0) = iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_374]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_5096,plain,
% 3.23/1.00      ( k2_pre_topc(sK0,sK2) = sK2
% 3.23/1.00      | v4_tops_1(sK3,sK1) != iProver_top
% 3.23/1.00      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.23/1.00      | r1_tarski(k1_tops_1(sK1,sK3),sK3) = iProver_top ),
% 3.23/1.00      inference(superposition,[status(thm)],[c_5012,c_1197]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_29,plain,
% 3.23/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_5387,plain,
% 3.23/1.00      ( v4_tops_1(sK3,sK1) != iProver_top
% 3.23/1.00      | k2_pre_topc(sK0,sK2) = sK2
% 3.23/1.00      | r1_tarski(k1_tops_1(sK1,sK3),sK3) = iProver_top ),
% 3.23/1.00      inference(global_propositional_subsumption,
% 3.23/1.00                [status(thm)],
% 3.23/1.00                [c_5096,c_29]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_5388,plain,
% 3.23/1.00      ( k2_pre_topc(sK0,sK2) = sK2
% 3.23/1.00      | v4_tops_1(sK3,sK1) != iProver_top
% 3.23/1.00      | r1_tarski(k1_tops_1(sK1,sK3),sK3) = iProver_top ),
% 3.23/1.00      inference(renaming,[status(thm)],[c_5387]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_331,plain,
% 3.23/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.23/1.00      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.23/1.00      | sK1 != X1 ),
% 3.23/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_22]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_332,plain,
% 3.23/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.23/1.00      | m1_subset_1(k1_tops_1(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 3.23/1.00      inference(unflattening,[status(thm)],[c_331]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1200,plain,
% 3.23/1.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.23/1.00      | m1_subset_1(k1_tops_1(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_332]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_13,plain,
% 3.23/1.00      ( ~ v4_pre_topc(X0,X1)
% 3.23/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.23/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.23/1.00      | ~ r1_tarski(X2,X0)
% 3.23/1.00      | r1_tarski(k2_pre_topc(X1,X2),X0)
% 3.23/1.00      | ~ l1_pre_topc(X1) ),
% 3.23/1.00      inference(cnf_transformation,[],[f47]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_310,plain,
% 3.23/1.00      ( ~ v4_pre_topc(X0,X1)
% 3.23/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.23/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.23/1.00      | ~ r1_tarski(X2,X0)
% 3.23/1.00      | r1_tarski(k2_pre_topc(X1,X2),X0)
% 3.23/1.00      | sK1 != X1 ),
% 3.23/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_22]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_311,plain,
% 3.23/1.00      ( ~ v4_pre_topc(X0,sK1)
% 3.23/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.23/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.23/1.00      | ~ r1_tarski(X1,X0)
% 3.23/1.00      | r1_tarski(k2_pre_topc(sK1,X1),X0) ),
% 3.23/1.00      inference(unflattening,[status(thm)],[c_310]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1201,plain,
% 3.23/1.00      ( v4_pre_topc(X0,sK1) != iProver_top
% 3.23/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.23/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.23/1.00      | r1_tarski(X1,X0) != iProver_top
% 3.23/1.00      | r1_tarski(k2_pre_topc(sK1,X1),X0) = iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_311]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_3004,plain,
% 3.23/1.00      ( v4_pre_topc(X0,sK1) != iProver_top
% 3.23/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.23/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.23/1.00      | r1_tarski(k1_tops_1(sK1,X1),X0) != iProver_top
% 3.23/1.00      | r1_tarski(k2_pre_topc(sK1,k1_tops_1(sK1,X1)),X0) = iProver_top ),
% 3.23/1.00      inference(superposition,[status(thm)],[c_1200,c_1201]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_7,plain,
% 3.23/1.00      ( ~ v4_tops_1(X0,X1)
% 3.23/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.23/1.00      | r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
% 3.23/1.00      | ~ l1_pre_topc(X1) ),
% 3.23/1.00      inference(cnf_transformation,[],[f41]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_388,plain,
% 3.23/1.00      ( ~ v4_tops_1(X0,X1)
% 3.23/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.23/1.00      | r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
% 3.23/1.00      | sK1 != X1 ),
% 3.23/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_22]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_389,plain,
% 3.23/1.00      ( ~ v4_tops_1(X0,sK1)
% 3.23/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.23/1.00      | r1_tarski(X0,k2_pre_topc(sK1,k1_tops_1(sK1,X0))) ),
% 3.23/1.00      inference(unflattening,[status(thm)],[c_388]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1196,plain,
% 3.23/1.00      ( v4_tops_1(X0,sK1) != iProver_top
% 3.23/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.23/1.00      | r1_tarski(X0,k2_pre_topc(sK1,k1_tops_1(sK1,X0))) = iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_389]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_0,plain,
% 3.23/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.23/1.00      inference(cnf_transformation,[],[f36]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1213,plain,
% 3.23/1.00      ( X0 = X1
% 3.23/1.00      | r1_tarski(X0,X1) != iProver_top
% 3.23/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_2756,plain,
% 3.23/1.00      ( k2_pre_topc(sK1,k1_tops_1(sK1,X0)) = X0
% 3.23/1.00      | v4_tops_1(X0,sK1) != iProver_top
% 3.23/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.23/1.00      | r1_tarski(k2_pre_topc(sK1,k1_tops_1(sK1,X0)),X0) != iProver_top ),
% 3.23/1.00      inference(superposition,[status(thm)],[c_1196,c_1213]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_4096,plain,
% 3.23/1.00      ( k2_pre_topc(sK1,k1_tops_1(sK1,X0)) = X0
% 3.23/1.00      | v4_tops_1(X0,sK1) != iProver_top
% 3.23/1.00      | v4_pre_topc(X0,sK1) != iProver_top
% 3.23/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.23/1.00      | r1_tarski(k1_tops_1(sK1,X0),X0) != iProver_top ),
% 3.23/1.00      inference(superposition,[status(thm)],[c_3004,c_2756]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_4359,plain,
% 3.23/1.00      ( k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) = sK3
% 3.23/1.00      | v4_tops_1(sK3,sK1) != iProver_top
% 3.23/1.00      | v4_pre_topc(sK3,sK1) != iProver_top
% 3.23/1.00      | r1_tarski(k1_tops_1(sK1,sK3),sK3) != iProver_top ),
% 3.23/1.00      inference(superposition,[status(thm)],[c_1205,c_4096]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_5395,plain,
% 3.23/1.00      ( k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) = sK3
% 3.23/1.00      | k2_pre_topc(sK0,sK2) = sK2
% 3.23/1.00      | v4_tops_1(sK3,sK1) != iProver_top
% 3.23/1.00      | v4_pre_topc(sK3,sK1) != iProver_top ),
% 3.23/1.00      inference(superposition,[status(thm)],[c_5388,c_4359]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_5419,plain,
% 3.23/1.00      ( k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) = sK3
% 3.23/1.00      | k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = sK2
% 3.23/1.00      | k2_pre_topc(sK0,sK2) = sK2
% 3.23/1.00      | v4_pre_topc(sK3,sK1) != iProver_top ),
% 3.23/1.00      inference(superposition,[status(thm)],[c_2339,c_5395]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_17,negated_conjecture,
% 3.23/1.00      ( ~ v5_tops_1(sK3,sK1) | v5_tops_1(sK2,sK0) ),
% 3.23/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_32,plain,
% 3.23/1.00      ( v5_tops_1(sK3,sK1) != iProver_top
% 3.23/1.00      | v5_tops_1(sK2,sK0) = iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_9,plain,
% 3.23/1.00      ( v5_tops_1(X0,X1)
% 3.23/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.23/1.00      | ~ l1_pre_topc(X1)
% 3.23/1.00      | k2_pre_topc(X1,k1_tops_1(X1,X0)) != X0 ),
% 3.23/1.00      inference(cnf_transformation,[],[f44]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_358,plain,
% 3.23/1.00      ( v5_tops_1(X0,X1)
% 3.23/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.23/1.00      | k2_pre_topc(X1,k1_tops_1(X1,X0)) != X0
% 3.23/1.00      | sK1 != X1 ),
% 3.23/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_22]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_359,plain,
% 3.23/1.00      ( v5_tops_1(X0,sK1)
% 3.23/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.23/1.00      | k2_pre_topc(sK1,k1_tops_1(sK1,X0)) != X0 ),
% 3.23/1.00      inference(unflattening,[status(thm)],[c_358]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1465,plain,
% 3.23/1.00      ( v5_tops_1(sK3,sK1)
% 3.23/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.23/1.00      | k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) != sK3 ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_359]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1466,plain,
% 3.23/1.00      ( k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) != sK3
% 3.23/1.00      | v5_tops_1(sK3,sK1) = iProver_top
% 3.23/1.00      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_1465]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_5518,plain,
% 3.23/1.00      ( k2_pre_topc(sK0,sK2) = sK2
% 3.23/1.00      | k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = sK2 ),
% 3.23/1.00      inference(global_propositional_subsumption,
% 3.23/1.00                [status(thm)],
% 3.23/1.00                [c_5419,c_29,c_32,c_1466,c_2291,c_2339,c_2340,c_4359,
% 3.23/1.00                 c_5096]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_5519,plain,
% 3.23/1.00      ( k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = sK2
% 3.23/1.00      | k2_pre_topc(sK0,sK2) = sK2 ),
% 3.23/1.00      inference(renaming,[status(thm)],[c_5518]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_496,plain,
% 3.23/1.00      ( v5_tops_1(X0,X1)
% 3.23/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.23/1.00      | k2_pre_topc(X1,k1_tops_1(X1,X0)) != X0
% 3.23/1.00      | sK0 != X1 ),
% 3.23/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_23]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_497,plain,
% 3.23/1.00      ( v5_tops_1(X0,sK0)
% 3.23/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.23/1.00      | k2_pre_topc(sK0,k1_tops_1(sK0,X0)) != X0 ),
% 3.23/1.00      inference(unflattening,[status(thm)],[c_496]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1189,plain,
% 3.23/1.00      ( k2_pre_topc(sK0,k1_tops_1(sK0,X0)) != X0
% 3.23/1.00      | v5_tops_1(X0,sK0) = iProver_top
% 3.23/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_497]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_5536,plain,
% 3.23/1.00      ( k2_pre_topc(sK0,sK2) = sK2
% 3.23/1.00      | v5_tops_1(sK2,sK0) = iProver_top
% 3.23/1.00      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.23/1.00      inference(superposition,[status(thm)],[c_5519,c_1189]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_2002,plain,
% 3.23/1.00      ( ~ v4_pre_topc(sK2,sK0) | k2_pre_topc(sK0,sK2) = sK2 ),
% 3.23/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_1990]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_5533,plain,
% 3.23/1.00      ( k2_pre_topc(sK0,sK2) = sK2
% 3.23/1.00      | v4_pre_topc(sK2,sK0) = iProver_top
% 3.23/1.00      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.23/1.00      inference(superposition,[status(thm)],[c_5519,c_1879]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_5653,plain,
% 3.23/1.00      ( v4_pre_topc(sK2,sK0)
% 3.23/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.23/1.00      | k2_pre_topc(sK0,sK2) = sK2 ),
% 3.23/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_5533]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_5656,plain,
% 3.23/1.00      ( k2_pre_topc(sK0,sK2) = sK2 ),
% 3.23/1.00      inference(global_propositional_subsumption,
% 3.23/1.00                [status(thm)],
% 3.23/1.00                [c_5536,c_21,c_2002,c_5653]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_6,plain,
% 3.23/1.00      ( v4_tops_1(X0,X1)
% 3.23/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.23/1.00      | ~ r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
% 3.23/1.00      | ~ r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
% 3.23/1.00      | ~ l1_pre_topc(X1) ),
% 3.23/1.00      inference(cnf_transformation,[],[f42]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_541,plain,
% 3.23/1.00      ( v4_tops_1(X0,X1)
% 3.23/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.23/1.00      | ~ r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
% 3.23/1.00      | ~ r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
% 3.23/1.00      | sK0 != X1 ),
% 3.23/1.00      inference(resolution_lifted,[status(thm)],[c_6,c_23]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_542,plain,
% 3.23/1.00      ( v4_tops_1(X0,sK0)
% 3.23/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.23/1.00      | ~ r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,X0)))
% 3.23/1.00      | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X0) ),
% 3.23/1.00      inference(unflattening,[status(thm)],[c_541]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1186,plain,
% 3.23/1.00      ( v4_tops_1(X0,sK0) = iProver_top
% 3.23/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.23/1.00      | r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,X0))) != iProver_top
% 3.23/1.00      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X0) != iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_542]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_5678,plain,
% 3.23/1.00      ( v4_tops_1(sK2,sK0) = iProver_top
% 3.23/1.00      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.23/1.00      | r1_tarski(k1_tops_1(sK0,sK2),sK2) != iProver_top
% 3.23/1.00      | r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) != iProver_top ),
% 3.23/1.00      inference(superposition,[status(thm)],[c_5656,c_1186]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_6042,plain,
% 3.23/1.00      ( v4_tops_1(sK2,sK0) = iProver_top
% 3.23/1.00      | r1_tarski(k1_tops_1(sK0,sK2),sK2) != iProver_top
% 3.23/1.00      | r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) != iProver_top ),
% 3.23/1.00      inference(global_propositional_subsumption,
% 3.23/1.00                [status(thm)],
% 3.23/1.00                [c_5678,c_28]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_6051,plain,
% 3.23/1.00      ( k2_pre_topc(sK1,sK3) = sK3
% 3.23/1.00      | v4_tops_1(sK2,sK0) = iProver_top
% 3.23/1.00      | r1_tarski(k1_tops_1(sK0,sK2),sK2) != iProver_top
% 3.23/1.00      | r1_tarski(sK2,sK2) != iProver_top ),
% 3.23/1.00      inference(superposition,[status(thm)],[c_2637,c_6042]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_6065,plain,
% 3.23/1.00      ( k2_pre_topc(sK1,sK3) = sK3 ),
% 3.23/1.00      inference(global_propositional_subsumption,
% 3.23/1.00                [status(thm)],
% 3.23/1.00                [c_3342,c_21,c_28,c_33,c_1463,c_2002,c_2154,c_3131,
% 3.23/1.00                 c_5653,c_6051]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_6099,plain,
% 3.23/1.00      ( v4_tops_1(sK3,sK1) != iProver_top
% 3.23/1.00      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.23/1.00      | r1_tarski(k1_tops_1(sK1,sK3),sK3) = iProver_top ),
% 3.23/1.00      inference(superposition,[status(thm)],[c_6065,c_1197]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_6187,plain,
% 3.23/1.00      ( v4_tops_1(sK3,sK1) != iProver_top
% 3.23/1.00      | r1_tarski(k1_tops_1(sK1,sK3),sK3) = iProver_top ),
% 3.23/1.00      inference(global_propositional_subsumption,
% 3.23/1.00                [status(thm)],
% 3.23/1.00                [c_6099,c_29]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_6194,plain,
% 3.23/1.00      ( k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) = sK3
% 3.23/1.00      | v4_tops_1(sK3,sK1) != iProver_top
% 3.23/1.00      | v4_pre_topc(sK3,sK1) != iProver_top ),
% 3.23/1.00      inference(superposition,[status(thm)],[c_6187,c_4359]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_6279,plain,
% 3.23/1.00      ( k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) = sK3
% 3.23/1.00      | k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = sK2
% 3.23/1.00      | v4_pre_topc(sK3,sK1) != iProver_top ),
% 3.23/1.00      inference(superposition,[status(thm)],[c_2339,c_6194]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_6346,plain,
% 3.23/1.00      ( k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = sK2 ),
% 3.23/1.00      inference(global_propositional_subsumption,
% 3.23/1.00                [status(thm)],
% 3.23/1.00                [c_6279,c_29,c_32,c_1466,c_2291,c_2339,c_2340,c_4359,
% 3.23/1.00                 c_6099]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_6361,plain,
% 3.23/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.23/1.00      | r1_tarski(k1_tops_1(sK0,sK2),sK2) = iProver_top ),
% 3.23/1.00      inference(superposition,[status(thm)],[c_6346,c_1880]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_6349,plain,
% 3.23/1.00      ( v4_tops_1(sK2,sK0) = iProver_top
% 3.23/1.00      | r1_tarski(k1_tops_1(sK0,sK2),sK2) != iProver_top
% 3.23/1.00      | r1_tarski(sK2,sK2) != iProver_top ),
% 3.23/1.00      inference(demodulation,[status(thm)],[c_6346,c_6042]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_511,plain,
% 3.23/1.00      ( ~ v4_tops_1(X0,X1)
% 3.23/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.23/1.00      | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
% 3.23/1.00      | sK0 != X1 ),
% 3.23/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_23]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_512,plain,
% 3.23/1.00      ( ~ v4_tops_1(X0,sK0)
% 3.23/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.23/1.00      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X0) ),
% 3.23/1.00      inference(unflattening,[status(thm)],[c_511]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1188,plain,
% 3.23/1.00      ( v4_tops_1(X0,sK0) != iProver_top
% 3.23/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.23/1.00      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X0) = iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_512]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_5676,plain,
% 3.23/1.00      ( v4_tops_1(sK2,sK0) != iProver_top
% 3.23/1.00      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.23/1.00      | r1_tarski(k1_tops_1(sK0,sK2),sK2) = iProver_top ),
% 3.23/1.00      inference(superposition,[status(thm)],[c_5656,c_1188]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_5830,plain,
% 3.23/1.00      ( v4_tops_1(sK2,sK0) != iProver_top
% 3.23/1.00      | r1_tarski(k1_tops_1(sK0,sK2),sK2) = iProver_top ),
% 3.23/1.00      inference(global_propositional_subsumption,
% 3.23/1.00                [status(thm)],
% 3.23/1.00                [c_5676,c_28]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_5836,plain,
% 3.23/1.00      ( k1_tops_1(sK0,sK2) = sK2
% 3.23/1.00      | v4_tops_1(sK2,sK0) != iProver_top
% 3.23/1.00      | r1_tarski(sK2,k1_tops_1(sK0,sK2)) != iProver_top ),
% 3.23/1.00      inference(superposition,[status(thm)],[c_5830,c_1213]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_15,negated_conjecture,
% 3.23/1.00      ( v4_tops_1(sK3,sK1)
% 3.23/1.00      | ~ v4_tops_1(sK2,sK0)
% 3.23/1.00      | ~ v4_pre_topc(sK2,sK0) ),
% 3.23/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_34,plain,
% 3.23/1.00      ( v4_tops_1(sK3,sK1) = iProver_top
% 3.23/1.00      | v4_tops_1(sK2,sK0) != iProver_top
% 3.23/1.00      | v4_pre_topc(sK2,sK0) != iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_14,negated_conjecture,
% 3.23/1.00      ( ~ v5_tops_1(sK3,sK1)
% 3.23/1.00      | ~ v4_tops_1(sK2,sK0)
% 3.23/1.00      | ~ v4_pre_topc(sK2,sK0) ),
% 3.23/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_35,plain,
% 3.23/1.00      ( v5_tops_1(sK3,sK1) != iProver_top
% 3.23/1.00      | v4_tops_1(sK2,sK0) != iProver_top
% 3.23/1.00      | v4_pre_topc(sK2,sK0) != iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_6172,plain,
% 3.23/1.00      ( v4_tops_1(sK2,sK0) != iProver_top ),
% 3.23/1.00      inference(global_propositional_subsumption,
% 3.23/1.00                [status(thm)],
% 3.23/1.00                [c_5836,c_21,c_28,c_29,c_33,c_34,c_35,c_1463,c_1466,
% 3.23/1.00                 c_2002,c_4359,c_5653,c_6099]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(contradiction,plain,
% 3.23/1.00      ( $false ),
% 3.23/1.00      inference(minisat,[status(thm)],[c_6361,c_6349,c_6172,c_3131,c_28]) ).
% 3.23/1.00  
% 3.23/1.00  
% 3.23/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.23/1.00  
% 3.23/1.00  ------                               Statistics
% 3.23/1.00  
% 3.23/1.00  ------ General
% 3.23/1.00  
% 3.23/1.00  abstr_ref_over_cycles:                  0
% 3.23/1.00  abstr_ref_under_cycles:                 0
% 3.23/1.00  gc_basic_clause_elim:                   0
% 3.23/1.00  forced_gc_time:                         0
% 3.23/1.00  parsing_time:                           0.012
% 3.23/1.00  unif_index_cands_time:                  0.
% 3.23/1.00  unif_index_add_time:                    0.
% 3.23/1.00  orderings_time:                         0.
% 3.23/1.00  out_proof_time:                         0.012
% 3.23/1.00  total_time:                             0.213
% 3.23/1.00  num_of_symbols:                         46
% 3.23/1.00  num_of_terms:                           4325
% 3.23/1.00  
% 3.23/1.00  ------ Preprocessing
% 3.23/1.00  
% 3.23/1.00  num_of_splits:                          0
% 3.23/1.00  num_of_split_atoms:                     0
% 3.23/1.00  num_of_reused_defs:                     0
% 3.23/1.00  num_eq_ax_congr_red:                    2
% 3.23/1.00  num_of_sem_filtered_clauses:            1
% 3.23/1.00  num_of_subtypes:                        0
% 3.23/1.00  monotx_restored_types:                  0
% 3.23/1.00  sat_num_of_epr_types:                   0
% 3.23/1.00  sat_num_of_non_cyclic_types:            0
% 3.23/1.00  sat_guarded_non_collapsed_types:        0
% 3.23/1.00  num_pure_diseq_elim:                    0
% 3.23/1.00  simp_replaced_by:                       0
% 3.23/1.00  res_preprocessed:                       107
% 3.23/1.00  prep_upred:                             0
% 3.23/1.00  prep_unflattend:                        20
% 3.23/1.00  smt_new_axioms:                         0
% 3.23/1.00  pred_elim_cands:                        7
% 3.23/1.00  pred_elim:                              2
% 3.23/1.00  pred_elim_cl:                           -6
% 3.23/1.00  pred_elim_cycles:                       3
% 3.23/1.00  merged_defs:                            0
% 3.23/1.00  merged_defs_ncl:                        0
% 3.23/1.00  bin_hyper_res:                          0
% 3.23/1.00  prep_cycles:                            3
% 3.23/1.00  pred_elim_time:                         0.007
% 3.23/1.00  splitting_time:                         0.
% 3.23/1.00  sem_filter_time:                        0.
% 3.23/1.00  monotx_time:                            0.
% 3.23/1.00  subtype_inf_time:                       0.
% 3.23/1.00  
% 3.23/1.00  ------ Problem properties
% 3.23/1.00  
% 3.23/1.00  clauses:                                30
% 3.23/1.00  conjectures:                            8
% 3.23/1.00  epr:                                    8
% 3.23/1.00  horn:                                   28
% 3.23/1.00  ground:                                 8
% 3.23/1.00  unary:                                  3
% 3.23/1.00  binary:                                 8
% 3.23/1.00  lits:                                   82
% 3.23/1.00  lits_eq:                                8
% 3.23/1.00  fd_pure:                                0
% 3.23/1.00  fd_pseudo:                              0
% 3.23/1.00  fd_cond:                                0
% 3.23/1.00  fd_pseudo_cond:                         1
% 3.23/1.00  ac_symbols:                             0
% 3.23/1.00  
% 3.23/1.00  ------ Propositional Solver
% 3.23/1.00  
% 3.23/1.00  prop_solver_calls:                      25
% 3.23/1.00  prop_fast_solver_calls:                 1109
% 3.23/1.00  smt_solver_calls:                       0
% 3.23/1.00  smt_fast_solver_calls:                  0
% 3.23/1.00  prop_num_of_clauses:                    2302
% 3.23/1.00  prop_preprocess_simplified:             6186
% 3.23/1.00  prop_fo_subsumed:                       44
% 3.23/1.00  prop_solver_time:                       0.
% 3.23/1.00  smt_solver_time:                        0.
% 3.23/1.00  smt_fast_solver_time:                   0.
% 3.23/1.00  prop_fast_solver_time:                  0.
% 3.23/1.00  prop_unsat_core_time:                   0.
% 3.23/1.00  
% 3.23/1.00  ------ QBF
% 3.23/1.00  
% 3.23/1.00  qbf_q_res:                              0
% 3.23/1.00  qbf_num_tautologies:                    0
% 3.23/1.00  qbf_prep_cycles:                        0
% 3.23/1.00  
% 3.23/1.00  ------ BMC1
% 3.23/1.00  
% 3.23/1.00  bmc1_current_bound:                     -1
% 3.23/1.00  bmc1_last_solved_bound:                 -1
% 3.23/1.01  bmc1_unsat_core_size:                   -1
% 3.23/1.01  bmc1_unsat_core_parents_size:           -1
% 3.23/1.01  bmc1_merge_next_fun:                    0
% 3.23/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.23/1.01  
% 3.23/1.01  ------ Instantiation
% 3.23/1.01  
% 3.23/1.01  inst_num_of_clauses:                    742
% 3.23/1.01  inst_num_in_passive:                    230
% 3.23/1.01  inst_num_in_active:                     465
% 3.23/1.01  inst_num_in_unprocessed:                47
% 3.23/1.01  inst_num_of_loops:                      510
% 3.23/1.01  inst_num_of_learning_restarts:          0
% 3.23/1.01  inst_num_moves_active_passive:          41
% 3.23/1.01  inst_lit_activity:                      0
% 3.23/1.01  inst_lit_activity_moves:                0
% 3.23/1.01  inst_num_tautologies:                   0
% 3.23/1.01  inst_num_prop_implied:                  0
% 3.23/1.01  inst_num_existing_simplified:           0
% 3.23/1.01  inst_num_eq_res_simplified:             0
% 3.23/1.01  inst_num_child_elim:                    0
% 3.23/1.01  inst_num_of_dismatching_blockings:      59
% 3.23/1.01  inst_num_of_non_proper_insts:           769
% 3.23/1.01  inst_num_of_duplicates:                 0
% 3.23/1.01  inst_inst_num_from_inst_to_res:         0
% 3.23/1.01  inst_dismatching_checking_time:         0.
% 3.23/1.01  
% 3.23/1.01  ------ Resolution
% 3.23/1.01  
% 3.23/1.01  res_num_of_clauses:                     0
% 3.23/1.01  res_num_in_passive:                     0
% 3.23/1.01  res_num_in_active:                      0
% 3.23/1.01  res_num_of_loops:                       110
% 3.23/1.01  res_forward_subset_subsumed:            72
% 3.23/1.01  res_backward_subset_subsumed:           2
% 3.23/1.01  res_forward_subsumed:                   0
% 3.23/1.01  res_backward_subsumed:                  0
% 3.23/1.01  res_forward_subsumption_resolution:     0
% 3.23/1.01  res_backward_subsumption_resolution:    0
% 3.23/1.01  res_clause_to_clause_subsumption:       825
% 3.23/1.01  res_orphan_elimination:                 0
% 3.23/1.01  res_tautology_del:                      99
% 3.23/1.01  res_num_eq_res_simplified:              0
% 3.23/1.01  res_num_sel_changes:                    0
% 3.23/1.01  res_moves_from_active_to_pass:          0
% 3.23/1.01  
% 3.23/1.01  ------ Superposition
% 3.23/1.01  
% 3.23/1.01  sup_time_total:                         0.
% 3.23/1.01  sup_time_generating:                    0.
% 3.23/1.01  sup_time_sim_full:                      0.
% 3.23/1.01  sup_time_sim_immed:                     0.
% 3.23/1.01  
% 3.23/1.01  sup_num_of_clauses:                     84
% 3.23/1.01  sup_num_in_active:                      66
% 3.23/1.01  sup_num_in_passive:                     18
% 3.23/1.01  sup_num_of_loops:                       100
% 3.23/1.01  sup_fw_superposition:                   54
% 3.23/1.01  sup_bw_superposition:                   94
% 3.23/1.01  sup_immediate_simplified:               37
% 3.23/1.01  sup_given_eliminated:                   0
% 3.23/1.01  comparisons_done:                       0
% 3.23/1.01  comparisons_avoided:                    24
% 3.23/1.01  
% 3.23/1.01  ------ Simplifications
% 3.23/1.01  
% 3.23/1.01  
% 3.23/1.01  sim_fw_subset_subsumed:                 15
% 3.23/1.01  sim_bw_subset_subsumed:                 29
% 3.23/1.01  sim_fw_subsumed:                        17
% 3.23/1.01  sim_bw_subsumed:                        0
% 3.23/1.01  sim_fw_subsumption_res:                 3
% 3.23/1.01  sim_bw_subsumption_res:                 0
% 3.23/1.01  sim_tautology_del:                      9
% 3.23/1.01  sim_eq_tautology_del:                   8
% 3.23/1.01  sim_eq_res_simp:                        0
% 3.23/1.01  sim_fw_demodulated:                     0
% 3.23/1.01  sim_bw_demodulated:                     15
% 3.23/1.01  sim_light_normalised:                   9
% 3.23/1.01  sim_joinable_taut:                      0
% 3.23/1.01  sim_joinable_simp:                      0
% 3.23/1.01  sim_ac_normalised:                      0
% 3.23/1.01  sim_smt_subsumption:                    0
% 3.23/1.01  
%------------------------------------------------------------------------------
