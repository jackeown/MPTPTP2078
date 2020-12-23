%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:15:52 EST 2020

% Result     : Theorem 3.84s
% Output     : CNFRefutation 3.84s
% Verified   : 
% Statistics : Number of formulae       :  220 (15131 expanded)
%              Number of clauses        :  162 (4131 expanded)
%              Number of leaves         :   13 (5017 expanded)
%              Depth                    :   43
%              Number of atoms          :  797 (133320 expanded)
%              Number of equality atoms :  320 (6595 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
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
    inference(nnf_transformation,[],[f16])).

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

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f3])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f50,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

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
    inference(cnf_transformation,[],[f14])).

fof(f48,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f36,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_tops_1(X1,X0)
          <=> ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
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
    inference(nnf_transformation,[],[f15])).

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

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
      | ~ v4_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

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

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f60,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f34])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v4_tops_1(X1,X0)
      | ~ r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
      | ~ r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)
      | ~ v4_tops_1(X1,X0)
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

cnf(c_1199,plain,
    ( v5_tops_1(sK2,sK0) = iProver_top
    | v4_tops_1(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1196,plain,
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

cnf(c_469,plain,
    ( ~ v5_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,k1_tops_1(X1,X0)) = X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_23])).

cnf(c_470,plain,
    ( ~ v5_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k1_tops_1(sK0,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_469])).

cnf(c_1182,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,X0)) = X0
    | v5_tops_1(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_470])).

cnf(c_2380,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = sK2
    | v5_tops_1(sK2,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1196,c_1182])).

cnf(c_2454,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = sK2
    | v4_tops_1(sK3,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1199,c_2380])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_457,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_23])).

cnf(c_458,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_457])).

cnf(c_1183,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_458])).

cnf(c_19,negated_conjecture,
    ( v5_tops_1(sK2,sK0)
    | v4_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1198,plain,
    ( v5_tops_1(sK2,sK0) = iProver_top
    | v4_pre_topc(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2455,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = sK2
    | v4_pre_topc(sK3,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1198,c_2380])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1197,plain,
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

cnf(c_412,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,X0) = X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_22])).

cnf(c_413,plain,
    ( ~ v4_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_412])).

cnf(c_1186,plain,
    ( k2_pre_topc(sK1,X0) = X0
    | v4_pre_topc(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_413])).

cnf(c_2249,plain,
    ( k2_pre_topc(sK1,sK3) = sK3
    | v4_pre_topc(sK3,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1197,c_1186])).

cnf(c_2763,plain,
    ( k2_pre_topc(sK1,sK3) = sK3
    | k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_2455,c_2249])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_562,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_23])).

cnf(c_563,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X1,X0)
    | r1_tarski(k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_562])).

cnf(c_1176,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_563])).

cnf(c_2805,plain,
    ( k2_pre_topc(sK1,sK3) = sK3
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k1_tops_1(sK0,sK2)) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,X0),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2763,c_1176])).

cnf(c_28,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1441,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_458])).

cnf(c_1442,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1441])).

cnf(c_6644,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | k2_pre_topc(sK1,sK3) = sK3
    | r1_tarski(X0,k1_tops_1(sK0,sK2)) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,X0),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2805,c_28,c_1442])).

cnf(c_6645,plain,
    ( k2_pre_topc(sK1,sK3) = sK3
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k1_tops_1(sK0,sK2)) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,X0),sK2) = iProver_top ),
    inference(renaming,[status(thm)],[c_6644])).

cnf(c_6655,plain,
    ( k2_pre_topc(sK1,sK3) = sK3
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK2)) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,X0)),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1183,c_6645])).

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

cnf(c_1450,plain,
    ( v4_pre_topc(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,sK2) != sK2 ),
    inference(instantiation,[status(thm)],[c_288])).

cnf(c_1451,plain,
    ( k2_pre_topc(sK0,sK2) != sK2
    | v4_pre_topc(sK2,sK0) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1450])).

cnf(c_322,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_22])).

cnf(c_323,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k1_tops_1(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_322])).

cnf(c_1192,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k1_tops_1(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_323])).

cnf(c_2801,plain,
    ( k2_pre_topc(sK1,sK3) = sK3
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK2),X0) != iProver_top
    | r1_tarski(sK2,k2_pre_topc(sK0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2763,c_1176])).

cnf(c_5238,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | k2_pre_topc(sK1,sK3) = sK3
    | r1_tarski(k1_tops_1(sK0,sK2),X0) != iProver_top
    | r1_tarski(sK2,k2_pre_topc(sK0,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2801,c_28,c_1442])).

cnf(c_5239,plain,
    ( k2_pre_topc(sK1,sK3) = sK3
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK2),X0) != iProver_top
    | r1_tarski(sK2,k2_pre_topc(sK0,X0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_5238])).

cnf(c_5248,plain,
    ( k2_pre_topc(sK1,sK3) = sK3
    | r1_tarski(k1_tops_1(sK0,sK2),sK2) != iProver_top
    | r1_tarski(sK2,k2_pre_topc(sK0,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1196,c_5239])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_445,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_23])).

cnf(c_446,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,X0),X0) ),
    inference(unflattening,[status(thm)],[c_445])).

cnf(c_1447,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    inference(instantiation,[status(thm)],[c_446])).

cnf(c_1448,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK2),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1447])).

cnf(c_5310,plain,
    ( k2_pre_topc(sK1,sK3) = sK3
    | r1_tarski(sK2,k2_pre_topc(sK0,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5248,c_28,c_1448])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1205,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_5316,plain,
    ( k2_pre_topc(sK1,sK3) = sK3
    | k2_pre_topc(sK0,sK2) = sK2
    | r1_tarski(k2_pre_topc(sK0,sK2),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5310,c_1205])).

cnf(c_547,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,X0) = X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_23])).

cnf(c_548,plain,
    ( ~ v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_547])).

cnf(c_1177,plain,
    ( k2_pre_topc(sK0,X0) = X0
    | v4_pre_topc(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_548])).

cnf(c_2075,plain,
    ( k2_pre_topc(sK0,sK2) = sK2
    | v4_pre_topc(sK2,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1196,c_1177])).

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

cnf(c_1195,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,X0),sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_270])).

cnf(c_1988,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,k1_tops_1(sK0,X0)),sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1183,c_1195])).

cnf(c_3148,plain,
    ( k2_pre_topc(sK1,sK3) = sK3
    | v4_pre_topc(sK2,sK0) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2763,c_1988])).

cnf(c_5319,plain,
    ( k2_pre_topc(sK0,sK2) = sK2
    | k2_pre_topc(sK1,sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5316,c_28,c_2075,c_3148])).

cnf(c_5320,plain,
    ( k2_pre_topc(sK1,sK3) = sK3
    | k2_pre_topc(sK0,sK2) = sK2 ),
    inference(renaming,[status(thm)],[c_5319])).

cnf(c_427,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X0))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_22])).

cnf(c_428,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X1,X0)
    | r1_tarski(k2_pre_topc(sK1,X1),k2_pre_topc(sK1,X0)) ),
    inference(unflattening,[status(thm)],[c_427])).

cnf(c_1185,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(k2_pre_topc(sK1,X1),k2_pre_topc(sK1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_428])).

cnf(c_5328,plain,
    ( k2_pre_topc(sK0,sK2) = sK2
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(k2_pre_topc(sK1,X0),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_5320,c_1185])).

cnf(c_29,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_6003,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | k2_pre_topc(sK0,sK2) = sK2
    | r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(k2_pre_topc(sK1,X0),sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5328,c_29])).

cnf(c_6004,plain,
    ( k2_pre_topc(sK0,sK2) = sK2
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(k2_pre_topc(sK1,X0),sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_6003])).

cnf(c_6014,plain,
    ( k2_pre_topc(sK0,sK2) = sK2
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(k1_tops_1(sK1,X0),sK3) != iProver_top
    | r1_tarski(k2_pre_topc(sK1,k1_tops_1(sK1,X0)),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1192,c_6004])).

cnf(c_7,plain,
    ( ~ v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_379,plain,
    ( ~ v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_22])).

cnf(c_380,plain,
    ( ~ v4_tops_1(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(X0,k2_pre_topc(sK1,k1_tops_1(sK1,X0))) ),
    inference(unflattening,[status(thm)],[c_379])).

cnf(c_1188,plain,
    ( v4_tops_1(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK1,k1_tops_1(sK1,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_380])).

cnf(c_3002,plain,
    ( k2_pre_topc(sK1,k1_tops_1(sK1,X0)) = X0
    | v4_tops_1(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(k2_pre_topc(sK1,k1_tops_1(sK1,X0)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1188,c_1205])).

cnf(c_6428,plain,
    ( k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) = sK3
    | k2_pre_topc(sK0,sK2) = sK2
    | v4_tops_1(sK3,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(k1_tops_1(sK1,sK3),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6014,c_3002])).

cnf(c_310,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_22])).

cnf(c_311,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(k1_tops_1(sK1,X0),X0) ),
    inference(unflattening,[status(thm)],[c_310])).

cnf(c_1444,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(k1_tops_1(sK1,sK3),sK3) ),
    inference(instantiation,[status(thm)],[c_311])).

cnf(c_1445,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(k1_tops_1(sK1,sK3),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1444])).

cnf(c_6887,plain,
    ( k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) = sK3
    | k2_pre_topc(sK0,sK2) = sK2
    | v4_tops_1(sK3,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6428,c_29,c_1445])).

cnf(c_6894,plain,
    ( k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) = sK3
    | k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = sK2
    | k2_pre_topc(sK0,sK2) = sK2 ),
    inference(superposition,[status(thm)],[c_2454,c_6887])).

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

cnf(c_349,plain,
    ( v5_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,k1_tops_1(X1,X0)) != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_22])).

cnf(c_350,plain,
    ( v5_tops_1(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,k1_tops_1(sK1,X0)) != X0 ),
    inference(unflattening,[status(thm)],[c_349])).

cnf(c_1453,plain,
    ( v5_tops_1(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) != sK3 ),
    inference(instantiation,[status(thm)],[c_350])).

cnf(c_1454,plain,
    ( k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) != sK3
    | v5_tops_1(sK3,sK1) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1453])).

cnf(c_6963,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = sK2
    | k2_pre_topc(sK0,sK2) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6894,c_29,c_32,c_1454,c_2380])).

cnf(c_484,plain,
    ( v5_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,k1_tops_1(X1,X0)) != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_23])).

cnf(c_485,plain,
    ( v5_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k1_tops_1(sK0,X0)) != X0 ),
    inference(unflattening,[status(thm)],[c_484])).

cnf(c_1181,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,X0)) != X0
    | v5_tops_1(X0,sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_485])).

cnf(c_6980,plain,
    ( k2_pre_topc(sK0,sK2) = sK2
    | v5_tops_1(sK2,sK0) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6963,c_1181])).

cnf(c_2087,plain,
    ( ~ v4_pre_topc(sK2,sK0)
    | k2_pre_topc(sK0,sK2) = sK2 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2075])).

cnf(c_6977,plain,
    ( k2_pre_topc(sK0,sK2) = sK2
    | v4_pre_topc(sK2,sK0) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6963,c_1988])).

cnf(c_7132,plain,
    ( v4_pre_topc(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,sK2) = sK2 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6977])).

cnf(c_7136,plain,
    ( k2_pre_topc(sK0,sK2) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6980,c_21,c_2087,c_7132])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1204,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_5249,plain,
    ( k2_pre_topc(sK1,sK3) = sK3
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,X0)) != iProver_top
    | r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1183,c_5239])).

cnf(c_5964,plain,
    ( k2_pre_topc(sK1,sK3) = sK3
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1204,c_5249])).

cnf(c_6121,plain,
    ( k2_pre_topc(sK1,sK3) = sK3
    | r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5964,c_28])).

cnf(c_6,plain,
    ( v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
    | ~ r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_529,plain,
    ( v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
    | ~ r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_23])).

cnf(c_530,plain,
    ( v4_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,X0)))
    | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X0) ),
    inference(unflattening,[status(thm)],[c_529])).

cnf(c_1178,plain,
    ( v4_tops_1(X0,sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,X0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_530])).

cnf(c_7204,plain,
    ( v4_tops_1(sK2,sK0) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK2),sK2) != iProver_top
    | r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7136,c_1178])).

cnf(c_7886,plain,
    ( v4_tops_1(sK2,sK0) = iProver_top
    | r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7204,c_28,c_1448])).

cnf(c_7893,plain,
    ( k2_pre_topc(sK1,sK3) = sK3
    | v4_tops_1(sK2,sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6121,c_7886])).

cnf(c_7919,plain,
    ( k2_pre_topc(sK1,sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6655,c_21,c_28,c_33,c_1451,c_2087,c_2249,c_7132,c_7893])).

cnf(c_8,plain,
    ( ~ v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_364,plain,
    ( ~ v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_22])).

cnf(c_365,plain,
    ( ~ v4_tops_1(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,X0)),X0) ),
    inference(unflattening,[status(thm)],[c_364])).

cnf(c_1189,plain,
    ( v4_tops_1(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,X0)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_365])).

cnf(c_3602,plain,
    ( k2_pre_topc(sK1,k1_tops_1(sK1,k2_pre_topc(sK1,X0))) = k2_pre_topc(sK1,X0)
    | v4_tops_1(k2_pre_topc(sK1,X0),sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k1_tops_1(sK1,k2_pre_topc(sK1,X0)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,X0)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1185,c_3002])).

cnf(c_5177,plain,
    ( k2_pre_topc(sK1,k1_tops_1(sK1,k2_pre_topc(sK1,X0))) = k2_pre_topc(sK1,X0)
    | v4_tops_1(k2_pre_topc(sK1,X0),sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,X0)),X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3602,c_1192])).

cnf(c_5181,plain,
    ( k2_pre_topc(sK1,k1_tops_1(sK1,k2_pre_topc(sK1,X0))) = k2_pre_topc(sK1,X0)
    | v4_tops_1(X0,sK1) != iProver_top
    | v4_tops_1(k2_pre_topc(sK1,X0),sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1189,c_5177])).

cnf(c_7966,plain,
    ( k2_pre_topc(sK1,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) = k2_pre_topc(sK1,sK3)
    | v4_tops_1(k2_pre_topc(sK1,sK3),sK1) != iProver_top
    | v4_tops_1(sK3,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7919,c_5181])).

cnf(c_8040,plain,
    ( k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) = sK3
    | v4_tops_1(sK3,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7966,c_7919])).

cnf(c_9013,plain,
    ( v4_tops_1(sK3,sK1) != iProver_top
    | k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8040,c_29])).

cnf(c_9014,plain,
    ( k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) = sK3
    | v4_tops_1(sK3,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_9013])).

cnf(c_9019,plain,
    ( k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) = sK3
    | k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_2454,c_9014])).

cnf(c_2392,plain,
    ( ~ v5_tops_1(sK2,sK0)
    | k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = sK2 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2380])).

cnf(c_9090,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9019,c_20,c_17,c_1453,c_2392])).

cnf(c_9093,plain,
    ( v4_tops_1(sK2,sK0) = iProver_top
    | r1_tarski(sK2,sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9090,c_7886])).

cnf(c_499,plain,
    ( ~ v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_23])).

cnf(c_500,plain,
    ( ~ v4_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X0) ),
    inference(unflattening,[status(thm)],[c_499])).

cnf(c_1180,plain,
    ( v4_tops_1(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_500])).

cnf(c_514,plain,
    ( ~ v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_23])).

cnf(c_515,plain,
    ( ~ v4_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,X0))) ),
    inference(unflattening,[status(thm)],[c_514])).

cnf(c_1179,plain,
    ( v4_tops_1(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_515])).

cnf(c_1663,plain,
    ( k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1176,c_1205])).

cnf(c_2646,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,X0))) = k2_pre_topc(sK0,X0)
    | v4_tops_1(k2_pre_topc(sK0,X0),sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1179,c_1663])).

cnf(c_3686,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,X0))) = k2_pre_topc(sK0,X0)
    | v4_tops_1(k2_pre_topc(sK0,X0),sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2646,c_1183])).

cnf(c_3690,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,X0))) = k2_pre_topc(sK0,X0)
    | v4_tops_1(X0,sK0) != iProver_top
    | v4_tops_1(k2_pre_topc(sK0,X0),sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1180,c_3686])).

cnf(c_7199,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK2))) = k2_pre_topc(sK0,sK2)
    | v4_tops_1(k2_pre_topc(sK0,sK2),sK0) != iProver_top
    | v4_tops_1(sK2,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7136,c_3690])).

cnf(c_7253,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = sK2
    | v4_tops_1(sK2,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7199,c_7136])).

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

cnf(c_8902,plain,
    ( v4_tops_1(sK2,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7253,c_21,c_28,c_29,c_34,c_35,c_1451,c_1454,c_2087,c_7132,c_8040])).

cnf(c_1717,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1720,plain,
    ( r1_tarski(sK2,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1717])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9093,c_8902,c_1720])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:23:49 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.84/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.84/0.99  
% 3.84/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.84/0.99  
% 3.84/0.99  ------  iProver source info
% 3.84/0.99  
% 3.84/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.84/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.84/0.99  git: non_committed_changes: false
% 3.84/0.99  git: last_make_outside_of_git: false
% 3.84/0.99  
% 3.84/0.99  ------ 
% 3.84/0.99  
% 3.84/0.99  ------ Input Options
% 3.84/0.99  
% 3.84/0.99  --out_options                           all
% 3.84/0.99  --tptp_safe_out                         true
% 3.84/0.99  --problem_path                          ""
% 3.84/0.99  --include_path                          ""
% 3.84/0.99  --clausifier                            res/vclausify_rel
% 3.84/0.99  --clausifier_options                    --mode clausify
% 3.84/0.99  --stdin                                 false
% 3.84/0.99  --stats_out                             all
% 3.84/0.99  
% 3.84/0.99  ------ General Options
% 3.84/0.99  
% 3.84/0.99  --fof                                   false
% 3.84/0.99  --time_out_real                         305.
% 3.84/0.99  --time_out_virtual                      -1.
% 3.84/0.99  --symbol_type_check                     false
% 3.84/0.99  --clausify_out                          false
% 3.84/0.99  --sig_cnt_out                           false
% 3.84/0.99  --trig_cnt_out                          false
% 3.84/0.99  --trig_cnt_out_tolerance                1.
% 3.84/0.99  --trig_cnt_out_sk_spl                   false
% 3.84/0.99  --abstr_cl_out                          false
% 3.84/0.99  
% 3.84/0.99  ------ Global Options
% 3.84/0.99  
% 3.84/0.99  --schedule                              default
% 3.84/0.99  --add_important_lit                     false
% 3.84/0.99  --prop_solver_per_cl                    1000
% 3.84/0.99  --min_unsat_core                        false
% 3.84/0.99  --soft_assumptions                      false
% 3.84/0.99  --soft_lemma_size                       3
% 3.84/0.99  --prop_impl_unit_size                   0
% 3.84/0.99  --prop_impl_unit                        []
% 3.84/0.99  --share_sel_clauses                     true
% 3.84/0.99  --reset_solvers                         false
% 3.84/0.99  --bc_imp_inh                            [conj_cone]
% 3.84/0.99  --conj_cone_tolerance                   3.
% 3.84/0.99  --extra_neg_conj                        none
% 3.84/0.99  --large_theory_mode                     true
% 3.84/0.99  --prolific_symb_bound                   200
% 3.84/0.99  --lt_threshold                          2000
% 3.84/0.99  --clause_weak_htbl                      true
% 3.84/0.99  --gc_record_bc_elim                     false
% 3.84/0.99  
% 3.84/0.99  ------ Preprocessing Options
% 3.84/0.99  
% 3.84/0.99  --preprocessing_flag                    true
% 3.84/0.99  --time_out_prep_mult                    0.1
% 3.84/0.99  --splitting_mode                        input
% 3.84/0.99  --splitting_grd                         true
% 3.84/0.99  --splitting_cvd                         false
% 3.84/0.99  --splitting_cvd_svl                     false
% 3.84/0.99  --splitting_nvd                         32
% 3.84/0.99  --sub_typing                            true
% 3.84/0.99  --prep_gs_sim                           true
% 3.84/0.99  --prep_unflatten                        true
% 3.84/0.99  --prep_res_sim                          true
% 3.84/0.99  --prep_upred                            true
% 3.84/0.99  --prep_sem_filter                       exhaustive
% 3.84/0.99  --prep_sem_filter_out                   false
% 3.84/0.99  --pred_elim                             true
% 3.84/0.99  --res_sim_input                         true
% 3.84/0.99  --eq_ax_congr_red                       true
% 3.84/0.99  --pure_diseq_elim                       true
% 3.84/0.99  --brand_transform                       false
% 3.84/0.99  --non_eq_to_eq                          false
% 3.84/0.99  --prep_def_merge                        true
% 3.84/0.99  --prep_def_merge_prop_impl              false
% 3.84/0.99  --prep_def_merge_mbd                    true
% 3.84/0.99  --prep_def_merge_tr_red                 false
% 3.84/0.99  --prep_def_merge_tr_cl                  false
% 3.84/0.99  --smt_preprocessing                     true
% 3.84/0.99  --smt_ac_axioms                         fast
% 3.84/0.99  --preprocessed_out                      false
% 3.84/0.99  --preprocessed_stats                    false
% 3.84/0.99  
% 3.84/0.99  ------ Abstraction refinement Options
% 3.84/0.99  
% 3.84/0.99  --abstr_ref                             []
% 3.84/0.99  --abstr_ref_prep                        false
% 3.84/0.99  --abstr_ref_until_sat                   false
% 3.84/0.99  --abstr_ref_sig_restrict                funpre
% 3.84/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.84/0.99  --abstr_ref_under                       []
% 3.84/0.99  
% 3.84/0.99  ------ SAT Options
% 3.84/0.99  
% 3.84/0.99  --sat_mode                              false
% 3.84/0.99  --sat_fm_restart_options                ""
% 3.84/0.99  --sat_gr_def                            false
% 3.84/0.99  --sat_epr_types                         true
% 3.84/0.99  --sat_non_cyclic_types                  false
% 3.84/0.99  --sat_finite_models                     false
% 3.84/0.99  --sat_fm_lemmas                         false
% 3.84/0.99  --sat_fm_prep                           false
% 3.84/0.99  --sat_fm_uc_incr                        true
% 3.84/0.99  --sat_out_model                         small
% 3.84/0.99  --sat_out_clauses                       false
% 3.84/0.99  
% 3.84/0.99  ------ QBF Options
% 3.84/0.99  
% 3.84/0.99  --qbf_mode                              false
% 3.84/0.99  --qbf_elim_univ                         false
% 3.84/0.99  --qbf_dom_inst                          none
% 3.84/0.99  --qbf_dom_pre_inst                      false
% 3.84/0.99  --qbf_sk_in                             false
% 3.84/0.99  --qbf_pred_elim                         true
% 3.84/0.99  --qbf_split                             512
% 3.84/0.99  
% 3.84/0.99  ------ BMC1 Options
% 3.84/0.99  
% 3.84/0.99  --bmc1_incremental                      false
% 3.84/0.99  --bmc1_axioms                           reachable_all
% 3.84/0.99  --bmc1_min_bound                        0
% 3.84/0.99  --bmc1_max_bound                        -1
% 3.84/0.99  --bmc1_max_bound_default                -1
% 3.84/0.99  --bmc1_symbol_reachability              true
% 3.84/0.99  --bmc1_property_lemmas                  false
% 3.84/0.99  --bmc1_k_induction                      false
% 3.84/0.99  --bmc1_non_equiv_states                 false
% 3.84/0.99  --bmc1_deadlock                         false
% 3.84/0.99  --bmc1_ucm                              false
% 3.84/0.99  --bmc1_add_unsat_core                   none
% 3.84/0.99  --bmc1_unsat_core_children              false
% 3.84/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.84/0.99  --bmc1_out_stat                         full
% 3.84/0.99  --bmc1_ground_init                      false
% 3.84/0.99  --bmc1_pre_inst_next_state              false
% 3.84/0.99  --bmc1_pre_inst_state                   false
% 3.84/0.99  --bmc1_pre_inst_reach_state             false
% 3.84/0.99  --bmc1_out_unsat_core                   false
% 3.84/0.99  --bmc1_aig_witness_out                  false
% 3.84/0.99  --bmc1_verbose                          false
% 3.84/0.99  --bmc1_dump_clauses_tptp                false
% 3.84/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.84/0.99  --bmc1_dump_file                        -
% 3.84/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.84/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.84/0.99  --bmc1_ucm_extend_mode                  1
% 3.84/0.99  --bmc1_ucm_init_mode                    2
% 3.84/0.99  --bmc1_ucm_cone_mode                    none
% 3.84/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.84/0.99  --bmc1_ucm_relax_model                  4
% 3.84/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.84/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.84/0.99  --bmc1_ucm_layered_model                none
% 3.84/0.99  --bmc1_ucm_max_lemma_size               10
% 3.84/0.99  
% 3.84/0.99  ------ AIG Options
% 3.84/0.99  
% 3.84/0.99  --aig_mode                              false
% 3.84/0.99  
% 3.84/0.99  ------ Instantiation Options
% 3.84/0.99  
% 3.84/0.99  --instantiation_flag                    true
% 3.84/0.99  --inst_sos_flag                         false
% 3.84/0.99  --inst_sos_phase                        true
% 3.84/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.84/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.84/0.99  --inst_lit_sel_side                     num_symb
% 3.84/0.99  --inst_solver_per_active                1400
% 3.84/0.99  --inst_solver_calls_frac                1.
% 3.84/0.99  --inst_passive_queue_type               priority_queues
% 3.84/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.84/0.99  --inst_passive_queues_freq              [25;2]
% 3.84/0.99  --inst_dismatching                      true
% 3.84/0.99  --inst_eager_unprocessed_to_passive     true
% 3.84/0.99  --inst_prop_sim_given                   true
% 3.84/0.99  --inst_prop_sim_new                     false
% 3.84/0.99  --inst_subs_new                         false
% 3.84/0.99  --inst_eq_res_simp                      false
% 3.84/0.99  --inst_subs_given                       false
% 3.84/0.99  --inst_orphan_elimination               true
% 3.84/0.99  --inst_learning_loop_flag               true
% 3.84/0.99  --inst_learning_start                   3000
% 3.84/0.99  --inst_learning_factor                  2
% 3.84/0.99  --inst_start_prop_sim_after_learn       3
% 3.84/0.99  --inst_sel_renew                        solver
% 3.84/0.99  --inst_lit_activity_flag                true
% 3.84/0.99  --inst_restr_to_given                   false
% 3.84/0.99  --inst_activity_threshold               500
% 3.84/0.99  --inst_out_proof                        true
% 3.84/0.99  
% 3.84/0.99  ------ Resolution Options
% 3.84/0.99  
% 3.84/0.99  --resolution_flag                       true
% 3.84/0.99  --res_lit_sel                           adaptive
% 3.84/0.99  --res_lit_sel_side                      none
% 3.84/0.99  --res_ordering                          kbo
% 3.84/0.99  --res_to_prop_solver                    active
% 3.84/0.99  --res_prop_simpl_new                    false
% 3.84/0.99  --res_prop_simpl_given                  true
% 3.84/0.99  --res_passive_queue_type                priority_queues
% 3.84/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.84/0.99  --res_passive_queues_freq               [15;5]
% 3.84/0.99  --res_forward_subs                      full
% 3.84/0.99  --res_backward_subs                     full
% 3.84/0.99  --res_forward_subs_resolution           true
% 3.84/0.99  --res_backward_subs_resolution          true
% 3.84/0.99  --res_orphan_elimination                true
% 3.84/0.99  --res_time_limit                        2.
% 3.84/0.99  --res_out_proof                         true
% 3.84/0.99  
% 3.84/0.99  ------ Superposition Options
% 3.84/0.99  
% 3.84/0.99  --superposition_flag                    true
% 3.84/0.99  --sup_passive_queue_type                priority_queues
% 3.84/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.84/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.84/0.99  --demod_completeness_check              fast
% 3.84/0.99  --demod_use_ground                      true
% 3.84/0.99  --sup_to_prop_solver                    passive
% 3.84/0.99  --sup_prop_simpl_new                    true
% 3.84/0.99  --sup_prop_simpl_given                  true
% 3.84/0.99  --sup_fun_splitting                     false
% 3.84/0.99  --sup_smt_interval                      50000
% 3.84/0.99  
% 3.84/0.99  ------ Superposition Simplification Setup
% 3.84/0.99  
% 3.84/0.99  --sup_indices_passive                   []
% 3.84/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.84/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.84/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.84/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.84/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.84/0.99  --sup_full_bw                           [BwDemod]
% 3.84/0.99  --sup_immed_triv                        [TrivRules]
% 3.84/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.84/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.84/0.99  --sup_immed_bw_main                     []
% 3.84/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.84/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.84/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.84/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.84/0.99  
% 3.84/0.99  ------ Combination Options
% 3.84/0.99  
% 3.84/0.99  --comb_res_mult                         3
% 3.84/0.99  --comb_sup_mult                         2
% 3.84/0.99  --comb_inst_mult                        10
% 3.84/0.99  
% 3.84/0.99  ------ Debug Options
% 3.84/0.99  
% 3.84/0.99  --dbg_backtrace                         false
% 3.84/0.99  --dbg_dump_prop_clauses                 false
% 3.84/0.99  --dbg_dump_prop_clauses_file            -
% 3.84/0.99  --dbg_out_stat                          false
% 3.84/0.99  ------ Parsing...
% 3.84/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.84/0.99  
% 3.84/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 3.84/0.99  
% 3.84/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.84/0.99  
% 3.84/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.84/0.99  ------ Proving...
% 3.84/0.99  ------ Problem Properties 
% 3.84/0.99  
% 3.84/0.99  
% 3.84/0.99  clauses                                 30
% 3.84/0.99  conjectures                             8
% 3.84/0.99  EPR                                     8
% 3.84/0.99  Horn                                    28
% 3.84/0.99  unary                                   3
% 3.84/0.99  binary                                  8
% 3.84/0.99  lits                                    80
% 3.84/0.99  lits eq                                 8
% 3.84/0.99  fd_pure                                 0
% 3.84/0.99  fd_pseudo                               0
% 3.84/0.99  fd_cond                                 0
% 3.84/0.99  fd_pseudo_cond                          1
% 3.84/0.99  AC symbols                              0
% 3.84/0.99  
% 3.84/0.99  ------ Schedule dynamic 5 is on 
% 3.84/0.99  
% 3.84/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.84/0.99  
% 3.84/0.99  
% 3.84/0.99  ------ 
% 3.84/0.99  Current options:
% 3.84/0.99  ------ 
% 3.84/0.99  
% 3.84/0.99  ------ Input Options
% 3.84/0.99  
% 3.84/0.99  --out_options                           all
% 3.84/0.99  --tptp_safe_out                         true
% 3.84/0.99  --problem_path                          ""
% 3.84/0.99  --include_path                          ""
% 3.84/0.99  --clausifier                            res/vclausify_rel
% 3.84/0.99  --clausifier_options                    --mode clausify
% 3.84/0.99  --stdin                                 false
% 3.84/0.99  --stats_out                             all
% 3.84/0.99  
% 3.84/0.99  ------ General Options
% 3.84/0.99  
% 3.84/0.99  --fof                                   false
% 3.84/0.99  --time_out_real                         305.
% 3.84/0.99  --time_out_virtual                      -1.
% 3.84/0.99  --symbol_type_check                     false
% 3.84/0.99  --clausify_out                          false
% 3.84/0.99  --sig_cnt_out                           false
% 3.84/0.99  --trig_cnt_out                          false
% 3.84/0.99  --trig_cnt_out_tolerance                1.
% 3.84/0.99  --trig_cnt_out_sk_spl                   false
% 3.84/0.99  --abstr_cl_out                          false
% 3.84/0.99  
% 3.84/0.99  ------ Global Options
% 3.84/0.99  
% 3.84/0.99  --schedule                              default
% 3.84/0.99  --add_important_lit                     false
% 3.84/0.99  --prop_solver_per_cl                    1000
% 3.84/0.99  --min_unsat_core                        false
% 3.84/0.99  --soft_assumptions                      false
% 3.84/0.99  --soft_lemma_size                       3
% 3.84/0.99  --prop_impl_unit_size                   0
% 3.84/0.99  --prop_impl_unit                        []
% 3.84/0.99  --share_sel_clauses                     true
% 3.84/0.99  --reset_solvers                         false
% 3.84/0.99  --bc_imp_inh                            [conj_cone]
% 3.84/0.99  --conj_cone_tolerance                   3.
% 3.84/0.99  --extra_neg_conj                        none
% 3.84/0.99  --large_theory_mode                     true
% 3.84/0.99  --prolific_symb_bound                   200
% 3.84/0.99  --lt_threshold                          2000
% 3.84/0.99  --clause_weak_htbl                      true
% 3.84/0.99  --gc_record_bc_elim                     false
% 3.84/0.99  
% 3.84/0.99  ------ Preprocessing Options
% 3.84/0.99  
% 3.84/0.99  --preprocessing_flag                    true
% 3.84/0.99  --time_out_prep_mult                    0.1
% 3.84/0.99  --splitting_mode                        input
% 3.84/0.99  --splitting_grd                         true
% 3.84/0.99  --splitting_cvd                         false
% 3.84/0.99  --splitting_cvd_svl                     false
% 3.84/0.99  --splitting_nvd                         32
% 3.84/0.99  --sub_typing                            true
% 3.84/0.99  --prep_gs_sim                           true
% 3.84/0.99  --prep_unflatten                        true
% 3.84/0.99  --prep_res_sim                          true
% 3.84/0.99  --prep_upred                            true
% 3.84/0.99  --prep_sem_filter                       exhaustive
% 3.84/0.99  --prep_sem_filter_out                   false
% 3.84/0.99  --pred_elim                             true
% 3.84/0.99  --res_sim_input                         true
% 3.84/0.99  --eq_ax_congr_red                       true
% 3.84/0.99  --pure_diseq_elim                       true
% 3.84/0.99  --brand_transform                       false
% 3.84/0.99  --non_eq_to_eq                          false
% 3.84/0.99  --prep_def_merge                        true
% 3.84/0.99  --prep_def_merge_prop_impl              false
% 3.84/0.99  --prep_def_merge_mbd                    true
% 3.84/0.99  --prep_def_merge_tr_red                 false
% 3.84/0.99  --prep_def_merge_tr_cl                  false
% 3.84/0.99  --smt_preprocessing                     true
% 3.84/0.99  --smt_ac_axioms                         fast
% 3.84/0.99  --preprocessed_out                      false
% 3.84/0.99  --preprocessed_stats                    false
% 3.84/0.99  
% 3.84/0.99  ------ Abstraction refinement Options
% 3.84/0.99  
% 3.84/0.99  --abstr_ref                             []
% 3.84/0.99  --abstr_ref_prep                        false
% 3.84/0.99  --abstr_ref_until_sat                   false
% 3.84/0.99  --abstr_ref_sig_restrict                funpre
% 3.84/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.84/0.99  --abstr_ref_under                       []
% 3.84/0.99  
% 3.84/0.99  ------ SAT Options
% 3.84/0.99  
% 3.84/0.99  --sat_mode                              false
% 3.84/0.99  --sat_fm_restart_options                ""
% 3.84/0.99  --sat_gr_def                            false
% 3.84/0.99  --sat_epr_types                         true
% 3.84/0.99  --sat_non_cyclic_types                  false
% 3.84/0.99  --sat_finite_models                     false
% 3.84/0.99  --sat_fm_lemmas                         false
% 3.84/0.99  --sat_fm_prep                           false
% 3.84/0.99  --sat_fm_uc_incr                        true
% 3.84/0.99  --sat_out_model                         small
% 3.84/0.99  --sat_out_clauses                       false
% 3.84/0.99  
% 3.84/0.99  ------ QBF Options
% 3.84/0.99  
% 3.84/0.99  --qbf_mode                              false
% 3.84/0.99  --qbf_elim_univ                         false
% 3.84/0.99  --qbf_dom_inst                          none
% 3.84/0.99  --qbf_dom_pre_inst                      false
% 3.84/0.99  --qbf_sk_in                             false
% 3.84/0.99  --qbf_pred_elim                         true
% 3.84/0.99  --qbf_split                             512
% 3.84/0.99  
% 3.84/0.99  ------ BMC1 Options
% 3.84/0.99  
% 3.84/0.99  --bmc1_incremental                      false
% 3.84/0.99  --bmc1_axioms                           reachable_all
% 3.84/0.99  --bmc1_min_bound                        0
% 3.84/0.99  --bmc1_max_bound                        -1
% 3.84/0.99  --bmc1_max_bound_default                -1
% 3.84/0.99  --bmc1_symbol_reachability              true
% 3.84/0.99  --bmc1_property_lemmas                  false
% 3.84/0.99  --bmc1_k_induction                      false
% 3.84/0.99  --bmc1_non_equiv_states                 false
% 3.84/0.99  --bmc1_deadlock                         false
% 3.84/0.99  --bmc1_ucm                              false
% 3.84/0.99  --bmc1_add_unsat_core                   none
% 3.84/0.99  --bmc1_unsat_core_children              false
% 3.84/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.84/0.99  --bmc1_out_stat                         full
% 3.84/0.99  --bmc1_ground_init                      false
% 3.84/0.99  --bmc1_pre_inst_next_state              false
% 3.84/0.99  --bmc1_pre_inst_state                   false
% 3.84/0.99  --bmc1_pre_inst_reach_state             false
% 3.84/0.99  --bmc1_out_unsat_core                   false
% 3.84/0.99  --bmc1_aig_witness_out                  false
% 3.84/0.99  --bmc1_verbose                          false
% 3.84/0.99  --bmc1_dump_clauses_tptp                false
% 3.84/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.84/0.99  --bmc1_dump_file                        -
% 3.84/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.84/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.84/0.99  --bmc1_ucm_extend_mode                  1
% 3.84/0.99  --bmc1_ucm_init_mode                    2
% 3.84/0.99  --bmc1_ucm_cone_mode                    none
% 3.84/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.84/0.99  --bmc1_ucm_relax_model                  4
% 3.84/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.84/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.84/0.99  --bmc1_ucm_layered_model                none
% 3.84/0.99  --bmc1_ucm_max_lemma_size               10
% 3.84/0.99  
% 3.84/0.99  ------ AIG Options
% 3.84/0.99  
% 3.84/0.99  --aig_mode                              false
% 3.84/0.99  
% 3.84/0.99  ------ Instantiation Options
% 3.84/0.99  
% 3.84/0.99  --instantiation_flag                    true
% 3.84/0.99  --inst_sos_flag                         false
% 3.84/0.99  --inst_sos_phase                        true
% 3.84/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.84/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.84/0.99  --inst_lit_sel_side                     none
% 3.84/0.99  --inst_solver_per_active                1400
% 3.84/0.99  --inst_solver_calls_frac                1.
% 3.84/0.99  --inst_passive_queue_type               priority_queues
% 3.84/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.84/0.99  --inst_passive_queues_freq              [25;2]
% 3.84/0.99  --inst_dismatching                      true
% 3.84/0.99  --inst_eager_unprocessed_to_passive     true
% 3.84/0.99  --inst_prop_sim_given                   true
% 3.84/0.99  --inst_prop_sim_new                     false
% 3.84/0.99  --inst_subs_new                         false
% 3.84/0.99  --inst_eq_res_simp                      false
% 3.84/0.99  --inst_subs_given                       false
% 3.84/0.99  --inst_orphan_elimination               true
% 3.84/0.99  --inst_learning_loop_flag               true
% 3.84/0.99  --inst_learning_start                   3000
% 3.84/0.99  --inst_learning_factor                  2
% 3.84/0.99  --inst_start_prop_sim_after_learn       3
% 3.84/0.99  --inst_sel_renew                        solver
% 3.84/0.99  --inst_lit_activity_flag                true
% 3.84/0.99  --inst_restr_to_given                   false
% 3.84/0.99  --inst_activity_threshold               500
% 3.84/0.99  --inst_out_proof                        true
% 3.84/0.99  
% 3.84/0.99  ------ Resolution Options
% 3.84/0.99  
% 3.84/0.99  --resolution_flag                       false
% 3.84/0.99  --res_lit_sel                           adaptive
% 3.84/0.99  --res_lit_sel_side                      none
% 3.84/0.99  --res_ordering                          kbo
% 3.84/0.99  --res_to_prop_solver                    active
% 3.84/0.99  --res_prop_simpl_new                    false
% 3.84/0.99  --res_prop_simpl_given                  true
% 3.84/0.99  --res_passive_queue_type                priority_queues
% 3.84/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.84/0.99  --res_passive_queues_freq               [15;5]
% 3.84/0.99  --res_forward_subs                      full
% 3.84/0.99  --res_backward_subs                     full
% 3.84/0.99  --res_forward_subs_resolution           true
% 3.84/0.99  --res_backward_subs_resolution          true
% 3.84/0.99  --res_orphan_elimination                true
% 3.84/0.99  --res_time_limit                        2.
% 3.84/0.99  --res_out_proof                         true
% 3.84/0.99  
% 3.84/0.99  ------ Superposition Options
% 3.84/0.99  
% 3.84/0.99  --superposition_flag                    true
% 3.84/0.99  --sup_passive_queue_type                priority_queues
% 3.84/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.84/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.84/0.99  --demod_completeness_check              fast
% 3.84/0.99  --demod_use_ground                      true
% 3.84/0.99  --sup_to_prop_solver                    passive
% 3.84/0.99  --sup_prop_simpl_new                    true
% 3.84/0.99  --sup_prop_simpl_given                  true
% 3.84/0.99  --sup_fun_splitting                     false
% 3.84/0.99  --sup_smt_interval                      50000
% 3.84/0.99  
% 3.84/0.99  ------ Superposition Simplification Setup
% 3.84/0.99  
% 3.84/0.99  --sup_indices_passive                   []
% 3.84/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.84/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.84/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.84/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.84/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.84/0.99  --sup_full_bw                           [BwDemod]
% 3.84/0.99  --sup_immed_triv                        [TrivRules]
% 3.84/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.84/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.84/0.99  --sup_immed_bw_main                     []
% 3.84/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.84/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.84/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.84/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.84/0.99  
% 3.84/0.99  ------ Combination Options
% 3.84/0.99  
% 3.84/0.99  --comb_res_mult                         3
% 3.84/0.99  --comb_sup_mult                         2
% 3.84/0.99  --comb_inst_mult                        10
% 3.84/0.99  
% 3.84/0.99  ------ Debug Options
% 3.84/0.99  
% 3.84/0.99  --dbg_backtrace                         false
% 3.84/0.99  --dbg_dump_prop_clauses                 false
% 3.84/0.99  --dbg_dump_prop_clauses_file            -
% 3.84/0.99  --dbg_out_stat                          false
% 3.84/0.99  
% 3.84/0.99  
% 3.84/0.99  
% 3.84/0.99  
% 3.84/0.99  ------ Proving...
% 3.84/0.99  
% 3.84/0.99  
% 3.84/0.99  % SZS status Theorem for theBenchmark.p
% 3.84/0.99  
% 3.84/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.84/0.99  
% 3.84/0.99  fof(f9,conjecture,(
% 3.84/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v5_tops_1(X2,X0) => (v4_tops_1(X2,X0) & v4_pre_topc(X2,X0))) & ((v4_tops_1(X3,X1) & v4_pre_topc(X3,X1)) => v5_tops_1(X3,X1)))))))),
% 3.84/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f10,negated_conjecture,(
% 3.84/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v5_tops_1(X2,X0) => (v4_tops_1(X2,X0) & v4_pre_topc(X2,X0))) & ((v4_tops_1(X3,X1) & v4_pre_topc(X3,X1)) => v5_tops_1(X3,X1)))))))),
% 3.84/0.99    inference(negated_conjecture,[],[f9])).
% 3.84/0.99  
% 3.84/0.99  fof(f22,plain,(
% 3.84/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v4_pre_topc(X2,X0)) & v5_tops_1(X2,X0)) | (~v5_tops_1(X3,X1) & (v4_tops_1(X3,X1) & v4_pre_topc(X3,X1)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.84/0.99    inference(ennf_transformation,[],[f10])).
% 3.84/0.99  
% 3.84/0.99  fof(f23,plain,(
% 3.84/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v4_pre_topc(X2,X0)) & v5_tops_1(X2,X0)) | (~v5_tops_1(X3,X1) & v4_tops_1(X3,X1) & v4_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.84/0.99    inference(flattening,[],[f22])).
% 3.84/0.99  
% 3.84/0.99  fof(f32,plain,(
% 3.84/0.99    ( ! [X2,X0,X1] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v4_pre_topc(X2,X0)) & v5_tops_1(X2,X0)) | (~v5_tops_1(X3,X1) & v4_tops_1(X3,X1) & v4_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => ((((~v4_tops_1(X2,X0) | ~v4_pre_topc(X2,X0)) & v5_tops_1(X2,X0)) | (~v5_tops_1(sK3,X1) & v4_tops_1(sK3,X1) & v4_pre_topc(sK3,X1))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X1))))) )),
% 3.84/0.99    introduced(choice_axiom,[])).
% 3.84/0.99  
% 3.84/0.99  fof(f31,plain,(
% 3.84/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v4_pre_topc(X2,X0)) & v5_tops_1(X2,X0)) | (~v5_tops_1(X3,X1) & v4_tops_1(X3,X1) & v4_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X3] : ((((~v4_tops_1(sK2,X0) | ~v4_pre_topc(sK2,X0)) & v5_tops_1(sK2,X0)) | (~v5_tops_1(X3,X1) & v4_tops_1(X3,X1) & v4_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.84/0.99    introduced(choice_axiom,[])).
% 3.84/0.99  
% 3.84/0.99  fof(f30,plain,(
% 3.84/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v4_pre_topc(X2,X0)) & v5_tops_1(X2,X0)) | (~v5_tops_1(X3,X1) & v4_tops_1(X3,X1) & v4_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) => (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v4_pre_topc(X2,X0)) & v5_tops_1(X2,X0)) | (~v5_tops_1(X3,sK1) & v4_tops_1(X3,sK1) & v4_pre_topc(X3,sK1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(sK1))) )),
% 3.84/0.99    introduced(choice_axiom,[])).
% 3.84/0.99  
% 3.84/0.99  fof(f29,plain,(
% 3.84/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v4_pre_topc(X2,X0)) & v5_tops_1(X2,X0)) | (~v5_tops_1(X3,X1) & v4_tops_1(X3,X1) & v4_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,sK0) | ~v4_pre_topc(X2,sK0)) & v5_tops_1(X2,sK0)) | (~v5_tops_1(X3,X1) & v4_tops_1(X3,X1) & v4_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 3.84/0.99    introduced(choice_axiom,[])).
% 3.84/0.99  
% 3.84/0.99  fof(f33,plain,(
% 3.84/0.99    ((((((~v4_tops_1(sK2,sK0) | ~v4_pre_topc(sK2,sK0)) & v5_tops_1(sK2,sK0)) | (~v5_tops_1(sK3,sK1) & v4_tops_1(sK3,sK1) & v4_pre_topc(sK3,sK1))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 3.84/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f32,f31,f30,f29])).
% 3.84/0.99  
% 3.84/0.99  fof(f54,plain,(
% 3.84/0.99    v5_tops_1(sK2,sK0) | v4_tops_1(sK3,sK1)),
% 3.84/0.99    inference(cnf_transformation,[],[f33])).
% 3.84/0.99  
% 3.84/0.99  fof(f51,plain,(
% 3.84/0.99    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.84/0.99    inference(cnf_transformation,[],[f33])).
% 3.84/0.99  
% 3.84/0.99  fof(f5,axiom,(
% 3.84/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1)))),
% 3.84/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f16,plain,(
% 3.84/0.99    ! [X0] : (! [X1] : ((v5_tops_1(X1,X0) <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.84/0.99    inference(ennf_transformation,[],[f5])).
% 3.84/0.99  
% 3.84/0.99  fof(f28,plain,(
% 3.84/0.99    ! [X0] : (! [X1] : (((v5_tops_1(X1,X0) | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1) & (k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 | ~v5_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.84/0.99    inference(nnf_transformation,[],[f16])).
% 3.84/0.99  
% 3.84/0.99  fof(f43,plain,(
% 3.84/0.99    ( ! [X0,X1] : (k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 | ~v5_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f28])).
% 3.84/0.99  
% 3.84/0.99  fof(f49,plain,(
% 3.84/0.99    l1_pre_topc(sK0)),
% 3.84/0.99    inference(cnf_transformation,[],[f33])).
% 3.84/0.99  
% 3.84/0.99  fof(f6,axiom,(
% 3.84/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.84/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f17,plain,(
% 3.84/0.99    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.84/0.99    inference(ennf_transformation,[],[f6])).
% 3.84/0.99  
% 3.84/0.99  fof(f18,plain,(
% 3.84/0.99    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.84/0.99    inference(flattening,[],[f17])).
% 3.84/0.99  
% 3.84/0.99  fof(f45,plain,(
% 3.84/0.99    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f18])).
% 3.84/0.99  
% 3.84/0.99  fof(f53,plain,(
% 3.84/0.99    v5_tops_1(sK2,sK0) | v4_pre_topc(sK3,sK1)),
% 3.84/0.99    inference(cnf_transformation,[],[f33])).
% 3.84/0.99  
% 3.84/0.99  fof(f52,plain,(
% 3.84/0.99    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 3.84/0.99    inference(cnf_transformation,[],[f33])).
% 3.84/0.99  
% 3.84/0.99  fof(f3,axiom,(
% 3.84/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 3.84/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f13,plain,(
% 3.84/0.99    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.84/0.99    inference(ennf_transformation,[],[f3])).
% 3.84/0.99  
% 3.84/0.99  fof(f14,plain,(
% 3.84/0.99    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.84/0.99    inference(flattening,[],[f13])).
% 3.84/0.99  
% 3.84/0.99  fof(f38,plain,(
% 3.84/0.99    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f14])).
% 3.84/0.99  
% 3.84/0.99  fof(f50,plain,(
% 3.84/0.99    l1_pre_topc(sK1)),
% 3.84/0.99    inference(cnf_transformation,[],[f33])).
% 3.84/0.99  
% 3.84/0.99  fof(f2,axiom,(
% 3.84/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 3.84/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f11,plain,(
% 3.84/0.99    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.84/0.99    inference(ennf_transformation,[],[f2])).
% 3.84/0.99  
% 3.84/0.99  fof(f12,plain,(
% 3.84/0.99    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.84/0.99    inference(flattening,[],[f11])).
% 3.84/0.99  
% 3.84/0.99  fof(f37,plain,(
% 3.84/0.99    ( ! [X2,X0,X1] : (r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f12])).
% 3.84/0.99  
% 3.84/0.99  fof(f56,plain,(
% 3.84/0.99    ~v4_tops_1(sK2,sK0) | ~v4_pre_topc(sK2,sK0) | v4_pre_topc(sK3,sK1)),
% 3.84/0.99    inference(cnf_transformation,[],[f33])).
% 3.84/0.99  
% 3.84/0.99  fof(f39,plain,(
% 3.84/0.99    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f14])).
% 3.84/0.99  
% 3.84/0.99  fof(f48,plain,(
% 3.84/0.99    v2_pre_topc(sK0)),
% 3.84/0.99    inference(cnf_transformation,[],[f33])).
% 3.84/0.99  
% 3.84/0.99  fof(f8,axiom,(
% 3.84/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 3.84/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f21,plain,(
% 3.84/0.99    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.84/0.99    inference(ennf_transformation,[],[f8])).
% 3.84/0.99  
% 3.84/0.99  fof(f47,plain,(
% 3.84/0.99    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f21])).
% 3.84/0.99  
% 3.84/0.99  fof(f1,axiom,(
% 3.84/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.84/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f24,plain,(
% 3.84/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.84/0.99    inference(nnf_transformation,[],[f1])).
% 3.84/0.99  
% 3.84/0.99  fof(f25,plain,(
% 3.84/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.84/0.99    inference(flattening,[],[f24])).
% 3.84/0.99  
% 3.84/0.99  fof(f36,plain,(
% 3.84/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f25])).
% 3.84/0.99  
% 3.84/0.99  fof(f7,axiom,(
% 3.84/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 3.84/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f19,plain,(
% 3.84/0.99    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.84/0.99    inference(ennf_transformation,[],[f7])).
% 3.84/0.99  
% 3.84/0.99  fof(f20,plain,(
% 3.84/0.99    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.84/0.99    inference(flattening,[],[f19])).
% 3.84/0.99  
% 3.84/0.99  fof(f46,plain,(
% 3.84/0.99    ( ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f20])).
% 3.84/0.99  
% 3.84/0.99  fof(f4,axiom,(
% 3.84/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)))))),
% 3.84/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f15,plain,(
% 3.84/0.99    ! [X0] : (! [X1] : ((v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.84/0.99    inference(ennf_transformation,[],[f4])).
% 3.84/0.99  
% 3.84/0.99  fof(f26,plain,(
% 3.84/0.99    ! [X0] : (! [X1] : (((v4_tops_1(X1,X0) | (~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1))) & ((r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) | ~v4_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.84/0.99    inference(nnf_transformation,[],[f15])).
% 3.84/0.99  
% 3.84/0.99  fof(f27,plain,(
% 3.84/0.99    ! [X0] : (! [X1] : (((v4_tops_1(X1,X0) | ~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) & ((r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) | ~v4_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.84/0.99    inference(flattening,[],[f26])).
% 3.84/0.99  
% 3.84/0.99  fof(f41,plain,(
% 3.84/0.99    ( ! [X0,X1] : (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~v4_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f27])).
% 3.84/0.99  
% 3.84/0.99  fof(f55,plain,(
% 3.84/0.99    v5_tops_1(sK2,sK0) | ~v5_tops_1(sK3,sK1)),
% 3.84/0.99    inference(cnf_transformation,[],[f33])).
% 3.84/0.99  
% 3.84/0.99  fof(f44,plain,(
% 3.84/0.99    ( ! [X0,X1] : (v5_tops_1(X1,X0) | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f28])).
% 3.84/0.99  
% 3.84/0.99  fof(f34,plain,(
% 3.84/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.84/0.99    inference(cnf_transformation,[],[f25])).
% 3.84/0.99  
% 3.84/0.99  fof(f60,plain,(
% 3.84/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.84/0.99    inference(equality_resolution,[],[f34])).
% 3.84/0.99  
% 3.84/0.99  fof(f42,plain,(
% 3.84/0.99    ( ! [X0,X1] : (v4_tops_1(X1,X0) | ~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f27])).
% 3.84/0.99  
% 3.84/0.99  fof(f40,plain,(
% 3.84/0.99    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) | ~v4_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f27])).
% 3.84/0.99  
% 3.84/0.99  fof(f57,plain,(
% 3.84/0.99    ~v4_tops_1(sK2,sK0) | ~v4_pre_topc(sK2,sK0) | v4_tops_1(sK3,sK1)),
% 3.84/0.99    inference(cnf_transformation,[],[f33])).
% 3.84/0.99  
% 3.84/0.99  fof(f58,plain,(
% 3.84/0.99    ~v4_tops_1(sK2,sK0) | ~v4_pre_topc(sK2,sK0) | ~v5_tops_1(sK3,sK1)),
% 3.84/0.99    inference(cnf_transformation,[],[f33])).
% 3.84/0.99  
% 3.84/0.99  cnf(c_18,negated_conjecture,
% 3.84/0.99      ( v5_tops_1(sK2,sK0) | v4_tops_1(sK3,sK1) ),
% 3.84/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1199,plain,
% 3.84/0.99      ( v5_tops_1(sK2,sK0) = iProver_top
% 3.84/0.99      | v4_tops_1(sK3,sK1) = iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_21,negated_conjecture,
% 3.84/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.84/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1196,plain,
% 3.84/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_10,plain,
% 3.84/0.99      ( ~ v5_tops_1(X0,X1)
% 3.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.84/0.99      | ~ l1_pre_topc(X1)
% 3.84/0.99      | k2_pre_topc(X1,k1_tops_1(X1,X0)) = X0 ),
% 3.84/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_23,negated_conjecture,
% 3.84/0.99      ( l1_pre_topc(sK0) ),
% 3.84/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_469,plain,
% 3.84/0.99      ( ~ v5_tops_1(X0,X1)
% 3.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.84/0.99      | k2_pre_topc(X1,k1_tops_1(X1,X0)) = X0
% 3.84/0.99      | sK0 != X1 ),
% 3.84/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_23]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_470,plain,
% 3.84/0.99      ( ~ v5_tops_1(X0,sK0)
% 3.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.84/0.99      | k2_pre_topc(sK0,k1_tops_1(sK0,X0)) = X0 ),
% 3.84/0.99      inference(unflattening,[status(thm)],[c_469]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1182,plain,
% 3.84/0.99      ( k2_pre_topc(sK0,k1_tops_1(sK0,X0)) = X0
% 3.84/0.99      | v5_tops_1(X0,sK0) != iProver_top
% 3.84/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_470]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_2380,plain,
% 3.84/0.99      ( k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = sK2
% 3.84/0.99      | v5_tops_1(sK2,sK0) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_1196,c_1182]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_2454,plain,
% 3.84/0.99      ( k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = sK2
% 3.84/0.99      | v4_tops_1(sK3,sK1) = iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_1199,c_2380]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_11,plain,
% 3.84/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.84/0.99      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.84/0.99      | ~ l1_pre_topc(X1) ),
% 3.84/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_457,plain,
% 3.84/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.84/0.99      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.84/0.99      | sK0 != X1 ),
% 3.84/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_23]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_458,plain,
% 3.84/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.84/0.99      | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.84/0.99      inference(unflattening,[status(thm)],[c_457]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1183,plain,
% 3.84/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.84/0.99      | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_458]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_19,negated_conjecture,
% 3.84/0.99      ( v5_tops_1(sK2,sK0) | v4_pre_topc(sK3,sK1) ),
% 3.84/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1198,plain,
% 3.84/0.99      ( v5_tops_1(sK2,sK0) = iProver_top
% 3.84/0.99      | v4_pre_topc(sK3,sK1) = iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_2455,plain,
% 3.84/0.99      ( k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = sK2
% 3.84/0.99      | v4_pre_topc(sK3,sK1) = iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_1198,c_2380]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_20,negated_conjecture,
% 3.84/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 3.84/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1197,plain,
% 3.84/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_5,plain,
% 3.84/0.99      ( ~ v4_pre_topc(X0,X1)
% 3.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.84/0.99      | ~ l1_pre_topc(X1)
% 3.84/0.99      | k2_pre_topc(X1,X0) = X0 ),
% 3.84/0.99      inference(cnf_transformation,[],[f38]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_22,negated_conjecture,
% 3.84/0.99      ( l1_pre_topc(sK1) ),
% 3.84/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_412,plain,
% 3.84/0.99      ( ~ v4_pre_topc(X0,X1)
% 3.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.84/0.99      | k2_pre_topc(X1,X0) = X0
% 3.84/0.99      | sK1 != X1 ),
% 3.84/0.99      inference(resolution_lifted,[status(thm)],[c_5,c_22]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_413,plain,
% 3.84/0.99      ( ~ v4_pre_topc(X0,sK1)
% 3.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.84/0.99      | k2_pre_topc(sK1,X0) = X0 ),
% 3.84/0.99      inference(unflattening,[status(thm)],[c_412]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1186,plain,
% 3.84/0.99      ( k2_pre_topc(sK1,X0) = X0
% 3.84/0.99      | v4_pre_topc(X0,sK1) != iProver_top
% 3.84/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_413]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_2249,plain,
% 3.84/0.99      ( k2_pre_topc(sK1,sK3) = sK3
% 3.84/0.99      | v4_pre_topc(sK3,sK1) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_1197,c_1186]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_2763,plain,
% 3.84/0.99      ( k2_pre_topc(sK1,sK3) = sK3
% 3.84/0.99      | k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = sK2 ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_2455,c_2249]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_3,plain,
% 3.84/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.84/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.84/0.99      | ~ r1_tarski(X2,X0)
% 3.84/0.99      | r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X0))
% 3.84/0.99      | ~ l1_pre_topc(X1) ),
% 3.84/0.99      inference(cnf_transformation,[],[f37]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_562,plain,
% 3.84/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.84/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.84/0.99      | ~ r1_tarski(X2,X0)
% 3.84/0.99      | r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X0))
% 3.84/0.99      | sK0 != X1 ),
% 3.84/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_23]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_563,plain,
% 3.84/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.84/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.84/0.99      | ~ r1_tarski(X1,X0)
% 3.84/0.99      | r1_tarski(k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X0)) ),
% 3.84/0.99      inference(unflattening,[status(thm)],[c_562]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1176,plain,
% 3.84/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.84/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.84/0.99      | r1_tarski(X1,X0) != iProver_top
% 3.84/0.99      | r1_tarski(k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X0)) = iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_563]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_2805,plain,
% 3.84/0.99      ( k2_pre_topc(sK1,sK3) = sK3
% 3.84/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.84/0.99      | m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.84/0.99      | r1_tarski(X0,k1_tops_1(sK0,sK2)) != iProver_top
% 3.84/0.99      | r1_tarski(k2_pre_topc(sK0,X0),sK2) = iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_2763,c_1176]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_28,plain,
% 3.84/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1441,plain,
% 3.84/0.99      ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.84/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_458]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1442,plain,
% 3.84/0.99      ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 3.84/0.99      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_1441]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_6644,plain,
% 3.84/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.84/0.99      | k2_pre_topc(sK1,sK3) = sK3
% 3.84/0.99      | r1_tarski(X0,k1_tops_1(sK0,sK2)) != iProver_top
% 3.84/0.99      | r1_tarski(k2_pre_topc(sK0,X0),sK2) = iProver_top ),
% 3.84/0.99      inference(global_propositional_subsumption,
% 3.84/0.99                [status(thm)],
% 3.84/0.99                [c_2805,c_28,c_1442]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_6645,plain,
% 3.84/0.99      ( k2_pre_topc(sK1,sK3) = sK3
% 3.84/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.84/0.99      | r1_tarski(X0,k1_tops_1(sK0,sK2)) != iProver_top
% 3.84/0.99      | r1_tarski(k2_pre_topc(sK0,X0),sK2) = iProver_top ),
% 3.84/0.99      inference(renaming,[status(thm)],[c_6644]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_6655,plain,
% 3.84/0.99      ( k2_pre_topc(sK1,sK3) = sK3
% 3.84/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.84/0.99      | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK2)) != iProver_top
% 3.84/0.99      | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,X0)),sK2) = iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_1183,c_6645]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_16,negated_conjecture,
% 3.84/0.99      ( ~ v4_tops_1(sK2,sK0)
% 3.84/0.99      | v4_pre_topc(sK3,sK1)
% 3.84/0.99      | ~ v4_pre_topc(sK2,sK0) ),
% 3.84/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_33,plain,
% 3.84/0.99      ( v4_tops_1(sK2,sK0) != iProver_top
% 3.84/0.99      | v4_pre_topc(sK3,sK1) = iProver_top
% 3.84/0.99      | v4_pre_topc(sK2,sK0) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_4,plain,
% 3.84/0.99      ( v4_pre_topc(X0,X1)
% 3.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.84/0.99      | ~ v2_pre_topc(X1)
% 3.84/0.99      | ~ l1_pre_topc(X1)
% 3.84/0.99      | k2_pre_topc(X1,X0) != X0 ),
% 3.84/0.99      inference(cnf_transformation,[],[f39]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_24,negated_conjecture,
% 3.84/0.99      ( v2_pre_topc(sK0) ),
% 3.84/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_282,plain,
% 3.84/0.99      ( v4_pre_topc(X0,X1)
% 3.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.84/0.99      | ~ l1_pre_topc(X1)
% 3.84/0.99      | k2_pre_topc(X1,X0) != X0
% 3.84/0.99      | sK0 != X1 ),
% 3.84/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_24]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_283,plain,
% 3.84/0.99      ( v4_pre_topc(X0,sK0)
% 3.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.84/0.99      | ~ l1_pre_topc(sK0)
% 3.84/0.99      | k2_pre_topc(sK0,X0) != X0 ),
% 3.84/0.99      inference(unflattening,[status(thm)],[c_282]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_287,plain,
% 3.84/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.84/0.99      | v4_pre_topc(X0,sK0)
% 3.84/0.99      | k2_pre_topc(sK0,X0) != X0 ),
% 3.84/0.99      inference(global_propositional_subsumption,
% 3.84/0.99                [status(thm)],
% 3.84/0.99                [c_283,c_23]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_288,plain,
% 3.84/0.99      ( v4_pre_topc(X0,sK0)
% 3.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.84/0.99      | k2_pre_topc(sK0,X0) != X0 ),
% 3.84/0.99      inference(renaming,[status(thm)],[c_287]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1450,plain,
% 3.84/0.99      ( v4_pre_topc(sK2,sK0)
% 3.84/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.84/0.99      | k2_pre_topc(sK0,sK2) != sK2 ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_288]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1451,plain,
% 3.84/0.99      ( k2_pre_topc(sK0,sK2) != sK2
% 3.84/0.99      | v4_pre_topc(sK2,sK0) = iProver_top
% 3.84/0.99      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_1450]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_322,plain,
% 3.84/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.84/0.99      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.84/0.99      | sK1 != X1 ),
% 3.84/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_22]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_323,plain,
% 3.84/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.84/0.99      | m1_subset_1(k1_tops_1(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 3.84/0.99      inference(unflattening,[status(thm)],[c_322]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1192,plain,
% 3.84/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.84/0.99      | m1_subset_1(k1_tops_1(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_323]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_2801,plain,
% 3.84/0.99      ( k2_pre_topc(sK1,sK3) = sK3
% 3.84/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.84/0.99      | m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.84/0.99      | r1_tarski(k1_tops_1(sK0,sK2),X0) != iProver_top
% 3.84/0.99      | r1_tarski(sK2,k2_pre_topc(sK0,X0)) = iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_2763,c_1176]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_5238,plain,
% 3.84/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.84/0.99      | k2_pre_topc(sK1,sK3) = sK3
% 3.84/0.99      | r1_tarski(k1_tops_1(sK0,sK2),X0) != iProver_top
% 3.84/0.99      | r1_tarski(sK2,k2_pre_topc(sK0,X0)) = iProver_top ),
% 3.84/0.99      inference(global_propositional_subsumption,
% 3.84/0.99                [status(thm)],
% 3.84/0.99                [c_2801,c_28,c_1442]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_5239,plain,
% 3.84/0.99      ( k2_pre_topc(sK1,sK3) = sK3
% 3.84/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.84/0.99      | r1_tarski(k1_tops_1(sK0,sK2),X0) != iProver_top
% 3.84/0.99      | r1_tarski(sK2,k2_pre_topc(sK0,X0)) = iProver_top ),
% 3.84/0.99      inference(renaming,[status(thm)],[c_5238]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_5248,plain,
% 3.84/0.99      ( k2_pre_topc(sK1,sK3) = sK3
% 3.84/0.99      | r1_tarski(k1_tops_1(sK0,sK2),sK2) != iProver_top
% 3.84/0.99      | r1_tarski(sK2,k2_pre_topc(sK0,sK2)) = iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_1196,c_5239]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_13,plain,
% 3.84/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.84/0.99      | r1_tarski(k1_tops_1(X1,X0),X0)
% 3.84/0.99      | ~ l1_pre_topc(X1) ),
% 3.84/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_445,plain,
% 3.84/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.84/0.99      | r1_tarski(k1_tops_1(X1,X0),X0)
% 3.84/0.99      | sK0 != X1 ),
% 3.84/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_23]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_446,plain,
% 3.84/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.84/0.99      | r1_tarski(k1_tops_1(sK0,X0),X0) ),
% 3.84/0.99      inference(unflattening,[status(thm)],[c_445]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1447,plain,
% 3.84/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.84/0.99      | r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_446]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1448,plain,
% 3.84/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.84/0.99      | r1_tarski(k1_tops_1(sK0,sK2),sK2) = iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_1447]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_5310,plain,
% 3.84/0.99      ( k2_pre_topc(sK1,sK3) = sK3
% 3.84/0.99      | r1_tarski(sK2,k2_pre_topc(sK0,sK2)) = iProver_top ),
% 3.84/0.99      inference(global_propositional_subsumption,
% 3.84/0.99                [status(thm)],
% 3.84/0.99                [c_5248,c_28,c_1448]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_0,plain,
% 3.84/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.84/0.99      inference(cnf_transformation,[],[f36]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1205,plain,
% 3.84/0.99      ( X0 = X1
% 3.84/0.99      | r1_tarski(X0,X1) != iProver_top
% 3.84/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_5316,plain,
% 3.84/0.99      ( k2_pre_topc(sK1,sK3) = sK3
% 3.84/0.99      | k2_pre_topc(sK0,sK2) = sK2
% 3.84/0.99      | r1_tarski(k2_pre_topc(sK0,sK2),sK2) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_5310,c_1205]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_547,plain,
% 3.84/0.99      ( ~ v4_pre_topc(X0,X1)
% 3.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.84/0.99      | k2_pre_topc(X1,X0) = X0
% 3.84/0.99      | sK0 != X1 ),
% 3.84/0.99      inference(resolution_lifted,[status(thm)],[c_5,c_23]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_548,plain,
% 3.84/0.99      ( ~ v4_pre_topc(X0,sK0)
% 3.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.84/0.99      | k2_pre_topc(sK0,X0) = X0 ),
% 3.84/0.99      inference(unflattening,[status(thm)],[c_547]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1177,plain,
% 3.84/0.99      ( k2_pre_topc(sK0,X0) = X0
% 3.84/0.99      | v4_pre_topc(X0,sK0) != iProver_top
% 3.84/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_548]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_2075,plain,
% 3.84/0.99      ( k2_pre_topc(sK0,sK2) = sK2
% 3.84/0.99      | v4_pre_topc(sK2,sK0) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_1196,c_1177]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_12,plain,
% 3.84/0.99      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
% 3.84/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.84/0.99      | ~ v2_pre_topc(X0)
% 3.84/0.99      | ~ l1_pre_topc(X0) ),
% 3.84/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_264,plain,
% 3.84/0.99      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
% 3.84/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.84/0.99      | ~ l1_pre_topc(X0)
% 3.84/0.99      | sK0 != X0 ),
% 3.84/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_24]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_265,plain,
% 3.84/0.99      ( v4_pre_topc(k2_pre_topc(sK0,X0),sK0)
% 3.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.84/0.99      | ~ l1_pre_topc(sK0) ),
% 3.84/0.99      inference(unflattening,[status(thm)],[c_264]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_269,plain,
% 3.84/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.84/0.99      | v4_pre_topc(k2_pre_topc(sK0,X0),sK0) ),
% 3.84/0.99      inference(global_propositional_subsumption,
% 3.84/0.99                [status(thm)],
% 3.84/0.99                [c_265,c_23]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_270,plain,
% 3.84/0.99      ( v4_pre_topc(k2_pre_topc(sK0,X0),sK0)
% 3.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.84/0.99      inference(renaming,[status(thm)],[c_269]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1195,plain,
% 3.84/0.99      ( v4_pre_topc(k2_pre_topc(sK0,X0),sK0) = iProver_top
% 3.84/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_270]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1988,plain,
% 3.84/0.99      ( v4_pre_topc(k2_pre_topc(sK0,k1_tops_1(sK0,X0)),sK0) = iProver_top
% 3.84/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_1183,c_1195]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_3148,plain,
% 3.84/0.99      ( k2_pre_topc(sK1,sK3) = sK3
% 3.84/0.99      | v4_pre_topc(sK2,sK0) = iProver_top
% 3.84/0.99      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_2763,c_1988]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_5319,plain,
% 3.84/0.99      ( k2_pre_topc(sK0,sK2) = sK2 | k2_pre_topc(sK1,sK3) = sK3 ),
% 3.84/0.99      inference(global_propositional_subsumption,
% 3.84/0.99                [status(thm)],
% 3.84/0.99                [c_5316,c_28,c_2075,c_3148]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_5320,plain,
% 3.84/0.99      ( k2_pre_topc(sK1,sK3) = sK3 | k2_pre_topc(sK0,sK2) = sK2 ),
% 3.84/0.99      inference(renaming,[status(thm)],[c_5319]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_427,plain,
% 3.84/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.84/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.84/0.99      | ~ r1_tarski(X2,X0)
% 3.84/0.99      | r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X0))
% 3.84/0.99      | sK1 != X1 ),
% 3.84/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_22]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_428,plain,
% 3.84/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.84/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.84/0.99      | ~ r1_tarski(X1,X0)
% 3.84/0.99      | r1_tarski(k2_pre_topc(sK1,X1),k2_pre_topc(sK1,X0)) ),
% 3.84/0.99      inference(unflattening,[status(thm)],[c_427]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1185,plain,
% 3.84/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.84/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.84/0.99      | r1_tarski(X1,X0) != iProver_top
% 3.84/0.99      | r1_tarski(k2_pre_topc(sK1,X1),k2_pre_topc(sK1,X0)) = iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_428]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_5328,plain,
% 3.84/0.99      ( k2_pre_topc(sK0,sK2) = sK2
% 3.84/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.84/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.84/0.99      | r1_tarski(X0,sK3) != iProver_top
% 3.84/0.99      | r1_tarski(k2_pre_topc(sK1,X0),sK3) = iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_5320,c_1185]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_29,plain,
% 3.84/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_6003,plain,
% 3.84/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.84/0.99      | k2_pre_topc(sK0,sK2) = sK2
% 3.84/0.99      | r1_tarski(X0,sK3) != iProver_top
% 3.84/0.99      | r1_tarski(k2_pre_topc(sK1,X0),sK3) = iProver_top ),
% 3.84/0.99      inference(global_propositional_subsumption,
% 3.84/0.99                [status(thm)],
% 3.84/0.99                [c_5328,c_29]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_6004,plain,
% 3.84/0.99      ( k2_pre_topc(sK0,sK2) = sK2
% 3.84/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.84/0.99      | r1_tarski(X0,sK3) != iProver_top
% 3.84/0.99      | r1_tarski(k2_pre_topc(sK1,X0),sK3) = iProver_top ),
% 3.84/0.99      inference(renaming,[status(thm)],[c_6003]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_6014,plain,
% 3.84/0.99      ( k2_pre_topc(sK0,sK2) = sK2
% 3.84/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.84/0.99      | r1_tarski(k1_tops_1(sK1,X0),sK3) != iProver_top
% 3.84/0.99      | r1_tarski(k2_pre_topc(sK1,k1_tops_1(sK1,X0)),sK3) = iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_1192,c_6004]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_7,plain,
% 3.84/0.99      ( ~ v4_tops_1(X0,X1)
% 3.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.84/0.99      | r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
% 3.84/0.99      | ~ l1_pre_topc(X1) ),
% 3.84/0.99      inference(cnf_transformation,[],[f41]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_379,plain,
% 3.84/0.99      ( ~ v4_tops_1(X0,X1)
% 3.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.84/0.99      | r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
% 3.84/0.99      | sK1 != X1 ),
% 3.84/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_22]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_380,plain,
% 3.84/0.99      ( ~ v4_tops_1(X0,sK1)
% 3.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.84/0.99      | r1_tarski(X0,k2_pre_topc(sK1,k1_tops_1(sK1,X0))) ),
% 3.84/0.99      inference(unflattening,[status(thm)],[c_379]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1188,plain,
% 3.84/0.99      ( v4_tops_1(X0,sK1) != iProver_top
% 3.84/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.84/0.99      | r1_tarski(X0,k2_pre_topc(sK1,k1_tops_1(sK1,X0))) = iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_380]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_3002,plain,
% 3.84/0.99      ( k2_pre_topc(sK1,k1_tops_1(sK1,X0)) = X0
% 3.84/0.99      | v4_tops_1(X0,sK1) != iProver_top
% 3.84/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.84/0.99      | r1_tarski(k2_pre_topc(sK1,k1_tops_1(sK1,X0)),X0) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_1188,c_1205]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_6428,plain,
% 3.84/0.99      ( k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) = sK3
% 3.84/0.99      | k2_pre_topc(sK0,sK2) = sK2
% 3.84/0.99      | v4_tops_1(sK3,sK1) != iProver_top
% 3.84/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.84/0.99      | r1_tarski(k1_tops_1(sK1,sK3),sK3) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_6014,c_3002]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_310,plain,
% 3.84/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.84/0.99      | r1_tarski(k1_tops_1(X1,X0),X0)
% 3.84/0.99      | sK1 != X1 ),
% 3.84/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_22]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_311,plain,
% 3.84/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.84/0.99      | r1_tarski(k1_tops_1(sK1,X0),X0) ),
% 3.84/0.99      inference(unflattening,[status(thm)],[c_310]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1444,plain,
% 3.84/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.84/0.99      | r1_tarski(k1_tops_1(sK1,sK3),sK3) ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_311]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1445,plain,
% 3.84/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.84/0.99      | r1_tarski(k1_tops_1(sK1,sK3),sK3) = iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_1444]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_6887,plain,
% 3.84/0.99      ( k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) = sK3
% 3.84/0.99      | k2_pre_topc(sK0,sK2) = sK2
% 3.84/0.99      | v4_tops_1(sK3,sK1) != iProver_top ),
% 3.84/0.99      inference(global_propositional_subsumption,
% 3.84/0.99                [status(thm)],
% 3.84/0.99                [c_6428,c_29,c_1445]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_6894,plain,
% 3.84/0.99      ( k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) = sK3
% 3.84/0.99      | k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = sK2
% 3.84/0.99      | k2_pre_topc(sK0,sK2) = sK2 ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_2454,c_6887]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_17,negated_conjecture,
% 3.84/0.99      ( ~ v5_tops_1(sK3,sK1) | v5_tops_1(sK2,sK0) ),
% 3.84/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_32,plain,
% 3.84/0.99      ( v5_tops_1(sK3,sK1) != iProver_top
% 3.84/0.99      | v5_tops_1(sK2,sK0) = iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_9,plain,
% 3.84/0.99      ( v5_tops_1(X0,X1)
% 3.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.84/0.99      | ~ l1_pre_topc(X1)
% 3.84/0.99      | k2_pre_topc(X1,k1_tops_1(X1,X0)) != X0 ),
% 3.84/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_349,plain,
% 3.84/0.99      ( v5_tops_1(X0,X1)
% 3.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.84/0.99      | k2_pre_topc(X1,k1_tops_1(X1,X0)) != X0
% 3.84/0.99      | sK1 != X1 ),
% 3.84/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_22]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_350,plain,
% 3.84/0.99      ( v5_tops_1(X0,sK1)
% 3.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.84/0.99      | k2_pre_topc(sK1,k1_tops_1(sK1,X0)) != X0 ),
% 3.84/0.99      inference(unflattening,[status(thm)],[c_349]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1453,plain,
% 3.84/0.99      ( v5_tops_1(sK3,sK1)
% 3.84/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.84/0.99      | k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) != sK3 ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_350]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1454,plain,
% 3.84/0.99      ( k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) != sK3
% 3.84/0.99      | v5_tops_1(sK3,sK1) = iProver_top
% 3.84/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_1453]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_6963,plain,
% 3.84/0.99      ( k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = sK2
% 3.84/0.99      | k2_pre_topc(sK0,sK2) = sK2 ),
% 3.84/0.99      inference(global_propositional_subsumption,
% 3.84/0.99                [status(thm)],
% 3.84/0.99                [c_6894,c_29,c_32,c_1454,c_2380]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_484,plain,
% 3.84/0.99      ( v5_tops_1(X0,X1)
% 3.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.84/0.99      | k2_pre_topc(X1,k1_tops_1(X1,X0)) != X0
% 3.84/0.99      | sK0 != X1 ),
% 3.84/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_23]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_485,plain,
% 3.84/0.99      ( v5_tops_1(X0,sK0)
% 3.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.84/0.99      | k2_pre_topc(sK0,k1_tops_1(sK0,X0)) != X0 ),
% 3.84/0.99      inference(unflattening,[status(thm)],[c_484]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1181,plain,
% 3.84/0.99      ( k2_pre_topc(sK0,k1_tops_1(sK0,X0)) != X0
% 3.84/0.99      | v5_tops_1(X0,sK0) = iProver_top
% 3.84/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_485]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_6980,plain,
% 3.84/0.99      ( k2_pre_topc(sK0,sK2) = sK2
% 3.84/0.99      | v5_tops_1(sK2,sK0) = iProver_top
% 3.84/0.99      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_6963,c_1181]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_2087,plain,
% 3.84/0.99      ( ~ v4_pre_topc(sK2,sK0) | k2_pre_topc(sK0,sK2) = sK2 ),
% 3.84/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_2075]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_6977,plain,
% 3.84/0.99      ( k2_pre_topc(sK0,sK2) = sK2
% 3.84/0.99      | v4_pre_topc(sK2,sK0) = iProver_top
% 3.84/0.99      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_6963,c_1988]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_7132,plain,
% 3.84/0.99      ( v4_pre_topc(sK2,sK0)
% 3.84/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.84/0.99      | k2_pre_topc(sK0,sK2) = sK2 ),
% 3.84/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_6977]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_7136,plain,
% 3.84/0.99      ( k2_pre_topc(sK0,sK2) = sK2 ),
% 3.84/0.99      inference(global_propositional_subsumption,
% 3.84/0.99                [status(thm)],
% 3.84/0.99                [c_6980,c_21,c_2087,c_7132]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_2,plain,
% 3.84/0.99      ( r1_tarski(X0,X0) ),
% 3.84/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1204,plain,
% 3.84/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_5249,plain,
% 3.84/0.99      ( k2_pre_topc(sK1,sK3) = sK3
% 3.84/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.84/0.99      | r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,X0)) != iProver_top
% 3.84/0.99      | r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,X0))) = iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_1183,c_5239]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_5964,plain,
% 3.84/0.99      ( k2_pre_topc(sK1,sK3) = sK3
% 3.84/0.99      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.84/0.99      | r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) = iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_1204,c_5249]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_6121,plain,
% 3.84/0.99      ( k2_pre_topc(sK1,sK3) = sK3
% 3.84/0.99      | r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) = iProver_top ),
% 3.84/0.99      inference(global_propositional_subsumption,
% 3.84/0.99                [status(thm)],
% 3.84/0.99                [c_5964,c_28]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_6,plain,
% 3.84/0.99      ( v4_tops_1(X0,X1)
% 3.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.84/0.99      | ~ r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
% 3.84/0.99      | ~ r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
% 3.84/0.99      | ~ l1_pre_topc(X1) ),
% 3.84/0.99      inference(cnf_transformation,[],[f42]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_529,plain,
% 3.84/0.99      ( v4_tops_1(X0,X1)
% 3.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.84/0.99      | ~ r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
% 3.84/0.99      | ~ r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
% 3.84/0.99      | sK0 != X1 ),
% 3.84/0.99      inference(resolution_lifted,[status(thm)],[c_6,c_23]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_530,plain,
% 3.84/0.99      ( v4_tops_1(X0,sK0)
% 3.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.84/0.99      | ~ r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,X0)))
% 3.84/0.99      | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X0) ),
% 3.84/0.99      inference(unflattening,[status(thm)],[c_529]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1178,plain,
% 3.84/0.99      ( v4_tops_1(X0,sK0) = iProver_top
% 3.84/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.84/0.99      | r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,X0))) != iProver_top
% 3.84/0.99      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X0) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_530]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_7204,plain,
% 3.84/0.99      ( v4_tops_1(sK2,sK0) = iProver_top
% 3.84/0.99      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.84/0.99      | r1_tarski(k1_tops_1(sK0,sK2),sK2) != iProver_top
% 3.84/0.99      | r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_7136,c_1178]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_7886,plain,
% 3.84/0.99      ( v4_tops_1(sK2,sK0) = iProver_top
% 3.84/0.99      | r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) != iProver_top ),
% 3.84/0.99      inference(global_propositional_subsumption,
% 3.84/0.99                [status(thm)],
% 3.84/0.99                [c_7204,c_28,c_1448]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_7893,plain,
% 3.84/0.99      ( k2_pre_topc(sK1,sK3) = sK3 | v4_tops_1(sK2,sK0) = iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_6121,c_7886]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_7919,plain,
% 3.84/0.99      ( k2_pre_topc(sK1,sK3) = sK3 ),
% 3.84/0.99      inference(global_propositional_subsumption,
% 3.84/0.99                [status(thm)],
% 3.84/0.99                [c_6655,c_21,c_28,c_33,c_1451,c_2087,c_2249,c_7132,
% 3.84/0.99                 c_7893]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_8,plain,
% 3.84/0.99      ( ~ v4_tops_1(X0,X1)
% 3.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.84/0.99      | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
% 3.84/0.99      | ~ l1_pre_topc(X1) ),
% 3.84/0.99      inference(cnf_transformation,[],[f40]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_364,plain,
% 3.84/0.99      ( ~ v4_tops_1(X0,X1)
% 3.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.84/0.99      | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
% 3.84/0.99      | sK1 != X1 ),
% 3.84/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_22]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_365,plain,
% 3.84/0.99      ( ~ v4_tops_1(X0,sK1)
% 3.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.84/0.99      | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,X0)),X0) ),
% 3.84/0.99      inference(unflattening,[status(thm)],[c_364]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1189,plain,
% 3.84/0.99      ( v4_tops_1(X0,sK1) != iProver_top
% 3.84/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.84/0.99      | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,X0)),X0) = iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_365]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_3602,plain,
% 3.84/0.99      ( k2_pre_topc(sK1,k1_tops_1(sK1,k2_pre_topc(sK1,X0))) = k2_pre_topc(sK1,X0)
% 3.84/0.99      | v4_tops_1(k2_pre_topc(sK1,X0),sK1) != iProver_top
% 3.84/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.84/0.99      | m1_subset_1(k1_tops_1(sK1,k2_pre_topc(sK1,X0)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.84/0.99      | m1_subset_1(k2_pre_topc(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.84/0.99      | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,X0)),X0) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_1185,c_3002]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_5177,plain,
% 3.84/0.99      ( k2_pre_topc(sK1,k1_tops_1(sK1,k2_pre_topc(sK1,X0))) = k2_pre_topc(sK1,X0)
% 3.84/0.99      | v4_tops_1(k2_pre_topc(sK1,X0),sK1) != iProver_top
% 3.84/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.84/0.99      | m1_subset_1(k2_pre_topc(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.84/0.99      | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,X0)),X0) != iProver_top ),
% 3.84/0.99      inference(forward_subsumption_resolution,
% 3.84/0.99                [status(thm)],
% 3.84/0.99                [c_3602,c_1192]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_5181,plain,
% 3.84/0.99      ( k2_pre_topc(sK1,k1_tops_1(sK1,k2_pre_topc(sK1,X0))) = k2_pre_topc(sK1,X0)
% 3.84/0.99      | v4_tops_1(X0,sK1) != iProver_top
% 3.84/0.99      | v4_tops_1(k2_pre_topc(sK1,X0),sK1) != iProver_top
% 3.84/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.84/0.99      | m1_subset_1(k2_pre_topc(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_1189,c_5177]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_7966,plain,
% 3.84/0.99      ( k2_pre_topc(sK1,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) = k2_pre_topc(sK1,sK3)
% 3.84/0.99      | v4_tops_1(k2_pre_topc(sK1,sK3),sK1) != iProver_top
% 3.84/0.99      | v4_tops_1(sK3,sK1) != iProver_top
% 3.84/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_7919,c_5181]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_8040,plain,
% 3.84/0.99      ( k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) = sK3
% 3.84/0.99      | v4_tops_1(sK3,sK1) != iProver_top
% 3.84/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 3.84/0.99      inference(light_normalisation,[status(thm)],[c_7966,c_7919]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_9013,plain,
% 3.84/0.99      ( v4_tops_1(sK3,sK1) != iProver_top
% 3.84/0.99      | k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) = sK3 ),
% 3.84/0.99      inference(global_propositional_subsumption,
% 3.84/0.99                [status(thm)],
% 3.84/0.99                [c_8040,c_29]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_9014,plain,
% 3.84/0.99      ( k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) = sK3
% 3.84/0.99      | v4_tops_1(sK3,sK1) != iProver_top ),
% 3.84/0.99      inference(renaming,[status(thm)],[c_9013]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_9019,plain,
% 3.84/0.99      ( k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) = sK3
% 3.84/0.99      | k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = sK2 ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_2454,c_9014]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_2392,plain,
% 3.84/0.99      ( ~ v5_tops_1(sK2,sK0)
% 3.84/0.99      | k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = sK2 ),
% 3.84/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_2380]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_9090,plain,
% 3.84/0.99      ( k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = sK2 ),
% 3.84/0.99      inference(global_propositional_subsumption,
% 3.84/0.99                [status(thm)],
% 3.84/0.99                [c_9019,c_20,c_17,c_1453,c_2392]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_9093,plain,
% 3.84/0.99      ( v4_tops_1(sK2,sK0) = iProver_top
% 3.84/0.99      | r1_tarski(sK2,sK2) != iProver_top ),
% 3.84/0.99      inference(demodulation,[status(thm)],[c_9090,c_7886]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_499,plain,
% 3.84/0.99      ( ~ v4_tops_1(X0,X1)
% 3.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.84/0.99      | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
% 3.84/0.99      | sK0 != X1 ),
% 3.84/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_23]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_500,plain,
% 3.84/0.99      ( ~ v4_tops_1(X0,sK0)
% 3.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.84/0.99      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X0) ),
% 3.84/0.99      inference(unflattening,[status(thm)],[c_499]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1180,plain,
% 3.84/0.99      ( v4_tops_1(X0,sK0) != iProver_top
% 3.84/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.84/0.99      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X0) = iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_500]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_514,plain,
% 3.84/0.99      ( ~ v4_tops_1(X0,X1)
% 3.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.84/0.99      | r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
% 3.84/0.99      | sK0 != X1 ),
% 3.84/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_23]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_515,plain,
% 3.84/0.99      ( ~ v4_tops_1(X0,sK0)
% 3.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.84/0.99      | r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,X0))) ),
% 3.84/0.99      inference(unflattening,[status(thm)],[c_514]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1179,plain,
% 3.84/0.99      ( v4_tops_1(X0,sK0) != iProver_top
% 3.84/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.84/0.99      | r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,X0))) = iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_515]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1663,plain,
% 3.84/0.99      ( k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,X1)
% 3.84/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.84/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.84/0.99      | r1_tarski(X1,X0) != iProver_top
% 3.84/0.99      | r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,X1)) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_1176,c_1205]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_2646,plain,
% 3.84/0.99      ( k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,X0))) = k2_pre_topc(sK0,X0)
% 3.84/0.99      | v4_tops_1(k2_pre_topc(sK0,X0),sK0) != iProver_top
% 3.84/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.84/0.99      | m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.84/0.99      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.84/0.99      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X0) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_1179,c_1663]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_3686,plain,
% 3.84/0.99      ( k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,X0))) = k2_pre_topc(sK0,X0)
% 3.84/0.99      | v4_tops_1(k2_pre_topc(sK0,X0),sK0) != iProver_top
% 3.84/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.84/0.99      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.84/0.99      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X0) != iProver_top ),
% 3.84/0.99      inference(forward_subsumption_resolution,
% 3.84/0.99                [status(thm)],
% 3.84/0.99                [c_2646,c_1183]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_3690,plain,
% 3.84/0.99      ( k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,X0))) = k2_pre_topc(sK0,X0)
% 3.84/0.99      | v4_tops_1(X0,sK0) != iProver_top
% 3.84/0.99      | v4_tops_1(k2_pre_topc(sK0,X0),sK0) != iProver_top
% 3.84/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.84/0.99      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_1180,c_3686]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_7199,plain,
% 3.84/0.99      ( k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK2))) = k2_pre_topc(sK0,sK2)
% 3.84/0.99      | v4_tops_1(k2_pre_topc(sK0,sK2),sK0) != iProver_top
% 3.84/0.99      | v4_tops_1(sK2,sK0) != iProver_top
% 3.84/0.99      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_7136,c_3690]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_7253,plain,
% 3.84/0.99      ( k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = sK2
% 3.84/0.99      | v4_tops_1(sK2,sK0) != iProver_top
% 3.84/0.99      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.84/0.99      inference(light_normalisation,[status(thm)],[c_7199,c_7136]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_15,negated_conjecture,
% 3.84/0.99      ( v4_tops_1(sK3,sK1)
% 3.84/0.99      | ~ v4_tops_1(sK2,sK0)
% 3.84/0.99      | ~ v4_pre_topc(sK2,sK0) ),
% 3.84/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_34,plain,
% 3.84/0.99      ( v4_tops_1(sK3,sK1) = iProver_top
% 3.84/0.99      | v4_tops_1(sK2,sK0) != iProver_top
% 3.84/0.99      | v4_pre_topc(sK2,sK0) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_14,negated_conjecture,
% 3.84/0.99      ( ~ v5_tops_1(sK3,sK1)
% 3.84/0.99      | ~ v4_tops_1(sK2,sK0)
% 3.84/0.99      | ~ v4_pre_topc(sK2,sK0) ),
% 3.84/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_35,plain,
% 3.84/0.99      ( v5_tops_1(sK3,sK1) != iProver_top
% 3.84/0.99      | v4_tops_1(sK2,sK0) != iProver_top
% 3.84/0.99      | v4_pre_topc(sK2,sK0) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_8902,plain,
% 3.84/0.99      ( v4_tops_1(sK2,sK0) != iProver_top ),
% 3.84/0.99      inference(global_propositional_subsumption,
% 3.84/0.99                [status(thm)],
% 3.84/0.99                [c_7253,c_21,c_28,c_29,c_34,c_35,c_1451,c_1454,c_2087,
% 3.84/0.99                 c_7132,c_8040]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1717,plain,
% 3.84/0.99      ( r1_tarski(sK2,sK2) ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1720,plain,
% 3.84/0.99      ( r1_tarski(sK2,sK2) = iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_1717]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(contradiction,plain,
% 3.84/0.99      ( $false ),
% 3.84/0.99      inference(minisat,[status(thm)],[c_9093,c_8902,c_1720]) ).
% 3.84/0.99  
% 3.84/0.99  
% 3.84/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.84/0.99  
% 3.84/0.99  ------                               Statistics
% 3.84/0.99  
% 3.84/0.99  ------ General
% 3.84/0.99  
% 3.84/0.99  abstr_ref_over_cycles:                  0
% 3.84/0.99  abstr_ref_under_cycles:                 0
% 3.84/0.99  gc_basic_clause_elim:                   0
% 3.84/0.99  forced_gc_time:                         0
% 3.84/0.99  parsing_time:                           0.011
% 3.84/0.99  unif_index_cands_time:                  0.
% 3.84/0.99  unif_index_add_time:                    0.
% 3.84/0.99  orderings_time:                         0.
% 3.84/0.99  out_proof_time:                         0.021
% 3.84/0.99  total_time:                             0.379
% 3.84/0.99  num_of_symbols:                         46
% 3.84/0.99  num_of_terms:                           5901
% 3.84/0.99  
% 3.84/0.99  ------ Preprocessing
% 3.84/0.99  
% 3.84/0.99  num_of_splits:                          0
% 3.84/0.99  num_of_split_atoms:                     0
% 3.84/0.99  num_of_reused_defs:                     0
% 3.84/0.99  num_eq_ax_congr_red:                    2
% 3.84/0.99  num_of_sem_filtered_clauses:            1
% 3.84/0.99  num_of_subtypes:                        0
% 3.84/0.99  monotx_restored_types:                  0
% 3.84/0.99  sat_num_of_epr_types:                   0
% 3.84/0.99  sat_num_of_non_cyclic_types:            0
% 3.84/0.99  sat_guarded_non_collapsed_types:        0
% 3.84/0.99  num_pure_diseq_elim:                    0
% 3.84/0.99  simp_replaced_by:                       0
% 3.84/0.99  res_preprocessed:                       107
% 3.84/0.99  prep_upred:                             0
% 3.84/0.99  prep_unflattend:                        20
% 3.84/0.99  smt_new_axioms:                         0
% 3.84/0.99  pred_elim_cands:                        7
% 3.84/0.99  pred_elim:                              2
% 3.84/0.99  pred_elim_cl:                           -6
% 3.84/0.99  pred_elim_cycles:                       3
% 3.84/0.99  merged_defs:                            0
% 3.84/0.99  merged_defs_ncl:                        0
% 3.84/0.99  bin_hyper_res:                          0
% 3.84/0.99  prep_cycles:                            3
% 3.84/0.99  pred_elim_time:                         0.011
% 3.84/0.99  splitting_time:                         0.
% 3.84/0.99  sem_filter_time:                        0.
% 3.84/0.99  monotx_time:                            0.001
% 3.84/0.99  subtype_inf_time:                       0.
% 3.84/0.99  
% 3.84/0.99  ------ Problem properties
% 3.84/0.99  
% 3.84/0.99  clauses:                                30
% 3.84/0.99  conjectures:                            8
% 3.84/0.99  epr:                                    8
% 3.84/0.99  horn:                                   28
% 3.84/0.99  ground:                                 8
% 3.84/0.99  unary:                                  3
% 3.84/0.99  binary:                                 8
% 3.84/0.99  lits:                                   80
% 3.84/0.99  lits_eq:                                8
% 3.84/0.99  fd_pure:                                0
% 3.84/0.99  fd_pseudo:                              0
% 3.84/0.99  fd_cond:                                0
% 3.84/0.99  fd_pseudo_cond:                         1
% 3.84/0.99  ac_symbols:                             0
% 3.84/0.99  
% 3.84/0.99  ------ Propositional Solver
% 3.84/0.99  
% 3.84/0.99  prop_solver_calls:                      25
% 3.84/0.99  prop_fast_solver_calls:                 1356
% 3.84/0.99  smt_solver_calls:                       0
% 3.84/0.99  smt_fast_solver_calls:                  0
% 3.84/0.99  prop_num_of_clauses:                    3507
% 3.84/0.99  prop_preprocess_simplified:             7380
% 3.84/0.99  prop_fo_subsumed:                       88
% 3.84/0.99  prop_solver_time:                       0.
% 3.84/0.99  smt_solver_time:                        0.
% 3.84/0.99  smt_fast_solver_time:                   0.
% 3.84/0.99  prop_fast_solver_time:                  0.
% 3.84/0.99  prop_unsat_core_time:                   0.
% 3.84/0.99  
% 3.84/0.99  ------ QBF
% 3.84/0.99  
% 3.84/0.99  qbf_q_res:                              0
% 3.84/0.99  qbf_num_tautologies:                    0
% 3.84/0.99  qbf_prep_cycles:                        0
% 3.84/0.99  
% 3.84/0.99  ------ BMC1
% 3.84/0.99  
% 3.84/0.99  bmc1_current_bound:                     -1
% 3.84/0.99  bmc1_last_solved_bound:                 -1
% 3.84/0.99  bmc1_unsat_core_size:                   -1
% 3.84/0.99  bmc1_unsat_core_parents_size:           -1
% 3.84/0.99  bmc1_merge_next_fun:                    0
% 3.84/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.84/0.99  
% 3.84/0.99  ------ Instantiation
% 3.84/0.99  
% 3.84/0.99  inst_num_of_clauses:                    1118
% 3.84/0.99  inst_num_in_passive:                    37
% 3.84/0.99  inst_num_in_active:                     675
% 3.84/0.99  inst_num_in_unprocessed:                406
% 3.84/0.99  inst_num_of_loops:                      730
% 3.84/0.99  inst_num_of_learning_restarts:          0
% 3.84/0.99  inst_num_moves_active_passive:          51
% 3.84/0.99  inst_lit_activity:                      0
% 3.84/0.99  inst_lit_activity_moves:                0
% 3.84/0.99  inst_num_tautologies:                   0
% 3.84/0.99  inst_num_prop_implied:                  0
% 3.84/0.99  inst_num_existing_simplified:           0
% 3.84/0.99  inst_num_eq_res_simplified:             0
% 3.84/0.99  inst_num_child_elim:                    0
% 3.84/0.99  inst_num_of_dismatching_blockings:      126
% 3.84/0.99  inst_num_of_non_proper_insts:           1269
% 3.84/0.99  inst_num_of_duplicates:                 0
% 3.84/0.99  inst_inst_num_from_inst_to_res:         0
% 3.84/0.99  inst_dismatching_checking_time:         0.
% 3.84/0.99  
% 3.84/0.99  ------ Resolution
% 3.84/0.99  
% 3.84/0.99  res_num_of_clauses:                     0
% 3.84/0.99  res_num_in_passive:                     0
% 3.84/0.99  res_num_in_active:                      0
% 3.84/0.99  res_num_of_loops:                       110
% 3.84/0.99  res_forward_subset_subsumed:            127
% 3.84/0.99  res_backward_subset_subsumed:           2
% 3.84/0.99  res_forward_subsumed:                   0
% 3.84/0.99  res_backward_subsumed:                  0
% 3.84/0.99  res_forward_subsumption_resolution:     0
% 3.84/0.99  res_backward_subsumption_resolution:    0
% 3.84/0.99  res_clause_to_clause_subsumption:       1064
% 3.84/0.99  res_orphan_elimination:                 0
% 3.84/0.99  res_tautology_del:                      133
% 3.84/0.99  res_num_eq_res_simplified:              0
% 3.84/0.99  res_num_sel_changes:                    0
% 3.84/0.99  res_moves_from_active_to_pass:          0
% 3.84/0.99  
% 3.84/0.99  ------ Superposition
% 3.84/0.99  
% 3.84/0.99  sup_time_total:                         0.
% 3.84/0.99  sup_time_generating:                    0.
% 3.84/0.99  sup_time_sim_full:                      0.
% 3.84/0.99  sup_time_sim_immed:                     0.
% 3.84/0.99  
% 3.84/0.99  sup_num_of_clauses:                     108
% 3.84/0.99  sup_num_in_active:                      92
% 3.84/0.99  sup_num_in_passive:                     16
% 3.84/0.99  sup_num_of_loops:                       144
% 3.84/0.99  sup_fw_superposition:                   133
% 3.84/0.99  sup_bw_superposition:                   85
% 3.84/0.99  sup_immediate_simplified:               52
% 3.84/0.99  sup_given_eliminated:                   0
% 3.84/0.99  comparisons_done:                       0
% 3.84/0.99  comparisons_avoided:                    33
% 3.84/0.99  
% 3.84/0.99  ------ Simplifications
% 3.84/0.99  
% 3.84/0.99  
% 3.84/0.99  sim_fw_subset_subsumed:                 24
% 3.84/0.99  sim_bw_subset_subsumed:                 42
% 3.84/0.99  sim_fw_subsumed:                        14
% 3.84/0.99  sim_bw_subsumed:                        0
% 3.84/0.99  sim_fw_subsumption_res:                 2
% 3.84/0.99  sim_bw_subsumption_res:                 0
% 3.84/0.99  sim_tautology_del:                      10
% 3.84/0.99  sim_eq_tautology_del:                   19
% 3.84/0.99  sim_eq_res_simp:                        0
% 3.84/0.99  sim_fw_demodulated:                     0
% 3.84/0.99  sim_bw_demodulated:                     25
% 3.84/0.99  sim_light_normalised:                   14
% 3.84/0.99  sim_joinable_taut:                      0
% 3.84/0.99  sim_joinable_simp:                      0
% 3.84/0.99  sim_ac_normalised:                      0
% 3.84/0.99  sim_smt_subsumption:                    0
% 3.84/0.99  
%------------------------------------------------------------------------------
