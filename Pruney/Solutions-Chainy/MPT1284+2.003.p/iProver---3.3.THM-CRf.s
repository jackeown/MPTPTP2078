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
% DateTime   : Thu Dec  3 12:15:51 EST 2020

% Result     : Theorem 3.93s
% Output     : CNFRefutation 3.93s
% Verified   : 
% Statistics : Number of formulae       :  207 (2250 expanded)
%              Number of clauses        :  145 ( 707 expanded)
%              Number of leaves         :   19 ( 728 expanded)
%              Depth                    :   20
%              Number of atoms          :  742 (18798 expanded)
%              Number of equality atoms :  255 (1235 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
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

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f35,plain,(
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

fof(f34,plain,(
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

fof(f33,plain,(
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

fof(f32,plain,
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

fof(f36,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f26,f35,f34,f33,f32])).

fof(f57,plain,
    ( v5_tops_1(sK2,sK0)
    | v4_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f55,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f36])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_tops_1(X1,X0)
              | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1 )
            & ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
              | ~ v5_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
      | ~ v5_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f53,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f56,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f36])).

fof(f5,axiom,(
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

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f54,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v5_tops_1(X1,X0)
      | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f58,plain,
    ( v5_tops_1(sK2,sK0)
    | v4_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f59,plain,
    ( v5_tops_1(sK2,sK0)
    | ~ v5_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_tops_1(X1,X0)
          <=> ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_tops_1(X1,X0)
          <=> ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
      | ~ v4_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f27])).

fof(f39,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)
      | ~ v4_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v4_tops_1(X1,X0)
      | ~ r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
      | ~ r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f52,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f64,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f37])).

fof(f62,plain,
    ( ~ v4_tops_1(sK2,sK0)
    | ~ v4_pre_topc(sK2,sK0)
    | ~ v5_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f61,plain,
    ( ~ v4_tops_1(sK2,sK0)
    | ~ v4_pre_topc(sK2,sK0)
    | v4_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f60,plain,
    ( ~ v4_tops_1(sK2,sK0)
    | ~ v4_pre_topc(sK2,sK0)
    | v4_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_20,negated_conjecture,
    ( v5_tops_1(sK2,sK0)
    | v4_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1266,plain,
    ( v5_tops_1(sK2,sK0) = iProver_top
    | v4_pre_topc(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1264,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_12,plain,
    ( ~ v5_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k1_tops_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_480,plain,
    ( ~ v5_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,k1_tops_1(X1,X0)) = X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_24])).

cnf(c_481,plain,
    ( ~ v5_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k1_tops_1(sK0,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_480])).

cnf(c_1250,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,X0)) = X0
    | v5_tops_1(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_481])).

cnf(c_2403,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = sK2
    | v5_tops_1(sK2,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1264,c_1250])).

cnf(c_2428,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = sK2
    | v4_pre_topc(sK3,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1266,c_2403])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1265,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_7,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_23,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_411,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,X0) = X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_23])).

cnf(c_412,plain,
    ( ~ v4_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_411])).

cnf(c_1255,plain,
    ( k2_pre_topc(sK1,X0) = X0
    | v4_pre_topc(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_412])).

cnf(c_2239,plain,
    ( k2_pre_topc(sK1,sK3) = sK3
    | v4_pre_topc(sK3,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1265,c_1255])).

cnf(c_2458,plain,
    ( k2_pre_topc(sK1,sK3) = sK3
    | k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_2428,c_2239])).

cnf(c_11,plain,
    ( v5_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k1_tops_1(X1,X0)) != X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_495,plain,
    ( v5_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,k1_tops_1(X1,X0)) != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_24])).

cnf(c_496,plain,
    ( v5_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k1_tops_1(sK0,X0)) != X0 ),
    inference(unflattening,[status(thm)],[c_495])).

cnf(c_1249,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,X0)) != X0
    | v5_tops_1(X0,sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_496])).

cnf(c_2465,plain,
    ( k2_pre_topc(sK1,sK3) = sK3
    | v5_tops_1(sK2,sK0) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2458,c_1249])).

cnf(c_29,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_30,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_19,negated_conjecture,
    ( v5_tops_1(sK2,sK0)
    | v4_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_32,plain,
    ( v5_tops_1(sK2,sK0) = iProver_top
    | v4_tops_1(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_18,negated_conjecture,
    ( ~ v5_tops_1(sK3,sK1)
    | v5_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_33,plain,
    ( v5_tops_1(sK3,sK1) != iProver_top
    | v5_tops_1(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_694,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1885,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_694])).

cnf(c_2101,plain,
    ( k1_zfmisc_1(u1_struct_0(sK1)) = k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_694])).

cnf(c_2654,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_694])).

cnf(c_702,plain,
    ( ~ v4_tops_1(X0,X1)
    | v4_tops_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1398,plain,
    ( ~ v4_tops_1(X0,X1)
    | v4_tops_1(X2,sK1)
    | X2 != X0
    | sK1 != X1 ),
    inference(instantiation,[status(thm)],[c_702])).

cnf(c_1597,plain,
    ( ~ v4_tops_1(X0,sK1)
    | v4_tops_1(X1,sK1)
    | X1 != X0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1398])).

cnf(c_2814,plain,
    ( v4_tops_1(X0,sK1)
    | ~ v4_tops_1(sK3,sK1)
    | X0 != sK3
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1597])).

cnf(c_3349,plain,
    ( v4_tops_1(k2_pre_topc(sK1,sK3),sK1)
    | ~ v4_tops_1(sK3,sK1)
    | k2_pre_topc(sK1,sK3) != sK3
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_2814])).

cnf(c_3350,plain,
    ( k2_pre_topc(sK1,sK3) != sK3
    | sK1 != sK1
    | v4_tops_1(k2_pre_topc(sK1,sK3),sK1) = iProver_top
    | v4_tops_1(sK3,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3349])).

cnf(c_700,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1358,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | X2 != X0
    | k1_zfmisc_1(u1_struct_0(sK1)) != X1 ),
    inference(instantiation,[status(thm)],[c_700])).

cnf(c_1658,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | X1 != X0
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1358])).

cnf(c_2925,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | X0 != sK3
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1658])).

cnf(c_3364,plain,
    ( m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,sK3) != sK3
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_2925])).

cnf(c_3365,plain,
    ( k2_pre_topc(sK1,sK3) != sK3
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
    | m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3364])).

cnf(c_348,plain,
    ( v5_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,k1_tops_1(X1,X0)) != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_23])).

cnf(c_349,plain,
    ( v5_tops_1(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,k1_tops_1(sK1,X0)) != X0 ),
    inference(unflattening,[status(thm)],[c_348])).

cnf(c_3975,plain,
    ( v5_tops_1(k2_pre_topc(sK1,sK3),sK1)
    | ~ m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) != k2_pre_topc(sK1,sK3) ),
    inference(instantiation,[status(thm)],[c_349])).

cnf(c_3985,plain,
    ( k2_pre_topc(sK1,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) != k2_pre_topc(sK1,sK3)
    | v5_tops_1(k2_pre_topc(sK1,sK3),sK1) = iProver_top
    | m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3975])).

cnf(c_695,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1882,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_695])).

cnf(c_3011,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1882])).

cnf(c_5018,plain,
    ( k2_pre_topc(sK1,sK3) != sK3
    | sK3 = k2_pre_topc(sK1,sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_3011])).

cnf(c_704,plain,
    ( ~ v5_tops_1(X0,X1)
    | v5_tops_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1336,plain,
    ( ~ v5_tops_1(X0,X1)
    | v5_tops_1(sK3,sK1)
    | sK1 != X1
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_704])).

cnf(c_1568,plain,
    ( ~ v5_tops_1(X0,sK1)
    | v5_tops_1(sK3,sK1)
    | sK1 != sK1
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_1336])).

cnf(c_7458,plain,
    ( ~ v5_tops_1(k2_pre_topc(sK1,sK3),sK1)
    | v5_tops_1(sK3,sK1)
    | sK1 != sK1
    | sK3 != k2_pre_topc(sK1,sK3) ),
    inference(instantiation,[status(thm)],[c_1568])).

cnf(c_7462,plain,
    ( sK1 != sK1
    | sK3 != k2_pre_topc(sK1,sK3)
    | v5_tops_1(k2_pre_topc(sK1,sK3),sK1) != iProver_top
    | v5_tops_1(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7458])).

cnf(c_9,plain,
    ( ~ v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_378,plain,
    ( ~ v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_23])).

cnf(c_379,plain,
    ( ~ v4_tops_1(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(X0,k2_pre_topc(sK1,k1_tops_1(sK1,X0))) ),
    inference(unflattening,[status(thm)],[c_378])).

cnf(c_1257,plain,
    ( v4_tops_1(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK1,k1_tops_1(sK1,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_379])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_456,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_23])).

cnf(c_457,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,k2_pre_topc(sK1,X0)) = k2_pre_topc(sK1,X0) ),
    inference(unflattening,[status(thm)],[c_456])).

cnf(c_1252,plain,
    ( k2_pre_topc(sK1,k2_pre_topc(sK1,X0)) = k2_pre_topc(sK1,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_457])).

cnf(c_1868,plain,
    ( k2_pre_topc(sK1,k2_pre_topc(sK1,sK3)) = k2_pre_topc(sK1,sK3) ),
    inference(superposition,[status(thm)],[c_1265,c_1252])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k2_pre_topc(X1,X0),k2_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_426,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k2_pre_topc(X1,X0),k2_pre_topc(X1,X2))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_23])).

cnf(c_427,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X0,X1)
    | r1_tarski(k2_pre_topc(sK1,X0),k2_pre_topc(sK1,X1)) ),
    inference(unflattening,[status(thm)],[c_426])).

cnf(c_1254,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_pre_topc(sK1,X0),k2_pre_topc(sK1,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_427])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1273,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2728,plain,
    ( k2_pre_topc(sK1,X0) = k2_pre_topc(sK1,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(k2_pre_topc(sK1,X0),k2_pre_topc(sK1,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1254,c_1273])).

cnf(c_3498,plain,
    ( k2_pre_topc(sK1,k2_pre_topc(sK1,sK3)) = k2_pre_topc(sK1,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK1,sK3)) != iProver_top
    | r1_tarski(k2_pre_topc(sK1,sK3),k2_pre_topc(sK1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1868,c_2728])).

cnf(c_3505,plain,
    ( k2_pre_topc(sK1,X0) = k2_pre_topc(sK1,sK3)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK1,sK3)) != iProver_top
    | r1_tarski(k2_pre_topc(sK1,sK3),k2_pre_topc(sK1,X0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3498,c_1868])).

cnf(c_6522,plain,
    ( k2_pre_topc(sK1,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) = k2_pre_topc(sK1,sK3)
    | v4_tops_1(k2_pre_topc(sK1,sK3),sK1) != iProver_top
    | m1_subset_1(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),k2_pre_topc(sK1,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1257,c_3505])).

cnf(c_10,plain,
    ( ~ v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_363,plain,
    ( ~ v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_23])).

cnf(c_364,plain,
    ( ~ v4_tops_1(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,X0)),X0) ),
    inference(unflattening,[status(thm)],[c_363])).

cnf(c_1258,plain,
    ( v4_tops_1(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,X0)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_364])).

cnf(c_2719,plain,
    ( v4_tops_1(k2_pre_topc(sK1,sK3),sK1) != iProver_top
    | m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),k2_pre_topc(sK1,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1868,c_1258])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_321,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_23])).

cnf(c_322,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k1_tops_1(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_321])).

cnf(c_3978,plain,
    ( m1_subset_1(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_322])).

cnf(c_3979,plain,
    ( m1_subset_1(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3978])).

cnf(c_9093,plain,
    ( m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | k2_pre_topc(sK1,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) = k2_pre_topc(sK1,sK3)
    | v4_tops_1(k2_pre_topc(sK1,sK3),sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6522,c_2719,c_3979])).

cnf(c_9094,plain,
    ( k2_pre_topc(sK1,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) = k2_pre_topc(sK1,sK3)
    | v4_tops_1(k2_pre_topc(sK1,sK3),sK1) != iProver_top
    | m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_9093])).

cnf(c_10199,plain,
    ( v5_tops_1(sK2,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2465,c_29,c_30,c_32,c_33,c_1885,c_2101,c_2654,c_3350,c_3365,c_3985,c_5018,c_7462,c_9094])).

cnf(c_10203,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_10199,c_2403])).

cnf(c_468,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_24])).

cnf(c_469,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_468])).

cnf(c_1251,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_469])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_591,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_24])).

cnf(c_592,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,k2_pre_topc(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_591])).

cnf(c_1243,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_592])).

cnf(c_1856,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),k2_pre_topc(sK0,k1_tops_1(sK0,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1251,c_1243])).

cnf(c_10352,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK2),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_10203,c_1856])).

cnf(c_603,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_24])).

cnf(c_604,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) = k2_pre_topc(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_603])).

cnf(c_1242,plain,
    ( k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) = k2_pre_topc(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_604])).

cnf(c_1857,plain,
    ( k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,X0))) = k2_pre_topc(sK0,k1_tops_1(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1251,c_1242])).

cnf(c_3100,plain,
    ( k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) = k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) ),
    inference(superposition,[status(thm)],[c_1264,c_1857])).

cnf(c_8,plain,
    ( v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
    | ~ r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_540,plain,
    ( v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
    | ~ r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_24])).

cnf(c_541,plain,
    ( v4_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,X0)))
    | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X0) ),
    inference(unflattening,[status(thm)],[c_540])).

cnf(c_1246,plain,
    ( v4_tops_1(X0,sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,X0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_541])).

cnf(c_3110,plain,
    ( v4_tops_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),sK0) = iProver_top
    | m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))),k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3100,c_1246])).

cnf(c_10285,plain,
    ( v4_tops_1(sK2,sK0) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK2),sK2) != iProver_top
    | r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10203,c_3110])).

cnf(c_10309,plain,
    ( v4_tops_1(sK2,sK0) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK2),sK2) != iProver_top
    | r1_tarski(sK2,sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10285,c_10203])).

cnf(c_6,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_25,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_293,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_25])).

cnf(c_294,plain,
    ( v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_293])).

cnf(c_298,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(X0,sK0)
    | k2_pre_topc(sK0,X0) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_294,c_24])).

cnf(c_299,plain,
    ( v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X0) != X0 ),
    inference(renaming,[status(thm)],[c_298])).

cnf(c_1262,plain,
    ( k2_pre_topc(sK0,X0) != X0
    | v4_pre_topc(X0,sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_299])).

cnf(c_3111,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),sK0) = iProver_top
    | m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3100,c_1262])).

cnf(c_1365,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_469])).

cnf(c_1366,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1365])).

cnf(c_14,plain,
    ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_275,plain,
    ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_25])).

cnf(c_276,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_275])).

cnf(c_280,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(k2_pre_topc(sK0,X0),sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_276,c_24])).

cnf(c_281,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(renaming,[status(thm)],[c_280])).

cnf(c_1487,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),sK0)
    | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_281])).

cnf(c_1488,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),sK0) = iProver_top
    | m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1487])).

cnf(c_3326,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3111,c_29,c_1366,c_1488])).

cnf(c_10304,plain,
    ( v4_pre_topc(sK2,sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_10203,c_3326])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1817,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1818,plain,
    ( r1_tarski(sK2,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1817])).

cnf(c_1526,plain,
    ( ~ v4_pre_topc(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,sK3) = sK3 ),
    inference(instantiation,[status(thm)],[c_412])).

cnf(c_1527,plain,
    ( k2_pre_topc(sK1,sK3) = sK3
    | v4_pre_topc(sK3,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1526])).

cnf(c_15,negated_conjecture,
    ( ~ v5_tops_1(sK3,sK1)
    | ~ v4_tops_1(sK2,sK0)
    | ~ v4_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_36,plain,
    ( v5_tops_1(sK3,sK1) != iProver_top
    | v4_tops_1(sK2,sK0) != iProver_top
    | v4_pre_topc(sK2,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_16,negated_conjecture,
    ( v4_tops_1(sK3,sK1)
    | ~ v4_tops_1(sK2,sK0)
    | ~ v4_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_35,plain,
    ( v4_tops_1(sK3,sK1) = iProver_top
    | v4_tops_1(sK2,sK0) != iProver_top
    | v4_pre_topc(sK2,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_17,negated_conjecture,
    ( ~ v4_tops_1(sK2,sK0)
    | v4_pre_topc(sK3,sK1)
    | ~ v4_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_34,plain,
    ( v4_tops_1(sK2,sK0) != iProver_top
    | v4_pre_topc(sK3,sK1) = iProver_top
    | v4_pre_topc(sK2,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10352,c_10309,c_10304,c_9094,c_7462,c_5018,c_3985,c_3365,c_3350,c_2654,c_2101,c_1885,c_1818,c_1527,c_36,c_35,c_34,c_30,c_29])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:47:46 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.93/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.93/0.98  
% 3.93/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.93/0.98  
% 3.93/0.98  ------  iProver source info
% 3.93/0.98  
% 3.93/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.93/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.93/0.98  git: non_committed_changes: false
% 3.93/0.98  git: last_make_outside_of_git: false
% 3.93/0.98  
% 3.93/0.98  ------ 
% 3.93/0.98  
% 3.93/0.98  ------ Input Options
% 3.93/0.98  
% 3.93/0.98  --out_options                           all
% 3.93/0.98  --tptp_safe_out                         true
% 3.93/0.98  --problem_path                          ""
% 3.93/0.98  --include_path                          ""
% 3.93/0.98  --clausifier                            res/vclausify_rel
% 3.93/0.98  --clausifier_options                    ""
% 3.93/0.98  --stdin                                 false
% 3.93/0.98  --stats_out                             all
% 3.93/0.98  
% 3.93/0.98  ------ General Options
% 3.93/0.98  
% 3.93/0.98  --fof                                   false
% 3.93/0.98  --time_out_real                         305.
% 3.93/0.98  --time_out_virtual                      -1.
% 3.93/0.98  --symbol_type_check                     false
% 3.93/0.98  --clausify_out                          false
% 3.93/0.98  --sig_cnt_out                           false
% 3.93/0.98  --trig_cnt_out                          false
% 3.93/0.98  --trig_cnt_out_tolerance                1.
% 3.93/0.98  --trig_cnt_out_sk_spl                   false
% 3.93/0.98  --abstr_cl_out                          false
% 3.93/0.98  
% 3.93/0.98  ------ Global Options
% 3.93/0.98  
% 3.93/0.98  --schedule                              default
% 3.93/0.98  --add_important_lit                     false
% 3.93/0.98  --prop_solver_per_cl                    1000
% 3.93/0.98  --min_unsat_core                        false
% 3.93/0.98  --soft_assumptions                      false
% 3.93/0.98  --soft_lemma_size                       3
% 3.93/0.98  --prop_impl_unit_size                   0
% 3.93/0.98  --prop_impl_unit                        []
% 3.93/0.98  --share_sel_clauses                     true
% 3.93/0.98  --reset_solvers                         false
% 3.93/0.98  --bc_imp_inh                            [conj_cone]
% 3.93/0.98  --conj_cone_tolerance                   3.
% 3.93/0.98  --extra_neg_conj                        none
% 3.93/0.98  --large_theory_mode                     true
% 3.93/0.98  --prolific_symb_bound                   200
% 3.93/0.98  --lt_threshold                          2000
% 3.93/0.98  --clause_weak_htbl                      true
% 3.93/0.98  --gc_record_bc_elim                     false
% 3.93/0.98  
% 3.93/0.98  ------ Preprocessing Options
% 3.93/0.98  
% 3.93/0.98  --preprocessing_flag                    true
% 3.93/0.98  --time_out_prep_mult                    0.1
% 3.93/0.98  --splitting_mode                        input
% 3.93/0.98  --splitting_grd                         true
% 3.93/0.98  --splitting_cvd                         false
% 3.93/0.98  --splitting_cvd_svl                     false
% 3.93/0.98  --splitting_nvd                         32
% 3.93/0.98  --sub_typing                            true
% 3.93/0.98  --prep_gs_sim                           true
% 3.93/0.98  --prep_unflatten                        true
% 3.93/0.98  --prep_res_sim                          true
% 3.93/0.98  --prep_upred                            true
% 3.93/0.98  --prep_sem_filter                       exhaustive
% 3.93/0.98  --prep_sem_filter_out                   false
% 3.93/0.98  --pred_elim                             true
% 3.93/0.98  --res_sim_input                         true
% 3.93/0.98  --eq_ax_congr_red                       true
% 3.93/0.98  --pure_diseq_elim                       true
% 3.93/0.98  --brand_transform                       false
% 3.93/0.98  --non_eq_to_eq                          false
% 3.93/0.98  --prep_def_merge                        true
% 3.93/0.98  --prep_def_merge_prop_impl              false
% 3.93/0.98  --prep_def_merge_mbd                    true
% 3.93/0.98  --prep_def_merge_tr_red                 false
% 3.93/0.98  --prep_def_merge_tr_cl                  false
% 3.93/0.98  --smt_preprocessing                     true
% 3.93/0.98  --smt_ac_axioms                         fast
% 3.93/0.98  --preprocessed_out                      false
% 3.93/0.98  --preprocessed_stats                    false
% 3.93/0.98  
% 3.93/0.98  ------ Abstraction refinement Options
% 3.93/0.98  
% 3.93/0.98  --abstr_ref                             []
% 3.93/0.98  --abstr_ref_prep                        false
% 3.93/0.98  --abstr_ref_until_sat                   false
% 3.93/0.98  --abstr_ref_sig_restrict                funpre
% 3.93/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.93/0.98  --abstr_ref_under                       []
% 3.93/0.98  
% 3.93/0.98  ------ SAT Options
% 3.93/0.98  
% 3.93/0.98  --sat_mode                              false
% 3.93/0.98  --sat_fm_restart_options                ""
% 3.93/0.98  --sat_gr_def                            false
% 3.93/0.98  --sat_epr_types                         true
% 3.93/0.98  --sat_non_cyclic_types                  false
% 3.93/0.98  --sat_finite_models                     false
% 3.93/0.98  --sat_fm_lemmas                         false
% 3.93/0.98  --sat_fm_prep                           false
% 3.93/0.98  --sat_fm_uc_incr                        true
% 3.93/0.98  --sat_out_model                         small
% 3.93/0.98  --sat_out_clauses                       false
% 3.93/0.98  
% 3.93/0.98  ------ QBF Options
% 3.93/0.98  
% 3.93/0.98  --qbf_mode                              false
% 3.93/0.98  --qbf_elim_univ                         false
% 3.93/0.98  --qbf_dom_inst                          none
% 3.93/0.98  --qbf_dom_pre_inst                      false
% 3.93/0.98  --qbf_sk_in                             false
% 3.93/0.98  --qbf_pred_elim                         true
% 3.93/0.98  --qbf_split                             512
% 3.93/0.98  
% 3.93/0.98  ------ BMC1 Options
% 3.93/0.98  
% 3.93/0.98  --bmc1_incremental                      false
% 3.93/0.98  --bmc1_axioms                           reachable_all
% 3.93/0.98  --bmc1_min_bound                        0
% 3.93/0.98  --bmc1_max_bound                        -1
% 3.93/0.98  --bmc1_max_bound_default                -1
% 3.93/0.98  --bmc1_symbol_reachability              true
% 3.93/0.98  --bmc1_property_lemmas                  false
% 3.93/0.98  --bmc1_k_induction                      false
% 3.93/0.98  --bmc1_non_equiv_states                 false
% 3.93/0.98  --bmc1_deadlock                         false
% 3.93/0.98  --bmc1_ucm                              false
% 3.93/0.98  --bmc1_add_unsat_core                   none
% 3.93/0.98  --bmc1_unsat_core_children              false
% 3.93/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.93/0.98  --bmc1_out_stat                         full
% 3.93/0.98  --bmc1_ground_init                      false
% 3.93/0.98  --bmc1_pre_inst_next_state              false
% 3.93/0.98  --bmc1_pre_inst_state                   false
% 3.93/0.98  --bmc1_pre_inst_reach_state             false
% 3.93/0.98  --bmc1_out_unsat_core                   false
% 3.93/0.98  --bmc1_aig_witness_out                  false
% 3.93/0.98  --bmc1_verbose                          false
% 3.93/0.98  --bmc1_dump_clauses_tptp                false
% 3.93/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.93/0.98  --bmc1_dump_file                        -
% 3.93/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.93/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.93/0.98  --bmc1_ucm_extend_mode                  1
% 3.93/0.98  --bmc1_ucm_init_mode                    2
% 3.93/0.98  --bmc1_ucm_cone_mode                    none
% 3.93/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.93/0.98  --bmc1_ucm_relax_model                  4
% 3.93/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.93/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.93/0.98  --bmc1_ucm_layered_model                none
% 3.93/0.98  --bmc1_ucm_max_lemma_size               10
% 3.93/0.98  
% 3.93/0.98  ------ AIG Options
% 3.93/0.98  
% 3.93/0.98  --aig_mode                              false
% 3.93/0.98  
% 3.93/0.98  ------ Instantiation Options
% 3.93/0.98  
% 3.93/0.98  --instantiation_flag                    true
% 3.93/0.98  --inst_sos_flag                         true
% 3.93/0.98  --inst_sos_phase                        true
% 3.93/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.93/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.93/0.98  --inst_lit_sel_side                     num_symb
% 3.93/0.98  --inst_solver_per_active                1400
% 3.93/0.98  --inst_solver_calls_frac                1.
% 3.93/0.98  --inst_passive_queue_type               priority_queues
% 3.93/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.93/0.98  --inst_passive_queues_freq              [25;2]
% 3.93/0.98  --inst_dismatching                      true
% 3.93/0.98  --inst_eager_unprocessed_to_passive     true
% 3.93/0.98  --inst_prop_sim_given                   true
% 3.93/0.98  --inst_prop_sim_new                     false
% 3.93/0.98  --inst_subs_new                         false
% 3.93/0.98  --inst_eq_res_simp                      false
% 3.93/0.98  --inst_subs_given                       false
% 3.93/0.98  --inst_orphan_elimination               true
% 3.93/0.98  --inst_learning_loop_flag               true
% 3.93/0.98  --inst_learning_start                   3000
% 3.93/0.98  --inst_learning_factor                  2
% 3.93/0.98  --inst_start_prop_sim_after_learn       3
% 3.93/0.98  --inst_sel_renew                        solver
% 3.93/0.98  --inst_lit_activity_flag                true
% 3.93/0.98  --inst_restr_to_given                   false
% 3.93/0.98  --inst_activity_threshold               500
% 3.93/0.98  --inst_out_proof                        true
% 3.93/0.98  
% 3.93/0.98  ------ Resolution Options
% 3.93/0.98  
% 3.93/0.98  --resolution_flag                       true
% 3.93/0.98  --res_lit_sel                           adaptive
% 3.93/0.98  --res_lit_sel_side                      none
% 3.93/0.98  --res_ordering                          kbo
% 3.93/0.98  --res_to_prop_solver                    active
% 3.93/0.98  --res_prop_simpl_new                    false
% 3.93/0.98  --res_prop_simpl_given                  true
% 3.93/0.98  --res_passive_queue_type                priority_queues
% 3.93/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.93/0.98  --res_passive_queues_freq               [15;5]
% 3.93/0.98  --res_forward_subs                      full
% 3.93/0.98  --res_backward_subs                     full
% 3.93/0.98  --res_forward_subs_resolution           true
% 3.93/0.98  --res_backward_subs_resolution          true
% 3.93/0.98  --res_orphan_elimination                true
% 3.93/0.98  --res_time_limit                        2.
% 3.93/0.98  --res_out_proof                         true
% 3.93/0.98  
% 3.93/0.98  ------ Superposition Options
% 3.93/0.98  
% 3.93/0.98  --superposition_flag                    true
% 3.93/0.98  --sup_passive_queue_type                priority_queues
% 3.93/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.93/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.93/0.98  --demod_completeness_check              fast
% 3.93/0.98  --demod_use_ground                      true
% 3.93/0.98  --sup_to_prop_solver                    passive
% 3.93/0.98  --sup_prop_simpl_new                    true
% 3.93/0.98  --sup_prop_simpl_given                  true
% 3.93/0.98  --sup_fun_splitting                     true
% 3.93/0.98  --sup_smt_interval                      50000
% 3.93/0.98  
% 3.93/0.98  ------ Superposition Simplification Setup
% 3.93/0.98  
% 3.93/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.93/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.93/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.93/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.93/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.93/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.93/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.93/0.98  --sup_immed_triv                        [TrivRules]
% 3.93/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.93/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.93/0.98  --sup_immed_bw_main                     []
% 3.93/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.93/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.93/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.93/0.98  --sup_input_bw                          []
% 3.93/0.98  
% 3.93/0.98  ------ Combination Options
% 3.93/0.98  
% 3.93/0.98  --comb_res_mult                         3
% 3.93/0.98  --comb_sup_mult                         2
% 3.93/0.98  --comb_inst_mult                        10
% 3.93/0.98  
% 3.93/0.98  ------ Debug Options
% 3.93/0.98  
% 3.93/0.98  --dbg_backtrace                         false
% 3.93/0.98  --dbg_dump_prop_clauses                 false
% 3.93/0.98  --dbg_dump_prop_clauses_file            -
% 3.93/0.98  --dbg_out_stat                          false
% 3.93/0.98  ------ Parsing...
% 3.93/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.93/0.98  
% 3.93/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 3.93/0.98  
% 3.93/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.93/0.98  
% 3.93/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.93/0.98  ------ Proving...
% 3.93/0.98  ------ Problem Properties 
% 3.93/0.98  
% 3.93/0.98  
% 3.93/0.98  clauses                                 32
% 3.93/0.98  conjectures                             8
% 3.93/0.98  EPR                                     8
% 3.93/0.98  Horn                                    30
% 3.93/0.98  unary                                   3
% 3.93/0.98  binary                                  10
% 3.93/0.98  lits                                    84
% 3.93/0.98  lits eq                                 10
% 3.93/0.98  fd_pure                                 0
% 3.93/0.98  fd_pseudo                               0
% 3.93/0.98  fd_cond                                 0
% 3.93/0.98  fd_pseudo_cond                          1
% 3.93/0.98  AC symbols                              0
% 3.93/0.98  
% 3.93/0.98  ------ Schedule dynamic 5 is on 
% 3.93/0.98  
% 3.93/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.93/0.98  
% 3.93/0.98  
% 3.93/0.98  ------ 
% 3.93/0.98  Current options:
% 3.93/0.98  ------ 
% 3.93/0.98  
% 3.93/0.98  ------ Input Options
% 3.93/0.98  
% 3.93/0.98  --out_options                           all
% 3.93/0.98  --tptp_safe_out                         true
% 3.93/0.98  --problem_path                          ""
% 3.93/0.98  --include_path                          ""
% 3.93/0.98  --clausifier                            res/vclausify_rel
% 3.93/0.98  --clausifier_options                    ""
% 3.93/0.98  --stdin                                 false
% 3.93/0.98  --stats_out                             all
% 3.93/0.98  
% 3.93/0.98  ------ General Options
% 3.93/0.98  
% 3.93/0.98  --fof                                   false
% 3.93/0.98  --time_out_real                         305.
% 3.93/0.98  --time_out_virtual                      -1.
% 3.93/0.98  --symbol_type_check                     false
% 3.93/0.98  --clausify_out                          false
% 3.93/0.98  --sig_cnt_out                           false
% 3.93/0.98  --trig_cnt_out                          false
% 3.93/0.98  --trig_cnt_out_tolerance                1.
% 3.93/0.98  --trig_cnt_out_sk_spl                   false
% 3.93/0.98  --abstr_cl_out                          false
% 3.93/0.98  
% 3.93/0.98  ------ Global Options
% 3.93/0.98  
% 3.93/0.98  --schedule                              default
% 3.93/0.98  --add_important_lit                     false
% 3.93/0.98  --prop_solver_per_cl                    1000
% 3.93/0.98  --min_unsat_core                        false
% 3.93/0.98  --soft_assumptions                      false
% 3.93/0.98  --soft_lemma_size                       3
% 3.93/0.98  --prop_impl_unit_size                   0
% 3.93/0.98  --prop_impl_unit                        []
% 3.93/0.98  --share_sel_clauses                     true
% 3.93/0.98  --reset_solvers                         false
% 3.93/0.98  --bc_imp_inh                            [conj_cone]
% 3.93/0.98  --conj_cone_tolerance                   3.
% 3.93/0.98  --extra_neg_conj                        none
% 3.93/0.98  --large_theory_mode                     true
% 3.93/0.98  --prolific_symb_bound                   200
% 3.93/0.98  --lt_threshold                          2000
% 3.93/0.98  --clause_weak_htbl                      true
% 3.93/0.98  --gc_record_bc_elim                     false
% 3.93/0.98  
% 3.93/0.98  ------ Preprocessing Options
% 3.93/0.98  
% 3.93/0.98  --preprocessing_flag                    true
% 3.93/0.98  --time_out_prep_mult                    0.1
% 3.93/0.98  --splitting_mode                        input
% 3.93/0.98  --splitting_grd                         true
% 3.93/0.98  --splitting_cvd                         false
% 3.93/0.98  --splitting_cvd_svl                     false
% 3.93/0.98  --splitting_nvd                         32
% 3.93/0.98  --sub_typing                            true
% 3.93/0.98  --prep_gs_sim                           true
% 3.93/0.98  --prep_unflatten                        true
% 3.93/0.98  --prep_res_sim                          true
% 3.93/0.98  --prep_upred                            true
% 3.93/0.98  --prep_sem_filter                       exhaustive
% 3.93/0.98  --prep_sem_filter_out                   false
% 3.93/0.98  --pred_elim                             true
% 3.93/0.98  --res_sim_input                         true
% 3.93/0.98  --eq_ax_congr_red                       true
% 3.93/0.98  --pure_diseq_elim                       true
% 3.93/0.98  --brand_transform                       false
% 3.93/0.98  --non_eq_to_eq                          false
% 3.93/0.98  --prep_def_merge                        true
% 3.93/0.98  --prep_def_merge_prop_impl              false
% 3.93/0.98  --prep_def_merge_mbd                    true
% 3.93/0.98  --prep_def_merge_tr_red                 false
% 3.93/0.98  --prep_def_merge_tr_cl                  false
% 3.93/0.98  --smt_preprocessing                     true
% 3.93/0.98  --smt_ac_axioms                         fast
% 3.93/0.98  --preprocessed_out                      false
% 3.93/0.98  --preprocessed_stats                    false
% 3.93/0.98  
% 3.93/0.98  ------ Abstraction refinement Options
% 3.93/0.98  
% 3.93/0.98  --abstr_ref                             []
% 3.93/0.98  --abstr_ref_prep                        false
% 3.93/0.98  --abstr_ref_until_sat                   false
% 3.93/0.98  --abstr_ref_sig_restrict                funpre
% 3.93/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.93/0.98  --abstr_ref_under                       []
% 3.93/0.98  
% 3.93/0.98  ------ SAT Options
% 3.93/0.98  
% 3.93/0.98  --sat_mode                              false
% 3.93/0.98  --sat_fm_restart_options                ""
% 3.93/0.98  --sat_gr_def                            false
% 3.93/0.98  --sat_epr_types                         true
% 3.93/0.98  --sat_non_cyclic_types                  false
% 3.93/0.98  --sat_finite_models                     false
% 3.93/0.98  --sat_fm_lemmas                         false
% 3.93/0.98  --sat_fm_prep                           false
% 3.93/0.98  --sat_fm_uc_incr                        true
% 3.93/0.98  --sat_out_model                         small
% 3.93/0.98  --sat_out_clauses                       false
% 3.93/0.98  
% 3.93/0.98  ------ QBF Options
% 3.93/0.98  
% 3.93/0.98  --qbf_mode                              false
% 3.93/0.98  --qbf_elim_univ                         false
% 3.93/0.98  --qbf_dom_inst                          none
% 3.93/0.98  --qbf_dom_pre_inst                      false
% 3.93/0.98  --qbf_sk_in                             false
% 3.93/0.98  --qbf_pred_elim                         true
% 3.93/0.98  --qbf_split                             512
% 3.93/0.98  
% 3.93/0.98  ------ BMC1 Options
% 3.93/0.98  
% 3.93/0.98  --bmc1_incremental                      false
% 3.93/0.98  --bmc1_axioms                           reachable_all
% 3.93/0.98  --bmc1_min_bound                        0
% 3.93/0.98  --bmc1_max_bound                        -1
% 3.93/0.98  --bmc1_max_bound_default                -1
% 3.93/0.98  --bmc1_symbol_reachability              true
% 3.93/0.98  --bmc1_property_lemmas                  false
% 3.93/0.98  --bmc1_k_induction                      false
% 3.93/0.98  --bmc1_non_equiv_states                 false
% 3.93/0.98  --bmc1_deadlock                         false
% 3.93/0.98  --bmc1_ucm                              false
% 3.93/0.98  --bmc1_add_unsat_core                   none
% 3.93/0.98  --bmc1_unsat_core_children              false
% 3.93/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.93/0.98  --bmc1_out_stat                         full
% 3.93/0.98  --bmc1_ground_init                      false
% 3.93/0.98  --bmc1_pre_inst_next_state              false
% 3.93/0.98  --bmc1_pre_inst_state                   false
% 3.93/0.98  --bmc1_pre_inst_reach_state             false
% 3.93/0.98  --bmc1_out_unsat_core                   false
% 3.93/0.98  --bmc1_aig_witness_out                  false
% 3.93/0.98  --bmc1_verbose                          false
% 3.93/0.98  --bmc1_dump_clauses_tptp                false
% 3.93/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.93/0.98  --bmc1_dump_file                        -
% 3.93/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.93/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.93/0.98  --bmc1_ucm_extend_mode                  1
% 3.93/0.98  --bmc1_ucm_init_mode                    2
% 3.93/0.98  --bmc1_ucm_cone_mode                    none
% 3.93/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.93/0.98  --bmc1_ucm_relax_model                  4
% 3.93/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.93/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.93/0.98  --bmc1_ucm_layered_model                none
% 3.93/0.98  --bmc1_ucm_max_lemma_size               10
% 3.93/0.98  
% 3.93/0.98  ------ AIG Options
% 3.93/0.98  
% 3.93/0.98  --aig_mode                              false
% 3.93/0.98  
% 3.93/0.98  ------ Instantiation Options
% 3.93/0.98  
% 3.93/0.98  --instantiation_flag                    true
% 3.93/0.98  --inst_sos_flag                         true
% 3.93/0.98  --inst_sos_phase                        true
% 3.93/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.93/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.93/0.98  --inst_lit_sel_side                     none
% 3.93/0.98  --inst_solver_per_active                1400
% 3.93/0.98  --inst_solver_calls_frac                1.
% 3.93/0.98  --inst_passive_queue_type               priority_queues
% 3.93/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.93/0.98  --inst_passive_queues_freq              [25;2]
% 3.93/0.98  --inst_dismatching                      true
% 3.93/0.98  --inst_eager_unprocessed_to_passive     true
% 3.93/0.98  --inst_prop_sim_given                   true
% 3.93/0.98  --inst_prop_sim_new                     false
% 3.93/0.98  --inst_subs_new                         false
% 3.93/0.98  --inst_eq_res_simp                      false
% 3.93/0.98  --inst_subs_given                       false
% 3.93/0.98  --inst_orphan_elimination               true
% 3.93/0.98  --inst_learning_loop_flag               true
% 3.93/0.98  --inst_learning_start                   3000
% 3.93/0.98  --inst_learning_factor                  2
% 3.93/0.98  --inst_start_prop_sim_after_learn       3
% 3.93/0.98  --inst_sel_renew                        solver
% 3.93/0.98  --inst_lit_activity_flag                true
% 3.93/0.98  --inst_restr_to_given                   false
% 3.93/0.98  --inst_activity_threshold               500
% 3.93/0.98  --inst_out_proof                        true
% 3.93/0.98  
% 3.93/0.98  ------ Resolution Options
% 3.93/0.98  
% 3.93/0.98  --resolution_flag                       false
% 3.93/0.98  --res_lit_sel                           adaptive
% 3.93/0.98  --res_lit_sel_side                      none
% 3.93/0.98  --res_ordering                          kbo
% 3.93/0.98  --res_to_prop_solver                    active
% 3.93/0.98  --res_prop_simpl_new                    false
% 3.93/0.98  --res_prop_simpl_given                  true
% 3.93/0.98  --res_passive_queue_type                priority_queues
% 3.93/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.93/0.98  --res_passive_queues_freq               [15;5]
% 3.93/0.98  --res_forward_subs                      full
% 3.93/0.98  --res_backward_subs                     full
% 3.93/0.98  --res_forward_subs_resolution           true
% 3.93/0.98  --res_backward_subs_resolution          true
% 3.93/0.98  --res_orphan_elimination                true
% 3.93/0.98  --res_time_limit                        2.
% 3.93/0.98  --res_out_proof                         true
% 3.93/0.98  
% 3.93/0.98  ------ Superposition Options
% 3.93/0.98  
% 3.93/0.98  --superposition_flag                    true
% 3.93/0.98  --sup_passive_queue_type                priority_queues
% 3.93/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.93/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.93/0.98  --demod_completeness_check              fast
% 3.93/0.98  --demod_use_ground                      true
% 3.93/0.98  --sup_to_prop_solver                    passive
% 3.93/0.98  --sup_prop_simpl_new                    true
% 3.93/0.98  --sup_prop_simpl_given                  true
% 3.93/0.98  --sup_fun_splitting                     true
% 3.93/0.98  --sup_smt_interval                      50000
% 3.93/0.98  
% 3.93/0.98  ------ Superposition Simplification Setup
% 3.93/0.98  
% 3.93/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.93/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.93/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.93/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.93/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.93/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.93/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.93/0.98  --sup_immed_triv                        [TrivRules]
% 3.93/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.93/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.93/0.98  --sup_immed_bw_main                     []
% 3.93/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.93/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.93/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.93/0.98  --sup_input_bw                          []
% 3.93/0.98  
% 3.93/0.98  ------ Combination Options
% 3.93/0.98  
% 3.93/0.98  --comb_res_mult                         3
% 3.93/0.98  --comb_sup_mult                         2
% 3.93/0.98  --comb_inst_mult                        10
% 3.93/0.98  
% 3.93/0.98  ------ Debug Options
% 3.93/0.98  
% 3.93/0.98  --dbg_backtrace                         false
% 3.93/0.98  --dbg_dump_prop_clauses                 false
% 3.93/0.98  --dbg_dump_prop_clauses_file            -
% 3.93/0.98  --dbg_out_stat                          false
% 3.93/0.98  
% 3.93/0.98  
% 3.93/0.98  
% 3.93/0.98  
% 3.93/0.98  ------ Proving...
% 3.93/0.98  
% 3.93/0.98  
% 3.93/0.98  % SZS status Theorem for theBenchmark.p
% 3.93/0.98  
% 3.93/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.93/0.98  
% 3.93/0.98  fof(f10,conjecture,(
% 3.93/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v5_tops_1(X2,X0) => (v4_tops_1(X2,X0) & v4_pre_topc(X2,X0))) & ((v4_tops_1(X3,X1) & v4_pre_topc(X3,X1)) => v5_tops_1(X3,X1)))))))),
% 3.93/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.93/0.98  
% 3.93/0.98  fof(f11,negated_conjecture,(
% 3.93/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v5_tops_1(X2,X0) => (v4_tops_1(X2,X0) & v4_pre_topc(X2,X0))) & ((v4_tops_1(X3,X1) & v4_pre_topc(X3,X1)) => v5_tops_1(X3,X1)))))))),
% 3.93/0.98    inference(negated_conjecture,[],[f10])).
% 3.93/0.98  
% 3.93/0.98  fof(f25,plain,(
% 3.93/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v4_pre_topc(X2,X0)) & v5_tops_1(X2,X0)) | (~v5_tops_1(X3,X1) & (v4_tops_1(X3,X1) & v4_pre_topc(X3,X1)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.93/0.98    inference(ennf_transformation,[],[f11])).
% 3.93/0.98  
% 3.93/0.98  fof(f26,plain,(
% 3.93/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v4_pre_topc(X2,X0)) & v5_tops_1(X2,X0)) | (~v5_tops_1(X3,X1) & v4_tops_1(X3,X1) & v4_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.93/0.98    inference(flattening,[],[f25])).
% 3.93/0.98  
% 3.93/0.98  fof(f35,plain,(
% 3.93/0.98    ( ! [X2,X0,X1] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v4_pre_topc(X2,X0)) & v5_tops_1(X2,X0)) | (~v5_tops_1(X3,X1) & v4_tops_1(X3,X1) & v4_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => ((((~v4_tops_1(X2,X0) | ~v4_pre_topc(X2,X0)) & v5_tops_1(X2,X0)) | (~v5_tops_1(sK3,X1) & v4_tops_1(sK3,X1) & v4_pre_topc(sK3,X1))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X1))))) )),
% 3.93/0.98    introduced(choice_axiom,[])).
% 3.93/0.98  
% 3.93/0.98  fof(f34,plain,(
% 3.93/0.98    ( ! [X0,X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v4_pre_topc(X2,X0)) & v5_tops_1(X2,X0)) | (~v5_tops_1(X3,X1) & v4_tops_1(X3,X1) & v4_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X3] : ((((~v4_tops_1(sK2,X0) | ~v4_pre_topc(sK2,X0)) & v5_tops_1(sK2,X0)) | (~v5_tops_1(X3,X1) & v4_tops_1(X3,X1) & v4_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.93/0.98    introduced(choice_axiom,[])).
% 3.93/0.98  
% 3.93/0.98  fof(f33,plain,(
% 3.93/0.98    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v4_pre_topc(X2,X0)) & v5_tops_1(X2,X0)) | (~v5_tops_1(X3,X1) & v4_tops_1(X3,X1) & v4_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) => (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v4_pre_topc(X2,X0)) & v5_tops_1(X2,X0)) | (~v5_tops_1(X3,sK1) & v4_tops_1(X3,sK1) & v4_pre_topc(X3,sK1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(sK1))) )),
% 3.93/0.98    introduced(choice_axiom,[])).
% 3.93/0.98  
% 3.93/0.98  fof(f32,plain,(
% 3.93/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v4_pre_topc(X2,X0)) & v5_tops_1(X2,X0)) | (~v5_tops_1(X3,X1) & v4_tops_1(X3,X1) & v4_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,sK0) | ~v4_pre_topc(X2,sK0)) & v5_tops_1(X2,sK0)) | (~v5_tops_1(X3,X1) & v4_tops_1(X3,X1) & v4_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 3.93/0.98    introduced(choice_axiom,[])).
% 3.93/0.98  
% 3.93/0.98  fof(f36,plain,(
% 3.93/0.98    ((((((~v4_tops_1(sK2,sK0) | ~v4_pre_topc(sK2,sK0)) & v5_tops_1(sK2,sK0)) | (~v5_tops_1(sK3,sK1) & v4_tops_1(sK3,sK1) & v4_pre_topc(sK3,sK1))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 3.93/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f26,f35,f34,f33,f32])).
% 3.93/0.98  
% 3.93/0.98  fof(f57,plain,(
% 3.93/0.98    v5_tops_1(sK2,sK0) | v4_pre_topc(sK3,sK1)),
% 3.93/0.98    inference(cnf_transformation,[],[f36])).
% 3.93/0.98  
% 3.93/0.98  fof(f55,plain,(
% 3.93/0.98    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.93/0.98    inference(cnf_transformation,[],[f36])).
% 3.93/0.98  
% 3.93/0.98  fof(f7,axiom,(
% 3.93/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1)))),
% 3.93/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.93/0.98  
% 3.93/0.98  fof(f20,plain,(
% 3.93/0.98    ! [X0] : (! [X1] : ((v5_tops_1(X1,X0) <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.93/0.98    inference(ennf_transformation,[],[f7])).
% 3.93/0.98  
% 3.93/0.98  fof(f31,plain,(
% 3.93/0.98    ! [X0] : (! [X1] : (((v5_tops_1(X1,X0) | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1) & (k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 | ~v5_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.93/0.98    inference(nnf_transformation,[],[f20])).
% 3.93/0.98  
% 3.93/0.98  fof(f48,plain,(
% 3.93/0.98    ( ! [X0,X1] : (k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 | ~v5_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.93/0.98    inference(cnf_transformation,[],[f31])).
% 3.93/0.98  
% 3.93/0.98  fof(f53,plain,(
% 3.93/0.98    l1_pre_topc(sK0)),
% 3.93/0.98    inference(cnf_transformation,[],[f36])).
% 3.93/0.98  
% 3.93/0.98  fof(f56,plain,(
% 3.93/0.98    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 3.93/0.98    inference(cnf_transformation,[],[f36])).
% 3.93/0.98  
% 3.93/0.98  fof(f5,axiom,(
% 3.93/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 3.93/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.93/0.98  
% 3.93/0.98  fof(f17,plain,(
% 3.93/0.98    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.93/0.98    inference(ennf_transformation,[],[f5])).
% 3.93/0.98  
% 3.93/0.98  fof(f18,plain,(
% 3.93/0.98    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.93/0.98    inference(flattening,[],[f17])).
% 3.93/0.98  
% 3.93/0.98  fof(f43,plain,(
% 3.93/0.98    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.93/0.98    inference(cnf_transformation,[],[f18])).
% 3.93/0.98  
% 3.93/0.98  fof(f54,plain,(
% 3.93/0.98    l1_pre_topc(sK1)),
% 3.93/0.98    inference(cnf_transformation,[],[f36])).
% 3.93/0.98  
% 3.93/0.98  fof(f49,plain,(
% 3.93/0.98    ( ! [X0,X1] : (v5_tops_1(X1,X0) | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.93/0.98    inference(cnf_transformation,[],[f31])).
% 3.93/0.98  
% 3.93/0.98  fof(f58,plain,(
% 3.93/0.98    v5_tops_1(sK2,sK0) | v4_tops_1(sK3,sK1)),
% 3.93/0.98    inference(cnf_transformation,[],[f36])).
% 3.93/0.98  
% 3.93/0.98  fof(f59,plain,(
% 3.93/0.98    v5_tops_1(sK2,sK0) | ~v5_tops_1(sK3,sK1)),
% 3.93/0.98    inference(cnf_transformation,[],[f36])).
% 3.93/0.98  
% 3.93/0.98  fof(f6,axiom,(
% 3.93/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)))))),
% 3.93/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.93/0.98  
% 3.93/0.98  fof(f19,plain,(
% 3.93/0.98    ! [X0] : (! [X1] : ((v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.93/0.98    inference(ennf_transformation,[],[f6])).
% 3.93/0.98  
% 3.93/0.98  fof(f29,plain,(
% 3.93/0.98    ! [X0] : (! [X1] : (((v4_tops_1(X1,X0) | (~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1))) & ((r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) | ~v4_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.93/0.98    inference(nnf_transformation,[],[f19])).
% 3.93/0.98  
% 3.93/0.98  fof(f30,plain,(
% 3.93/0.98    ! [X0] : (! [X1] : (((v4_tops_1(X1,X0) | ~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) & ((r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) | ~v4_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.93/0.98    inference(flattening,[],[f29])).
% 3.93/0.98  
% 3.93/0.98  fof(f46,plain,(
% 3.93/0.98    ( ! [X0,X1] : (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~v4_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.93/0.98    inference(cnf_transformation,[],[f30])).
% 3.93/0.98  
% 3.93/0.98  fof(f2,axiom,(
% 3.93/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)))),
% 3.93/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.93/0.98  
% 3.93/0.98  fof(f12,plain,(
% 3.93/0.98    ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.93/0.98    inference(ennf_transformation,[],[f2])).
% 3.93/0.98  
% 3.93/0.98  fof(f13,plain,(
% 3.93/0.98    ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.93/0.98    inference(flattening,[],[f12])).
% 3.93/0.98  
% 3.93/0.98  fof(f40,plain,(
% 3.93/0.98    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.93/0.98    inference(cnf_transformation,[],[f13])).
% 3.93/0.98  
% 3.93/0.98  fof(f4,axiom,(
% 3.93/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 3.93/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.93/0.98  
% 3.93/0.98  fof(f15,plain,(
% 3.93/0.98    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.93/0.98    inference(ennf_transformation,[],[f4])).
% 3.93/0.98  
% 3.93/0.98  fof(f16,plain,(
% 3.93/0.98    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.93/0.98    inference(flattening,[],[f15])).
% 3.93/0.98  
% 3.93/0.98  fof(f42,plain,(
% 3.93/0.98    ( ! [X2,X0,X1] : (r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.93/0.98    inference(cnf_transformation,[],[f16])).
% 3.93/0.98  
% 3.93/0.98  fof(f1,axiom,(
% 3.93/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.93/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.93/0.98  
% 3.93/0.98  fof(f27,plain,(
% 3.93/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.93/0.98    inference(nnf_transformation,[],[f1])).
% 3.93/0.98  
% 3.93/0.98  fof(f28,plain,(
% 3.93/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.93/0.98    inference(flattening,[],[f27])).
% 3.93/0.98  
% 3.93/0.98  fof(f39,plain,(
% 3.93/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.93/0.98    inference(cnf_transformation,[],[f28])).
% 3.93/0.98  
% 3.93/0.98  fof(f45,plain,(
% 3.93/0.98    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) | ~v4_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.93/0.98    inference(cnf_transformation,[],[f30])).
% 3.93/0.98  
% 3.93/0.98  fof(f8,axiom,(
% 3.93/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.93/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.93/0.98  
% 3.93/0.98  fof(f21,plain,(
% 3.93/0.98    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.93/0.98    inference(ennf_transformation,[],[f8])).
% 3.93/0.98  
% 3.93/0.98  fof(f22,plain,(
% 3.93/0.98    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.93/0.98    inference(flattening,[],[f21])).
% 3.93/0.98  
% 3.93/0.98  fof(f50,plain,(
% 3.93/0.98    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.93/0.98    inference(cnf_transformation,[],[f22])).
% 3.93/0.98  
% 3.93/0.98  fof(f3,axiom,(
% 3.93/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 3.93/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.93/0.98  
% 3.93/0.98  fof(f14,plain,(
% 3.93/0.98    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.93/0.98    inference(ennf_transformation,[],[f3])).
% 3.93/0.98  
% 3.93/0.98  fof(f41,plain,(
% 3.93/0.98    ( ! [X0,X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.93/0.98    inference(cnf_transformation,[],[f14])).
% 3.93/0.98  
% 3.93/0.98  fof(f47,plain,(
% 3.93/0.98    ( ! [X0,X1] : (v4_tops_1(X1,X0) | ~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.93/0.98    inference(cnf_transformation,[],[f30])).
% 3.93/0.98  
% 3.93/0.98  fof(f44,plain,(
% 3.93/0.98    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.93/0.98    inference(cnf_transformation,[],[f18])).
% 3.93/0.98  
% 3.93/0.98  fof(f52,plain,(
% 3.93/0.98    v2_pre_topc(sK0)),
% 3.93/0.98    inference(cnf_transformation,[],[f36])).
% 3.93/0.98  
% 3.93/0.98  fof(f9,axiom,(
% 3.93/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 3.93/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.93/0.98  
% 3.93/0.98  fof(f23,plain,(
% 3.93/0.98    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.93/0.98    inference(ennf_transformation,[],[f9])).
% 3.93/0.98  
% 3.93/0.98  fof(f24,plain,(
% 3.93/0.98    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.93/0.98    inference(flattening,[],[f23])).
% 3.93/0.98  
% 3.93/0.98  fof(f51,plain,(
% 3.93/0.98    ( ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.93/0.98    inference(cnf_transformation,[],[f24])).
% 3.93/0.98  
% 3.93/0.98  fof(f37,plain,(
% 3.93/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.93/0.98    inference(cnf_transformation,[],[f28])).
% 3.93/0.98  
% 3.93/0.98  fof(f64,plain,(
% 3.93/0.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.93/0.98    inference(equality_resolution,[],[f37])).
% 3.93/0.98  
% 3.93/0.98  fof(f62,plain,(
% 3.93/0.98    ~v4_tops_1(sK2,sK0) | ~v4_pre_topc(sK2,sK0) | ~v5_tops_1(sK3,sK1)),
% 3.93/0.98    inference(cnf_transformation,[],[f36])).
% 3.93/0.98  
% 3.93/0.98  fof(f61,plain,(
% 3.93/0.98    ~v4_tops_1(sK2,sK0) | ~v4_pre_topc(sK2,sK0) | v4_tops_1(sK3,sK1)),
% 3.93/0.98    inference(cnf_transformation,[],[f36])).
% 3.93/0.98  
% 3.93/0.98  fof(f60,plain,(
% 3.93/0.98    ~v4_tops_1(sK2,sK0) | ~v4_pre_topc(sK2,sK0) | v4_pre_topc(sK3,sK1)),
% 3.93/0.98    inference(cnf_transformation,[],[f36])).
% 3.93/0.98  
% 3.93/0.98  cnf(c_20,negated_conjecture,
% 3.93/0.98      ( v5_tops_1(sK2,sK0) | v4_pre_topc(sK3,sK1) ),
% 3.93/0.98      inference(cnf_transformation,[],[f57]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_1266,plain,
% 3.93/0.98      ( v5_tops_1(sK2,sK0) = iProver_top
% 3.93/0.98      | v4_pre_topc(sK3,sK1) = iProver_top ),
% 3.93/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_22,negated_conjecture,
% 3.93/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.93/0.98      inference(cnf_transformation,[],[f55]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_1264,plain,
% 3.93/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.93/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_12,plain,
% 3.93/0.98      ( ~ v5_tops_1(X0,X1)
% 3.93/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.93/0.98      | ~ l1_pre_topc(X1)
% 3.93/0.98      | k2_pre_topc(X1,k1_tops_1(X1,X0)) = X0 ),
% 3.93/0.98      inference(cnf_transformation,[],[f48]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_24,negated_conjecture,
% 3.93/0.98      ( l1_pre_topc(sK0) ),
% 3.93/0.98      inference(cnf_transformation,[],[f53]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_480,plain,
% 3.93/0.98      ( ~ v5_tops_1(X0,X1)
% 3.93/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.93/0.98      | k2_pre_topc(X1,k1_tops_1(X1,X0)) = X0
% 3.93/0.98      | sK0 != X1 ),
% 3.93/0.98      inference(resolution_lifted,[status(thm)],[c_12,c_24]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_481,plain,
% 3.93/0.98      ( ~ v5_tops_1(X0,sK0)
% 3.93/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.93/0.98      | k2_pre_topc(sK0,k1_tops_1(sK0,X0)) = X0 ),
% 3.93/0.98      inference(unflattening,[status(thm)],[c_480]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_1250,plain,
% 3.93/0.98      ( k2_pre_topc(sK0,k1_tops_1(sK0,X0)) = X0
% 3.93/0.98      | v5_tops_1(X0,sK0) != iProver_top
% 3.93/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.93/0.98      inference(predicate_to_equality,[status(thm)],[c_481]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_2403,plain,
% 3.93/0.98      ( k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = sK2
% 3.93/0.98      | v5_tops_1(sK2,sK0) != iProver_top ),
% 3.93/0.98      inference(superposition,[status(thm)],[c_1264,c_1250]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_2428,plain,
% 3.93/0.98      ( k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = sK2
% 3.93/0.98      | v4_pre_topc(sK3,sK1) = iProver_top ),
% 3.93/0.98      inference(superposition,[status(thm)],[c_1266,c_2403]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_21,negated_conjecture,
% 3.93/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 3.93/0.98      inference(cnf_transformation,[],[f56]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_1265,plain,
% 3.93/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 3.93/0.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_7,plain,
% 3.93/0.98      ( ~ v4_pre_topc(X0,X1)
% 3.93/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.93/0.98      | ~ l1_pre_topc(X1)
% 3.93/0.98      | k2_pre_topc(X1,X0) = X0 ),
% 3.93/0.98      inference(cnf_transformation,[],[f43]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_23,negated_conjecture,
% 3.93/0.98      ( l1_pre_topc(sK1) ),
% 3.93/0.98      inference(cnf_transformation,[],[f54]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_411,plain,
% 3.93/0.98      ( ~ v4_pre_topc(X0,X1)
% 3.93/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.93/0.98      | k2_pre_topc(X1,X0) = X0
% 3.93/0.98      | sK1 != X1 ),
% 3.93/0.98      inference(resolution_lifted,[status(thm)],[c_7,c_23]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_412,plain,
% 3.93/0.98      ( ~ v4_pre_topc(X0,sK1)
% 3.93/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.93/0.98      | k2_pre_topc(sK1,X0) = X0 ),
% 3.93/0.98      inference(unflattening,[status(thm)],[c_411]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_1255,plain,
% 3.93/0.98      ( k2_pre_topc(sK1,X0) = X0
% 3.93/0.98      | v4_pre_topc(X0,sK1) != iProver_top
% 3.93/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 3.93/0.98      inference(predicate_to_equality,[status(thm)],[c_412]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_2239,plain,
% 3.93/0.98      ( k2_pre_topc(sK1,sK3) = sK3
% 3.93/0.98      | v4_pre_topc(sK3,sK1) != iProver_top ),
% 3.93/0.98      inference(superposition,[status(thm)],[c_1265,c_1255]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_2458,plain,
% 3.93/0.98      ( k2_pre_topc(sK1,sK3) = sK3
% 3.93/0.98      | k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = sK2 ),
% 3.93/0.98      inference(superposition,[status(thm)],[c_2428,c_2239]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_11,plain,
% 3.93/0.98      ( v5_tops_1(X0,X1)
% 3.93/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.93/0.98      | ~ l1_pre_topc(X1)
% 3.93/0.98      | k2_pre_topc(X1,k1_tops_1(X1,X0)) != X0 ),
% 3.93/0.98      inference(cnf_transformation,[],[f49]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_495,plain,
% 3.93/0.98      ( v5_tops_1(X0,X1)
% 3.93/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.93/0.98      | k2_pre_topc(X1,k1_tops_1(X1,X0)) != X0
% 3.93/0.98      | sK0 != X1 ),
% 3.93/0.98      inference(resolution_lifted,[status(thm)],[c_11,c_24]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_496,plain,
% 3.93/0.98      ( v5_tops_1(X0,sK0)
% 3.93/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.93/0.98      | k2_pre_topc(sK0,k1_tops_1(sK0,X0)) != X0 ),
% 3.93/0.98      inference(unflattening,[status(thm)],[c_495]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_1249,plain,
% 3.93/0.98      ( k2_pre_topc(sK0,k1_tops_1(sK0,X0)) != X0
% 3.93/0.98      | v5_tops_1(X0,sK0) = iProver_top
% 3.93/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.93/0.98      inference(predicate_to_equality,[status(thm)],[c_496]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_2465,plain,
% 3.93/0.98      ( k2_pre_topc(sK1,sK3) = sK3
% 3.93/0.98      | v5_tops_1(sK2,sK0) = iProver_top
% 3.93/0.98      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.93/0.98      inference(superposition,[status(thm)],[c_2458,c_1249]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_29,plain,
% 3.93/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.93/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_30,plain,
% 3.93/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 3.93/0.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_19,negated_conjecture,
% 3.93/0.98      ( v5_tops_1(sK2,sK0) | v4_tops_1(sK3,sK1) ),
% 3.93/0.98      inference(cnf_transformation,[],[f58]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_32,plain,
% 3.93/0.98      ( v5_tops_1(sK2,sK0) = iProver_top
% 3.93/0.98      | v4_tops_1(sK3,sK1) = iProver_top ),
% 3.93/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_18,negated_conjecture,
% 3.93/0.98      ( ~ v5_tops_1(sK3,sK1) | v5_tops_1(sK2,sK0) ),
% 3.93/0.98      inference(cnf_transformation,[],[f59]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_33,plain,
% 3.93/0.98      ( v5_tops_1(sK3,sK1) != iProver_top
% 3.93/0.98      | v5_tops_1(sK2,sK0) = iProver_top ),
% 3.93/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_694,plain,( X0 = X0 ),theory(equality) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_1885,plain,
% 3.93/0.98      ( sK1 = sK1 ),
% 3.93/0.98      inference(instantiation,[status(thm)],[c_694]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_2101,plain,
% 3.93/0.98      ( k1_zfmisc_1(u1_struct_0(sK1)) = k1_zfmisc_1(u1_struct_0(sK1)) ),
% 3.93/0.98      inference(instantiation,[status(thm)],[c_694]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_2654,plain,
% 3.93/0.98      ( sK3 = sK3 ),
% 3.93/0.98      inference(instantiation,[status(thm)],[c_694]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_702,plain,
% 3.93/0.98      ( ~ v4_tops_1(X0,X1) | v4_tops_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.93/0.98      theory(equality) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_1398,plain,
% 3.93/0.98      ( ~ v4_tops_1(X0,X1) | v4_tops_1(X2,sK1) | X2 != X0 | sK1 != X1 ),
% 3.93/0.98      inference(instantiation,[status(thm)],[c_702]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_1597,plain,
% 3.93/0.98      ( ~ v4_tops_1(X0,sK1) | v4_tops_1(X1,sK1) | X1 != X0 | sK1 != sK1 ),
% 3.93/0.98      inference(instantiation,[status(thm)],[c_1398]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_2814,plain,
% 3.93/0.98      ( v4_tops_1(X0,sK1)
% 3.93/0.98      | ~ v4_tops_1(sK3,sK1)
% 3.93/0.98      | X0 != sK3
% 3.93/0.98      | sK1 != sK1 ),
% 3.93/0.98      inference(instantiation,[status(thm)],[c_1597]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_3349,plain,
% 3.93/0.98      ( v4_tops_1(k2_pre_topc(sK1,sK3),sK1)
% 3.93/0.98      | ~ v4_tops_1(sK3,sK1)
% 3.93/0.98      | k2_pre_topc(sK1,sK3) != sK3
% 3.93/0.98      | sK1 != sK1 ),
% 3.93/0.98      inference(instantiation,[status(thm)],[c_2814]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_3350,plain,
% 3.93/0.98      ( k2_pre_topc(sK1,sK3) != sK3
% 3.93/0.98      | sK1 != sK1
% 3.93/0.98      | v4_tops_1(k2_pre_topc(sK1,sK3),sK1) = iProver_top
% 3.93/0.98      | v4_tops_1(sK3,sK1) != iProver_top ),
% 3.93/0.98      inference(predicate_to_equality,[status(thm)],[c_3349]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_700,plain,
% 3.93/0.98      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.93/0.98      theory(equality) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_1358,plain,
% 3.93/0.98      ( ~ m1_subset_1(X0,X1)
% 3.93/0.98      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.93/0.98      | X2 != X0
% 3.93/0.98      | k1_zfmisc_1(u1_struct_0(sK1)) != X1 ),
% 3.93/0.98      inference(instantiation,[status(thm)],[c_700]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_1658,plain,
% 3.93/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.93/0.98      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.93/0.98      | X1 != X0
% 3.93/0.98      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 3.93/0.98      inference(instantiation,[status(thm)],[c_1358]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_2925,plain,
% 3.93/0.98      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.93/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.93/0.98      | X0 != sK3
% 3.93/0.98      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 3.93/0.98      inference(instantiation,[status(thm)],[c_1658]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_3364,plain,
% 3.93/0.98      ( m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 3.93/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.93/0.98      | k2_pre_topc(sK1,sK3) != sK3
% 3.93/0.98      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 3.93/0.98      inference(instantiation,[status(thm)],[c_2925]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_3365,plain,
% 3.93/0.98      ( k2_pre_topc(sK1,sK3) != sK3
% 3.93/0.98      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
% 3.93/0.98      | m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 3.93/0.98      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 3.93/0.98      inference(predicate_to_equality,[status(thm)],[c_3364]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_348,plain,
% 3.93/0.98      ( v5_tops_1(X0,X1)
% 3.93/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.93/0.98      | k2_pre_topc(X1,k1_tops_1(X1,X0)) != X0
% 3.93/0.98      | sK1 != X1 ),
% 3.93/0.98      inference(resolution_lifted,[status(thm)],[c_11,c_23]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_349,plain,
% 3.93/0.98      ( v5_tops_1(X0,sK1)
% 3.93/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.93/0.98      | k2_pre_topc(sK1,k1_tops_1(sK1,X0)) != X0 ),
% 3.93/0.98      inference(unflattening,[status(thm)],[c_348]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_3975,plain,
% 3.93/0.98      ( v5_tops_1(k2_pre_topc(sK1,sK3),sK1)
% 3.93/0.98      | ~ m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 3.93/0.98      | k2_pre_topc(sK1,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) != k2_pre_topc(sK1,sK3) ),
% 3.93/0.98      inference(instantiation,[status(thm)],[c_349]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_3985,plain,
% 3.93/0.98      ( k2_pre_topc(sK1,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) != k2_pre_topc(sK1,sK3)
% 3.93/0.98      | v5_tops_1(k2_pre_topc(sK1,sK3),sK1) = iProver_top
% 3.93/0.98      | m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 3.93/0.98      inference(predicate_to_equality,[status(thm)],[c_3975]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_695,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_1882,plain,
% 3.93/0.98      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 3.93/0.98      inference(instantiation,[status(thm)],[c_695]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_3011,plain,
% 3.93/0.98      ( X0 != sK3 | sK3 = X0 | sK3 != sK3 ),
% 3.93/0.98      inference(instantiation,[status(thm)],[c_1882]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_5018,plain,
% 3.93/0.98      ( k2_pre_topc(sK1,sK3) != sK3
% 3.93/0.98      | sK3 = k2_pre_topc(sK1,sK3)
% 3.93/0.98      | sK3 != sK3 ),
% 3.93/0.98      inference(instantiation,[status(thm)],[c_3011]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_704,plain,
% 3.93/0.98      ( ~ v5_tops_1(X0,X1) | v5_tops_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.93/0.98      theory(equality) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_1336,plain,
% 3.93/0.98      ( ~ v5_tops_1(X0,X1) | v5_tops_1(sK3,sK1) | sK1 != X1 | sK3 != X0 ),
% 3.93/0.98      inference(instantiation,[status(thm)],[c_704]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_1568,plain,
% 3.93/0.98      ( ~ v5_tops_1(X0,sK1)
% 3.93/0.98      | v5_tops_1(sK3,sK1)
% 3.93/0.98      | sK1 != sK1
% 3.93/0.98      | sK3 != X0 ),
% 3.93/0.98      inference(instantiation,[status(thm)],[c_1336]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_7458,plain,
% 3.93/0.98      ( ~ v5_tops_1(k2_pre_topc(sK1,sK3),sK1)
% 3.93/0.98      | v5_tops_1(sK3,sK1)
% 3.93/0.98      | sK1 != sK1
% 3.93/0.98      | sK3 != k2_pre_topc(sK1,sK3) ),
% 3.93/0.98      inference(instantiation,[status(thm)],[c_1568]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_7462,plain,
% 3.93/0.98      ( sK1 != sK1
% 3.93/0.98      | sK3 != k2_pre_topc(sK1,sK3)
% 3.93/0.98      | v5_tops_1(k2_pre_topc(sK1,sK3),sK1) != iProver_top
% 3.93/0.98      | v5_tops_1(sK3,sK1) = iProver_top ),
% 3.93/0.98      inference(predicate_to_equality,[status(thm)],[c_7458]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_9,plain,
% 3.93/0.98      ( ~ v4_tops_1(X0,X1)
% 3.93/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.93/0.98      | r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
% 3.93/0.98      | ~ l1_pre_topc(X1) ),
% 3.93/0.98      inference(cnf_transformation,[],[f46]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_378,plain,
% 3.93/0.98      ( ~ v4_tops_1(X0,X1)
% 3.93/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.93/0.98      | r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
% 3.93/0.98      | sK1 != X1 ),
% 3.93/0.98      inference(resolution_lifted,[status(thm)],[c_9,c_23]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_379,plain,
% 3.93/0.98      ( ~ v4_tops_1(X0,sK1)
% 3.93/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.93/0.98      | r1_tarski(X0,k2_pre_topc(sK1,k1_tops_1(sK1,X0))) ),
% 3.93/0.98      inference(unflattening,[status(thm)],[c_378]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_1257,plain,
% 3.93/0.98      ( v4_tops_1(X0,sK1) != iProver_top
% 3.93/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.93/0.98      | r1_tarski(X0,k2_pre_topc(sK1,k1_tops_1(sK1,X0))) = iProver_top ),
% 3.93/0.98      inference(predicate_to_equality,[status(thm)],[c_379]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_3,plain,
% 3.93/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.93/0.98      | ~ l1_pre_topc(X1)
% 3.93/0.98      | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0) ),
% 3.93/0.98      inference(cnf_transformation,[],[f40]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_456,plain,
% 3.93/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.93/0.98      | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0)
% 3.93/0.98      | sK1 != X1 ),
% 3.93/0.98      inference(resolution_lifted,[status(thm)],[c_3,c_23]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_457,plain,
% 3.93/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.93/0.98      | k2_pre_topc(sK1,k2_pre_topc(sK1,X0)) = k2_pre_topc(sK1,X0) ),
% 3.93/0.98      inference(unflattening,[status(thm)],[c_456]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_1252,plain,
% 3.93/0.98      ( k2_pre_topc(sK1,k2_pre_topc(sK1,X0)) = k2_pre_topc(sK1,X0)
% 3.93/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 3.93/0.98      inference(predicate_to_equality,[status(thm)],[c_457]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_1868,plain,
% 3.93/0.98      ( k2_pre_topc(sK1,k2_pre_topc(sK1,sK3)) = k2_pre_topc(sK1,sK3) ),
% 3.93/0.98      inference(superposition,[status(thm)],[c_1265,c_1252]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_5,plain,
% 3.93/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.93/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.93/0.98      | ~ r1_tarski(X0,X2)
% 3.93/0.98      | r1_tarski(k2_pre_topc(X1,X0),k2_pre_topc(X1,X2))
% 3.93/0.98      | ~ l1_pre_topc(X1) ),
% 3.93/0.98      inference(cnf_transformation,[],[f42]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_426,plain,
% 3.93/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.93/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.93/0.98      | ~ r1_tarski(X0,X2)
% 3.93/0.98      | r1_tarski(k2_pre_topc(X1,X0),k2_pre_topc(X1,X2))
% 3.93/0.98      | sK1 != X1 ),
% 3.93/0.98      inference(resolution_lifted,[status(thm)],[c_5,c_23]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_427,plain,
% 3.93/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.93/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.93/0.98      | ~ r1_tarski(X0,X1)
% 3.93/0.98      | r1_tarski(k2_pre_topc(sK1,X0),k2_pre_topc(sK1,X1)) ),
% 3.93/0.98      inference(unflattening,[status(thm)],[c_426]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_1254,plain,
% 3.93/0.98      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.93/0.98      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.93/0.98      | r1_tarski(X0,X1) != iProver_top
% 3.93/0.98      | r1_tarski(k2_pre_topc(sK1,X0),k2_pre_topc(sK1,X1)) = iProver_top ),
% 3.93/0.98      inference(predicate_to_equality,[status(thm)],[c_427]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_0,plain,
% 3.93/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.93/0.98      inference(cnf_transformation,[],[f39]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_1273,plain,
% 3.93/0.98      ( X0 = X1
% 3.93/0.98      | r1_tarski(X0,X1) != iProver_top
% 3.93/0.98      | r1_tarski(X1,X0) != iProver_top ),
% 3.93/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_2728,plain,
% 3.93/0.98      ( k2_pre_topc(sK1,X0) = k2_pre_topc(sK1,X1)
% 3.93/0.98      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.93/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.93/0.98      | r1_tarski(X1,X0) != iProver_top
% 3.93/0.98      | r1_tarski(k2_pre_topc(sK1,X0),k2_pre_topc(sK1,X1)) != iProver_top ),
% 3.93/0.98      inference(superposition,[status(thm)],[c_1254,c_1273]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_3498,plain,
% 3.93/0.98      ( k2_pre_topc(sK1,k2_pre_topc(sK1,sK3)) = k2_pre_topc(sK1,X0)
% 3.93/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.93/0.98      | m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.93/0.98      | r1_tarski(X0,k2_pre_topc(sK1,sK3)) != iProver_top
% 3.93/0.98      | r1_tarski(k2_pre_topc(sK1,sK3),k2_pre_topc(sK1,X0)) != iProver_top ),
% 3.93/0.98      inference(superposition,[status(thm)],[c_1868,c_2728]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_3505,plain,
% 3.93/0.98      ( k2_pre_topc(sK1,X0) = k2_pre_topc(sK1,sK3)
% 3.93/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.93/0.98      | m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.93/0.98      | r1_tarski(X0,k2_pre_topc(sK1,sK3)) != iProver_top
% 3.93/0.98      | r1_tarski(k2_pre_topc(sK1,sK3),k2_pre_topc(sK1,X0)) != iProver_top ),
% 3.93/0.98      inference(demodulation,[status(thm)],[c_3498,c_1868]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_6522,plain,
% 3.93/0.98      ( k2_pre_topc(sK1,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) = k2_pre_topc(sK1,sK3)
% 3.93/0.98      | v4_tops_1(k2_pre_topc(sK1,sK3),sK1) != iProver_top
% 3.93/0.98      | m1_subset_1(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.93/0.98      | m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.93/0.98      | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),k2_pre_topc(sK1,sK3)) != iProver_top ),
% 3.93/0.98      inference(superposition,[status(thm)],[c_1257,c_3505]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_10,plain,
% 3.93/0.98      ( ~ v4_tops_1(X0,X1)
% 3.93/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.93/0.98      | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
% 3.93/0.98      | ~ l1_pre_topc(X1) ),
% 3.93/0.98      inference(cnf_transformation,[],[f45]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_363,plain,
% 3.93/0.98      ( ~ v4_tops_1(X0,X1)
% 3.93/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.93/0.98      | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
% 3.93/0.98      | sK1 != X1 ),
% 3.93/0.98      inference(resolution_lifted,[status(thm)],[c_10,c_23]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_364,plain,
% 3.93/0.98      ( ~ v4_tops_1(X0,sK1)
% 3.93/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.93/0.98      | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,X0)),X0) ),
% 3.93/0.98      inference(unflattening,[status(thm)],[c_363]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_1258,plain,
% 3.93/0.98      ( v4_tops_1(X0,sK1) != iProver_top
% 3.93/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.93/0.98      | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,X0)),X0) = iProver_top ),
% 3.93/0.98      inference(predicate_to_equality,[status(thm)],[c_364]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_2719,plain,
% 3.93/0.98      ( v4_tops_1(k2_pre_topc(sK1,sK3),sK1) != iProver_top
% 3.93/0.98      | m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.93/0.98      | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),k2_pre_topc(sK1,sK3)) = iProver_top ),
% 3.93/0.98      inference(superposition,[status(thm)],[c_1868,c_1258]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_13,plain,
% 3.93/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.93/0.98      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.93/0.98      | ~ l1_pre_topc(X1) ),
% 3.93/0.98      inference(cnf_transformation,[],[f50]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_321,plain,
% 3.93/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.93/0.98      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.93/0.98      | sK1 != X1 ),
% 3.93/0.98      inference(resolution_lifted,[status(thm)],[c_13,c_23]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_322,plain,
% 3.93/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.93/0.98      | m1_subset_1(k1_tops_1(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 3.93/0.98      inference(unflattening,[status(thm)],[c_321]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_3978,plain,
% 3.93/0.98      ( m1_subset_1(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),k1_zfmisc_1(u1_struct_0(sK1)))
% 3.93/0.98      | ~ m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 3.93/0.98      inference(instantiation,[status(thm)],[c_322]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_3979,plain,
% 3.93/0.98      ( m1_subset_1(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 3.93/0.98      | m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 3.93/0.98      inference(predicate_to_equality,[status(thm)],[c_3978]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_9093,plain,
% 3.93/0.98      ( m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.93/0.98      | k2_pre_topc(sK1,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) = k2_pre_topc(sK1,sK3)
% 3.93/0.98      | v4_tops_1(k2_pre_topc(sK1,sK3),sK1) != iProver_top ),
% 3.93/0.98      inference(global_propositional_subsumption,
% 3.93/0.98                [status(thm)],
% 3.93/0.98                [c_6522,c_2719,c_3979]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_9094,plain,
% 3.93/0.98      ( k2_pre_topc(sK1,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) = k2_pre_topc(sK1,sK3)
% 3.93/0.98      | v4_tops_1(k2_pre_topc(sK1,sK3),sK1) != iProver_top
% 3.93/0.98      | m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 3.93/0.98      inference(renaming,[status(thm)],[c_9093]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_10199,plain,
% 3.93/0.98      ( v5_tops_1(sK2,sK0) = iProver_top ),
% 3.93/0.98      inference(global_propositional_subsumption,
% 3.93/0.98                [status(thm)],
% 3.93/0.98                [c_2465,c_29,c_30,c_32,c_33,c_1885,c_2101,c_2654,c_3350,
% 3.93/0.98                 c_3365,c_3985,c_5018,c_7462,c_9094]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_10203,plain,
% 3.93/0.98      ( k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = sK2 ),
% 3.93/0.98      inference(superposition,[status(thm)],[c_10199,c_2403]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_468,plain,
% 3.93/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.93/0.98      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.93/0.98      | sK0 != X1 ),
% 3.93/0.98      inference(resolution_lifted,[status(thm)],[c_13,c_24]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_469,plain,
% 3.93/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.93/0.98      | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.93/0.98      inference(unflattening,[status(thm)],[c_468]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_1251,plain,
% 3.93/0.98      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.93/0.98      | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.93/0.98      inference(predicate_to_equality,[status(thm)],[c_469]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_4,plain,
% 3.93/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.93/0.98      | r1_tarski(X0,k2_pre_topc(X1,X0))
% 3.93/0.98      | ~ l1_pre_topc(X1) ),
% 3.93/0.98      inference(cnf_transformation,[],[f41]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_591,plain,
% 3.93/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.93/0.98      | r1_tarski(X0,k2_pre_topc(X1,X0))
% 3.93/0.98      | sK0 != X1 ),
% 3.93/0.98      inference(resolution_lifted,[status(thm)],[c_4,c_24]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_592,plain,
% 3.93/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.93/0.98      | r1_tarski(X0,k2_pre_topc(sK0,X0)) ),
% 3.93/0.98      inference(unflattening,[status(thm)],[c_591]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_1243,plain,
% 3.93/0.98      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.93/0.98      | r1_tarski(X0,k2_pre_topc(sK0,X0)) = iProver_top ),
% 3.93/0.98      inference(predicate_to_equality,[status(thm)],[c_592]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_1856,plain,
% 3.93/0.98      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.93/0.98      | r1_tarski(k1_tops_1(sK0,X0),k2_pre_topc(sK0,k1_tops_1(sK0,X0))) = iProver_top ),
% 3.93/0.98      inference(superposition,[status(thm)],[c_1251,c_1243]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_10352,plain,
% 3.93/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.93/0.98      | r1_tarski(k1_tops_1(sK0,sK2),sK2) = iProver_top ),
% 3.93/0.98      inference(superposition,[status(thm)],[c_10203,c_1856]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_603,plain,
% 3.93/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.93/0.98      | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0)
% 3.93/0.98      | sK0 != X1 ),
% 3.93/0.98      inference(resolution_lifted,[status(thm)],[c_3,c_24]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_604,plain,
% 3.93/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.93/0.98      | k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) = k2_pre_topc(sK0,X0) ),
% 3.93/0.98      inference(unflattening,[status(thm)],[c_603]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_1242,plain,
% 3.93/0.98      ( k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) = k2_pre_topc(sK0,X0)
% 3.93/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.93/0.98      inference(predicate_to_equality,[status(thm)],[c_604]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_1857,plain,
% 3.93/0.98      ( k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,X0))) = k2_pre_topc(sK0,k1_tops_1(sK0,X0))
% 3.93/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.93/0.98      inference(superposition,[status(thm)],[c_1251,c_1242]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_3100,plain,
% 3.93/0.98      ( k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) = k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) ),
% 3.93/0.98      inference(superposition,[status(thm)],[c_1264,c_1857]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_8,plain,
% 3.93/0.98      ( v4_tops_1(X0,X1)
% 3.93/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.93/0.98      | ~ r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
% 3.93/0.98      | ~ r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
% 3.93/0.98      | ~ l1_pre_topc(X1) ),
% 3.93/0.98      inference(cnf_transformation,[],[f47]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_540,plain,
% 3.93/0.98      ( v4_tops_1(X0,X1)
% 3.93/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.93/0.98      | ~ r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
% 3.93/0.98      | ~ r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
% 3.93/0.98      | sK0 != X1 ),
% 3.93/0.98      inference(resolution_lifted,[status(thm)],[c_8,c_24]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_541,plain,
% 3.93/0.98      ( v4_tops_1(X0,sK0)
% 3.93/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.93/0.98      | ~ r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,X0)))
% 3.93/0.98      | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X0) ),
% 3.93/0.98      inference(unflattening,[status(thm)],[c_540]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_1246,plain,
% 3.93/0.98      ( v4_tops_1(X0,sK0) = iProver_top
% 3.93/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.93/0.98      | r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,X0))) != iProver_top
% 3.93/0.98      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X0) != iProver_top ),
% 3.93/0.98      inference(predicate_to_equality,[status(thm)],[c_541]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_3110,plain,
% 3.93/0.98      ( v4_tops_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),sK0) = iProver_top
% 3.93/0.98      | m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.93/0.98      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))),k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) != iProver_top
% 3.93/0.98      | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))))) != iProver_top ),
% 3.93/0.98      inference(superposition,[status(thm)],[c_3100,c_1246]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_10285,plain,
% 3.93/0.98      ( v4_tops_1(sK2,sK0) = iProver_top
% 3.93/0.98      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.93/0.98      | r1_tarski(k1_tops_1(sK0,sK2),sK2) != iProver_top
% 3.93/0.98      | r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) != iProver_top ),
% 3.93/0.98      inference(demodulation,[status(thm)],[c_10203,c_3110]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_10309,plain,
% 3.93/0.98      ( v4_tops_1(sK2,sK0) = iProver_top
% 3.93/0.98      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.93/0.98      | r1_tarski(k1_tops_1(sK0,sK2),sK2) != iProver_top
% 3.93/0.98      | r1_tarski(sK2,sK2) != iProver_top ),
% 3.93/0.98      inference(light_normalisation,[status(thm)],[c_10285,c_10203]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_6,plain,
% 3.93/0.98      ( v4_pre_topc(X0,X1)
% 3.93/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.93/0.98      | ~ v2_pre_topc(X1)
% 3.93/0.98      | ~ l1_pre_topc(X1)
% 3.93/0.98      | k2_pre_topc(X1,X0) != X0 ),
% 3.93/0.98      inference(cnf_transformation,[],[f44]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_25,negated_conjecture,
% 3.93/0.98      ( v2_pre_topc(sK0) ),
% 3.93/0.98      inference(cnf_transformation,[],[f52]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_293,plain,
% 3.93/0.98      ( v4_pre_topc(X0,X1)
% 3.93/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.93/0.98      | ~ l1_pre_topc(X1)
% 3.93/0.98      | k2_pre_topc(X1,X0) != X0
% 3.93/0.98      | sK0 != X1 ),
% 3.93/0.98      inference(resolution_lifted,[status(thm)],[c_6,c_25]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_294,plain,
% 3.93/0.98      ( v4_pre_topc(X0,sK0)
% 3.93/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.93/0.98      | ~ l1_pre_topc(sK0)
% 3.93/0.98      | k2_pre_topc(sK0,X0) != X0 ),
% 3.93/0.98      inference(unflattening,[status(thm)],[c_293]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_298,plain,
% 3.93/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.93/0.98      | v4_pre_topc(X0,sK0)
% 3.93/0.98      | k2_pre_topc(sK0,X0) != X0 ),
% 3.93/0.98      inference(global_propositional_subsumption,
% 3.93/0.98                [status(thm)],
% 3.93/0.98                [c_294,c_24]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_299,plain,
% 3.93/0.98      ( v4_pre_topc(X0,sK0)
% 3.93/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.93/0.98      | k2_pre_topc(sK0,X0) != X0 ),
% 3.93/0.98      inference(renaming,[status(thm)],[c_298]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_1262,plain,
% 3.93/0.98      ( k2_pre_topc(sK0,X0) != X0
% 3.93/0.98      | v4_pre_topc(X0,sK0) = iProver_top
% 3.93/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.93/0.98      inference(predicate_to_equality,[status(thm)],[c_299]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_3111,plain,
% 3.93/0.98      ( v4_pre_topc(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),sK0) = iProver_top
% 3.93/0.98      | m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.93/0.98      inference(superposition,[status(thm)],[c_3100,c_1262]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_1365,plain,
% 3.93/0.98      ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.93/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.93/0.98      inference(instantiation,[status(thm)],[c_469]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_1366,plain,
% 3.93/0.98      ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 3.93/0.98      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.93/0.98      inference(predicate_to_equality,[status(thm)],[c_1365]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_14,plain,
% 3.93/0.98      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
% 3.93/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.93/0.98      | ~ v2_pre_topc(X0)
% 3.93/0.98      | ~ l1_pre_topc(X0) ),
% 3.93/0.98      inference(cnf_transformation,[],[f51]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_275,plain,
% 3.93/0.98      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
% 3.93/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.93/0.98      | ~ l1_pre_topc(X0)
% 3.93/0.98      | sK0 != X0 ),
% 3.93/0.98      inference(resolution_lifted,[status(thm)],[c_14,c_25]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_276,plain,
% 3.93/0.98      ( v4_pre_topc(k2_pre_topc(sK0,X0),sK0)
% 3.93/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.93/0.98      | ~ l1_pre_topc(sK0) ),
% 3.93/0.98      inference(unflattening,[status(thm)],[c_275]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_280,plain,
% 3.93/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.93/0.98      | v4_pre_topc(k2_pre_topc(sK0,X0),sK0) ),
% 3.93/0.98      inference(global_propositional_subsumption,
% 3.93/0.98                [status(thm)],
% 3.93/0.98                [c_276,c_24]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_281,plain,
% 3.93/0.98      ( v4_pre_topc(k2_pre_topc(sK0,X0),sK0)
% 3.93/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.93/0.98      inference(renaming,[status(thm)],[c_280]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_1487,plain,
% 3.93/0.98      ( v4_pre_topc(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),sK0)
% 3.93/0.98      | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.93/0.98      inference(instantiation,[status(thm)],[c_281]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_1488,plain,
% 3.93/0.98      ( v4_pre_topc(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),sK0) = iProver_top
% 3.93/0.98      | m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.93/0.98      inference(predicate_to_equality,[status(thm)],[c_1487]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_3326,plain,
% 3.93/0.98      ( v4_pre_topc(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),sK0) = iProver_top ),
% 3.93/0.98      inference(global_propositional_subsumption,
% 3.93/0.98                [status(thm)],
% 3.93/0.98                [c_3111,c_29,c_1366,c_1488]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_10304,plain,
% 3.93/0.98      ( v4_pre_topc(sK2,sK0) = iProver_top ),
% 3.93/0.98      inference(demodulation,[status(thm)],[c_10203,c_3326]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_2,plain,
% 3.93/0.98      ( r1_tarski(X0,X0) ),
% 3.93/0.98      inference(cnf_transformation,[],[f64]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_1817,plain,
% 3.93/0.98      ( r1_tarski(sK2,sK2) ),
% 3.93/0.98      inference(instantiation,[status(thm)],[c_2]) ).
% 3.93/0.98  
% 3.93/0.98  cnf(c_1818,plain,
% 3.93/0.98      ( r1_tarski(sK2,sK2) = iProver_top ),
% 3.93/0.98      inference(predicate_to_equality,[status(thm)],[c_1817]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_1526,plain,
% 3.93/0.99      ( ~ v4_pre_topc(sK3,sK1)
% 3.93/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.93/0.99      | k2_pre_topc(sK1,sK3) = sK3 ),
% 3.93/0.99      inference(instantiation,[status(thm)],[c_412]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_1527,plain,
% 3.93/0.99      ( k2_pre_topc(sK1,sK3) = sK3
% 3.93/0.99      | v4_pre_topc(sK3,sK1) != iProver_top
% 3.93/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 3.93/0.99      inference(predicate_to_equality,[status(thm)],[c_1526]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_15,negated_conjecture,
% 3.93/0.99      ( ~ v5_tops_1(sK3,sK1)
% 3.93/0.99      | ~ v4_tops_1(sK2,sK0)
% 3.93/0.99      | ~ v4_pre_topc(sK2,sK0) ),
% 3.93/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_36,plain,
% 3.93/0.99      ( v5_tops_1(sK3,sK1) != iProver_top
% 3.93/0.99      | v4_tops_1(sK2,sK0) != iProver_top
% 3.93/0.99      | v4_pre_topc(sK2,sK0) != iProver_top ),
% 3.93/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_16,negated_conjecture,
% 3.93/0.99      ( v4_tops_1(sK3,sK1)
% 3.93/0.99      | ~ v4_tops_1(sK2,sK0)
% 3.93/0.99      | ~ v4_pre_topc(sK2,sK0) ),
% 3.93/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_35,plain,
% 3.93/0.99      ( v4_tops_1(sK3,sK1) = iProver_top
% 3.93/0.99      | v4_tops_1(sK2,sK0) != iProver_top
% 3.93/0.99      | v4_pre_topc(sK2,sK0) != iProver_top ),
% 3.93/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_17,negated_conjecture,
% 3.93/0.99      ( ~ v4_tops_1(sK2,sK0)
% 3.93/0.99      | v4_pre_topc(sK3,sK1)
% 3.93/0.99      | ~ v4_pre_topc(sK2,sK0) ),
% 3.93/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_34,plain,
% 3.93/0.99      ( v4_tops_1(sK2,sK0) != iProver_top
% 3.93/0.99      | v4_pre_topc(sK3,sK1) = iProver_top
% 3.93/0.99      | v4_pre_topc(sK2,sK0) != iProver_top ),
% 3.93/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(contradiction,plain,
% 3.93/0.99      ( $false ),
% 3.93/0.99      inference(minisat,
% 3.93/0.99                [status(thm)],
% 3.93/0.99                [c_10352,c_10309,c_10304,c_9094,c_7462,c_5018,c_3985,
% 3.93/0.99                 c_3365,c_3350,c_2654,c_2101,c_1885,c_1818,c_1527,c_36,
% 3.93/0.99                 c_35,c_34,c_30,c_29]) ).
% 3.93/0.99  
% 3.93/0.99  
% 3.93/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.93/0.99  
% 3.93/0.99  ------                               Statistics
% 3.93/0.99  
% 3.93/0.99  ------ General
% 3.93/0.99  
% 3.93/0.99  abstr_ref_over_cycles:                  0
% 3.93/0.99  abstr_ref_under_cycles:                 0
% 3.93/0.99  gc_basic_clause_elim:                   0
% 3.93/0.99  forced_gc_time:                         0
% 3.93/0.99  parsing_time:                           0.007
% 3.93/0.99  unif_index_cands_time:                  0.
% 3.93/0.99  unif_index_add_time:                    0.
% 3.93/0.99  orderings_time:                         0.
% 3.93/0.99  out_proof_time:                         0.021
% 3.93/0.99  total_time:                             0.428
% 3.93/0.99  num_of_symbols:                         46
% 3.93/0.99  num_of_terms:                           8909
% 3.93/0.99  
% 3.93/0.99  ------ Preprocessing
% 3.93/0.99  
% 3.93/0.99  num_of_splits:                          0
% 3.93/0.99  num_of_split_atoms:                     0
% 3.93/0.99  num_of_reused_defs:                     0
% 3.93/0.99  num_eq_ax_congr_red:                    2
% 3.93/0.99  num_of_sem_filtered_clauses:            1
% 3.93/0.99  num_of_subtypes:                        0
% 3.93/0.99  monotx_restored_types:                  0
% 3.93/0.99  sat_num_of_epr_types:                   0
% 3.93/0.99  sat_num_of_non_cyclic_types:            0
% 3.93/0.99  sat_guarded_non_collapsed_types:        0
% 3.93/0.99  num_pure_diseq_elim:                    0
% 3.93/0.99  simp_replaced_by:                       0
% 3.93/0.99  res_preprocessed:                       112
% 3.93/0.99  prep_upred:                             0
% 3.93/0.99  prep_unflattend:                        22
% 3.93/0.99  smt_new_axioms:                         0
% 3.93/0.99  pred_elim_cands:                        7
% 3.93/0.99  pred_elim:                              2
% 3.93/0.99  pred_elim_cl:                           -7
% 3.93/0.99  pred_elim_cycles:                       3
% 3.93/0.99  merged_defs:                            0
% 3.93/0.99  merged_defs_ncl:                        0
% 3.93/0.99  bin_hyper_res:                          0
% 3.93/0.99  prep_cycles:                            3
% 3.93/0.99  pred_elim_time:                         0.004
% 3.93/0.99  splitting_time:                         0.
% 3.93/0.99  sem_filter_time:                        0.
% 3.93/0.99  monotx_time:                            0.
% 3.93/0.99  subtype_inf_time:                       0.
% 3.93/0.99  
% 3.93/0.99  ------ Problem properties
% 3.93/0.99  
% 3.93/0.99  clauses:                                32
% 3.93/0.99  conjectures:                            8
% 3.93/0.99  epr:                                    8
% 3.93/0.99  horn:                                   30
% 3.93/0.99  ground:                                 8
% 3.93/0.99  unary:                                  3
% 3.93/0.99  binary:                                 10
% 3.93/0.99  lits:                                   84
% 3.93/0.99  lits_eq:                                10
% 3.93/0.99  fd_pure:                                0
% 3.93/0.99  fd_pseudo:                              0
% 3.93/0.99  fd_cond:                                0
% 3.93/0.99  fd_pseudo_cond:                         1
% 3.93/0.99  ac_symbols:                             0
% 3.93/0.99  
% 3.93/0.99  ------ Propositional Solver
% 3.93/0.99  
% 3.93/0.99  prop_solver_calls:                      26
% 3.93/0.99  prop_fast_solver_calls:                 1398
% 3.93/0.99  smt_solver_calls:                       0
% 3.93/0.99  smt_fast_solver_calls:                  0
% 3.93/0.99  prop_num_of_clauses:                    5519
% 3.93/0.99  prop_preprocess_simplified:             9453
% 3.93/0.99  prop_fo_subsumed:                       39
% 3.93/0.99  prop_solver_time:                       0.
% 3.93/0.99  smt_solver_time:                        0.
% 3.93/0.99  smt_fast_solver_time:                   0.
% 3.93/0.99  prop_fast_solver_time:                  0.
% 3.93/0.99  prop_unsat_core_time:                   0.
% 3.93/0.99  
% 3.93/0.99  ------ QBF
% 3.93/0.99  
% 3.93/0.99  qbf_q_res:                              0
% 3.93/0.99  qbf_num_tautologies:                    0
% 3.93/0.99  qbf_prep_cycles:                        0
% 3.93/0.99  
% 3.93/0.99  ------ BMC1
% 3.93/0.99  
% 3.93/0.99  bmc1_current_bound:                     -1
% 3.93/0.99  bmc1_last_solved_bound:                 -1
% 3.93/0.99  bmc1_unsat_core_size:                   -1
% 3.93/0.99  bmc1_unsat_core_parents_size:           -1
% 3.93/0.99  bmc1_merge_next_fun:                    0
% 3.93/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.93/0.99  
% 3.93/0.99  ------ Instantiation
% 3.93/0.99  
% 3.93/0.99  inst_num_of_clauses:                    1575
% 3.93/0.99  inst_num_in_passive:                    94
% 3.93/0.99  inst_num_in_active:                     942
% 3.93/0.99  inst_num_in_unprocessed:                539
% 3.93/0.99  inst_num_of_loops:                      1020
% 3.93/0.99  inst_num_of_learning_restarts:          0
% 3.93/0.99  inst_num_moves_active_passive:          73
% 3.93/0.99  inst_lit_activity:                      0
% 3.93/0.99  inst_lit_activity_moves:                0
% 3.93/0.99  inst_num_tautologies:                   0
% 3.93/0.99  inst_num_prop_implied:                  0
% 3.93/0.99  inst_num_existing_simplified:           0
% 3.93/0.99  inst_num_eq_res_simplified:             0
% 3.93/0.99  inst_num_child_elim:                    0
% 3.93/0.99  inst_num_of_dismatching_blockings:      352
% 3.93/0.99  inst_num_of_non_proper_insts:           1897
% 3.93/0.99  inst_num_of_duplicates:                 0
% 3.93/0.99  inst_inst_num_from_inst_to_res:         0
% 3.93/0.99  inst_dismatching_checking_time:         0.
% 3.93/0.99  
% 3.93/0.99  ------ Resolution
% 3.93/0.99  
% 3.93/0.99  res_num_of_clauses:                     0
% 3.93/0.99  res_num_in_passive:                     0
% 3.93/0.99  res_num_in_active:                      0
% 3.93/0.99  res_num_of_loops:                       115
% 3.93/0.99  res_forward_subset_subsumed:            143
% 3.93/0.99  res_backward_subset_subsumed:           0
% 3.93/0.99  res_forward_subsumed:                   0
% 3.93/0.99  res_backward_subsumed:                  0
% 3.93/0.99  res_forward_subsumption_resolution:     0
% 3.93/0.99  res_backward_subsumption_resolution:    0
% 3.93/0.99  res_clause_to_clause_subsumption:       2212
% 3.93/0.99  res_orphan_elimination:                 0
% 3.93/0.99  res_tautology_del:                      207
% 3.93/0.99  res_num_eq_res_simplified:              0
% 3.93/0.99  res_num_sel_changes:                    0
% 3.93/0.99  res_moves_from_active_to_pass:          0
% 3.93/0.99  
% 3.93/0.99  ------ Superposition
% 3.93/0.99  
% 3.93/0.99  sup_time_total:                         0.
% 3.93/0.99  sup_time_generating:                    0.
% 3.93/0.99  sup_time_sim_full:                      0.
% 3.93/0.99  sup_time_sim_immed:                     0.
% 3.93/0.99  
% 3.93/0.99  sup_num_of_clauses:                     386
% 3.93/0.99  sup_num_in_active:                      171
% 3.93/0.99  sup_num_in_passive:                     215
% 3.93/0.99  sup_num_of_loops:                       202
% 3.93/0.99  sup_fw_superposition:                   261
% 3.93/0.99  sup_bw_superposition:                   252
% 3.93/0.99  sup_immediate_simplified:               195
% 3.93/0.99  sup_given_eliminated:                   0
% 3.93/0.99  comparisons_done:                       0
% 3.93/0.99  comparisons_avoided:                    27
% 3.93/0.99  
% 3.93/0.99  ------ Simplifications
% 3.93/0.99  
% 3.93/0.99  
% 3.93/0.99  sim_fw_subset_subsumed:                 31
% 3.93/0.99  sim_bw_subset_subsumed:                 9
% 3.93/0.99  sim_fw_subsumed:                        61
% 3.93/0.99  sim_bw_subsumed:                        3
% 3.93/0.99  sim_fw_subsumption_res:                 0
% 3.93/0.99  sim_bw_subsumption_res:                 0
% 3.93/0.99  sim_tautology_del:                      6
% 3.93/0.99  sim_eq_tautology_del:                   23
% 3.93/0.99  sim_eq_res_simp:                        0
% 3.93/0.99  sim_fw_demodulated:                     126
% 3.93/0.99  sim_bw_demodulated:                     22
% 3.93/0.99  sim_light_normalised:                   38
% 3.93/0.99  sim_joinable_taut:                      0
% 3.93/0.99  sim_joinable_simp:                      0
% 3.93/0.99  sim_ac_normalised:                      0
% 3.93/0.99  sim_smt_subsumption:                    0
% 3.93/0.99  
%------------------------------------------------------------------------------
