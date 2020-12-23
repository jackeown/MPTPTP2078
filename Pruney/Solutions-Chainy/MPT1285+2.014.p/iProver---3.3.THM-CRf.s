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
% DateTime   : Thu Dec  3 12:15:55 EST 2020

% Result     : Theorem 2.83s
% Output     : CNFRefutation 2.83s
% Verified   : 
% Statistics : Number of formulae       :  172 (1350 expanded)
%              Number of clauses        :  116 ( 369 expanded)
%              Number of leaves         :   15 ( 444 expanded)
%              Depth                    :   22
%              Number of atoms          :  657 (11945 expanded)
%              Number of equality atoms :  181 ( 494 expanded)
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
                 => ( ( v6_tops_1(X2,X0)
                     => ( v4_tops_1(X2,X0)
                        & v3_pre_topc(X2,X0) ) )
                    & ( ( v4_tops_1(X3,X1)
                        & v3_pre_topc(X3,X1) )
                     => v6_tops_1(X3,X1) ) ) ) ) ) ) ),
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
                   => ( ( v6_tops_1(X2,X0)
                       => ( v4_tops_1(X2,X0)
                          & v3_pre_topc(X2,X0) ) )
                      & ( ( v4_tops_1(X3,X1)
                          & v3_pre_topc(X3,X1) )
                       => v6_tops_1(X3,X1) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ v4_tops_1(X2,X0)
                        | ~ v3_pre_topc(X2,X0) )
                      & v6_tops_1(X2,X0) )
                    | ( ~ v6_tops_1(X3,X1)
                      & v4_tops_1(X3,X1)
                      & v3_pre_topc(X3,X1) ) )
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
                        | ~ v3_pre_topc(X2,X0) )
                      & v6_tops_1(X2,X0) )
                    | ( ~ v6_tops_1(X3,X1)
                      & v4_tops_1(X3,X1)
                      & v3_pre_topc(X3,X1) ) )
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
                | ~ v3_pre_topc(X2,X0) )
              & v6_tops_1(X2,X0) )
            | ( ~ v6_tops_1(X3,X1)
              & v4_tops_1(X3,X1)
              & v3_pre_topc(X3,X1) ) )
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ( ( ( ~ v4_tops_1(X2,X0)
              | ~ v3_pre_topc(X2,X0) )
            & v6_tops_1(X2,X0) )
          | ( ~ v6_tops_1(sK3,X1)
            & v4_tops_1(sK3,X1)
            & v3_pre_topc(sK3,X1) ) )
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ( ( ( ~ v4_tops_1(X2,X0)
                    | ~ v3_pre_topc(X2,X0) )
                  & v6_tops_1(X2,X0) )
                | ( ~ v6_tops_1(X3,X1)
                  & v4_tops_1(X3,X1)
                  & v3_pre_topc(X3,X1) ) )
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X3] :
            ( ( ( ( ~ v4_tops_1(sK2,X0)
                  | ~ v3_pre_topc(sK2,X0) )
                & v6_tops_1(sK2,X0) )
              | ( ~ v6_tops_1(X3,X1)
                & v4_tops_1(X3,X1)
                & v3_pre_topc(X3,X1) ) )
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ v4_tops_1(X2,X0)
                        | ~ v3_pre_topc(X2,X0) )
                      & v6_tops_1(X2,X0) )
                    | ( ~ v6_tops_1(X3,X1)
                      & v4_tops_1(X3,X1)
                      & v3_pre_topc(X3,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ( ( ( ~ v4_tops_1(X2,X0)
                      | ~ v3_pre_topc(X2,X0) )
                    & v6_tops_1(X2,X0) )
                  | ( ~ v6_tops_1(X3,sK1)
                    & v4_tops_1(X3,sK1)
                    & v3_pre_topc(X3,sK1) ) )
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
                          | ~ v3_pre_topc(X2,X0) )
                        & v6_tops_1(X2,X0) )
                      | ( ~ v6_tops_1(X3,X1)
                        & v4_tops_1(X3,X1)
                        & v3_pre_topc(X3,X1) ) )
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ v4_tops_1(X2,sK0)
                        | ~ v3_pre_topc(X2,sK0) )
                      & v6_tops_1(X2,sK0) )
                    | ( ~ v6_tops_1(X3,X1)
                      & v4_tops_1(X3,X1)
                      & v3_pre_topc(X3,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ( ( ( ~ v4_tops_1(sK2,sK0)
          | ~ v3_pre_topc(sK2,sK0) )
        & v6_tops_1(sK2,sK0) )
      | ( ~ v6_tops_1(sK3,sK1)
        & v4_tops_1(sK3,sK1)
        & v3_pre_topc(sK3,sK1) ) )
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f32,f31,f30,f29])).

fof(f51,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f33])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v6_tops_1(X1,X0)
          <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v6_tops_1(X1,X0)
          <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v6_tops_1(X1,X0)
              | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1 )
            & ( k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1
              | ~ v6_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1
      | ~ v6_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f49,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f52,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f33])).

fof(f53,plain,
    ( v6_tops_1(sK2,sK0)
    | v3_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f54,plain,
    ( v6_tops_1(sK2,sK0)
    | v4_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f55,plain,
    ( v6_tops_1(sK2,sK0)
    | ~ v6_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f50,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v6_tops_1(X1,X0)
      | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

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

fof(f36,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

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

fof(f39,plain,(
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
             => ( ( r1_tarski(X1,X2)
                  & v3_pre_topc(X1,X0) )
               => r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v4_tops_1(X1,X0)
      | ~ r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
      | ~ r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f56,plain,
    ( ~ v4_tops_1(sK2,sK0)
    | ~ v3_pre_topc(sK2,sK0)
    | v3_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f57,plain,
    ( ~ v4_tops_1(sK2,sK0)
    | ~ v3_pre_topc(sK2,sK0)
    | v4_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f58,plain,
    ( ~ v4_tops_1(sK2,sK0)
    | ~ v3_pre_topc(sK2,sK0)
    | ~ v6_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f33])).

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
    inference(ennf_transformation,[],[f7])).

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
    inference(flattening,[],[f18])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X2,X0)
      | k1_tops_1(X0,X2) != X2
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f48,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f60,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f34])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1426,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_9,plain,
    ( ~ v6_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,k2_pre_topc(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_23,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_530,plain,
    ( ~ v6_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,k2_pre_topc(X1,X0)) = X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_23])).

cnf(c_531,plain,
    ( ~ v6_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,k2_pre_topc(sK0,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_530])).

cnf(c_1408,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,X0)) = X0
    | v6_tops_1(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_531])).

cnf(c_2557,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = sK2
    | v6_tops_1(sK2,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1426,c_1408])).

cnf(c_28,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_29,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_19,negated_conjecture,
    ( v3_pre_topc(sK3,sK1)
    | v6_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_30,plain,
    ( v3_pre_topc(sK3,sK1) = iProver_top
    | v6_tops_1(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_18,negated_conjecture,
    ( v6_tops_1(sK2,sK0)
    | v4_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_31,plain,
    ( v6_tops_1(sK2,sK0) = iProver_top
    | v4_tops_1(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_17,negated_conjecture,
    ( ~ v6_tops_1(sK3,sK1)
    | v6_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_32,plain,
    ( v6_tops_1(sK3,sK1) != iProver_top
    | v6_tops_1(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_22,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_467,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_22])).

cnf(c_468,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k2_pre_topc(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_467])).

cnf(c_1712,plain,
    ( m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_468])).

cnf(c_1713,plain,
    ( m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1712])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_455,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_22])).

cnf(c_456,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(X0,k2_pre_topc(sK1,X0)) ),
    inference(unflattening,[status(thm)],[c_455])).

cnf(c_1725,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(sK3,k2_pre_topc(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_456])).

cnf(c_1726,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(sK3,k2_pre_topc(sK1,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1725])).

cnf(c_8,plain,
    ( v6_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,k2_pre_topc(X1,X0)) != X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_392,plain,
    ( v6_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,k2_pre_topc(X1,X0)) != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_22])).

cnf(c_393,plain,
    ( v6_tops_1(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,k2_pre_topc(sK1,X0)) != X0 ),
    inference(unflattening,[status(thm)],[c_392])).

cnf(c_1734,plain,
    ( v6_tops_1(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) != sK3 ),
    inference(instantiation,[status(thm)],[c_393])).

cnf(c_1735,plain,
    ( k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) != sK3
    | v6_tops_1(sK3,sK1) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1734])).

cnf(c_1737,plain,
    ( ~ v6_tops_1(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_531])).

cnf(c_1738,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = sK2
    | v6_tops_1(sK2,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1737])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1844,plain,
    ( ~ r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3)
    | ~ r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))
    | k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) = sK3 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1845,plain,
    ( k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) = sK3
    | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3) != iProver_top
    | r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1844])).

cnf(c_7,plain,
    ( ~ v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_407,plain,
    ( ~ v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_22])).

cnf(c_408,plain,
    ( ~ v4_tops_1(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,X0)),X0) ),
    inference(unflattening,[status(thm)],[c_407])).

cnf(c_1855,plain,
    ( ~ v4_tops_1(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3) ),
    inference(instantiation,[status(thm)],[c_408])).

cnf(c_1856,plain,
    ( v4_tops_1(sK3,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1855])).

cnf(c_13,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_344,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k1_tops_1(X1,X2))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_22])).

cnf(c_345,plain,
    ( ~ v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k1_tops_1(sK1,X1)) ),
    inference(unflattening,[status(thm)],[c_344])).

cnf(c_1865,plain,
    ( ~ v3_pre_topc(sK3,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(sK3,X0)
    | r1_tarski(sK3,k1_tops_1(sK1,X0)) ),
    inference(instantiation,[status(thm)],[c_345])).

cnf(c_1957,plain,
    ( ~ v3_pre_topc(sK3,sK1)
    | ~ m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))
    | ~ r1_tarski(sK3,k2_pre_topc(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_1865])).

cnf(c_1958,plain,
    ( v3_pre_topc(sK3,sK1) != iProver_top
    | m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) = iProver_top
    | r1_tarski(sK3,k2_pre_topc(sK1,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1957])).

cnf(c_2574,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2557,c_28,c_29,c_30,c_31,c_32,c_1713,c_1726,c_1735,c_1738,c_1845,c_1856,c_1958])).

cnf(c_5,plain,
    ( v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
    | ~ r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_590,plain,
    ( v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
    | ~ r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_23])).

cnf(c_591,plain,
    ( v4_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,X0)))
    | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X0) ),
    inference(unflattening,[status(thm)],[c_590])).

cnf(c_1404,plain,
    ( v4_tops_1(X0,sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,X0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_591])).

cnf(c_2579,plain,
    ( v4_tops_1(sK2,sK0) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) != iProver_top
    | r1_tarski(sK2,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2574,c_1404])).

cnf(c_16,negated_conjecture,
    ( v3_pre_topc(sK3,sK1)
    | ~ v3_pre_topc(sK2,sK0)
    | ~ v4_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_33,plain,
    ( v3_pre_topc(sK3,sK1) = iProver_top
    | v3_pre_topc(sK2,sK0) != iProver_top
    | v4_tops_1(sK2,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_15,negated_conjecture,
    ( ~ v3_pre_topc(sK2,sK0)
    | v4_tops_1(sK3,sK1)
    | ~ v4_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_34,plain,
    ( v3_pre_topc(sK2,sK0) != iProver_top
    | v4_tops_1(sK3,sK1) = iProver_top
    | v4_tops_1(sK2,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_14,negated_conjecture,
    ( ~ v3_pre_topc(sK2,sK0)
    | ~ v6_tops_1(sK3,sK1)
    | ~ v4_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_35,plain,
    ( v3_pre_topc(sK2,sK0) != iProver_top
    | v6_tops_1(sK3,sK1) != iProver_top
    | v4_tops_1(sK2,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_11,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_24,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_264,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X1,X0) != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_24])).

cnf(c_265,plain,
    ( v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(sK0)
    | k1_tops_1(sK0,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_264])).

cnf(c_269,plain,
    ( ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | v3_pre_topc(X0,sK0)
    | k1_tops_1(sK0,X0) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_265,c_23])).

cnf(c_270,plain,
    ( v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(X2)
    | k1_tops_1(sK0,X0) != X0 ),
    inference(renaming,[status(thm)],[c_269])).

cnf(c_650,plain,
    ( v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) != X0
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_270])).

cnf(c_651,plain,
    ( v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_650])).

cnf(c_761,plain,
    ( v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) != X0
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_651])).

cnf(c_762,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_651])).

cnf(c_760,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_651])).

cnf(c_890,plain,
    ( k1_tops_1(sK0,X0) != X0
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(X0,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_761,c_762,c_760])).

cnf(c_891,plain,
    ( v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) != X0 ),
    inference(renaming,[status(thm)],[c_890])).

cnf(c_897,plain,
    ( k1_tops_1(sK0,X0) != X0
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(X0,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_761,c_891])).

cnf(c_898,plain,
    ( v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) != X0 ),
    inference(renaming,[status(thm)],[c_897])).

cnf(c_1750,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,sK2) != sK2 ),
    inference(instantiation,[status(thm)],[c_898])).

cnf(c_1751,plain,
    ( k1_tops_1(sK0,sK2) != sK2
    | v3_pre_topc(sK2,sK0) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1750])).

cnf(c_1756,plain,
    ( v4_tops_1(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK2)
    | ~ r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) ),
    inference(instantiation,[status(thm)],[c_591])).

cnf(c_1757,plain,
    ( v4_tops_1(sK2,sK0) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK2) != iProver_top
    | r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1756])).

cnf(c_770,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1976,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_770])).

cnf(c_772,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1894,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK2)
    | k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) != X0
    | sK2 != X1 ),
    inference(instantiation,[status(thm)],[c_772])).

cnf(c_2233,plain,
    ( ~ r1_tarski(X0,sK2)
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK2)
    | k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) != X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1894])).

cnf(c_2743,plain,
    ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK2)
    | ~ r1_tarski(sK2,sK2)
    | k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) != sK2
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_2233])).

cnf(c_2745,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) != sK2
    | sK2 != sK2
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK2) = iProver_top
    | r1_tarski(sK2,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2743])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2744,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2747,plain,
    ( r1_tarski(sK2,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2744])).

cnf(c_620,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_23])).

cnf(c_621,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_620])).

cnf(c_1402,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_621])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_518,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_23])).

cnf(c_519,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,k1_tops_1(sK0,X0)) = k1_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_518])).

cnf(c_1409,plain,
    ( k1_tops_1(sK0,k1_tops_1(sK0,X0)) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_519])).

cnf(c_2202,plain,
    ( k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,X0))) = k1_tops_1(sK0,k2_pre_topc(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1402,c_1409])).

cnf(c_3883,plain,
    ( k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK2))) = k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) ),
    inference(superposition,[status(thm)],[c_1426,c_2202])).

cnf(c_3890,plain,
    ( k1_tops_1(sK0,sK2) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_3883,c_2574])).

cnf(c_1414,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_468])).

cnf(c_1427,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1422,plain,
    ( v3_pre_topc(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k1_tops_1(sK1,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_345])).

cnf(c_3461,plain,
    ( v3_pre_topc(sK3,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top
    | r1_tarski(sK3,k1_tops_1(sK1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1427,c_1422])).

cnf(c_3697,plain,
    ( v3_pre_topc(sK3,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,X0))) = iProver_top
    | r1_tarski(sK3,k2_pre_topc(sK1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1414,c_3461])).

cnf(c_1418,plain,
    ( v4_tops_1(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,X0)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_408])).

cnf(c_1435,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3088,plain,
    ( k1_tops_1(sK1,k2_pre_topc(sK1,X0)) = X0
    | v4_tops_1(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X0,k1_tops_1(sK1,k2_pre_topc(sK1,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1418,c_1435])).

cnf(c_4707,plain,
    ( k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) = sK3
    | v3_pre_topc(sK3,sK1) != iProver_top
    | v4_tops_1(sK3,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(sK3,k2_pre_topc(sK1,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3697,c_3088])).

cnf(c_5101,plain,
    ( r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2579,c_28,c_29,c_30,c_31,c_32,c_33,c_34,c_35,c_1713,c_1726,c_1735,c_1738,c_1751,c_1757,c_1845,c_1856,c_1958,c_1976,c_2745,c_2747,c_3890,c_4707])).

cnf(c_5105,plain,
    ( r1_tarski(sK2,k2_pre_topc(sK0,sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5101,c_3890])).

cnf(c_608,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_23])).

cnf(c_609,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,k2_pre_topc(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_608])).

cnf(c_1403,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_609])).

cnf(c_1889,plain,
    ( r1_tarski(sK2,k2_pre_topc(sK0,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1426,c_1403])).

cnf(c_5107,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5105,c_1889])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:21:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.83/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.83/0.99  
% 2.83/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.83/0.99  
% 2.83/0.99  ------  iProver source info
% 2.83/0.99  
% 2.83/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.83/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.83/0.99  git: non_committed_changes: false
% 2.83/0.99  git: last_make_outside_of_git: false
% 2.83/0.99  
% 2.83/0.99  ------ 
% 2.83/0.99  
% 2.83/0.99  ------ Input Options
% 2.83/0.99  
% 2.83/0.99  --out_options                           all
% 2.83/0.99  --tptp_safe_out                         true
% 2.83/0.99  --problem_path                          ""
% 2.83/0.99  --include_path                          ""
% 2.83/0.99  --clausifier                            res/vclausify_rel
% 2.83/0.99  --clausifier_options                    --mode clausify
% 2.83/0.99  --stdin                                 false
% 2.83/0.99  --stats_out                             all
% 2.83/0.99  
% 2.83/0.99  ------ General Options
% 2.83/0.99  
% 2.83/0.99  --fof                                   false
% 2.83/0.99  --time_out_real                         305.
% 2.83/0.99  --time_out_virtual                      -1.
% 2.83/0.99  --symbol_type_check                     false
% 2.83/0.99  --clausify_out                          false
% 2.83/0.99  --sig_cnt_out                           false
% 2.83/0.99  --trig_cnt_out                          false
% 2.83/0.99  --trig_cnt_out_tolerance                1.
% 2.83/0.99  --trig_cnt_out_sk_spl                   false
% 2.83/0.99  --abstr_cl_out                          false
% 2.83/0.99  
% 2.83/0.99  ------ Global Options
% 2.83/0.99  
% 2.83/0.99  --schedule                              default
% 2.83/0.99  --add_important_lit                     false
% 2.83/0.99  --prop_solver_per_cl                    1000
% 2.83/0.99  --min_unsat_core                        false
% 2.83/0.99  --soft_assumptions                      false
% 2.83/0.99  --soft_lemma_size                       3
% 2.83/0.99  --prop_impl_unit_size                   0
% 2.83/0.99  --prop_impl_unit                        []
% 2.83/0.99  --share_sel_clauses                     true
% 2.83/0.99  --reset_solvers                         false
% 2.83/0.99  --bc_imp_inh                            [conj_cone]
% 2.83/0.99  --conj_cone_tolerance                   3.
% 2.83/0.99  --extra_neg_conj                        none
% 2.83/0.99  --large_theory_mode                     true
% 2.83/0.99  --prolific_symb_bound                   200
% 2.83/0.99  --lt_threshold                          2000
% 2.83/0.99  --clause_weak_htbl                      true
% 2.83/0.99  --gc_record_bc_elim                     false
% 2.83/0.99  
% 2.83/0.99  ------ Preprocessing Options
% 2.83/0.99  
% 2.83/0.99  --preprocessing_flag                    true
% 2.83/0.99  --time_out_prep_mult                    0.1
% 2.83/0.99  --splitting_mode                        input
% 2.83/0.99  --splitting_grd                         true
% 2.83/0.99  --splitting_cvd                         false
% 2.83/0.99  --splitting_cvd_svl                     false
% 2.83/0.99  --splitting_nvd                         32
% 2.83/0.99  --sub_typing                            true
% 2.83/0.99  --prep_gs_sim                           true
% 2.83/0.99  --prep_unflatten                        true
% 2.83/0.99  --prep_res_sim                          true
% 2.83/0.99  --prep_upred                            true
% 2.83/0.99  --prep_sem_filter                       exhaustive
% 2.83/0.99  --prep_sem_filter_out                   false
% 2.83/0.99  --pred_elim                             true
% 2.83/0.99  --res_sim_input                         true
% 2.83/0.99  --eq_ax_congr_red                       true
% 2.83/0.99  --pure_diseq_elim                       true
% 2.83/0.99  --brand_transform                       false
% 2.83/0.99  --non_eq_to_eq                          false
% 2.83/0.99  --prep_def_merge                        true
% 2.83/0.99  --prep_def_merge_prop_impl              false
% 2.83/0.99  --prep_def_merge_mbd                    true
% 2.83/0.99  --prep_def_merge_tr_red                 false
% 2.83/0.99  --prep_def_merge_tr_cl                  false
% 2.83/0.99  --smt_preprocessing                     true
% 2.83/0.99  --smt_ac_axioms                         fast
% 2.83/0.99  --preprocessed_out                      false
% 2.83/0.99  --preprocessed_stats                    false
% 2.83/0.99  
% 2.83/0.99  ------ Abstraction refinement Options
% 2.83/0.99  
% 2.83/0.99  --abstr_ref                             []
% 2.83/0.99  --abstr_ref_prep                        false
% 2.83/0.99  --abstr_ref_until_sat                   false
% 2.83/0.99  --abstr_ref_sig_restrict                funpre
% 2.83/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.83/0.99  --abstr_ref_under                       []
% 2.83/0.99  
% 2.83/0.99  ------ SAT Options
% 2.83/0.99  
% 2.83/0.99  --sat_mode                              false
% 2.83/0.99  --sat_fm_restart_options                ""
% 2.83/0.99  --sat_gr_def                            false
% 2.83/0.99  --sat_epr_types                         true
% 2.83/0.99  --sat_non_cyclic_types                  false
% 2.83/0.99  --sat_finite_models                     false
% 2.83/0.99  --sat_fm_lemmas                         false
% 2.83/0.99  --sat_fm_prep                           false
% 2.83/0.99  --sat_fm_uc_incr                        true
% 2.83/0.99  --sat_out_model                         small
% 2.83/0.99  --sat_out_clauses                       false
% 2.83/0.99  
% 2.83/0.99  ------ QBF Options
% 2.83/0.99  
% 2.83/0.99  --qbf_mode                              false
% 2.83/0.99  --qbf_elim_univ                         false
% 2.83/0.99  --qbf_dom_inst                          none
% 2.83/0.99  --qbf_dom_pre_inst                      false
% 2.83/0.99  --qbf_sk_in                             false
% 2.83/0.99  --qbf_pred_elim                         true
% 2.83/0.99  --qbf_split                             512
% 2.83/0.99  
% 2.83/0.99  ------ BMC1 Options
% 2.83/0.99  
% 2.83/0.99  --bmc1_incremental                      false
% 2.83/0.99  --bmc1_axioms                           reachable_all
% 2.83/0.99  --bmc1_min_bound                        0
% 2.83/0.99  --bmc1_max_bound                        -1
% 2.83/0.99  --bmc1_max_bound_default                -1
% 2.83/0.99  --bmc1_symbol_reachability              true
% 2.83/0.99  --bmc1_property_lemmas                  false
% 2.83/0.99  --bmc1_k_induction                      false
% 2.83/0.99  --bmc1_non_equiv_states                 false
% 2.83/0.99  --bmc1_deadlock                         false
% 2.83/0.99  --bmc1_ucm                              false
% 2.83/0.99  --bmc1_add_unsat_core                   none
% 2.83/0.99  --bmc1_unsat_core_children              false
% 2.83/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.83/0.99  --bmc1_out_stat                         full
% 2.83/0.99  --bmc1_ground_init                      false
% 2.83/0.99  --bmc1_pre_inst_next_state              false
% 2.83/0.99  --bmc1_pre_inst_state                   false
% 2.83/0.99  --bmc1_pre_inst_reach_state             false
% 2.83/0.99  --bmc1_out_unsat_core                   false
% 2.83/0.99  --bmc1_aig_witness_out                  false
% 2.83/0.99  --bmc1_verbose                          false
% 2.83/0.99  --bmc1_dump_clauses_tptp                false
% 2.83/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.83/0.99  --bmc1_dump_file                        -
% 2.83/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.83/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.83/0.99  --bmc1_ucm_extend_mode                  1
% 2.83/0.99  --bmc1_ucm_init_mode                    2
% 2.83/0.99  --bmc1_ucm_cone_mode                    none
% 2.83/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.83/0.99  --bmc1_ucm_relax_model                  4
% 2.83/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.83/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.83/0.99  --bmc1_ucm_layered_model                none
% 2.83/0.99  --bmc1_ucm_max_lemma_size               10
% 2.83/0.99  
% 2.83/0.99  ------ AIG Options
% 2.83/0.99  
% 2.83/0.99  --aig_mode                              false
% 2.83/0.99  
% 2.83/0.99  ------ Instantiation Options
% 2.83/0.99  
% 2.83/0.99  --instantiation_flag                    true
% 2.83/0.99  --inst_sos_flag                         false
% 2.83/0.99  --inst_sos_phase                        true
% 2.83/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.83/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.83/0.99  --inst_lit_sel_side                     num_symb
% 2.83/0.99  --inst_solver_per_active                1400
% 2.83/0.99  --inst_solver_calls_frac                1.
% 2.83/0.99  --inst_passive_queue_type               priority_queues
% 2.83/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.83/0.99  --inst_passive_queues_freq              [25;2]
% 2.83/0.99  --inst_dismatching                      true
% 2.83/0.99  --inst_eager_unprocessed_to_passive     true
% 2.83/0.99  --inst_prop_sim_given                   true
% 2.83/0.99  --inst_prop_sim_new                     false
% 2.83/0.99  --inst_subs_new                         false
% 2.83/0.99  --inst_eq_res_simp                      false
% 2.83/0.99  --inst_subs_given                       false
% 2.83/0.99  --inst_orphan_elimination               true
% 2.83/0.99  --inst_learning_loop_flag               true
% 2.83/0.99  --inst_learning_start                   3000
% 2.83/0.99  --inst_learning_factor                  2
% 2.83/0.99  --inst_start_prop_sim_after_learn       3
% 2.83/0.99  --inst_sel_renew                        solver
% 2.83/0.99  --inst_lit_activity_flag                true
% 2.83/0.99  --inst_restr_to_given                   false
% 2.83/0.99  --inst_activity_threshold               500
% 2.83/0.99  --inst_out_proof                        true
% 2.83/0.99  
% 2.83/0.99  ------ Resolution Options
% 2.83/0.99  
% 2.83/0.99  --resolution_flag                       true
% 2.83/0.99  --res_lit_sel                           adaptive
% 2.83/0.99  --res_lit_sel_side                      none
% 2.83/0.99  --res_ordering                          kbo
% 2.83/0.99  --res_to_prop_solver                    active
% 2.83/0.99  --res_prop_simpl_new                    false
% 2.83/0.99  --res_prop_simpl_given                  true
% 2.83/0.99  --res_passive_queue_type                priority_queues
% 2.83/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.83/0.99  --res_passive_queues_freq               [15;5]
% 2.83/0.99  --res_forward_subs                      full
% 2.83/0.99  --res_backward_subs                     full
% 2.83/0.99  --res_forward_subs_resolution           true
% 2.83/0.99  --res_backward_subs_resolution          true
% 2.83/0.99  --res_orphan_elimination                true
% 2.83/0.99  --res_time_limit                        2.
% 2.83/0.99  --res_out_proof                         true
% 2.83/0.99  
% 2.83/0.99  ------ Superposition Options
% 2.83/0.99  
% 2.83/0.99  --superposition_flag                    true
% 2.83/0.99  --sup_passive_queue_type                priority_queues
% 2.83/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.83/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.83/0.99  --demod_completeness_check              fast
% 2.83/0.99  --demod_use_ground                      true
% 2.83/0.99  --sup_to_prop_solver                    passive
% 2.83/0.99  --sup_prop_simpl_new                    true
% 2.83/0.99  --sup_prop_simpl_given                  true
% 2.83/0.99  --sup_fun_splitting                     false
% 2.83/0.99  --sup_smt_interval                      50000
% 2.83/0.99  
% 2.83/0.99  ------ Superposition Simplification Setup
% 2.83/0.99  
% 2.83/0.99  --sup_indices_passive                   []
% 2.83/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.83/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.83/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.83/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.83/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.83/0.99  --sup_full_bw                           [BwDemod]
% 2.83/0.99  --sup_immed_triv                        [TrivRules]
% 2.83/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.83/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.83/0.99  --sup_immed_bw_main                     []
% 2.83/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.83/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.83/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.83/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.83/0.99  
% 2.83/0.99  ------ Combination Options
% 2.83/0.99  
% 2.83/0.99  --comb_res_mult                         3
% 2.83/0.99  --comb_sup_mult                         2
% 2.83/0.99  --comb_inst_mult                        10
% 2.83/0.99  
% 2.83/0.99  ------ Debug Options
% 2.83/0.99  
% 2.83/0.99  --dbg_backtrace                         false
% 2.83/0.99  --dbg_dump_prop_clauses                 false
% 2.83/0.99  --dbg_dump_prop_clauses_file            -
% 2.83/0.99  --dbg_out_stat                          false
% 2.83/0.99  ------ Parsing...
% 2.83/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.83/0.99  
% 2.83/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 2.83/0.99  
% 2.83/0.99  ------ Preprocessing... gs_s  sp: 8 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.83/0.99  
% 2.83/0.99  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.83/0.99  ------ Proving...
% 2.83/0.99  ------ Problem Properties 
% 2.83/0.99  
% 2.83/0.99  
% 2.83/0.99  clauses                                 40
% 2.83/0.99  conjectures                             8
% 2.83/0.99  EPR                                     12
% 2.83/0.99  Horn                                    34
% 2.83/0.99  unary                                   3
% 2.83/0.99  binary                                  17
% 2.83/0.99  lits                                    107
% 2.83/0.99  lits eq                                 11
% 2.83/0.99  fd_pure                                 0
% 2.83/0.99  fd_pseudo                               0
% 2.83/0.99  fd_cond                                 0
% 2.83/0.99  fd_pseudo_cond                          1
% 2.83/0.99  AC symbols                              0
% 2.83/0.99  
% 2.83/0.99  ------ Schedule dynamic 5 is on 
% 2.83/0.99  
% 2.83/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.83/0.99  
% 2.83/0.99  
% 2.83/0.99  ------ 
% 2.83/0.99  Current options:
% 2.83/0.99  ------ 
% 2.83/0.99  
% 2.83/0.99  ------ Input Options
% 2.83/0.99  
% 2.83/0.99  --out_options                           all
% 2.83/0.99  --tptp_safe_out                         true
% 2.83/0.99  --problem_path                          ""
% 2.83/0.99  --include_path                          ""
% 2.83/0.99  --clausifier                            res/vclausify_rel
% 2.83/0.99  --clausifier_options                    --mode clausify
% 2.83/0.99  --stdin                                 false
% 2.83/0.99  --stats_out                             all
% 2.83/0.99  
% 2.83/0.99  ------ General Options
% 2.83/0.99  
% 2.83/0.99  --fof                                   false
% 2.83/0.99  --time_out_real                         305.
% 2.83/0.99  --time_out_virtual                      -1.
% 2.83/0.99  --symbol_type_check                     false
% 2.83/0.99  --clausify_out                          false
% 2.83/0.99  --sig_cnt_out                           false
% 2.83/0.99  --trig_cnt_out                          false
% 2.83/0.99  --trig_cnt_out_tolerance                1.
% 2.83/0.99  --trig_cnt_out_sk_spl                   false
% 2.83/0.99  --abstr_cl_out                          false
% 2.83/0.99  
% 2.83/0.99  ------ Global Options
% 2.83/0.99  
% 2.83/0.99  --schedule                              default
% 2.83/0.99  --add_important_lit                     false
% 2.83/0.99  --prop_solver_per_cl                    1000
% 2.83/0.99  --min_unsat_core                        false
% 2.83/0.99  --soft_assumptions                      false
% 2.83/0.99  --soft_lemma_size                       3
% 2.83/0.99  --prop_impl_unit_size                   0
% 2.83/0.99  --prop_impl_unit                        []
% 2.83/0.99  --share_sel_clauses                     true
% 2.83/0.99  --reset_solvers                         false
% 2.83/0.99  --bc_imp_inh                            [conj_cone]
% 2.83/0.99  --conj_cone_tolerance                   3.
% 2.83/0.99  --extra_neg_conj                        none
% 2.83/0.99  --large_theory_mode                     true
% 2.83/0.99  --prolific_symb_bound                   200
% 2.83/0.99  --lt_threshold                          2000
% 2.83/0.99  --clause_weak_htbl                      true
% 2.83/0.99  --gc_record_bc_elim                     false
% 2.83/0.99  
% 2.83/0.99  ------ Preprocessing Options
% 2.83/0.99  
% 2.83/0.99  --preprocessing_flag                    true
% 2.83/0.99  --time_out_prep_mult                    0.1
% 2.83/0.99  --splitting_mode                        input
% 2.83/0.99  --splitting_grd                         true
% 2.83/0.99  --splitting_cvd                         false
% 2.83/0.99  --splitting_cvd_svl                     false
% 2.83/0.99  --splitting_nvd                         32
% 2.83/0.99  --sub_typing                            true
% 2.83/0.99  --prep_gs_sim                           true
% 2.83/0.99  --prep_unflatten                        true
% 2.83/0.99  --prep_res_sim                          true
% 2.83/0.99  --prep_upred                            true
% 2.83/0.99  --prep_sem_filter                       exhaustive
% 2.83/0.99  --prep_sem_filter_out                   false
% 2.83/0.99  --pred_elim                             true
% 2.83/0.99  --res_sim_input                         true
% 2.83/0.99  --eq_ax_congr_red                       true
% 2.83/0.99  --pure_diseq_elim                       true
% 2.83/0.99  --brand_transform                       false
% 2.83/0.99  --non_eq_to_eq                          false
% 2.83/0.99  --prep_def_merge                        true
% 2.83/0.99  --prep_def_merge_prop_impl              false
% 2.83/0.99  --prep_def_merge_mbd                    true
% 2.83/0.99  --prep_def_merge_tr_red                 false
% 2.83/0.99  --prep_def_merge_tr_cl                  false
% 2.83/0.99  --smt_preprocessing                     true
% 2.83/0.99  --smt_ac_axioms                         fast
% 2.83/0.99  --preprocessed_out                      false
% 2.83/0.99  --preprocessed_stats                    false
% 2.83/0.99  
% 2.83/0.99  ------ Abstraction refinement Options
% 2.83/0.99  
% 2.83/0.99  --abstr_ref                             []
% 2.83/0.99  --abstr_ref_prep                        false
% 2.83/0.99  --abstr_ref_until_sat                   false
% 2.83/0.99  --abstr_ref_sig_restrict                funpre
% 2.83/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.83/0.99  --abstr_ref_under                       []
% 2.83/0.99  
% 2.83/0.99  ------ SAT Options
% 2.83/0.99  
% 2.83/0.99  --sat_mode                              false
% 2.83/0.99  --sat_fm_restart_options                ""
% 2.83/0.99  --sat_gr_def                            false
% 2.83/0.99  --sat_epr_types                         true
% 2.83/0.99  --sat_non_cyclic_types                  false
% 2.83/0.99  --sat_finite_models                     false
% 2.83/0.99  --sat_fm_lemmas                         false
% 2.83/0.99  --sat_fm_prep                           false
% 2.83/0.99  --sat_fm_uc_incr                        true
% 2.83/0.99  --sat_out_model                         small
% 2.83/0.99  --sat_out_clauses                       false
% 2.83/0.99  
% 2.83/0.99  ------ QBF Options
% 2.83/0.99  
% 2.83/0.99  --qbf_mode                              false
% 2.83/0.99  --qbf_elim_univ                         false
% 2.83/0.99  --qbf_dom_inst                          none
% 2.83/0.99  --qbf_dom_pre_inst                      false
% 2.83/0.99  --qbf_sk_in                             false
% 2.83/0.99  --qbf_pred_elim                         true
% 2.83/0.99  --qbf_split                             512
% 2.83/0.99  
% 2.83/0.99  ------ BMC1 Options
% 2.83/0.99  
% 2.83/0.99  --bmc1_incremental                      false
% 2.83/0.99  --bmc1_axioms                           reachable_all
% 2.83/0.99  --bmc1_min_bound                        0
% 2.83/0.99  --bmc1_max_bound                        -1
% 2.83/0.99  --bmc1_max_bound_default                -1
% 2.83/0.99  --bmc1_symbol_reachability              true
% 2.83/0.99  --bmc1_property_lemmas                  false
% 2.83/0.99  --bmc1_k_induction                      false
% 2.83/0.99  --bmc1_non_equiv_states                 false
% 2.83/0.99  --bmc1_deadlock                         false
% 2.83/0.99  --bmc1_ucm                              false
% 2.83/0.99  --bmc1_add_unsat_core                   none
% 2.83/0.99  --bmc1_unsat_core_children              false
% 2.83/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.83/0.99  --bmc1_out_stat                         full
% 2.83/0.99  --bmc1_ground_init                      false
% 2.83/0.99  --bmc1_pre_inst_next_state              false
% 2.83/0.99  --bmc1_pre_inst_state                   false
% 2.83/0.99  --bmc1_pre_inst_reach_state             false
% 2.83/0.99  --bmc1_out_unsat_core                   false
% 2.83/0.99  --bmc1_aig_witness_out                  false
% 2.83/0.99  --bmc1_verbose                          false
% 2.83/0.99  --bmc1_dump_clauses_tptp                false
% 2.83/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.83/0.99  --bmc1_dump_file                        -
% 2.83/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.83/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.83/0.99  --bmc1_ucm_extend_mode                  1
% 2.83/0.99  --bmc1_ucm_init_mode                    2
% 2.83/0.99  --bmc1_ucm_cone_mode                    none
% 2.83/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.83/0.99  --bmc1_ucm_relax_model                  4
% 2.83/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.83/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.83/0.99  --bmc1_ucm_layered_model                none
% 2.83/0.99  --bmc1_ucm_max_lemma_size               10
% 2.83/0.99  
% 2.83/0.99  ------ AIG Options
% 2.83/0.99  
% 2.83/0.99  --aig_mode                              false
% 2.83/0.99  
% 2.83/0.99  ------ Instantiation Options
% 2.83/0.99  
% 2.83/0.99  --instantiation_flag                    true
% 2.83/0.99  --inst_sos_flag                         false
% 2.83/0.99  --inst_sos_phase                        true
% 2.83/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.83/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.83/0.99  --inst_lit_sel_side                     none
% 2.83/0.99  --inst_solver_per_active                1400
% 2.83/0.99  --inst_solver_calls_frac                1.
% 2.83/0.99  --inst_passive_queue_type               priority_queues
% 2.83/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.83/0.99  --inst_passive_queues_freq              [25;2]
% 2.83/0.99  --inst_dismatching                      true
% 2.83/0.99  --inst_eager_unprocessed_to_passive     true
% 2.83/0.99  --inst_prop_sim_given                   true
% 2.83/0.99  --inst_prop_sim_new                     false
% 2.83/0.99  --inst_subs_new                         false
% 2.83/0.99  --inst_eq_res_simp                      false
% 2.83/0.99  --inst_subs_given                       false
% 2.83/0.99  --inst_orphan_elimination               true
% 2.83/0.99  --inst_learning_loop_flag               true
% 2.83/0.99  --inst_learning_start                   3000
% 2.83/0.99  --inst_learning_factor                  2
% 2.83/0.99  --inst_start_prop_sim_after_learn       3
% 2.83/0.99  --inst_sel_renew                        solver
% 2.83/0.99  --inst_lit_activity_flag                true
% 2.83/0.99  --inst_restr_to_given                   false
% 2.83/0.99  --inst_activity_threshold               500
% 2.83/0.99  --inst_out_proof                        true
% 2.83/0.99  
% 2.83/0.99  ------ Resolution Options
% 2.83/0.99  
% 2.83/0.99  --resolution_flag                       false
% 2.83/0.99  --res_lit_sel                           adaptive
% 2.83/0.99  --res_lit_sel_side                      none
% 2.83/0.99  --res_ordering                          kbo
% 2.83/0.99  --res_to_prop_solver                    active
% 2.83/0.99  --res_prop_simpl_new                    false
% 2.83/0.99  --res_prop_simpl_given                  true
% 2.83/0.99  --res_passive_queue_type                priority_queues
% 2.83/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.83/0.99  --res_passive_queues_freq               [15;5]
% 2.83/0.99  --res_forward_subs                      full
% 2.83/0.99  --res_backward_subs                     full
% 2.83/0.99  --res_forward_subs_resolution           true
% 2.83/0.99  --res_backward_subs_resolution          true
% 2.83/0.99  --res_orphan_elimination                true
% 2.83/0.99  --res_time_limit                        2.
% 2.83/0.99  --res_out_proof                         true
% 2.83/0.99  
% 2.83/0.99  ------ Superposition Options
% 2.83/0.99  
% 2.83/0.99  --superposition_flag                    true
% 2.83/0.99  --sup_passive_queue_type                priority_queues
% 2.83/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.83/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.83/0.99  --demod_completeness_check              fast
% 2.83/0.99  --demod_use_ground                      true
% 2.83/0.99  --sup_to_prop_solver                    passive
% 2.83/0.99  --sup_prop_simpl_new                    true
% 2.83/0.99  --sup_prop_simpl_given                  true
% 2.83/0.99  --sup_fun_splitting                     false
% 2.83/0.99  --sup_smt_interval                      50000
% 2.83/0.99  
% 2.83/0.99  ------ Superposition Simplification Setup
% 2.83/0.99  
% 2.83/0.99  --sup_indices_passive                   []
% 2.83/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.83/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.83/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.83/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.83/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.83/0.99  --sup_full_bw                           [BwDemod]
% 2.83/0.99  --sup_immed_triv                        [TrivRules]
% 2.83/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.83/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.83/0.99  --sup_immed_bw_main                     []
% 2.83/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.83/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.83/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.83/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.83/0.99  
% 2.83/0.99  ------ Combination Options
% 2.83/0.99  
% 2.83/0.99  --comb_res_mult                         3
% 2.83/0.99  --comb_sup_mult                         2
% 2.83/0.99  --comb_inst_mult                        10
% 2.83/0.99  
% 2.83/0.99  ------ Debug Options
% 2.83/0.99  
% 2.83/0.99  --dbg_backtrace                         false
% 2.83/0.99  --dbg_dump_prop_clauses                 false
% 2.83/0.99  --dbg_dump_prop_clauses_file            -
% 2.83/0.99  --dbg_out_stat                          false
% 2.83/0.99  
% 2.83/0.99  
% 2.83/0.99  
% 2.83/0.99  
% 2.83/0.99  ------ Proving...
% 2.83/0.99  
% 2.83/0.99  
% 2.83/0.99  % SZS status Theorem for theBenchmark.p
% 2.83/0.99  
% 2.83/0.99   Resolution empty clause
% 2.83/0.99  
% 2.83/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.83/0.99  
% 2.83/0.99  fof(f9,conjecture,(
% 2.83/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v6_tops_1(X2,X0) => (v4_tops_1(X2,X0) & v3_pre_topc(X2,X0))) & ((v4_tops_1(X3,X1) & v3_pre_topc(X3,X1)) => v6_tops_1(X3,X1)))))))),
% 2.83/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.83/0.99  
% 2.83/0.99  fof(f10,negated_conjecture,(
% 2.83/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v6_tops_1(X2,X0) => (v4_tops_1(X2,X0) & v3_pre_topc(X2,X0))) & ((v4_tops_1(X3,X1) & v3_pre_topc(X3,X1)) => v6_tops_1(X3,X1)))))))),
% 2.83/0.99    inference(negated_conjecture,[],[f9])).
% 2.83/0.99  
% 2.83/0.99  fof(f22,plain,(
% 2.83/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(X3,X1) & (v4_tops_1(X3,X1) & v3_pre_topc(X3,X1)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.83/0.99    inference(ennf_transformation,[],[f10])).
% 2.83/0.99  
% 2.83/0.99  fof(f23,plain,(
% 2.83/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.83/0.99    inference(flattening,[],[f22])).
% 2.83/0.99  
% 2.83/0.99  fof(f32,plain,(
% 2.83/0.99    ( ! [X2,X0,X1] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(sK3,X1) & v4_tops_1(sK3,X1) & v3_pre_topc(sK3,X1))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X1))))) )),
% 2.83/0.99    introduced(choice_axiom,[])).
% 2.83/0.99  
% 2.83/0.99  fof(f31,plain,(
% 2.83/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X3] : ((((~v4_tops_1(sK2,X0) | ~v3_pre_topc(sK2,X0)) & v6_tops_1(sK2,X0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.83/0.99    introduced(choice_axiom,[])).
% 2.83/0.99  
% 2.83/0.99  fof(f30,plain,(
% 2.83/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) => (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(X3,sK1) & v4_tops_1(X3,sK1) & v3_pre_topc(X3,sK1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(sK1))) )),
% 2.83/0.99    introduced(choice_axiom,[])).
% 2.83/0.99  
% 2.83/0.99  fof(f29,plain,(
% 2.83/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,sK0) | ~v3_pre_topc(X2,sK0)) & v6_tops_1(X2,sK0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 2.83/0.99    introduced(choice_axiom,[])).
% 2.83/0.99  
% 2.83/0.99  fof(f33,plain,(
% 2.83/0.99    ((((((~v4_tops_1(sK2,sK0) | ~v3_pre_topc(sK2,sK0)) & v6_tops_1(sK2,sK0)) | (~v6_tops_1(sK3,sK1) & v4_tops_1(sK3,sK1) & v3_pre_topc(sK3,sK1))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 2.83/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f32,f31,f30,f29])).
% 2.83/0.99  
% 2.83/0.99  fof(f51,plain,(
% 2.83/0.99    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.83/0.99    inference(cnf_transformation,[],[f33])).
% 2.83/0.99  
% 2.83/0.99  fof(f5,axiom,(
% 2.83/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v6_tops_1(X1,X0) <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1)))),
% 2.83/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.83/0.99  
% 2.83/0.99  fof(f15,plain,(
% 2.83/0.99    ! [X0] : (! [X1] : ((v6_tops_1(X1,X0) <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.83/0.99    inference(ennf_transformation,[],[f5])).
% 2.83/0.99  
% 2.83/0.99  fof(f28,plain,(
% 2.83/0.99    ! [X0] : (! [X1] : (((v6_tops_1(X1,X0) | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1) & (k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 | ~v6_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.83/0.99    inference(nnf_transformation,[],[f15])).
% 2.83/0.99  
% 2.83/0.99  fof(f42,plain,(
% 2.83/0.99    ( ! [X0,X1] : (k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 | ~v6_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.83/0.99    inference(cnf_transformation,[],[f28])).
% 2.83/0.99  
% 2.83/0.99  fof(f49,plain,(
% 2.83/0.99    l1_pre_topc(sK0)),
% 2.83/0.99    inference(cnf_transformation,[],[f33])).
% 2.83/0.99  
% 2.83/0.99  fof(f52,plain,(
% 2.83/0.99    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 2.83/0.99    inference(cnf_transformation,[],[f33])).
% 2.83/0.99  
% 2.83/0.99  fof(f53,plain,(
% 2.83/0.99    v6_tops_1(sK2,sK0) | v3_pre_topc(sK3,sK1)),
% 2.83/0.99    inference(cnf_transformation,[],[f33])).
% 2.83/0.99  
% 2.83/0.99  fof(f54,plain,(
% 2.83/0.99    v6_tops_1(sK2,sK0) | v4_tops_1(sK3,sK1)),
% 2.83/0.99    inference(cnf_transformation,[],[f33])).
% 2.83/0.99  
% 2.83/0.99  fof(f55,plain,(
% 2.83/0.99    v6_tops_1(sK2,sK0) | ~v6_tops_1(sK3,sK1)),
% 2.83/0.99    inference(cnf_transformation,[],[f33])).
% 2.83/0.99  
% 2.83/0.99  fof(f2,axiom,(
% 2.83/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.83/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.83/0.99  
% 2.83/0.99  fof(f11,plain,(
% 2.83/0.99    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.83/0.99    inference(ennf_transformation,[],[f2])).
% 2.83/0.99  
% 2.83/0.99  fof(f12,plain,(
% 2.83/0.99    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.83/0.99    inference(flattening,[],[f11])).
% 2.83/0.99  
% 2.83/0.99  fof(f37,plain,(
% 2.83/0.99    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.83/0.99    inference(cnf_transformation,[],[f12])).
% 2.83/0.99  
% 2.83/0.99  fof(f50,plain,(
% 2.83/0.99    l1_pre_topc(sK1)),
% 2.83/0.99    inference(cnf_transformation,[],[f33])).
% 2.83/0.99  
% 2.83/0.99  fof(f3,axiom,(
% 2.83/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 2.83/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.83/0.99  
% 2.83/0.99  fof(f13,plain,(
% 2.83/0.99    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.83/0.99    inference(ennf_transformation,[],[f3])).
% 2.83/0.99  
% 2.83/0.99  fof(f38,plain,(
% 2.83/0.99    ( ! [X0,X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.83/0.99    inference(cnf_transformation,[],[f13])).
% 2.83/0.99  
% 2.83/0.99  fof(f43,plain,(
% 2.83/0.99    ( ! [X0,X1] : (v6_tops_1(X1,X0) | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.83/0.99    inference(cnf_transformation,[],[f28])).
% 2.83/0.99  
% 2.83/0.99  fof(f1,axiom,(
% 2.83/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.83/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.83/0.99  
% 2.83/0.99  fof(f24,plain,(
% 2.83/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.83/0.99    inference(nnf_transformation,[],[f1])).
% 2.83/0.99  
% 2.83/0.99  fof(f25,plain,(
% 2.83/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.83/0.99    inference(flattening,[],[f24])).
% 2.83/0.99  
% 2.83/0.99  fof(f36,plain,(
% 2.83/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.83/0.99    inference(cnf_transformation,[],[f25])).
% 2.83/0.99  
% 2.83/0.99  fof(f4,axiom,(
% 2.83/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)))))),
% 2.83/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.83/0.99  
% 2.83/0.99  fof(f14,plain,(
% 2.83/0.99    ! [X0] : (! [X1] : ((v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.83/0.99    inference(ennf_transformation,[],[f4])).
% 2.83/0.99  
% 2.83/0.99  fof(f26,plain,(
% 2.83/0.99    ! [X0] : (! [X1] : (((v4_tops_1(X1,X0) | (~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1))) & ((r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) | ~v4_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.83/0.99    inference(nnf_transformation,[],[f14])).
% 2.83/0.99  
% 2.83/0.99  fof(f27,plain,(
% 2.83/0.99    ! [X0] : (! [X1] : (((v4_tops_1(X1,X0) | ~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) & ((r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) | ~v4_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.83/0.99    inference(flattening,[],[f26])).
% 2.83/0.99  
% 2.83/0.99  fof(f39,plain,(
% 2.83/0.99    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) | ~v4_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.83/0.99    inference(cnf_transformation,[],[f27])).
% 2.83/0.99  
% 2.83/0.99  fof(f8,axiom,(
% 2.83/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 2.83/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.83/0.99  
% 2.83/0.99  fof(f20,plain,(
% 2.83/0.99    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.83/0.99    inference(ennf_transformation,[],[f8])).
% 2.83/0.99  
% 2.83/0.99  fof(f21,plain,(
% 2.83/0.99    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.83/0.99    inference(flattening,[],[f20])).
% 2.83/0.99  
% 2.83/0.99  fof(f47,plain,(
% 2.83/0.99    ( ! [X2,X0,X1] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.83/0.99    inference(cnf_transformation,[],[f21])).
% 2.83/0.99  
% 2.83/0.99  fof(f41,plain,(
% 2.83/0.99    ( ! [X0,X1] : (v4_tops_1(X1,X0) | ~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.83/0.99    inference(cnf_transformation,[],[f27])).
% 2.83/0.99  
% 2.83/0.99  fof(f56,plain,(
% 2.83/0.99    ~v4_tops_1(sK2,sK0) | ~v3_pre_topc(sK2,sK0) | v3_pre_topc(sK3,sK1)),
% 2.83/0.99    inference(cnf_transformation,[],[f33])).
% 2.83/0.99  
% 2.83/0.99  fof(f57,plain,(
% 2.83/0.99    ~v4_tops_1(sK2,sK0) | ~v3_pre_topc(sK2,sK0) | v4_tops_1(sK3,sK1)),
% 2.83/0.99    inference(cnf_transformation,[],[f33])).
% 2.83/0.99  
% 2.83/0.99  fof(f58,plain,(
% 2.83/0.99    ~v4_tops_1(sK2,sK0) | ~v3_pre_topc(sK2,sK0) | ~v6_tops_1(sK3,sK1)),
% 2.83/0.99    inference(cnf_transformation,[],[f33])).
% 2.83/0.99  
% 2.83/0.99  fof(f7,axiom,(
% 2.83/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 2.83/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.83/0.99  
% 2.83/0.99  fof(f18,plain,(
% 2.83/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.83/0.99    inference(ennf_transformation,[],[f7])).
% 2.83/0.99  
% 2.83/0.99  fof(f19,plain,(
% 2.83/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.83/0.99    inference(flattening,[],[f18])).
% 2.83/0.99  
% 2.83/0.99  fof(f46,plain,(
% 2.83/0.99    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.83/0.99    inference(cnf_transformation,[],[f19])).
% 2.83/0.99  
% 2.83/0.99  fof(f48,plain,(
% 2.83/0.99    v2_pre_topc(sK0)),
% 2.83/0.99    inference(cnf_transformation,[],[f33])).
% 2.83/0.99  
% 2.83/0.99  fof(f34,plain,(
% 2.83/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.83/0.99    inference(cnf_transformation,[],[f25])).
% 2.83/0.99  
% 2.83/0.99  fof(f60,plain,(
% 2.83/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.83/0.99    inference(equality_resolution,[],[f34])).
% 2.83/0.99  
% 2.83/0.99  fof(f6,axiom,(
% 2.83/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)))),
% 2.83/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.83/0.99  
% 2.83/0.99  fof(f16,plain,(
% 2.83/0.99    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.83/0.99    inference(ennf_transformation,[],[f6])).
% 2.83/0.99  
% 2.83/0.99  fof(f17,plain,(
% 2.83/0.99    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.83/0.99    inference(flattening,[],[f16])).
% 2.83/0.99  
% 2.83/0.99  fof(f44,plain,(
% 2.83/0.99    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.83/0.99    inference(cnf_transformation,[],[f17])).
% 2.83/0.99  
% 2.83/0.99  cnf(c_21,negated_conjecture,
% 2.83/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.83/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_1426,plain,
% 2.83/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.83/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_9,plain,
% 2.83/0.99      ( ~ v6_tops_1(X0,X1)
% 2.83/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.83/0.99      | ~ l1_pre_topc(X1)
% 2.83/0.99      | k1_tops_1(X1,k2_pre_topc(X1,X0)) = X0 ),
% 2.83/0.99      inference(cnf_transformation,[],[f42]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_23,negated_conjecture,
% 2.83/0.99      ( l1_pre_topc(sK0) ),
% 2.83/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_530,plain,
% 2.83/0.99      ( ~ v6_tops_1(X0,X1)
% 2.83/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.83/0.99      | k1_tops_1(X1,k2_pre_topc(X1,X0)) = X0
% 2.83/0.99      | sK0 != X1 ),
% 2.83/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_23]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_531,plain,
% 2.83/0.99      ( ~ v6_tops_1(X0,sK0)
% 2.83/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.83/0.99      | k1_tops_1(sK0,k2_pre_topc(sK0,X0)) = X0 ),
% 2.83/0.99      inference(unflattening,[status(thm)],[c_530]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_1408,plain,
% 2.83/0.99      ( k1_tops_1(sK0,k2_pre_topc(sK0,X0)) = X0
% 2.83/0.99      | v6_tops_1(X0,sK0) != iProver_top
% 2.83/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.83/0.99      inference(predicate_to_equality,[status(thm)],[c_531]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_2557,plain,
% 2.83/0.99      ( k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = sK2
% 2.83/0.99      | v6_tops_1(sK2,sK0) != iProver_top ),
% 2.83/0.99      inference(superposition,[status(thm)],[c_1426,c_1408]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_28,plain,
% 2.83/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.83/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_20,negated_conjecture,
% 2.83/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.83/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_29,plain,
% 2.83/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.83/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_19,negated_conjecture,
% 2.83/0.99      ( v3_pre_topc(sK3,sK1) | v6_tops_1(sK2,sK0) ),
% 2.83/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_30,plain,
% 2.83/0.99      ( v3_pre_topc(sK3,sK1) = iProver_top | v6_tops_1(sK2,sK0) = iProver_top ),
% 2.83/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_18,negated_conjecture,
% 2.83/0.99      ( v6_tops_1(sK2,sK0) | v4_tops_1(sK3,sK1) ),
% 2.83/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_31,plain,
% 2.83/0.99      ( v6_tops_1(sK2,sK0) = iProver_top | v4_tops_1(sK3,sK1) = iProver_top ),
% 2.83/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_17,negated_conjecture,
% 2.83/0.99      ( ~ v6_tops_1(sK3,sK1) | v6_tops_1(sK2,sK0) ),
% 2.83/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_32,plain,
% 2.83/0.99      ( v6_tops_1(sK3,sK1) != iProver_top | v6_tops_1(sK2,sK0) = iProver_top ),
% 2.83/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_3,plain,
% 2.83/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.83/0.99      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.83/0.99      | ~ l1_pre_topc(X1) ),
% 2.83/0.99      inference(cnf_transformation,[],[f37]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_22,negated_conjecture,
% 2.83/0.99      ( l1_pre_topc(sK1) ),
% 2.83/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_467,plain,
% 2.83/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.83/0.99      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.83/0.99      | sK1 != X1 ),
% 2.83/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_22]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_468,plain,
% 2.83/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.83/0.99      | m1_subset_1(k2_pre_topc(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.83/0.99      inference(unflattening,[status(thm)],[c_467]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_1712,plain,
% 2.83/0.99      ( m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.83/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.83/0.99      inference(instantiation,[status(thm)],[c_468]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_1713,plain,
% 2.83/0.99      ( m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 2.83/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.83/0.99      inference(predicate_to_equality,[status(thm)],[c_1712]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_4,plain,
% 2.83/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.83/0.99      | r1_tarski(X0,k2_pre_topc(X1,X0))
% 2.83/0.99      | ~ l1_pre_topc(X1) ),
% 2.83/0.99      inference(cnf_transformation,[],[f38]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_455,plain,
% 2.83/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.83/0.99      | r1_tarski(X0,k2_pre_topc(X1,X0))
% 2.83/0.99      | sK1 != X1 ),
% 2.83/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_22]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_456,plain,
% 2.83/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.83/0.99      | r1_tarski(X0,k2_pre_topc(sK1,X0)) ),
% 2.83/0.99      inference(unflattening,[status(thm)],[c_455]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_1725,plain,
% 2.83/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.83/0.99      | r1_tarski(sK3,k2_pre_topc(sK1,sK3)) ),
% 2.83/0.99      inference(instantiation,[status(thm)],[c_456]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_1726,plain,
% 2.83/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.83/0.99      | r1_tarski(sK3,k2_pre_topc(sK1,sK3)) = iProver_top ),
% 2.83/0.99      inference(predicate_to_equality,[status(thm)],[c_1725]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_8,plain,
% 2.83/0.99      ( v6_tops_1(X0,X1)
% 2.83/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.83/0.99      | ~ l1_pre_topc(X1)
% 2.83/0.99      | k1_tops_1(X1,k2_pre_topc(X1,X0)) != X0 ),
% 2.83/0.99      inference(cnf_transformation,[],[f43]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_392,plain,
% 2.83/0.99      ( v6_tops_1(X0,X1)
% 2.83/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.83/0.99      | k1_tops_1(X1,k2_pre_topc(X1,X0)) != X0
% 2.83/0.99      | sK1 != X1 ),
% 2.83/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_22]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_393,plain,
% 2.83/0.99      ( v6_tops_1(X0,sK1)
% 2.83/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.83/0.99      | k1_tops_1(sK1,k2_pre_topc(sK1,X0)) != X0 ),
% 2.83/0.99      inference(unflattening,[status(thm)],[c_392]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_1734,plain,
% 2.83/0.99      ( v6_tops_1(sK3,sK1)
% 2.83/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.83/0.99      | k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) != sK3 ),
% 2.83/0.99      inference(instantiation,[status(thm)],[c_393]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_1735,plain,
% 2.83/0.99      ( k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) != sK3
% 2.83/0.99      | v6_tops_1(sK3,sK1) = iProver_top
% 2.83/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.83/0.99      inference(predicate_to_equality,[status(thm)],[c_1734]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_1737,plain,
% 2.83/0.99      ( ~ v6_tops_1(sK2,sK0)
% 2.83/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.83/0.99      | k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = sK2 ),
% 2.83/0.99      inference(instantiation,[status(thm)],[c_531]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_1738,plain,
% 2.83/0.99      ( k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = sK2
% 2.83/0.99      | v6_tops_1(sK2,sK0) != iProver_top
% 2.83/0.99      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.83/0.99      inference(predicate_to_equality,[status(thm)],[c_1737]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_0,plain,
% 2.83/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.83/0.99      inference(cnf_transformation,[],[f36]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_1844,plain,
% 2.83/0.99      ( ~ r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3)
% 2.83/0.99      | ~ r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))
% 2.83/0.99      | k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) = sK3 ),
% 2.83/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_1845,plain,
% 2.83/0.99      ( k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) = sK3
% 2.83/0.99      | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3) != iProver_top
% 2.83/0.99      | r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) != iProver_top ),
% 2.83/0.99      inference(predicate_to_equality,[status(thm)],[c_1844]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_7,plain,
% 2.83/0.99      ( ~ v4_tops_1(X0,X1)
% 2.83/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.83/0.99      | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
% 2.83/0.99      | ~ l1_pre_topc(X1) ),
% 2.83/0.99      inference(cnf_transformation,[],[f39]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_407,plain,
% 2.83/0.99      ( ~ v4_tops_1(X0,X1)
% 2.83/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.83/0.99      | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
% 2.83/0.99      | sK1 != X1 ),
% 2.83/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_22]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_408,plain,
% 2.83/0.99      ( ~ v4_tops_1(X0,sK1)
% 2.83/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.83/0.99      | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,X0)),X0) ),
% 2.83/0.99      inference(unflattening,[status(thm)],[c_407]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_1855,plain,
% 2.83/0.99      ( ~ v4_tops_1(sK3,sK1)
% 2.83/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.83/0.99      | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3) ),
% 2.83/0.99      inference(instantiation,[status(thm)],[c_408]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_1856,plain,
% 2.83/0.99      ( v4_tops_1(sK3,sK1) != iProver_top
% 2.83/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.83/0.99      | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3) = iProver_top ),
% 2.83/0.99      inference(predicate_to_equality,[status(thm)],[c_1855]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_13,plain,
% 2.83/0.99      ( ~ v3_pre_topc(X0,X1)
% 2.83/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.83/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.83/0.99      | ~ r1_tarski(X0,X2)
% 2.83/0.99      | r1_tarski(X0,k1_tops_1(X1,X2))
% 2.83/0.99      | ~ l1_pre_topc(X1) ),
% 2.83/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_344,plain,
% 2.83/0.99      ( ~ v3_pre_topc(X0,X1)
% 2.83/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.83/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.83/0.99      | ~ r1_tarski(X0,X2)
% 2.83/0.99      | r1_tarski(X0,k1_tops_1(X1,X2))
% 2.83/0.99      | sK1 != X1 ),
% 2.83/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_22]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_345,plain,
% 2.83/0.99      ( ~ v3_pre_topc(X0,sK1)
% 2.83/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.83/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.83/0.99      | ~ r1_tarski(X0,X1)
% 2.83/0.99      | r1_tarski(X0,k1_tops_1(sK1,X1)) ),
% 2.83/0.99      inference(unflattening,[status(thm)],[c_344]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_1865,plain,
% 2.83/0.99      ( ~ v3_pre_topc(sK3,sK1)
% 2.83/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.83/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.83/0.99      | ~ r1_tarski(sK3,X0)
% 2.83/0.99      | r1_tarski(sK3,k1_tops_1(sK1,X0)) ),
% 2.83/0.99      inference(instantiation,[status(thm)],[c_345]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_1957,plain,
% 2.83/0.99      ( ~ v3_pre_topc(sK3,sK1)
% 2.83/0.99      | ~ m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.83/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.83/0.99      | r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))
% 2.83/0.99      | ~ r1_tarski(sK3,k2_pre_topc(sK1,sK3)) ),
% 2.83/0.99      inference(instantiation,[status(thm)],[c_1865]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_1958,plain,
% 2.83/0.99      ( v3_pre_topc(sK3,sK1) != iProver_top
% 2.83/0.99      | m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.83/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.83/0.99      | r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) = iProver_top
% 2.83/0.99      | r1_tarski(sK3,k2_pre_topc(sK1,sK3)) != iProver_top ),
% 2.83/0.99      inference(predicate_to_equality,[status(thm)],[c_1957]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_2574,plain,
% 2.83/0.99      ( k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = sK2 ),
% 2.83/0.99      inference(global_propositional_subsumption,
% 2.83/0.99                [status(thm)],
% 2.83/0.99                [c_2557,c_28,c_29,c_30,c_31,c_32,c_1713,c_1726,c_1735,c_1738,
% 2.83/0.99                 c_1845,c_1856,c_1958]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_5,plain,
% 2.83/0.99      ( v4_tops_1(X0,X1)
% 2.83/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.83/0.99      | ~ r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
% 2.83/0.99      | ~ r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
% 2.83/0.99      | ~ l1_pre_topc(X1) ),
% 2.83/0.99      inference(cnf_transformation,[],[f41]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_590,plain,
% 2.83/0.99      ( v4_tops_1(X0,X1)
% 2.83/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.83/0.99      | ~ r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
% 2.83/0.99      | ~ r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
% 2.83/0.99      | sK0 != X1 ),
% 2.83/0.99      inference(resolution_lifted,[status(thm)],[c_5,c_23]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_591,plain,
% 2.83/0.99      ( v4_tops_1(X0,sK0)
% 2.83/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.83/0.99      | ~ r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,X0)))
% 2.83/0.99      | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X0) ),
% 2.83/0.99      inference(unflattening,[status(thm)],[c_590]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_1404,plain,
% 2.83/0.99      ( v4_tops_1(X0,sK0) = iProver_top
% 2.83/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.83/0.99      | r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,X0))) != iProver_top
% 2.83/0.99      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X0) != iProver_top ),
% 2.83/0.99      inference(predicate_to_equality,[status(thm)],[c_591]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_2579,plain,
% 2.83/0.99      ( v4_tops_1(sK2,sK0) = iProver_top
% 2.83/0.99      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.83/0.99      | r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) != iProver_top
% 2.83/0.99      | r1_tarski(sK2,sK2) != iProver_top ),
% 2.83/0.99      inference(superposition,[status(thm)],[c_2574,c_1404]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_16,negated_conjecture,
% 2.83/0.99      ( v3_pre_topc(sK3,sK1) | ~ v3_pre_topc(sK2,sK0) | ~ v4_tops_1(sK2,sK0) ),
% 2.83/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_33,plain,
% 2.83/0.99      ( v3_pre_topc(sK3,sK1) = iProver_top
% 2.83/0.99      | v3_pre_topc(sK2,sK0) != iProver_top
% 2.83/0.99      | v4_tops_1(sK2,sK0) != iProver_top ),
% 2.83/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_15,negated_conjecture,
% 2.83/0.99      ( ~ v3_pre_topc(sK2,sK0) | v4_tops_1(sK3,sK1) | ~ v4_tops_1(sK2,sK0) ),
% 2.83/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_34,plain,
% 2.83/0.99      ( v3_pre_topc(sK2,sK0) != iProver_top
% 2.83/0.99      | v4_tops_1(sK3,sK1) = iProver_top
% 2.83/0.99      | v4_tops_1(sK2,sK0) != iProver_top ),
% 2.83/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_14,negated_conjecture,
% 2.83/0.99      ( ~ v3_pre_topc(sK2,sK0) | ~ v6_tops_1(sK3,sK1) | ~ v4_tops_1(sK2,sK0) ),
% 2.83/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_35,plain,
% 2.83/0.99      ( v3_pre_topc(sK2,sK0) != iProver_top
% 2.83/0.99      | v6_tops_1(sK3,sK1) != iProver_top
% 2.83/0.99      | v4_tops_1(sK2,sK0) != iProver_top ),
% 2.83/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_11,plain,
% 2.83/0.99      ( v3_pre_topc(X0,X1)
% 2.83/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 2.83/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.83/0.99      | ~ v2_pre_topc(X1)
% 2.83/0.99      | ~ l1_pre_topc(X1)
% 2.83/0.99      | ~ l1_pre_topc(X3)
% 2.83/0.99      | k1_tops_1(X1,X0) != X0 ),
% 2.83/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_24,negated_conjecture,
% 2.83/0.99      ( v2_pre_topc(sK0) ),
% 2.83/0.99      inference(cnf_transformation,[],[f48]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_264,plain,
% 2.83/0.99      ( v3_pre_topc(X0,X1)
% 2.83/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.83/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 2.83/0.99      | ~ l1_pre_topc(X1)
% 2.83/0.99      | ~ l1_pre_topc(X3)
% 2.83/0.99      | k1_tops_1(X1,X0) != X0
% 2.83/0.99      | sK0 != X1 ),
% 2.83/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_24]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_265,plain,
% 2.83/0.99      ( v3_pre_topc(X0,sK0)
% 2.83/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.83/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.83/0.99      | ~ l1_pre_topc(X2)
% 2.83/0.99      | ~ l1_pre_topc(sK0)
% 2.83/0.99      | k1_tops_1(sK0,X0) != X0 ),
% 2.83/0.99      inference(unflattening,[status(thm)],[c_264]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_269,plain,
% 2.83/0.99      ( ~ l1_pre_topc(X2)
% 2.83/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.83/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.83/0.99      | v3_pre_topc(X0,sK0)
% 2.83/0.99      | k1_tops_1(sK0,X0) != X0 ),
% 2.83/0.99      inference(global_propositional_subsumption,[status(thm)],[c_265,c_23]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_270,plain,
% 2.83/0.99      ( v3_pre_topc(X0,sK0)
% 2.83/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.83/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.83/0.99      | ~ l1_pre_topc(X2)
% 2.83/0.99      | k1_tops_1(sK0,X0) != X0 ),
% 2.83/0.99      inference(renaming,[status(thm)],[c_269]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_650,plain,
% 2.83/0.99      ( v3_pre_topc(X0,sK0)
% 2.83/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.83/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.83/0.99      | k1_tops_1(sK0,X0) != X0
% 2.83/0.99      | sK0 != X2 ),
% 2.83/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_270]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_651,plain,
% 2.83/0.99      ( v3_pre_topc(X0,sK0)
% 2.83/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.83/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.83/0.99      | k1_tops_1(sK0,X0) != X0 ),
% 2.83/0.99      inference(unflattening,[status(thm)],[c_650]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_761,plain,
% 2.83/0.99      ( v3_pre_topc(X0,sK0)
% 2.83/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.83/0.99      | k1_tops_1(sK0,X0) != X0
% 2.83/0.99      | ~ sP1_iProver_split ),
% 2.83/0.99      inference(splitting,
% 2.83/0.99                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 2.83/0.99                [c_651]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_762,plain,
% 2.83/0.99      ( sP1_iProver_split | sP0_iProver_split ),
% 2.83/0.99      inference(splitting,
% 2.83/0.99                [splitting(split),new_symbols(definition,[])],
% 2.83/0.99                [c_651]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_760,plain,
% 2.83/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~ sP0_iProver_split ),
% 2.83/0.99      inference(splitting,
% 2.83/0.99                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.83/0.99                [c_651]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_890,plain,
% 2.83/0.99      ( k1_tops_1(sK0,X0) != X0
% 2.83/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.83/0.99      | v3_pre_topc(X0,sK0) ),
% 2.83/0.99      inference(global_propositional_subsumption,
% 2.83/0.99                [status(thm)],
% 2.83/0.99                [c_761,c_762,c_760]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_891,plain,
% 2.83/0.99      ( v3_pre_topc(X0,sK0)
% 2.83/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.83/0.99      | k1_tops_1(sK0,X0) != X0 ),
% 2.83/0.99      inference(renaming,[status(thm)],[c_890]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_897,plain,
% 2.83/0.99      ( k1_tops_1(sK0,X0) != X0
% 2.83/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.83/0.99      | v3_pre_topc(X0,sK0) ),
% 2.83/0.99      inference(global_propositional_subsumption,[status(thm)],[c_761,c_891]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_898,plain,
% 2.83/0.99      ( v3_pre_topc(X0,sK0)
% 2.83/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.83/0.99      | k1_tops_1(sK0,X0) != X0 ),
% 2.83/0.99      inference(renaming,[status(thm)],[c_897]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_1750,plain,
% 2.83/0.99      ( v3_pre_topc(sK2,sK0)
% 2.83/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.83/0.99      | k1_tops_1(sK0,sK2) != sK2 ),
% 2.83/0.99      inference(instantiation,[status(thm)],[c_898]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_1751,plain,
% 2.83/0.99      ( k1_tops_1(sK0,sK2) != sK2
% 2.83/0.99      | v3_pre_topc(sK2,sK0) = iProver_top
% 2.83/0.99      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.83/0.99      inference(predicate_to_equality,[status(thm)],[c_1750]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_1756,plain,
% 2.83/0.99      ( v4_tops_1(sK2,sK0)
% 2.83/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.83/0.99      | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK2)
% 2.83/0.99      | ~ r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) ),
% 2.83/0.99      inference(instantiation,[status(thm)],[c_591]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_1757,plain,
% 2.83/0.99      ( v4_tops_1(sK2,sK0) = iProver_top
% 2.83/0.99      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.83/0.99      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK2) != iProver_top
% 2.83/0.99      | r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) != iProver_top ),
% 2.83/0.99      inference(predicate_to_equality,[status(thm)],[c_1756]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_770,plain,( X0 = X0 ),theory(equality) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_1976,plain,
% 2.83/0.99      ( sK2 = sK2 ),
% 2.83/0.99      inference(instantiation,[status(thm)],[c_770]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_772,plain,
% 2.83/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.83/0.99      theory(equality) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_1894,plain,
% 2.83/0.99      ( ~ r1_tarski(X0,X1)
% 2.83/0.99      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK2)
% 2.83/0.99      | k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) != X0
% 2.83/0.99      | sK2 != X1 ),
% 2.83/0.99      inference(instantiation,[status(thm)],[c_772]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_2233,plain,
% 2.83/0.99      ( ~ r1_tarski(X0,sK2)
% 2.83/0.99      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK2)
% 2.83/0.99      | k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) != X0
% 2.83/0.99      | sK2 != sK2 ),
% 2.83/0.99      inference(instantiation,[status(thm)],[c_1894]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_2743,plain,
% 2.83/0.99      ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK2)
% 2.83/0.99      | ~ r1_tarski(sK2,sK2)
% 2.83/0.99      | k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) != sK2
% 2.83/0.99      | sK2 != sK2 ),
% 2.83/0.99      inference(instantiation,[status(thm)],[c_2233]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_2745,plain,
% 2.83/0.99      ( k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) != sK2
% 2.83/0.99      | sK2 != sK2
% 2.83/0.99      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK2) = iProver_top
% 2.83/0.99      | r1_tarski(sK2,sK2) != iProver_top ),
% 2.83/0.99      inference(predicate_to_equality,[status(thm)],[c_2743]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_2,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f60]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_2744,plain,
% 2.83/0.99      ( r1_tarski(sK2,sK2) ),
% 2.83/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_2747,plain,
% 2.83/0.99      ( r1_tarski(sK2,sK2) = iProver_top ),
% 2.83/0.99      inference(predicate_to_equality,[status(thm)],[c_2744]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_620,plain,
% 2.83/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.83/0.99      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.83/0.99      | sK0 != X1 ),
% 2.83/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_23]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_621,plain,
% 2.83/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.83/0.99      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.83/0.99      inference(unflattening,[status(thm)],[c_620]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_1402,plain,
% 2.83/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.83/0.99      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.83/0.99      inference(predicate_to_equality,[status(thm)],[c_621]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_10,plain,
% 2.83/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.83/0.99      | ~ l1_pre_topc(X1)
% 2.83/0.99      | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
% 2.83/0.99      inference(cnf_transformation,[],[f44]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_518,plain,
% 2.83/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.83/0.99      | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0)
% 2.83/0.99      | sK0 != X1 ),
% 2.83/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_23]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_519,plain,
% 2.83/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.83/0.99      | k1_tops_1(sK0,k1_tops_1(sK0,X0)) = k1_tops_1(sK0,X0) ),
% 2.83/0.99      inference(unflattening,[status(thm)],[c_518]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_1409,plain,
% 2.83/0.99      ( k1_tops_1(sK0,k1_tops_1(sK0,X0)) = k1_tops_1(sK0,X0)
% 2.83/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.83/0.99      inference(predicate_to_equality,[status(thm)],[c_519]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_2202,plain,
% 2.83/0.99      ( k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,X0))) = k1_tops_1(sK0,k2_pre_topc(sK0,X0))
% 2.83/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.83/0.99      inference(superposition,[status(thm)],[c_1402,c_1409]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_3883,plain,
% 2.83/0.99      ( k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK2))) = k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) ),
% 2.83/0.99      inference(superposition,[status(thm)],[c_1426,c_2202]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_3890,plain,
% 2.83/0.99      ( k1_tops_1(sK0,sK2) = sK2 ),
% 2.83/0.99      inference(light_normalisation,[status(thm)],[c_3883,c_2574]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_1414,plain,
% 2.83/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.83/0.99      | m1_subset_1(k2_pre_topc(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.83/0.99      inference(predicate_to_equality,[status(thm)],[c_468]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_1427,plain,
% 2.83/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.83/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_1422,plain,
% 2.83/0.99      ( v3_pre_topc(X0,sK1) != iProver_top
% 2.83/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.83/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.83/0.99      | r1_tarski(X0,X1) != iProver_top
% 2.83/0.99      | r1_tarski(X0,k1_tops_1(sK1,X1)) = iProver_top ),
% 2.83/0.99      inference(predicate_to_equality,[status(thm)],[c_345]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_3461,plain,
% 2.83/0.99      ( v3_pre_topc(sK3,sK1) != iProver_top
% 2.83/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.83/0.99      | r1_tarski(sK3,X0) != iProver_top
% 2.83/0.99      | r1_tarski(sK3,k1_tops_1(sK1,X0)) = iProver_top ),
% 2.83/0.99      inference(superposition,[status(thm)],[c_1427,c_1422]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_3697,plain,
% 2.83/0.99      ( v3_pre_topc(sK3,sK1) != iProver_top
% 2.83/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.83/0.99      | r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,X0))) = iProver_top
% 2.83/0.99      | r1_tarski(sK3,k2_pre_topc(sK1,X0)) != iProver_top ),
% 2.83/0.99      inference(superposition,[status(thm)],[c_1414,c_3461]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_1418,plain,
% 2.83/0.99      ( v4_tops_1(X0,sK1) != iProver_top
% 2.83/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.83/0.99      | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,X0)),X0) = iProver_top ),
% 2.83/0.99      inference(predicate_to_equality,[status(thm)],[c_408]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_1435,plain,
% 2.83/0.99      ( X0 = X1
% 2.83/0.99      | r1_tarski(X0,X1) != iProver_top
% 2.83/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 2.83/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_3088,plain,
% 2.83/0.99      ( k1_tops_1(sK1,k2_pre_topc(sK1,X0)) = X0
% 2.83/0.99      | v4_tops_1(X0,sK1) != iProver_top
% 2.83/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.83/0.99      | r1_tarski(X0,k1_tops_1(sK1,k2_pre_topc(sK1,X0))) != iProver_top ),
% 2.83/0.99      inference(superposition,[status(thm)],[c_1418,c_1435]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_4707,plain,
% 2.83/0.99      ( k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) = sK3
% 2.83/0.99      | v3_pre_topc(sK3,sK1) != iProver_top
% 2.83/0.99      | v4_tops_1(sK3,sK1) != iProver_top
% 2.83/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.83/0.99      | r1_tarski(sK3,k2_pre_topc(sK1,sK3)) != iProver_top ),
% 2.83/0.99      inference(superposition,[status(thm)],[c_3697,c_3088]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_5101,plain,
% 2.83/0.99      ( r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) != iProver_top ),
% 2.83/0.99      inference(global_propositional_subsumption,
% 2.83/0.99                [status(thm)],
% 2.83/0.99                [c_2579,c_28,c_29,c_30,c_31,c_32,c_33,c_34,c_35,c_1713,
% 2.83/0.99                 c_1726,c_1735,c_1738,c_1751,c_1757,c_1845,c_1856,c_1958,
% 2.83/0.99                 c_1976,c_2745,c_2747,c_3890,c_4707]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_5105,plain,
% 2.83/0.99      ( r1_tarski(sK2,k2_pre_topc(sK0,sK2)) != iProver_top ),
% 2.83/0.99      inference(light_normalisation,[status(thm)],[c_5101,c_3890]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_608,plain,
% 2.83/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.83/0.99      | r1_tarski(X0,k2_pre_topc(X1,X0))
% 2.83/0.99      | sK0 != X1 ),
% 2.83/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_23]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_609,plain,
% 2.83/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.83/0.99      | r1_tarski(X0,k2_pre_topc(sK0,X0)) ),
% 2.83/0.99      inference(unflattening,[status(thm)],[c_608]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_1403,plain,
% 2.83/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.83/0.99      | r1_tarski(X0,k2_pre_topc(sK0,X0)) = iProver_top ),
% 2.83/0.99      inference(predicate_to_equality,[status(thm)],[c_609]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_1889,plain,
% 2.83/0.99      ( r1_tarski(sK2,k2_pre_topc(sK0,sK2)) = iProver_top ),
% 2.83/0.99      inference(superposition,[status(thm)],[c_1426,c_1403]) ).
% 2.83/0.99  
% 2.83/0.99  cnf(c_5107,plain,
% 2.83/0.99      ( $false ),
% 2.83/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_5105,c_1889]) ).
% 2.83/0.99  
% 2.83/0.99  
% 2.83/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.83/0.99  
% 2.83/0.99  ------                               Statistics
% 2.83/0.99  
% 2.83/0.99  ------ General
% 2.83/0.99  
% 2.83/0.99  abstr_ref_over_cycles:                  0
% 2.83/0.99  abstr_ref_under_cycles:                 0
% 2.83/0.99  gc_basic_clause_elim:                   0
% 2.83/0.99  forced_gc_time:                         0
% 2.83/0.99  parsing_time:                           0.011
% 2.83/0.99  unif_index_cands_time:                  0.
% 2.83/0.99  unif_index_add_time:                    0.
% 2.83/0.99  orderings_time:                         0.
% 2.83/0.99  out_proof_time:                         0.01
% 2.83/0.99  total_time:                             0.178
% 2.83/0.99  num_of_symbols:                         51
% 2.83/0.99  num_of_terms:                           3295
% 2.83/0.99  
% 2.83/0.99  ------ Preprocessing
% 2.83/0.99  
% 2.83/0.99  num_of_splits:                          8
% 2.83/0.99  num_of_split_atoms:                     5
% 2.83/0.99  num_of_reused_defs:                     3
% 2.83/0.99  num_eq_ax_congr_red:                    2
% 2.83/0.99  num_of_sem_filtered_clauses:            5
% 2.83/0.99  num_of_subtypes:                        0
% 2.83/0.99  monotx_restored_types:                  0
% 2.83/0.99  sat_num_of_epr_types:                   0
% 2.83/0.99  sat_num_of_non_cyclic_types:            0
% 2.83/0.99  sat_guarded_non_collapsed_types:        0
% 2.83/0.99  num_pure_diseq_elim:                    0
% 2.83/0.99  simp_replaced_by:                       0
% 2.83/0.99  res_preprocessed:                       117
% 2.83/0.99  prep_upred:                             0
% 2.83/0.99  prep_unflattend:                        24
% 2.83/0.99  smt_new_axioms:                         0
% 2.83/0.99  pred_elim_cands:                        7
% 2.83/0.99  pred_elim:                              2
% 2.83/0.99  pred_elim_cl:                           -8
% 2.83/0.99  pred_elim_cycles:                       3
% 2.83/0.99  merged_defs:                            0
% 2.83/0.99  merged_defs_ncl:                        0
% 2.83/0.99  bin_hyper_res:                          0
% 2.83/0.99  prep_cycles:                            3
% 2.83/0.99  pred_elim_time:                         0.009
% 2.83/0.99  splitting_time:                         0.
% 2.83/0.99  sem_filter_time:                        0.
% 2.83/0.99  monotx_time:                            0.001
% 2.83/0.99  subtype_inf_time:                       0.
% 2.83/0.99  
% 2.83/0.99  ------ Problem properties
% 2.83/0.99  
% 2.83/0.99  clauses:                                40
% 2.83/0.99  conjectures:                            8
% 2.83/0.99  epr:                                    12
% 2.83/0.99  horn:                                   34
% 2.83/0.99  ground:                                 12
% 2.83/0.99  unary:                                  3
% 2.83/0.99  binary:                                 17
% 2.83/0.99  lits:                                   107
% 2.83/0.99  lits_eq:                                11
% 2.83/0.99  fd_pure:                                0
% 2.83/0.99  fd_pseudo:                              0
% 2.83/0.99  fd_cond:                                0
% 2.83/0.99  fd_pseudo_cond:                         1
% 2.83/0.99  ac_symbols:                             0
% 2.83/0.99  
% 2.83/0.99  ------ Propositional Solver
% 2.83/0.99  
% 2.83/0.99  prop_solver_calls:                      24
% 2.83/0.99  prop_fast_solver_calls:                 1009
% 2.83/0.99  smt_solver_calls:                       0
% 2.83/0.99  smt_fast_solver_calls:                  0
% 2.83/0.99  prop_num_of_clauses:                    1751
% 2.83/0.99  prop_preprocess_simplified:             5429
% 2.83/0.99  prop_fo_subsumed:                       22
% 2.83/0.99  prop_solver_time:                       0.
% 2.83/0.99  smt_solver_time:                        0.
% 2.83/0.99  smt_fast_solver_time:                   0.
% 2.83/0.99  prop_fast_solver_time:                  0.
% 2.83/0.99  prop_unsat_core_time:                   0.
% 2.83/0.99  
% 2.83/0.99  ------ QBF
% 2.83/0.99  
% 2.83/0.99  qbf_q_res:                              0
% 2.83/0.99  qbf_num_tautologies:                    0
% 2.83/0.99  qbf_prep_cycles:                        0
% 2.83/0.99  
% 2.83/0.99  ------ BMC1
% 2.83/0.99  
% 2.83/0.99  bmc1_current_bound:                     -1
% 2.83/0.99  bmc1_last_solved_bound:                 -1
% 2.83/0.99  bmc1_unsat_core_size:                   -1
% 2.83/0.99  bmc1_unsat_core_parents_size:           -1
% 2.83/0.99  bmc1_merge_next_fun:                    0
% 2.83/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.83/0.99  
% 2.83/0.99  ------ Instantiation
% 2.83/0.99  
% 2.83/0.99  inst_num_of_clauses:                    575
% 2.83/0.99  inst_num_in_passive:                    159
% 2.83/0.99  inst_num_in_active:                     384
% 2.83/0.99  inst_num_in_unprocessed:                32
% 2.83/0.99  inst_num_of_loops:                      420
% 2.83/0.99  inst_num_of_learning_restarts:          0
% 2.83/0.99  inst_num_moves_active_passive:          32
% 2.83/0.99  inst_lit_activity:                      0
% 2.83/0.99  inst_lit_activity_moves:                0
% 2.83/0.99  inst_num_tautologies:                   0
% 2.83/0.99  inst_num_prop_implied:                  0
% 2.83/0.99  inst_num_existing_simplified:           0
% 2.83/0.99  inst_num_eq_res_simplified:             0
% 2.83/0.99  inst_num_child_elim:                    0
% 2.83/0.99  inst_num_of_dismatching_blockings:      72
% 2.83/0.99  inst_num_of_non_proper_insts:           628
% 2.83/0.99  inst_num_of_duplicates:                 0
% 2.83/0.99  inst_inst_num_from_inst_to_res:         0
% 2.83/0.99  inst_dismatching_checking_time:         0.
% 2.83/0.99  
% 2.83/0.99  ------ Resolution
% 2.83/0.99  
% 2.83/0.99  res_num_of_clauses:                     0
% 2.83/0.99  res_num_in_passive:                     0
% 2.83/0.99  res_num_in_active:                      0
% 2.83/0.99  res_num_of_loops:                       120
% 2.83/0.99  res_forward_subset_subsumed:            52
% 2.83/0.99  res_backward_subset_subsumed:           0
% 2.83/0.99  res_forward_subsumed:                   0
% 2.83/0.99  res_backward_subsumed:                  0
% 2.83/0.99  res_forward_subsumption_resolution:     0
% 2.83/0.99  res_backward_subsumption_resolution:    0
% 2.83/0.99  res_clause_to_clause_subsumption:       389
% 2.83/0.99  res_orphan_elimination:                 0
% 2.83/0.99  res_tautology_del:                      72
% 2.83/0.99  res_num_eq_res_simplified:              0
% 2.83/0.99  res_num_sel_changes:                    0
% 2.83/0.99  res_moves_from_active_to_pass:          0
% 2.83/0.99  
% 2.83/0.99  ------ Superposition
% 2.83/0.99  
% 2.83/0.99  sup_time_total:                         0.
% 2.83/0.99  sup_time_generating:                    0.
% 2.83/0.99  sup_time_sim_full:                      0.
% 2.83/0.99  sup_time_sim_immed:                     0.
% 2.83/0.99  
% 2.83/0.99  sup_num_of_clauses:                     94
% 2.83/0.99  sup_num_in_active:                      78
% 2.83/0.99  sup_num_in_passive:                     16
% 2.83/0.99  sup_num_of_loops:                       83
% 2.83/0.99  sup_fw_superposition:                   49
% 2.83/0.99  sup_bw_superposition:                   37
% 2.83/0.99  sup_immediate_simplified:               27
% 2.83/0.99  sup_given_eliminated:                   0
% 2.83/0.99  comparisons_done:                       0
% 2.83/0.99  comparisons_avoided:                    0
% 2.83/0.99  
% 2.83/0.99  ------ Simplifications
% 2.83/0.99  
% 2.83/0.99  
% 2.83/0.99  sim_fw_subset_subsumed:                 6
% 2.83/0.99  sim_bw_subset_subsumed:                 3
% 2.83/0.99  sim_fw_subsumed:                        12
% 2.83/0.99  sim_bw_subsumed:                        0
% 2.83/0.99  sim_fw_subsumption_res:                 1
% 2.83/0.99  sim_bw_subsumption_res:                 0
% 2.83/0.99  sim_tautology_del:                      1
% 2.83/0.99  sim_eq_tautology_del:                   2
% 2.83/0.99  sim_eq_res_simp:                        0
% 2.83/0.99  sim_fw_demodulated:                     0
% 2.83/0.99  sim_bw_demodulated:                     3
% 2.83/0.99  sim_light_normalised:                   11
% 2.83/0.99  sim_joinable_taut:                      0
% 2.83/0.99  sim_joinable_simp:                      0
% 2.83/0.99  sim_ac_normalised:                      0
% 2.83/0.99  sim_smt_subsumption:                    0
% 2.83/0.99  
%------------------------------------------------------------------------------
