%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:15:55 EST 2020

% Result     : Theorem 7.86s
% Output     : CNFRefutation 7.86s
% Verified   : 
% Statistics : Number of formulae       :  282 (11280 expanded)
%              Number of clauses        :  225 (3263 expanded)
%              Number of leaves         :   20 (3773 expanded)
%              Depth                    :   27
%              Number of atoms          : 1019 (103214 expanded)
%              Number of equality atoms :  414 (5248 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    5 (   2 average)

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

fof(f53,plain,
    ( v6_tops_1(sK2,sK0)
    | v3_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f52,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f33])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f48,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f49,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f50,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f51,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f33])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X2,X0)
      | k1_tops_1(X0,X2) != X2
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v6_tops_1(X1,X0)
          <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_tops_1(X1,X0)
          <=> ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f55,plain,
    ( v6_tops_1(sK2,sK0)
    | ~ v6_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f33])).

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

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f60,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f34])).

fof(f36,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f54,plain,
    ( v6_tops_1(sK2,sK0)
    | v4_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v4_tops_1(X1,X0)
      | ~ r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
      | ~ r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f58,plain,
    ( ~ v4_tops_1(sK2,sK0)
    | ~ v3_pre_topc(sK2,sK0)
    | ~ v6_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f57,plain,
    ( ~ v4_tops_1(sK2,sK0)
    | ~ v3_pre_topc(sK2,sK0)
    | v4_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f56,plain,
    ( ~ v4_tops_1(sK2,sK0)
    | ~ v3_pre_topc(sK2,sK0)
    | v3_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_19,negated_conjecture,
    ( v3_pre_topc(sK3,sK1)
    | v6_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1413,plain,
    ( v3_pre_topc(sK3,sK1) = iProver_top
    | v6_tops_1(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1412,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_13,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_24,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_289,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X1,X0) = X0
    | sK0 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_24])).

cnf(c_290,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK0)
    | k1_tops_1(X1,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_289])).

cnf(c_23,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_294,plain,
    ( ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X0,X1)
    | k1_tops_1(X1,X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_290,c_23])).

cnf(c_295,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = X0 ),
    inference(renaming,[status(thm)],[c_294])).

cnf(c_22,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_326,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(X1,X0) = X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_295,c_22])).

cnf(c_327,plain,
    ( ~ v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK1,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_326])).

cnf(c_759,plain,
    ( ~ v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,X0) = X0
    | ~ sP4_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP4_iProver_split])],[c_327])).

cnf(c_1409,plain,
    ( k1_tops_1(sK1,X0) = X0
    | v3_pre_topc(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | sP4_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_759])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_28,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_760,plain,
    ( sP4_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_327])).

cnf(c_815,plain,
    ( sP4_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_760])).

cnf(c_816,plain,
    ( k1_tops_1(sK1,X0) = X0
    | v3_pre_topc(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | sP4_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_759])).

cnf(c_12,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_264,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X1,X0) != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_24])).

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

cnf(c_644,plain,
    ( v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) != X0
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_270])).

cnf(c_645,plain,
    ( v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_644])).

cnf(c_752,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_645])).

cnf(c_1496,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ sP0_iProver_split ),
    inference(instantiation,[status(thm)],[c_752])).

cnf(c_1497,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1496])).

cnf(c_2694,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v3_pre_topc(X0,sK1) != iProver_top
    | k1_tops_1(sK1,X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1409,c_28,c_815,c_816,c_1497])).

cnf(c_2695,plain,
    ( k1_tops_1(sK1,X0) = X0
    | v3_pre_topc(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2694])).

cnf(c_2700,plain,
    ( k1_tops_1(sK1,sK3) = sK3
    | v3_pre_topc(sK3,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1412,c_2695])).

cnf(c_2707,plain,
    ( k1_tops_1(sK1,sK3) = sK3
    | v6_tops_1(sK2,sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1413,c_2700])).

cnf(c_1411,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_9,plain,
    ( ~ v6_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,k2_pre_topc(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_524,plain,
    ( ~ v6_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,k2_pre_topc(X1,X0)) = X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_23])).

cnf(c_525,plain,
    ( ~ v6_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,k2_pre_topc(sK0,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_524])).

cnf(c_1393,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,X0)) = X0
    | v6_tops_1(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_525])).

cnf(c_2297,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = sK2
    | v6_tops_1(sK2,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1411,c_1393])).

cnf(c_2817,plain,
    ( k1_tops_1(sK1,sK3) = sK3
    | k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_2707,c_2297])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_614,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_23])).

cnf(c_615,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_614])).

cnf(c_1387,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_615])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_512,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_23])).

cnf(c_513,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,k1_tops_1(sK0,X0)) = k1_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_512])).

cnf(c_1394,plain,
    ( k1_tops_1(sK0,k1_tops_1(sK0,X0)) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_513])).

cnf(c_1990,plain,
    ( k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,X0))) = k1_tops_1(sK0,k2_pre_topc(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1387,c_1394])).

cnf(c_3130,plain,
    ( k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK2))) = k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) ),
    inference(superposition,[status(thm)],[c_1411,c_1990])).

cnf(c_3875,plain,
    ( k1_tops_1(sK1,sK3) = sK3
    | k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = k1_tops_1(sK0,sK2) ),
    inference(superposition,[status(thm)],[c_2817,c_3130])).

cnf(c_7,plain,
    ( ~ v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_554,plain,
    ( ~ v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_23])).

cnf(c_555,plain,
    ( ~ v4_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X0) ),
    inference(unflattening,[status(thm)],[c_554])).

cnf(c_1391,plain,
    ( v4_tops_1(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_555])).

cnf(c_3935,plain,
    ( k1_tops_1(sK1,sK3) = sK3
    | v4_tops_1(sK2,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK2),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3875,c_1391])).

cnf(c_29,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_17,negated_conjecture,
    ( ~ v6_tops_1(sK3,sK1)
    | v6_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_32,plain,
    ( v6_tops_1(sK3,sK1) != iProver_top
    | v6_tops_1(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_70,plain,
    ( r1_tarski(sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_74,plain,
    ( ~ r1_tarski(sK0,sK0)
    | sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_464,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_22])).

cnf(c_465,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k2_pre_topc(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_464])).

cnf(c_1504,plain,
    ( m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_465])).

cnf(c_1505,plain,
    ( m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1504])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_452,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_22])).

cnf(c_453,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(X0,k2_pre_topc(sK1,X0)) ),
    inference(unflattening,[status(thm)],[c_452])).

cnf(c_1522,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(sK3,k2_pre_topc(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_453])).

cnf(c_1523,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(sK3,k2_pre_topc(sK1,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1522])).

cnf(c_8,plain,
    ( v6_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,k2_pre_topc(X1,X0)) != X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_389,plain,
    ( v6_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,k2_pre_topc(X1,X0)) != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_22])).

cnf(c_390,plain,
    ( v6_tops_1(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,k2_pre_topc(sK1,X0)) != X0 ),
    inference(unflattening,[status(thm)],[c_389])).

cnf(c_1539,plain,
    ( v6_tops_1(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) != sK3 ),
    inference(instantiation,[status(thm)],[c_390])).

cnf(c_1540,plain,
    ( k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) != sK3
    | v6_tops_1(sK3,sK1) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1539])).

cnf(c_1654,plain,
    ( ~ r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3)
    | ~ r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))
    | k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) = sK3 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1655,plain,
    ( k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) = sK3
    | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3) != iProver_top
    | r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1654])).

cnf(c_404,plain,
    ( ~ v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_22])).

cnf(c_405,plain,
    ( ~ v4_tops_1(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,X0)),X0) ),
    inference(unflattening,[status(thm)],[c_404])).

cnf(c_1664,plain,
    ( ~ v4_tops_1(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3) ),
    inference(instantiation,[status(thm)],[c_405])).

cnf(c_1665,plain,
    ( v4_tops_1(sK3,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1664])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_344,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_22])).

cnf(c_345,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X0,X1)
    | r1_tarski(k1_tops_1(sK1,X0),k1_tops_1(sK1,X1)) ),
    inference(unflattening,[status(thm)],[c_344])).

cnf(c_1569,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(k1_tops_1(sK1,sK3),k1_tops_1(sK1,X0))
    | ~ r1_tarski(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_345])).

cnf(c_1686,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(k1_tops_1(sK1,sK3),k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))
    | ~ r1_tarski(sK3,k2_pre_topc(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_1569])).

cnf(c_1687,plain,
    ( m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(k1_tops_1(sK1,sK3),k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) = iProver_top
    | r1_tarski(sK3,k2_pre_topc(sK1,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1686])).

cnf(c_1595,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),k1_tops_1(sK1,X0))
    | ~ r1_tarski(k2_pre_topc(sK1,sK3),X0) ),
    inference(instantiation,[status(thm)],[c_345])).

cnf(c_1825,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))
    | ~ r1_tarski(k2_pre_topc(sK1,sK3),k2_pre_topc(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_1595])).

cnf(c_1969,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1970,plain,
    ( r1_tarski(sK2,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1969])).

cnf(c_762,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2033,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_762])).

cnf(c_2067,plain,
    ( r1_tarski(k2_pre_topc(sK1,sK3),k2_pre_topc(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_18,negated_conjecture,
    ( v6_tops_1(sK2,sK0)
    | v4_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1414,plain,
    ( v6_tops_1(sK2,sK0) = iProver_top
    | v4_tops_1(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2304,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = sK2
    | v4_tops_1(sK3,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1414,c_2297])).

cnf(c_476,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(X1,X0) = X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_295,c_23])).

cnf(c_477,plain,
    ( ~ v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_476])).

cnf(c_757,plain,
    ( ~ v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) = X0
    | ~ sP3_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP3_iProver_split])],[c_477])).

cnf(c_1397,plain,
    ( k1_tops_1(sK0,X0) = X0
    | v3_pre_topc(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | sP3_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_757])).

cnf(c_758,plain,
    ( sP3_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_477])).

cnf(c_803,plain,
    ( sP3_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_758])).

cnf(c_804,plain,
    ( k1_tops_1(sK0,X0) = X0
    | v3_pre_topc(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | sP3_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_757])).

cnf(c_2590,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v3_pre_topc(X0,sK0) != iProver_top
    | k1_tops_1(sK0,X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1397,c_28,c_803,c_804,c_1497])).

cnf(c_2591,plain,
    ( k1_tops_1(sK0,X0) = X0
    | v3_pre_topc(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2590])).

cnf(c_2594,plain,
    ( k1_tops_1(sK0,sK2) = sK2
    | v3_pre_topc(sK2,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1411,c_2591])).

cnf(c_2686,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_762])).

cnf(c_3938,plain,
    ( k1_tops_1(sK1,sK3) = sK3
    | k1_tops_1(sK0,sK2) = sK2 ),
    inference(superposition,[status(thm)],[c_3875,c_2817])).

cnf(c_764,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1960,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | k1_tops_1(sK0,sK2) != X0
    | sK2 != X1 ),
    inference(instantiation,[status(thm)],[c_764])).

cnf(c_3077,plain,
    ( ~ r1_tarski(X0,sK2)
    | r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | k1_tops_1(sK0,sK2) != X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1960])).

cnf(c_4243,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ r1_tarski(sK2,sK2)
    | k1_tops_1(sK0,sK2) != sK2
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_3077])).

cnf(c_4244,plain,
    ( k1_tops_1(sK0,sK2) != sK2
    | sK2 != sK2
    | r1_tarski(k1_tops_1(sK0,sK2),sK2) = iProver_top
    | r1_tarski(sK2,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4243])).

cnf(c_763,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2081,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_763])).

cnf(c_3110,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2081])).

cnf(c_4248,plain,
    ( k1_tops_1(sK1,sK3) != sK3
    | sK3 = k1_tops_1(sK1,sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_3110])).

cnf(c_1692,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK3,X2)
    | X2 != X1
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_764])).

cnf(c_4650,plain,
    ( ~ r1_tarski(k1_tops_1(sK1,sK3),X0)
    | r1_tarski(sK3,X1)
    | X1 != X0
    | sK3 != k1_tops_1(sK1,sK3) ),
    inference(instantiation,[status(thm)],[c_1692])).

cnf(c_7380,plain,
    ( ~ r1_tarski(k1_tops_1(sK1,sK3),k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))
    | r1_tarski(sK3,X0)
    | X0 != k1_tops_1(sK1,k2_pre_topc(sK1,sK3))
    | sK3 != k1_tops_1(sK1,sK3) ),
    inference(instantiation,[status(thm)],[c_4650])).

cnf(c_9244,plain,
    ( ~ r1_tarski(k1_tops_1(sK1,sK3),k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))
    | r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))
    | k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) != k1_tops_1(sK1,k2_pre_topc(sK1,sK3))
    | sK3 != k1_tops_1(sK1,sK3) ),
    inference(instantiation,[status(thm)],[c_7380])).

cnf(c_9245,plain,
    ( k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) != k1_tops_1(sK1,k2_pre_topc(sK1,sK3))
    | sK3 != k1_tops_1(sK1,sK3)
    | r1_tarski(k1_tops_1(sK1,sK3),k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) != iProver_top
    | r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9244])).

cnf(c_1722,plain,
    ( X0 != X1
    | sK2 != X1
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_763])).

cnf(c_2129,plain,
    ( X0 != sK2
    | sK2 = X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1722])).

cnf(c_12892,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) != sK2
    | sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2))
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_2129])).

cnf(c_753,plain,
    ( v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) != X0
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_645])).

cnf(c_1382,plain,
    ( k1_tops_1(sK0,X0) != X0
    | v3_pre_topc(X0,sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_753])).

cnf(c_754,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_645])).

cnf(c_784,plain,
    ( sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_754])).

cnf(c_785,plain,
    ( k1_tops_1(sK0,X0) != X0
    | v3_pre_topc(X0,sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_753])).

cnf(c_1709,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v3_pre_topc(X0,sK0) = iProver_top
    | k1_tops_1(sK0,X0) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1382,c_28,c_784,c_785,c_1497])).

cnf(c_1710,plain,
    ( k1_tops_1(sK0,X0) != X0
    | v3_pre_topc(X0,sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1709])).

cnf(c_3138,plain,
    ( v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK0) = iProver_top
    | m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3130,c_1710])).

cnf(c_3874,plain,
    ( k1_tops_1(sK1,sK3) = sK3
    | v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK0) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2817,c_3138])).

cnf(c_2205,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_762])).

cnf(c_2267,plain,
    ( k1_zfmisc_1(u1_struct_0(sK0)) = k1_zfmisc_1(u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_762])).

cnf(c_2277,plain,
    ( k1_zfmisc_1(u1_struct_0(sK1)) = k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_762])).

cnf(c_768,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1507,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | X2 != X0
    | k1_zfmisc_1(u1_struct_0(sK1)) != X1 ),
    inference(instantiation,[status(thm)],[c_768])).

cnf(c_1869,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | X1 != X0
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1507])).

cnf(c_3046,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | X0 != sK3
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1869])).

cnf(c_3488,plain,
    ( m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,sK3) != sK3
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_3046])).

cnf(c_3489,plain,
    ( k1_tops_1(sK1,sK3) != sK3
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
    | m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3488])).

cnf(c_769,plain,
    ( ~ v4_tops_1(X0,X1)
    | v4_tops_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2537,plain,
    ( v4_tops_1(X0,X1)
    | ~ v4_tops_1(sK3,sK1)
    | X1 != sK1
    | X0 != sK3 ),
    inference(instantiation,[status(thm)],[c_769])).

cnf(c_2669,plain,
    ( v4_tops_1(X0,sK1)
    | ~ v4_tops_1(sK3,sK1)
    | X0 != sK3
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_2537])).

cnf(c_3682,plain,
    ( v4_tops_1(k1_tops_1(sK1,sK3),sK1)
    | ~ v4_tops_1(sK3,sK1)
    | k1_tops_1(sK1,sK3) != sK3
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_2669])).

cnf(c_3683,plain,
    ( k1_tops_1(sK1,sK3) != sK3
    | sK1 != sK1
    | v4_tops_1(k1_tops_1(sK1,sK3),sK1) = iProver_top
    | v4_tops_1(sK3,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3682])).

cnf(c_4414,plain,
    ( ~ m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(k1_tops_1(sK1,sK3),k2_pre_topc(sK1,k1_tops_1(sK1,sK3))) ),
    inference(instantiation,[status(thm)],[c_453])).

cnf(c_4421,plain,
    ( m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(k1_tops_1(sK1,sK3),k2_pre_topc(sK1,k1_tops_1(sK1,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4414])).

cnf(c_4413,plain,
    ( v6_tops_1(k1_tops_1(sK1,sK3),sK1)
    | ~ m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,k2_pre_topc(sK1,k1_tops_1(sK1,sK3))) != k1_tops_1(sK1,sK3) ),
    inference(instantiation,[status(thm)],[c_390])).

cnf(c_4423,plain,
    ( k1_tops_1(sK1,k2_pre_topc(sK1,k1_tops_1(sK1,sK3))) != k1_tops_1(sK1,sK3)
    | v6_tops_1(k1_tops_1(sK1,sK3),sK1) = iProver_top
    | m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4413])).

cnf(c_362,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_22])).

cnf(c_363,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,k1_tops_1(sK1,X0)) = k1_tops_1(sK1,X0) ),
    inference(unflattening,[status(thm)],[c_362])).

cnf(c_1406,plain,
    ( k1_tops_1(sK1,k1_tops_1(sK1,X0)) = k1_tops_1(sK1,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_363])).

cnf(c_2180,plain,
    ( k1_tops_1(sK1,k1_tops_1(sK1,sK3)) = k1_tops_1(sK1,sK3) ),
    inference(superposition,[status(thm)],[c_1412,c_1406])).

cnf(c_1399,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_465])).

cnf(c_1407,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_tops_1(sK1,X0),k1_tops_1(sK1,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_345])).

cnf(c_1403,plain,
    ( v4_tops_1(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,X0)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_405])).

cnf(c_1420,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2564,plain,
    ( k1_tops_1(sK1,k2_pre_topc(sK1,X0)) = X0
    | v4_tops_1(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X0,k1_tops_1(sK1,k2_pre_topc(sK1,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1403,c_1420])).

cnf(c_2954,plain,
    ( k1_tops_1(sK1,k2_pre_topc(sK1,k1_tops_1(sK1,X0))) = k1_tops_1(sK1,X0)
    | v4_tops_1(k1_tops_1(sK1,X0),sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k1_tops_1(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK1,k1_tops_1(sK1,X0)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK1,k1_tops_1(sK1,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1407,c_2564])).

cnf(c_6909,plain,
    ( k1_tops_1(sK1,k2_pre_topc(sK1,k1_tops_1(sK1,X0))) = k1_tops_1(sK1,X0)
    | v4_tops_1(k1_tops_1(sK1,X0),sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k1_tops_1(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK1,k1_tops_1(sK1,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1399,c_2954])).

cnf(c_7763,plain,
    ( k1_tops_1(sK1,k2_pre_topc(sK1,k1_tops_1(sK1,k1_tops_1(sK1,sK3)))) = k1_tops_1(sK1,k1_tops_1(sK1,sK3))
    | v4_tops_1(k1_tops_1(sK1,k1_tops_1(sK1,sK3)),sK1) != iProver_top
    | m1_subset_1(k1_tops_1(sK1,k1_tops_1(sK1,sK3)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(k1_tops_1(sK1,sK3),k2_pre_topc(sK1,k1_tops_1(sK1,sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2180,c_6909])).

cnf(c_7780,plain,
    ( k1_tops_1(sK1,k2_pre_topc(sK1,k1_tops_1(sK1,sK3))) = k1_tops_1(sK1,sK3)
    | v4_tops_1(k1_tops_1(sK1,sK3),sK1) != iProver_top
    | m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(k1_tops_1(sK1,sK3),k2_pre_topc(sK1,k1_tops_1(sK1,sK3))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7763,c_2180])).

cnf(c_771,plain,
    ( ~ v6_tops_1(X0,X1)
    | v6_tops_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1534,plain,
    ( ~ v6_tops_1(X0,X1)
    | v6_tops_1(X2,sK1)
    | X2 != X0
    | sK1 != X1 ),
    inference(instantiation,[status(thm)],[c_771])).

cnf(c_1736,plain,
    ( ~ v6_tops_1(X0,sK1)
    | v6_tops_1(X1,sK1)
    | X1 != X0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1534])).

cnf(c_6393,plain,
    ( v6_tops_1(X0,sK1)
    | ~ v6_tops_1(k1_tops_1(sK1,sK3),sK1)
    | X0 != k1_tops_1(sK1,sK3)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1736])).

cnf(c_9098,plain,
    ( ~ v6_tops_1(k1_tops_1(sK1,sK3),sK1)
    | v6_tops_1(sK3,sK1)
    | sK1 != sK1
    | sK3 != k1_tops_1(sK1,sK3) ),
    inference(instantiation,[status(thm)],[c_6393])).

cnf(c_9099,plain,
    ( sK1 != sK1
    | sK3 != k1_tops_1(sK1,sK3)
    | v6_tops_1(k1_tops_1(sK1,sK3),sK1) != iProver_top
    | v6_tops_1(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9098])).

cnf(c_1499,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
    | X2 != X0
    | k1_zfmisc_1(u1_struct_0(sK0)) != X1 ),
    inference(instantiation,[status(thm)],[c_768])).

cnf(c_1847,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | X1 != X0
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1499])).

cnf(c_3015,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | X0 != sK2
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1847])).

cnf(c_12891,plain,
    ( m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) != sK2
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_3015])).

cnf(c_12895,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) != sK2
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0))
    | m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12891])).

cnf(c_13695,plain,
    ( v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3874,c_28,c_29,c_32,c_2205,c_2267,c_2277,c_2297,c_2304,c_2686,c_3138,c_3489,c_3683,c_4248,c_4421,c_4423,c_7780,c_9099,c_12895])).

cnf(c_9239,plain,
    ( ~ r1_tarski(X0,k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))
    | ~ r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),X0)
    | X0 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_15287,plain,
    ( ~ r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))
    | k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) = k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_9239])).

cnf(c_772,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v3_pre_topc(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1489,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v3_pre_topc(sK2,sK0)
    | sK0 != X1
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_772])).

cnf(c_16755,plain,
    ( ~ v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),X0)
    | v3_pre_topc(sK2,sK0)
    | sK0 != X0
    | sK2 != k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_1489])).

cnf(c_16756,plain,
    ( sK0 != X0
    | sK2 != k1_tops_1(sK0,k2_pre_topc(sK0,sK2))
    | v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),X0) != iProver_top
    | v3_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16755])).

cnf(c_16758,plain,
    ( sK0 != sK0
    | sK2 != k1_tops_1(sK0,k2_pre_topc(sK0,sK2))
    | v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK0) != iProver_top
    | v3_pre_topc(sK2,sK0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_16756])).

cnf(c_17677,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3935,c_28,c_20,c_29,c_32,c_70,c_74,c_1504,c_1505,c_1523,c_1540,c_1655,c_1665,c_1687,c_1825,c_1970,c_2033,c_2067,c_2205,c_2267,c_2277,c_2297,c_2304,c_2594,c_2686,c_3138,c_3489,c_3683,c_3874,c_3938,c_4244,c_4248,c_4421,c_4423,c_7780,c_9099,c_9245,c_12892,c_12895,c_15287,c_16758])).

cnf(c_17681,plain,
    ( k1_tops_1(sK0,sK2) = sK2
    | r1_tarski(sK2,k1_tops_1(sK0,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_17677,c_1420])).

cnf(c_17684,plain,
    ( k1_tops_1(sK0,sK2) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_17681,c_28,c_20,c_29,c_32,c_70,c_74,c_1504,c_1505,c_1523,c_1540,c_1655,c_1665,c_1687,c_1825,c_2033,c_2067,c_2205,c_2267,c_2277,c_2297,c_2304,c_2594,c_2686,c_3138,c_3489,c_3683,c_3874,c_3938,c_4248,c_4421,c_4423,c_7780,c_9099,c_9245,c_12892,c_12895,c_15287,c_16758])).

cnf(c_5,plain,
    ( v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
    | ~ r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_584,plain,
    ( v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
    | ~ r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_23])).

cnf(c_585,plain,
    ( v4_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,X0)))
    | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X0) ),
    inference(unflattening,[status(thm)],[c_584])).

cnf(c_1389,plain,
    ( v4_tops_1(X0,sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,X0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_585])).

cnf(c_3873,plain,
    ( k1_tops_1(sK1,sK3) = sK3
    | v4_tops_1(sK2,sK0) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) != iProver_top
    | r1_tarski(sK2,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2817,c_1389])).

cnf(c_1588,plain,
    ( v4_tops_1(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK2)
    | ~ r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) ),
    inference(instantiation,[status(thm)],[c_585])).

cnf(c_1589,plain,
    ( v4_tops_1(sK2,sK0) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK2) != iProver_top
    | r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1588])).

cnf(c_1681,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK2)
    | k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) != X0
    | sK2 != X1 ),
    inference(instantiation,[status(thm)],[c_764])).

cnf(c_2122,plain,
    ( ~ r1_tarski(X0,sK2)
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK2)
    | k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) != X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1681])).

cnf(c_2963,plain,
    ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK2)
    | ~ r1_tarski(sK2,sK2)
    | k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) != sK2
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_2122])).

cnf(c_2964,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) != sK2
    | sK2 != sK2
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK2) = iProver_top
    | r1_tarski(sK2,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2963])).

cnf(c_13317,plain,
    ( r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) != iProver_top
    | v4_tops_1(sK2,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3873,c_28,c_29,c_32,c_1589,c_1970,c_2033,c_2205,c_2277,c_2297,c_2304,c_2686,c_2964,c_3489,c_3683,c_4248,c_4421,c_4423,c_7780,c_9099])).

cnf(c_13318,plain,
    ( v4_tops_1(sK2,sK0) = iProver_top
    | r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_13317])).

cnf(c_17706,plain,
    ( v4_tops_1(sK2,sK0) = iProver_top
    | r1_tarski(sK2,k2_pre_topc(sK0,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_17684,c_13318])).

cnf(c_1723,plain,
    ( ~ v3_pre_topc(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ sP4_iProver_split
    | k1_tops_1(sK1,sK3) = sK3 ),
    inference(instantiation,[status(thm)],[c_759])).

cnf(c_1724,plain,
    ( k1_tops_1(sK1,sK3) = sK3
    | v3_pre_topc(sK3,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | sP4_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1723])).

cnf(c_882,plain,
    ( k1_tops_1(sK0,X0) != X0
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(X0,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_753,c_754,c_752])).

cnf(c_883,plain,
    ( v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) != X0 ),
    inference(renaming,[status(thm)],[c_882])).

cnf(c_889,plain,
    ( k1_tops_1(sK0,X0) != X0
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(X0,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_753,c_883])).

cnf(c_890,plain,
    ( v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) != X0 ),
    inference(renaming,[status(thm)],[c_889])).

cnf(c_1565,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,sK2) != sK2 ),
    inference(instantiation,[status(thm)],[c_890])).

cnf(c_1566,plain,
    ( k1_tops_1(sK0,sK2) != sK2
    | v3_pre_topc(sK2,sK0) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1565])).

cnf(c_602,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_23])).

cnf(c_603,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,k2_pre_topc(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_602])).

cnf(c_1530,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK2,k2_pre_topc(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_603])).

cnf(c_1531,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK2,k2_pre_topc(sK0,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1530])).

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

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_17706,c_17684,c_15287,c_9245,c_4248,c_2686,c_2067,c_1825,c_1724,c_1687,c_1665,c_1655,c_1566,c_1540,c_1531,c_1523,c_1505,c_1504,c_1497,c_815,c_35,c_34,c_33,c_29,c_20,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 18:01:22 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.86/1.47  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.86/1.47  
% 7.86/1.47  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.86/1.47  
% 7.86/1.47  ------  iProver source info
% 7.86/1.47  
% 7.86/1.47  git: date: 2020-06-30 10:37:57 +0100
% 7.86/1.47  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.86/1.47  git: non_committed_changes: false
% 7.86/1.47  git: last_make_outside_of_git: false
% 7.86/1.47  
% 7.86/1.47  ------ 
% 7.86/1.47  
% 7.86/1.47  ------ Input Options
% 7.86/1.47  
% 7.86/1.47  --out_options                           all
% 7.86/1.47  --tptp_safe_out                         true
% 7.86/1.47  --problem_path                          ""
% 7.86/1.47  --include_path                          ""
% 7.86/1.47  --clausifier                            res/vclausify_rel
% 7.86/1.47  --clausifier_options                    ""
% 7.86/1.47  --stdin                                 false
% 7.86/1.47  --stats_out                             all
% 7.86/1.47  
% 7.86/1.47  ------ General Options
% 7.86/1.47  
% 7.86/1.47  --fof                                   false
% 7.86/1.47  --time_out_real                         305.
% 7.86/1.47  --time_out_virtual                      -1.
% 7.86/1.47  --symbol_type_check                     false
% 7.86/1.47  --clausify_out                          false
% 7.86/1.47  --sig_cnt_out                           false
% 7.86/1.47  --trig_cnt_out                          false
% 7.86/1.47  --trig_cnt_out_tolerance                1.
% 7.86/1.47  --trig_cnt_out_sk_spl                   false
% 7.86/1.47  --abstr_cl_out                          false
% 7.86/1.47  
% 7.86/1.47  ------ Global Options
% 7.86/1.47  
% 7.86/1.47  --schedule                              default
% 7.86/1.47  --add_important_lit                     false
% 7.86/1.47  --prop_solver_per_cl                    1000
% 7.86/1.47  --min_unsat_core                        false
% 7.86/1.47  --soft_assumptions                      false
% 7.86/1.47  --soft_lemma_size                       3
% 7.86/1.47  --prop_impl_unit_size                   0
% 7.86/1.47  --prop_impl_unit                        []
% 7.86/1.47  --share_sel_clauses                     true
% 7.86/1.47  --reset_solvers                         false
% 7.86/1.47  --bc_imp_inh                            [conj_cone]
% 7.86/1.47  --conj_cone_tolerance                   3.
% 7.86/1.47  --extra_neg_conj                        none
% 7.86/1.47  --large_theory_mode                     true
% 7.86/1.47  --prolific_symb_bound                   200
% 7.86/1.47  --lt_threshold                          2000
% 7.86/1.47  --clause_weak_htbl                      true
% 7.86/1.47  --gc_record_bc_elim                     false
% 7.86/1.47  
% 7.86/1.47  ------ Preprocessing Options
% 7.86/1.47  
% 7.86/1.47  --preprocessing_flag                    true
% 7.86/1.47  --time_out_prep_mult                    0.1
% 7.86/1.47  --splitting_mode                        input
% 7.86/1.47  --splitting_grd                         true
% 7.86/1.47  --splitting_cvd                         false
% 7.86/1.47  --splitting_cvd_svl                     false
% 7.86/1.47  --splitting_nvd                         32
% 7.86/1.47  --sub_typing                            true
% 7.86/1.47  --prep_gs_sim                           true
% 7.86/1.47  --prep_unflatten                        true
% 7.86/1.47  --prep_res_sim                          true
% 7.86/1.47  --prep_upred                            true
% 7.86/1.47  --prep_sem_filter                       exhaustive
% 7.86/1.47  --prep_sem_filter_out                   false
% 7.86/1.47  --pred_elim                             true
% 7.86/1.47  --res_sim_input                         true
% 7.86/1.47  --eq_ax_congr_red                       true
% 7.86/1.47  --pure_diseq_elim                       true
% 7.86/1.47  --brand_transform                       false
% 7.86/1.47  --non_eq_to_eq                          false
% 7.86/1.47  --prep_def_merge                        true
% 7.86/1.47  --prep_def_merge_prop_impl              false
% 7.86/1.47  --prep_def_merge_mbd                    true
% 7.86/1.47  --prep_def_merge_tr_red                 false
% 7.86/1.47  --prep_def_merge_tr_cl                  false
% 7.86/1.47  --smt_preprocessing                     true
% 7.86/1.47  --smt_ac_axioms                         fast
% 7.86/1.47  --preprocessed_out                      false
% 7.86/1.47  --preprocessed_stats                    false
% 7.86/1.47  
% 7.86/1.47  ------ Abstraction refinement Options
% 7.86/1.47  
% 7.86/1.47  --abstr_ref                             []
% 7.86/1.47  --abstr_ref_prep                        false
% 7.86/1.47  --abstr_ref_until_sat                   false
% 7.86/1.47  --abstr_ref_sig_restrict                funpre
% 7.86/1.47  --abstr_ref_af_restrict_to_split_sk     false
% 7.86/1.47  --abstr_ref_under                       []
% 7.86/1.47  
% 7.86/1.47  ------ SAT Options
% 7.86/1.47  
% 7.86/1.47  --sat_mode                              false
% 7.86/1.47  --sat_fm_restart_options                ""
% 7.86/1.47  --sat_gr_def                            false
% 7.86/1.47  --sat_epr_types                         true
% 7.86/1.47  --sat_non_cyclic_types                  false
% 7.86/1.47  --sat_finite_models                     false
% 7.86/1.47  --sat_fm_lemmas                         false
% 7.86/1.47  --sat_fm_prep                           false
% 7.86/1.47  --sat_fm_uc_incr                        true
% 7.86/1.47  --sat_out_model                         small
% 7.86/1.47  --sat_out_clauses                       false
% 7.86/1.47  
% 7.86/1.47  ------ QBF Options
% 7.86/1.47  
% 7.86/1.47  --qbf_mode                              false
% 7.86/1.47  --qbf_elim_univ                         false
% 7.86/1.47  --qbf_dom_inst                          none
% 7.86/1.47  --qbf_dom_pre_inst                      false
% 7.86/1.47  --qbf_sk_in                             false
% 7.86/1.47  --qbf_pred_elim                         true
% 7.86/1.47  --qbf_split                             512
% 7.86/1.47  
% 7.86/1.47  ------ BMC1 Options
% 7.86/1.47  
% 7.86/1.47  --bmc1_incremental                      false
% 7.86/1.47  --bmc1_axioms                           reachable_all
% 7.86/1.47  --bmc1_min_bound                        0
% 7.86/1.47  --bmc1_max_bound                        -1
% 7.86/1.47  --bmc1_max_bound_default                -1
% 7.86/1.47  --bmc1_symbol_reachability              true
% 7.86/1.47  --bmc1_property_lemmas                  false
% 7.86/1.47  --bmc1_k_induction                      false
% 7.86/1.47  --bmc1_non_equiv_states                 false
% 7.86/1.47  --bmc1_deadlock                         false
% 7.86/1.47  --bmc1_ucm                              false
% 7.86/1.47  --bmc1_add_unsat_core                   none
% 7.86/1.47  --bmc1_unsat_core_children              false
% 7.86/1.47  --bmc1_unsat_core_extrapolate_axioms    false
% 7.86/1.47  --bmc1_out_stat                         full
% 7.86/1.47  --bmc1_ground_init                      false
% 7.86/1.47  --bmc1_pre_inst_next_state              false
% 7.86/1.47  --bmc1_pre_inst_state                   false
% 7.86/1.47  --bmc1_pre_inst_reach_state             false
% 7.86/1.47  --bmc1_out_unsat_core                   false
% 7.86/1.47  --bmc1_aig_witness_out                  false
% 7.86/1.47  --bmc1_verbose                          false
% 7.86/1.47  --bmc1_dump_clauses_tptp                false
% 7.86/1.47  --bmc1_dump_unsat_core_tptp             false
% 7.86/1.47  --bmc1_dump_file                        -
% 7.86/1.47  --bmc1_ucm_expand_uc_limit              128
% 7.86/1.47  --bmc1_ucm_n_expand_iterations          6
% 7.86/1.47  --bmc1_ucm_extend_mode                  1
% 7.86/1.47  --bmc1_ucm_init_mode                    2
% 7.86/1.47  --bmc1_ucm_cone_mode                    none
% 7.86/1.47  --bmc1_ucm_reduced_relation_type        0
% 7.86/1.47  --bmc1_ucm_relax_model                  4
% 7.86/1.47  --bmc1_ucm_full_tr_after_sat            true
% 7.86/1.47  --bmc1_ucm_expand_neg_assumptions       false
% 7.86/1.47  --bmc1_ucm_layered_model                none
% 7.86/1.47  --bmc1_ucm_max_lemma_size               10
% 7.86/1.47  
% 7.86/1.47  ------ AIG Options
% 7.86/1.47  
% 7.86/1.47  --aig_mode                              false
% 7.86/1.47  
% 7.86/1.47  ------ Instantiation Options
% 7.86/1.47  
% 7.86/1.47  --instantiation_flag                    true
% 7.86/1.47  --inst_sos_flag                         true
% 7.86/1.47  --inst_sos_phase                        true
% 7.86/1.47  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.86/1.47  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.86/1.47  --inst_lit_sel_side                     num_symb
% 7.86/1.47  --inst_solver_per_active                1400
% 7.86/1.47  --inst_solver_calls_frac                1.
% 7.86/1.47  --inst_passive_queue_type               priority_queues
% 7.86/1.47  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.86/1.47  --inst_passive_queues_freq              [25;2]
% 7.86/1.47  --inst_dismatching                      true
% 7.86/1.47  --inst_eager_unprocessed_to_passive     true
% 7.86/1.47  --inst_prop_sim_given                   true
% 7.86/1.47  --inst_prop_sim_new                     false
% 7.86/1.47  --inst_subs_new                         false
% 7.86/1.47  --inst_eq_res_simp                      false
% 7.86/1.47  --inst_subs_given                       false
% 7.86/1.47  --inst_orphan_elimination               true
% 7.86/1.47  --inst_learning_loop_flag               true
% 7.86/1.47  --inst_learning_start                   3000
% 7.86/1.47  --inst_learning_factor                  2
% 7.86/1.47  --inst_start_prop_sim_after_learn       3
% 7.86/1.47  --inst_sel_renew                        solver
% 7.86/1.47  --inst_lit_activity_flag                true
% 7.86/1.47  --inst_restr_to_given                   false
% 7.86/1.47  --inst_activity_threshold               500
% 7.86/1.47  --inst_out_proof                        true
% 7.86/1.47  
% 7.86/1.47  ------ Resolution Options
% 7.86/1.47  
% 7.86/1.47  --resolution_flag                       true
% 7.86/1.47  --res_lit_sel                           adaptive
% 7.86/1.47  --res_lit_sel_side                      none
% 7.86/1.47  --res_ordering                          kbo
% 7.86/1.47  --res_to_prop_solver                    active
% 7.86/1.47  --res_prop_simpl_new                    false
% 7.86/1.47  --res_prop_simpl_given                  true
% 7.86/1.47  --res_passive_queue_type                priority_queues
% 7.86/1.47  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.86/1.47  --res_passive_queues_freq               [15;5]
% 7.86/1.47  --res_forward_subs                      full
% 7.86/1.47  --res_backward_subs                     full
% 7.86/1.47  --res_forward_subs_resolution           true
% 7.86/1.47  --res_backward_subs_resolution          true
% 7.86/1.47  --res_orphan_elimination                true
% 7.86/1.47  --res_time_limit                        2.
% 7.86/1.47  --res_out_proof                         true
% 7.86/1.47  
% 7.86/1.47  ------ Superposition Options
% 7.86/1.47  
% 7.86/1.47  --superposition_flag                    true
% 7.86/1.47  --sup_passive_queue_type                priority_queues
% 7.86/1.47  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.86/1.47  --sup_passive_queues_freq               [8;1;4]
% 7.86/1.47  --demod_completeness_check              fast
% 7.86/1.47  --demod_use_ground                      true
% 7.86/1.47  --sup_to_prop_solver                    passive
% 7.86/1.47  --sup_prop_simpl_new                    true
% 7.86/1.47  --sup_prop_simpl_given                  true
% 7.86/1.47  --sup_fun_splitting                     true
% 7.86/1.47  --sup_smt_interval                      50000
% 7.86/1.47  
% 7.86/1.47  ------ Superposition Simplification Setup
% 7.86/1.47  
% 7.86/1.47  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.86/1.47  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.86/1.47  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.86/1.47  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.86/1.47  --sup_full_triv                         [TrivRules;PropSubs]
% 7.86/1.47  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.86/1.47  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.86/1.47  --sup_immed_triv                        [TrivRules]
% 7.86/1.47  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.86/1.47  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.86/1.47  --sup_immed_bw_main                     []
% 7.86/1.47  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.86/1.47  --sup_input_triv                        [Unflattening;TrivRules]
% 7.86/1.47  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.86/1.47  --sup_input_bw                          []
% 7.86/1.47  
% 7.86/1.47  ------ Combination Options
% 7.86/1.47  
% 7.86/1.47  --comb_res_mult                         3
% 7.86/1.47  --comb_sup_mult                         2
% 7.86/1.47  --comb_inst_mult                        10
% 7.86/1.47  
% 7.86/1.47  ------ Debug Options
% 7.86/1.47  
% 7.86/1.47  --dbg_backtrace                         false
% 7.86/1.47  --dbg_dump_prop_clauses                 false
% 7.86/1.47  --dbg_dump_prop_clauses_file            -
% 7.86/1.47  --dbg_out_stat                          false
% 7.86/1.47  ------ Parsing...
% 7.86/1.47  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.86/1.47  
% 7.86/1.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 7.86/1.47  
% 7.86/1.47  ------ Preprocessing... gs_s  sp: 8 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.86/1.47  
% 7.86/1.47  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.86/1.47  ------ Proving...
% 7.86/1.47  ------ Problem Properties 
% 7.86/1.47  
% 7.86/1.47  
% 7.86/1.47  clauses                                 40
% 7.86/1.47  conjectures                             8
% 7.86/1.47  EPR                                     12
% 7.86/1.47  Horn                                    34
% 7.86/1.47  unary                                   3
% 7.86/1.47  binary                                  17
% 7.86/1.47  lits                                    105
% 7.86/1.47  lits eq                                 11
% 7.86/1.47  fd_pure                                 0
% 7.86/1.47  fd_pseudo                               0
% 7.86/1.47  fd_cond                                 0
% 7.86/1.47  fd_pseudo_cond                          1
% 7.86/1.47  AC symbols                              0
% 7.86/1.47  
% 7.86/1.47  ------ Schedule dynamic 5 is on 
% 7.86/1.47  
% 7.86/1.47  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.86/1.47  
% 7.86/1.47  
% 7.86/1.47  ------ 
% 7.86/1.47  Current options:
% 7.86/1.47  ------ 
% 7.86/1.47  
% 7.86/1.47  ------ Input Options
% 7.86/1.47  
% 7.86/1.47  --out_options                           all
% 7.86/1.47  --tptp_safe_out                         true
% 7.86/1.47  --problem_path                          ""
% 7.86/1.47  --include_path                          ""
% 7.86/1.47  --clausifier                            res/vclausify_rel
% 7.86/1.47  --clausifier_options                    ""
% 7.86/1.47  --stdin                                 false
% 7.86/1.47  --stats_out                             all
% 7.86/1.47  
% 7.86/1.47  ------ General Options
% 7.86/1.47  
% 7.86/1.47  --fof                                   false
% 7.86/1.47  --time_out_real                         305.
% 7.86/1.47  --time_out_virtual                      -1.
% 7.86/1.47  --symbol_type_check                     false
% 7.86/1.47  --clausify_out                          false
% 7.86/1.47  --sig_cnt_out                           false
% 7.86/1.47  --trig_cnt_out                          false
% 7.86/1.47  --trig_cnt_out_tolerance                1.
% 7.86/1.47  --trig_cnt_out_sk_spl                   false
% 7.86/1.47  --abstr_cl_out                          false
% 7.86/1.47  
% 7.86/1.47  ------ Global Options
% 7.86/1.47  
% 7.86/1.47  --schedule                              default
% 7.86/1.47  --add_important_lit                     false
% 7.86/1.47  --prop_solver_per_cl                    1000
% 7.86/1.47  --min_unsat_core                        false
% 7.86/1.47  --soft_assumptions                      false
% 7.86/1.47  --soft_lemma_size                       3
% 7.86/1.47  --prop_impl_unit_size                   0
% 7.86/1.47  --prop_impl_unit                        []
% 7.86/1.47  --share_sel_clauses                     true
% 7.86/1.47  --reset_solvers                         false
% 7.86/1.47  --bc_imp_inh                            [conj_cone]
% 7.86/1.47  --conj_cone_tolerance                   3.
% 7.86/1.47  --extra_neg_conj                        none
% 7.86/1.47  --large_theory_mode                     true
% 7.86/1.47  --prolific_symb_bound                   200
% 7.86/1.47  --lt_threshold                          2000
% 7.86/1.47  --clause_weak_htbl                      true
% 7.86/1.47  --gc_record_bc_elim                     false
% 7.86/1.47  
% 7.86/1.47  ------ Preprocessing Options
% 7.86/1.47  
% 7.86/1.47  --preprocessing_flag                    true
% 7.86/1.47  --time_out_prep_mult                    0.1
% 7.86/1.47  --splitting_mode                        input
% 7.86/1.47  --splitting_grd                         true
% 7.86/1.47  --splitting_cvd                         false
% 7.86/1.47  --splitting_cvd_svl                     false
% 7.86/1.47  --splitting_nvd                         32
% 7.86/1.47  --sub_typing                            true
% 7.86/1.47  --prep_gs_sim                           true
% 7.86/1.47  --prep_unflatten                        true
% 7.86/1.47  --prep_res_sim                          true
% 7.86/1.47  --prep_upred                            true
% 7.86/1.47  --prep_sem_filter                       exhaustive
% 7.86/1.47  --prep_sem_filter_out                   false
% 7.86/1.47  --pred_elim                             true
% 7.86/1.47  --res_sim_input                         true
% 7.86/1.47  --eq_ax_congr_red                       true
% 7.86/1.47  --pure_diseq_elim                       true
% 7.86/1.47  --brand_transform                       false
% 7.86/1.47  --non_eq_to_eq                          false
% 7.86/1.47  --prep_def_merge                        true
% 7.86/1.47  --prep_def_merge_prop_impl              false
% 7.86/1.47  --prep_def_merge_mbd                    true
% 7.86/1.47  --prep_def_merge_tr_red                 false
% 7.86/1.47  --prep_def_merge_tr_cl                  false
% 7.86/1.47  --smt_preprocessing                     true
% 7.86/1.47  --smt_ac_axioms                         fast
% 7.86/1.47  --preprocessed_out                      false
% 7.86/1.47  --preprocessed_stats                    false
% 7.86/1.47  
% 7.86/1.47  ------ Abstraction refinement Options
% 7.86/1.47  
% 7.86/1.47  --abstr_ref                             []
% 7.86/1.47  --abstr_ref_prep                        false
% 7.86/1.47  --abstr_ref_until_sat                   false
% 7.86/1.47  --abstr_ref_sig_restrict                funpre
% 7.86/1.47  --abstr_ref_af_restrict_to_split_sk     false
% 7.86/1.47  --abstr_ref_under                       []
% 7.86/1.47  
% 7.86/1.47  ------ SAT Options
% 7.86/1.47  
% 7.86/1.47  --sat_mode                              false
% 7.86/1.47  --sat_fm_restart_options                ""
% 7.86/1.47  --sat_gr_def                            false
% 7.86/1.47  --sat_epr_types                         true
% 7.86/1.47  --sat_non_cyclic_types                  false
% 7.86/1.47  --sat_finite_models                     false
% 7.86/1.47  --sat_fm_lemmas                         false
% 7.86/1.47  --sat_fm_prep                           false
% 7.86/1.47  --sat_fm_uc_incr                        true
% 7.86/1.47  --sat_out_model                         small
% 7.86/1.47  --sat_out_clauses                       false
% 7.86/1.47  
% 7.86/1.47  ------ QBF Options
% 7.86/1.47  
% 7.86/1.47  --qbf_mode                              false
% 7.86/1.47  --qbf_elim_univ                         false
% 7.86/1.47  --qbf_dom_inst                          none
% 7.86/1.47  --qbf_dom_pre_inst                      false
% 7.86/1.47  --qbf_sk_in                             false
% 7.86/1.47  --qbf_pred_elim                         true
% 7.86/1.47  --qbf_split                             512
% 7.86/1.47  
% 7.86/1.47  ------ BMC1 Options
% 7.86/1.47  
% 7.86/1.47  --bmc1_incremental                      false
% 7.86/1.47  --bmc1_axioms                           reachable_all
% 7.86/1.47  --bmc1_min_bound                        0
% 7.86/1.47  --bmc1_max_bound                        -1
% 7.86/1.47  --bmc1_max_bound_default                -1
% 7.86/1.47  --bmc1_symbol_reachability              true
% 7.86/1.47  --bmc1_property_lemmas                  false
% 7.86/1.47  --bmc1_k_induction                      false
% 7.86/1.47  --bmc1_non_equiv_states                 false
% 7.86/1.47  --bmc1_deadlock                         false
% 7.86/1.47  --bmc1_ucm                              false
% 7.86/1.47  --bmc1_add_unsat_core                   none
% 7.86/1.47  --bmc1_unsat_core_children              false
% 7.86/1.47  --bmc1_unsat_core_extrapolate_axioms    false
% 7.86/1.47  --bmc1_out_stat                         full
% 7.86/1.47  --bmc1_ground_init                      false
% 7.86/1.47  --bmc1_pre_inst_next_state              false
% 7.86/1.47  --bmc1_pre_inst_state                   false
% 7.86/1.47  --bmc1_pre_inst_reach_state             false
% 7.86/1.47  --bmc1_out_unsat_core                   false
% 7.86/1.47  --bmc1_aig_witness_out                  false
% 7.86/1.47  --bmc1_verbose                          false
% 7.86/1.47  --bmc1_dump_clauses_tptp                false
% 7.86/1.47  --bmc1_dump_unsat_core_tptp             false
% 7.86/1.47  --bmc1_dump_file                        -
% 7.86/1.47  --bmc1_ucm_expand_uc_limit              128
% 7.86/1.47  --bmc1_ucm_n_expand_iterations          6
% 7.86/1.47  --bmc1_ucm_extend_mode                  1
% 7.86/1.47  --bmc1_ucm_init_mode                    2
% 7.86/1.47  --bmc1_ucm_cone_mode                    none
% 7.86/1.47  --bmc1_ucm_reduced_relation_type        0
% 7.86/1.47  --bmc1_ucm_relax_model                  4
% 7.86/1.47  --bmc1_ucm_full_tr_after_sat            true
% 7.86/1.47  --bmc1_ucm_expand_neg_assumptions       false
% 7.86/1.47  --bmc1_ucm_layered_model                none
% 7.86/1.47  --bmc1_ucm_max_lemma_size               10
% 7.86/1.47  
% 7.86/1.47  ------ AIG Options
% 7.86/1.47  
% 7.86/1.47  --aig_mode                              false
% 7.86/1.47  
% 7.86/1.47  ------ Instantiation Options
% 7.86/1.47  
% 7.86/1.47  --instantiation_flag                    true
% 7.86/1.47  --inst_sos_flag                         true
% 7.86/1.47  --inst_sos_phase                        true
% 7.86/1.47  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.86/1.47  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.86/1.47  --inst_lit_sel_side                     none
% 7.86/1.47  --inst_solver_per_active                1400
% 7.86/1.47  --inst_solver_calls_frac                1.
% 7.86/1.47  --inst_passive_queue_type               priority_queues
% 7.86/1.47  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.86/1.47  --inst_passive_queues_freq              [25;2]
% 7.86/1.47  --inst_dismatching                      true
% 7.86/1.47  --inst_eager_unprocessed_to_passive     true
% 7.86/1.47  --inst_prop_sim_given                   true
% 7.86/1.47  --inst_prop_sim_new                     false
% 7.86/1.47  --inst_subs_new                         false
% 7.86/1.47  --inst_eq_res_simp                      false
% 7.86/1.47  --inst_subs_given                       false
% 7.86/1.47  --inst_orphan_elimination               true
% 7.86/1.47  --inst_learning_loop_flag               true
% 7.86/1.47  --inst_learning_start                   3000
% 7.86/1.47  --inst_learning_factor                  2
% 7.86/1.47  --inst_start_prop_sim_after_learn       3
% 7.86/1.47  --inst_sel_renew                        solver
% 7.86/1.47  --inst_lit_activity_flag                true
% 7.86/1.47  --inst_restr_to_given                   false
% 7.86/1.47  --inst_activity_threshold               500
% 7.86/1.47  --inst_out_proof                        true
% 7.86/1.47  
% 7.86/1.47  ------ Resolution Options
% 7.86/1.47  
% 7.86/1.47  --resolution_flag                       false
% 7.86/1.47  --res_lit_sel                           adaptive
% 7.86/1.47  --res_lit_sel_side                      none
% 7.86/1.47  --res_ordering                          kbo
% 7.86/1.47  --res_to_prop_solver                    active
% 7.86/1.47  --res_prop_simpl_new                    false
% 7.86/1.47  --res_prop_simpl_given                  true
% 7.86/1.47  --res_passive_queue_type                priority_queues
% 7.86/1.47  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.86/1.47  --res_passive_queues_freq               [15;5]
% 7.86/1.47  --res_forward_subs                      full
% 7.86/1.47  --res_backward_subs                     full
% 7.86/1.47  --res_forward_subs_resolution           true
% 7.86/1.47  --res_backward_subs_resolution          true
% 7.86/1.47  --res_orphan_elimination                true
% 7.86/1.47  --res_time_limit                        2.
% 7.86/1.47  --res_out_proof                         true
% 7.86/1.47  
% 7.86/1.47  ------ Superposition Options
% 7.86/1.47  
% 7.86/1.47  --superposition_flag                    true
% 7.86/1.47  --sup_passive_queue_type                priority_queues
% 7.86/1.47  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.86/1.47  --sup_passive_queues_freq               [8;1;4]
% 7.86/1.47  --demod_completeness_check              fast
% 7.86/1.47  --demod_use_ground                      true
% 7.86/1.47  --sup_to_prop_solver                    passive
% 7.86/1.47  --sup_prop_simpl_new                    true
% 7.86/1.47  --sup_prop_simpl_given                  true
% 7.86/1.47  --sup_fun_splitting                     true
% 7.86/1.47  --sup_smt_interval                      50000
% 7.86/1.47  
% 7.86/1.47  ------ Superposition Simplification Setup
% 7.86/1.47  
% 7.86/1.47  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.86/1.47  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.86/1.47  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.86/1.47  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.86/1.47  --sup_full_triv                         [TrivRules;PropSubs]
% 7.86/1.47  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.86/1.47  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.86/1.47  --sup_immed_triv                        [TrivRules]
% 7.86/1.47  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.86/1.47  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.86/1.47  --sup_immed_bw_main                     []
% 7.86/1.47  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.86/1.47  --sup_input_triv                        [Unflattening;TrivRules]
% 7.86/1.47  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.86/1.47  --sup_input_bw                          []
% 7.86/1.47  
% 7.86/1.47  ------ Combination Options
% 7.86/1.47  
% 7.86/1.47  --comb_res_mult                         3
% 7.86/1.47  --comb_sup_mult                         2
% 7.86/1.47  --comb_inst_mult                        10
% 7.86/1.47  
% 7.86/1.47  ------ Debug Options
% 7.86/1.47  
% 7.86/1.47  --dbg_backtrace                         false
% 7.86/1.47  --dbg_dump_prop_clauses                 false
% 7.86/1.47  --dbg_dump_prop_clauses_file            -
% 7.86/1.47  --dbg_out_stat                          false
% 7.86/1.47  
% 7.86/1.47  
% 7.86/1.47  
% 7.86/1.47  
% 7.86/1.47  ------ Proving...
% 7.86/1.47  
% 7.86/1.47  
% 7.86/1.47  % SZS status Theorem for theBenchmark.p
% 7.86/1.47  
% 7.86/1.47  % SZS output start CNFRefutation for theBenchmark.p
% 7.86/1.47  
% 7.86/1.47  fof(f9,conjecture,(
% 7.86/1.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v6_tops_1(X2,X0) => (v4_tops_1(X2,X0) & v3_pre_topc(X2,X0))) & ((v4_tops_1(X3,X1) & v3_pre_topc(X3,X1)) => v6_tops_1(X3,X1)))))))),
% 7.86/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.86/1.47  
% 7.86/1.47  fof(f10,negated_conjecture,(
% 7.86/1.47    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v6_tops_1(X2,X0) => (v4_tops_1(X2,X0) & v3_pre_topc(X2,X0))) & ((v4_tops_1(X3,X1) & v3_pre_topc(X3,X1)) => v6_tops_1(X3,X1)))))))),
% 7.86/1.47    inference(negated_conjecture,[],[f9])).
% 7.86/1.47  
% 7.86/1.47  fof(f22,plain,(
% 7.86/1.47    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(X3,X1) & (v4_tops_1(X3,X1) & v3_pre_topc(X3,X1)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 7.86/1.47    inference(ennf_transformation,[],[f10])).
% 7.86/1.47  
% 7.86/1.47  fof(f23,plain,(
% 7.86/1.47    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.86/1.47    inference(flattening,[],[f22])).
% 7.86/1.47  
% 7.86/1.47  fof(f32,plain,(
% 7.86/1.47    ( ! [X2,X0,X1] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(sK3,X1) & v4_tops_1(sK3,X1) & v3_pre_topc(sK3,X1))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X1))))) )),
% 7.86/1.47    introduced(choice_axiom,[])).
% 7.86/1.47  
% 7.86/1.47  fof(f31,plain,(
% 7.86/1.47    ( ! [X0,X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X3] : ((((~v4_tops_1(sK2,X0) | ~v3_pre_topc(sK2,X0)) & v6_tops_1(sK2,X0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 7.86/1.47    introduced(choice_axiom,[])).
% 7.86/1.47  
% 7.86/1.47  fof(f30,plain,(
% 7.86/1.47    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) => (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(X3,sK1) & v4_tops_1(X3,sK1) & v3_pre_topc(X3,sK1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(sK1))) )),
% 7.86/1.47    introduced(choice_axiom,[])).
% 7.86/1.47  
% 7.86/1.47  fof(f29,plain,(
% 7.86/1.47    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,sK0) | ~v3_pre_topc(X2,sK0)) & v6_tops_1(X2,sK0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 7.86/1.47    introduced(choice_axiom,[])).
% 7.86/1.47  
% 7.86/1.47  fof(f33,plain,(
% 7.86/1.47    ((((((~v4_tops_1(sK2,sK0) | ~v3_pre_topc(sK2,sK0)) & v6_tops_1(sK2,sK0)) | (~v6_tops_1(sK3,sK1) & v4_tops_1(sK3,sK1) & v3_pre_topc(sK3,sK1))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 7.86/1.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f32,f31,f30,f29])).
% 7.86/1.47  
% 7.86/1.47  fof(f53,plain,(
% 7.86/1.47    v6_tops_1(sK2,sK0) | v3_pre_topc(sK3,sK1)),
% 7.86/1.47    inference(cnf_transformation,[],[f33])).
% 7.86/1.47  
% 7.86/1.47  fof(f52,plain,(
% 7.86/1.47    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 7.86/1.47    inference(cnf_transformation,[],[f33])).
% 7.86/1.47  
% 7.86/1.47  fof(f8,axiom,(
% 7.86/1.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 7.86/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.86/1.47  
% 7.86/1.47  fof(f20,plain,(
% 7.86/1.47    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.86/1.47    inference(ennf_transformation,[],[f8])).
% 7.86/1.47  
% 7.86/1.47  fof(f21,plain,(
% 7.86/1.47    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.86/1.47    inference(flattening,[],[f20])).
% 7.86/1.47  
% 7.86/1.47  fof(f46,plain,(
% 7.86/1.47    ( ! [X2,X0,X3,X1] : (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.86/1.47    inference(cnf_transformation,[],[f21])).
% 7.86/1.47  
% 7.86/1.47  fof(f48,plain,(
% 7.86/1.47    v2_pre_topc(sK0)),
% 7.86/1.47    inference(cnf_transformation,[],[f33])).
% 7.86/1.47  
% 7.86/1.47  fof(f49,plain,(
% 7.86/1.47    l1_pre_topc(sK0)),
% 7.86/1.47    inference(cnf_transformation,[],[f33])).
% 7.86/1.47  
% 7.86/1.47  fof(f50,plain,(
% 7.86/1.47    l1_pre_topc(sK1)),
% 7.86/1.47    inference(cnf_transformation,[],[f33])).
% 7.86/1.47  
% 7.86/1.47  fof(f51,plain,(
% 7.86/1.47    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 7.86/1.47    inference(cnf_transformation,[],[f33])).
% 7.86/1.47  
% 7.86/1.47  fof(f47,plain,(
% 7.86/1.47    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.86/1.47    inference(cnf_transformation,[],[f21])).
% 7.86/1.47  
% 7.86/1.47  fof(f5,axiom,(
% 7.86/1.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v6_tops_1(X1,X0) <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1)))),
% 7.86/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.86/1.47  
% 7.86/1.47  fof(f15,plain,(
% 7.86/1.47    ! [X0] : (! [X1] : ((v6_tops_1(X1,X0) <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.86/1.47    inference(ennf_transformation,[],[f5])).
% 7.86/1.47  
% 7.86/1.47  fof(f28,plain,(
% 7.86/1.47    ! [X0] : (! [X1] : (((v6_tops_1(X1,X0) | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1) & (k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 | ~v6_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.86/1.47    inference(nnf_transformation,[],[f15])).
% 7.86/1.47  
% 7.86/1.47  fof(f42,plain,(
% 7.86/1.47    ( ! [X0,X1] : (k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 | ~v6_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.86/1.47    inference(cnf_transformation,[],[f28])).
% 7.86/1.47  
% 7.86/1.47  fof(f2,axiom,(
% 7.86/1.47    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 7.86/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.86/1.47  
% 7.86/1.47  fof(f11,plain,(
% 7.86/1.47    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 7.86/1.47    inference(ennf_transformation,[],[f2])).
% 7.86/1.47  
% 7.86/1.47  fof(f12,plain,(
% 7.86/1.47    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 7.86/1.47    inference(flattening,[],[f11])).
% 7.86/1.47  
% 7.86/1.47  fof(f37,plain,(
% 7.86/1.47    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.86/1.47    inference(cnf_transformation,[],[f12])).
% 7.86/1.47  
% 7.86/1.47  fof(f6,axiom,(
% 7.86/1.47    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)))),
% 7.86/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.86/1.47  
% 7.86/1.47  fof(f16,plain,(
% 7.86/1.47    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 7.86/1.47    inference(ennf_transformation,[],[f6])).
% 7.86/1.47  
% 7.86/1.47  fof(f17,plain,(
% 7.86/1.47    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 7.86/1.47    inference(flattening,[],[f16])).
% 7.86/1.47  
% 7.86/1.47  fof(f44,plain,(
% 7.86/1.47    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.86/1.47    inference(cnf_transformation,[],[f17])).
% 7.86/1.47  
% 7.86/1.47  fof(f4,axiom,(
% 7.86/1.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)))))),
% 7.86/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.86/1.47  
% 7.86/1.47  fof(f14,plain,(
% 7.86/1.47    ! [X0] : (! [X1] : ((v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.86/1.47    inference(ennf_transformation,[],[f4])).
% 7.86/1.47  
% 7.86/1.47  fof(f26,plain,(
% 7.86/1.47    ! [X0] : (! [X1] : (((v4_tops_1(X1,X0) | (~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1))) & ((r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) | ~v4_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.86/1.47    inference(nnf_transformation,[],[f14])).
% 7.86/1.47  
% 7.86/1.47  fof(f27,plain,(
% 7.86/1.47    ! [X0] : (! [X1] : (((v4_tops_1(X1,X0) | ~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) & ((r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) | ~v4_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.86/1.47    inference(flattening,[],[f26])).
% 7.86/1.47  
% 7.86/1.47  fof(f39,plain,(
% 7.86/1.47    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) | ~v4_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.86/1.47    inference(cnf_transformation,[],[f27])).
% 7.86/1.47  
% 7.86/1.47  fof(f55,plain,(
% 7.86/1.47    v6_tops_1(sK2,sK0) | ~v6_tops_1(sK3,sK1)),
% 7.86/1.47    inference(cnf_transformation,[],[f33])).
% 7.86/1.47  
% 7.86/1.47  fof(f1,axiom,(
% 7.86/1.47    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.86/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.86/1.47  
% 7.86/1.47  fof(f24,plain,(
% 7.86/1.47    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.86/1.47    inference(nnf_transformation,[],[f1])).
% 7.86/1.47  
% 7.86/1.47  fof(f25,plain,(
% 7.86/1.47    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.86/1.47    inference(flattening,[],[f24])).
% 7.86/1.47  
% 7.86/1.47  fof(f34,plain,(
% 7.86/1.47    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.86/1.47    inference(cnf_transformation,[],[f25])).
% 7.86/1.47  
% 7.86/1.47  fof(f60,plain,(
% 7.86/1.47    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.86/1.47    inference(equality_resolution,[],[f34])).
% 7.86/1.47  
% 7.86/1.47  fof(f36,plain,(
% 7.86/1.47    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.86/1.47    inference(cnf_transformation,[],[f25])).
% 7.86/1.47  
% 7.86/1.47  fof(f3,axiom,(
% 7.86/1.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 7.86/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.86/1.47  
% 7.86/1.47  fof(f13,plain,(
% 7.86/1.47    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.86/1.47    inference(ennf_transformation,[],[f3])).
% 7.86/1.47  
% 7.86/1.47  fof(f38,plain,(
% 7.86/1.47    ( ! [X0,X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.86/1.47    inference(cnf_transformation,[],[f13])).
% 7.86/1.47  
% 7.86/1.47  fof(f43,plain,(
% 7.86/1.47    ( ! [X0,X1] : (v6_tops_1(X1,X0) | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.86/1.47    inference(cnf_transformation,[],[f28])).
% 7.86/1.47  
% 7.86/1.47  fof(f7,axiom,(
% 7.86/1.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 7.86/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.86/1.47  
% 7.86/1.47  fof(f18,plain,(
% 7.86/1.47    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.86/1.47    inference(ennf_transformation,[],[f7])).
% 7.86/1.47  
% 7.86/1.47  fof(f19,plain,(
% 7.86/1.47    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.86/1.47    inference(flattening,[],[f18])).
% 7.86/1.47  
% 7.86/1.47  fof(f45,plain,(
% 7.86/1.47    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.86/1.47    inference(cnf_transformation,[],[f19])).
% 7.86/1.47  
% 7.86/1.47  fof(f54,plain,(
% 7.86/1.47    v6_tops_1(sK2,sK0) | v4_tops_1(sK3,sK1)),
% 7.86/1.47    inference(cnf_transformation,[],[f33])).
% 7.86/1.47  
% 7.86/1.47  fof(f41,plain,(
% 7.86/1.47    ( ! [X0,X1] : (v4_tops_1(X1,X0) | ~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.86/1.47    inference(cnf_transformation,[],[f27])).
% 7.86/1.47  
% 7.86/1.47  fof(f58,plain,(
% 7.86/1.47    ~v4_tops_1(sK2,sK0) | ~v3_pre_topc(sK2,sK0) | ~v6_tops_1(sK3,sK1)),
% 7.86/1.47    inference(cnf_transformation,[],[f33])).
% 7.86/1.47  
% 7.86/1.47  fof(f57,plain,(
% 7.86/1.47    ~v4_tops_1(sK2,sK0) | ~v3_pre_topc(sK2,sK0) | v4_tops_1(sK3,sK1)),
% 7.86/1.47    inference(cnf_transformation,[],[f33])).
% 7.86/1.47  
% 7.86/1.47  fof(f56,plain,(
% 7.86/1.47    ~v4_tops_1(sK2,sK0) | ~v3_pre_topc(sK2,sK0) | v3_pre_topc(sK3,sK1)),
% 7.86/1.47    inference(cnf_transformation,[],[f33])).
% 7.86/1.47  
% 7.86/1.47  cnf(c_19,negated_conjecture,
% 7.86/1.47      ( v3_pre_topc(sK3,sK1) | v6_tops_1(sK2,sK0) ),
% 7.86/1.47      inference(cnf_transformation,[],[f53]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1413,plain,
% 7.86/1.47      ( v3_pre_topc(sK3,sK1) = iProver_top
% 7.86/1.47      | v6_tops_1(sK2,sK0) = iProver_top ),
% 7.86/1.47      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_20,negated_conjecture,
% 7.86/1.47      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 7.86/1.47      inference(cnf_transformation,[],[f52]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1412,plain,
% 7.86/1.47      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 7.86/1.47      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_13,plain,
% 7.86/1.47      ( ~ v3_pre_topc(X0,X1)
% 7.86/1.47      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 7.86/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.86/1.47      | ~ v2_pre_topc(X3)
% 7.86/1.47      | ~ l1_pre_topc(X3)
% 7.86/1.47      | ~ l1_pre_topc(X1)
% 7.86/1.47      | k1_tops_1(X1,X0) = X0 ),
% 7.86/1.47      inference(cnf_transformation,[],[f46]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_24,negated_conjecture,
% 7.86/1.47      ( v2_pre_topc(sK0) ),
% 7.86/1.47      inference(cnf_transformation,[],[f48]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_289,plain,
% 7.86/1.47      ( ~ v3_pre_topc(X0,X1)
% 7.86/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.86/1.47      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 7.86/1.47      | ~ l1_pre_topc(X1)
% 7.86/1.47      | ~ l1_pre_topc(X3)
% 7.86/1.47      | k1_tops_1(X1,X0) = X0
% 7.86/1.47      | sK0 != X3 ),
% 7.86/1.47      inference(resolution_lifted,[status(thm)],[c_13,c_24]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_290,plain,
% 7.86/1.47      ( ~ v3_pre_topc(X0,X1)
% 7.86/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.86/1.47      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.86/1.47      | ~ l1_pre_topc(X1)
% 7.86/1.47      | ~ l1_pre_topc(sK0)
% 7.86/1.47      | k1_tops_1(X1,X0) = X0 ),
% 7.86/1.47      inference(unflattening,[status(thm)],[c_289]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_23,negated_conjecture,
% 7.86/1.47      ( l1_pre_topc(sK0) ),
% 7.86/1.47      inference(cnf_transformation,[],[f49]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_294,plain,
% 7.86/1.47      ( ~ l1_pre_topc(X1)
% 7.86/1.47      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.86/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.86/1.47      | ~ v3_pre_topc(X0,X1)
% 7.86/1.47      | k1_tops_1(X1,X0) = X0 ),
% 7.86/1.47      inference(global_propositional_subsumption,
% 7.86/1.47                [status(thm)],
% 7.86/1.47                [c_290,c_23]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_295,plain,
% 7.86/1.47      ( ~ v3_pre_topc(X0,X1)
% 7.86/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.86/1.47      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.86/1.47      | ~ l1_pre_topc(X1)
% 7.86/1.47      | k1_tops_1(X1,X0) = X0 ),
% 7.86/1.47      inference(renaming,[status(thm)],[c_294]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_22,negated_conjecture,
% 7.86/1.47      ( l1_pre_topc(sK1) ),
% 7.86/1.47      inference(cnf_transformation,[],[f50]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_326,plain,
% 7.86/1.47      ( ~ v3_pre_topc(X0,X1)
% 7.86/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.86/1.47      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.86/1.47      | k1_tops_1(X1,X0) = X0
% 7.86/1.47      | sK1 != X1 ),
% 7.86/1.47      inference(resolution_lifted,[status(thm)],[c_295,c_22]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_327,plain,
% 7.86/1.47      ( ~ v3_pre_topc(X0,sK1)
% 7.86/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.86/1.47      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.86/1.47      | k1_tops_1(sK1,X0) = X0 ),
% 7.86/1.47      inference(unflattening,[status(thm)],[c_326]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_759,plain,
% 7.86/1.47      ( ~ v3_pre_topc(X0,sK1)
% 7.86/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.86/1.47      | k1_tops_1(sK1,X0) = X0
% 7.86/1.47      | ~ sP4_iProver_split ),
% 7.86/1.47      inference(splitting,
% 7.86/1.47                [splitting(split),new_symbols(definition,[sP4_iProver_split])],
% 7.86/1.47                [c_327]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1409,plain,
% 7.86/1.47      ( k1_tops_1(sK1,X0) = X0
% 7.86/1.47      | v3_pre_topc(X0,sK1) != iProver_top
% 7.86/1.47      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 7.86/1.47      | sP4_iProver_split != iProver_top ),
% 7.86/1.47      inference(predicate_to_equality,[status(thm)],[c_759]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_21,negated_conjecture,
% 7.86/1.47      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.86/1.47      inference(cnf_transformation,[],[f51]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_28,plain,
% 7.86/1.47      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.86/1.47      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_760,plain,
% 7.86/1.47      ( sP4_iProver_split | sP0_iProver_split ),
% 7.86/1.47      inference(splitting,
% 7.86/1.47                [splitting(split),new_symbols(definition,[])],
% 7.86/1.47                [c_327]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_815,plain,
% 7.86/1.47      ( sP4_iProver_split = iProver_top
% 7.86/1.47      | sP0_iProver_split = iProver_top ),
% 7.86/1.47      inference(predicate_to_equality,[status(thm)],[c_760]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_816,plain,
% 7.86/1.47      ( k1_tops_1(sK1,X0) = X0
% 7.86/1.47      | v3_pre_topc(X0,sK1) != iProver_top
% 7.86/1.47      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 7.86/1.47      | sP4_iProver_split != iProver_top ),
% 7.86/1.47      inference(predicate_to_equality,[status(thm)],[c_759]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_12,plain,
% 7.86/1.47      ( v3_pre_topc(X0,X1)
% 7.86/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.86/1.47      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 7.86/1.47      | ~ v2_pre_topc(X1)
% 7.86/1.47      | ~ l1_pre_topc(X1)
% 7.86/1.47      | ~ l1_pre_topc(X3)
% 7.86/1.47      | k1_tops_1(X1,X0) != X0 ),
% 7.86/1.47      inference(cnf_transformation,[],[f47]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_264,plain,
% 7.86/1.47      ( v3_pre_topc(X0,X1)
% 7.86/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.86/1.47      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 7.86/1.47      | ~ l1_pre_topc(X1)
% 7.86/1.47      | ~ l1_pre_topc(X3)
% 7.86/1.47      | k1_tops_1(X1,X0) != X0
% 7.86/1.47      | sK0 != X1 ),
% 7.86/1.47      inference(resolution_lifted,[status(thm)],[c_12,c_24]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_265,plain,
% 7.86/1.47      ( v3_pre_topc(X0,sK0)
% 7.86/1.47      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 7.86/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.86/1.47      | ~ l1_pre_topc(X2)
% 7.86/1.47      | ~ l1_pre_topc(sK0)
% 7.86/1.47      | k1_tops_1(sK0,X0) != X0 ),
% 7.86/1.47      inference(unflattening,[status(thm)],[c_264]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_269,plain,
% 7.86/1.47      ( ~ l1_pre_topc(X2)
% 7.86/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.86/1.47      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 7.86/1.47      | v3_pre_topc(X0,sK0)
% 7.86/1.47      | k1_tops_1(sK0,X0) != X0 ),
% 7.86/1.47      inference(global_propositional_subsumption,
% 7.86/1.47                [status(thm)],
% 7.86/1.47                [c_265,c_23]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_270,plain,
% 7.86/1.47      ( v3_pre_topc(X0,sK0)
% 7.86/1.47      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 7.86/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.86/1.47      | ~ l1_pre_topc(X2)
% 7.86/1.47      | k1_tops_1(sK0,X0) != X0 ),
% 7.86/1.47      inference(renaming,[status(thm)],[c_269]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_644,plain,
% 7.86/1.47      ( v3_pre_topc(X0,sK0)
% 7.86/1.47      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 7.86/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.86/1.47      | k1_tops_1(sK0,X0) != X0
% 7.86/1.47      | sK0 != X2 ),
% 7.86/1.47      inference(resolution_lifted,[status(thm)],[c_23,c_270]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_645,plain,
% 7.86/1.47      ( v3_pre_topc(X0,sK0)
% 7.86/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.86/1.47      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.86/1.47      | k1_tops_1(sK0,X0) != X0 ),
% 7.86/1.47      inference(unflattening,[status(thm)],[c_644]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_752,plain,
% 7.86/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.86/1.47      | ~ sP0_iProver_split ),
% 7.86/1.47      inference(splitting,
% 7.86/1.47                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 7.86/1.47                [c_645]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1496,plain,
% 7.86/1.47      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.86/1.47      | ~ sP0_iProver_split ),
% 7.86/1.47      inference(instantiation,[status(thm)],[c_752]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1497,plain,
% 7.86/1.47      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.86/1.47      | sP0_iProver_split != iProver_top ),
% 7.86/1.47      inference(predicate_to_equality,[status(thm)],[c_1496]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_2694,plain,
% 7.86/1.47      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 7.86/1.47      | v3_pre_topc(X0,sK1) != iProver_top
% 7.86/1.47      | k1_tops_1(sK1,X0) = X0 ),
% 7.86/1.47      inference(global_propositional_subsumption,
% 7.86/1.47                [status(thm)],
% 7.86/1.47                [c_1409,c_28,c_815,c_816,c_1497]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_2695,plain,
% 7.86/1.47      ( k1_tops_1(sK1,X0) = X0
% 7.86/1.47      | v3_pre_topc(X0,sK1) != iProver_top
% 7.86/1.47      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 7.86/1.47      inference(renaming,[status(thm)],[c_2694]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_2700,plain,
% 7.86/1.47      ( k1_tops_1(sK1,sK3) = sK3 | v3_pre_topc(sK3,sK1) != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1412,c_2695]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_2707,plain,
% 7.86/1.47      ( k1_tops_1(sK1,sK3) = sK3 | v6_tops_1(sK2,sK0) = iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1413,c_2700]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1411,plain,
% 7.86/1.47      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.86/1.47      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_9,plain,
% 7.86/1.47      ( ~ v6_tops_1(X0,X1)
% 7.86/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.86/1.47      | ~ l1_pre_topc(X1)
% 7.86/1.47      | k1_tops_1(X1,k2_pre_topc(X1,X0)) = X0 ),
% 7.86/1.47      inference(cnf_transformation,[],[f42]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_524,plain,
% 7.86/1.47      ( ~ v6_tops_1(X0,X1)
% 7.86/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.86/1.47      | k1_tops_1(X1,k2_pre_topc(X1,X0)) = X0
% 7.86/1.47      | sK0 != X1 ),
% 7.86/1.47      inference(resolution_lifted,[status(thm)],[c_9,c_23]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_525,plain,
% 7.86/1.47      ( ~ v6_tops_1(X0,sK0)
% 7.86/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.86/1.47      | k1_tops_1(sK0,k2_pre_topc(sK0,X0)) = X0 ),
% 7.86/1.47      inference(unflattening,[status(thm)],[c_524]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1393,plain,
% 7.86/1.47      ( k1_tops_1(sK0,k2_pre_topc(sK0,X0)) = X0
% 7.86/1.47      | v6_tops_1(X0,sK0) != iProver_top
% 7.86/1.47      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.86/1.47      inference(predicate_to_equality,[status(thm)],[c_525]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_2297,plain,
% 7.86/1.47      ( k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = sK2
% 7.86/1.47      | v6_tops_1(sK2,sK0) != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1411,c_1393]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_2817,plain,
% 7.86/1.47      ( k1_tops_1(sK1,sK3) = sK3
% 7.86/1.47      | k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = sK2 ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_2707,c_2297]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_3,plain,
% 7.86/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.86/1.47      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.86/1.47      | ~ l1_pre_topc(X1) ),
% 7.86/1.47      inference(cnf_transformation,[],[f37]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_614,plain,
% 7.86/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.86/1.47      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.86/1.47      | sK0 != X1 ),
% 7.86/1.47      inference(resolution_lifted,[status(thm)],[c_3,c_23]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_615,plain,
% 7.86/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.86/1.47      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.86/1.47      inference(unflattening,[status(thm)],[c_614]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1387,plain,
% 7.86/1.47      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.86/1.47      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.86/1.47      inference(predicate_to_equality,[status(thm)],[c_615]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_10,plain,
% 7.86/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.86/1.47      | ~ l1_pre_topc(X1)
% 7.86/1.47      | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
% 7.86/1.47      inference(cnf_transformation,[],[f44]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_512,plain,
% 7.86/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.86/1.47      | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0)
% 7.86/1.47      | sK0 != X1 ),
% 7.86/1.47      inference(resolution_lifted,[status(thm)],[c_10,c_23]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_513,plain,
% 7.86/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.86/1.47      | k1_tops_1(sK0,k1_tops_1(sK0,X0)) = k1_tops_1(sK0,X0) ),
% 7.86/1.47      inference(unflattening,[status(thm)],[c_512]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1394,plain,
% 7.86/1.47      ( k1_tops_1(sK0,k1_tops_1(sK0,X0)) = k1_tops_1(sK0,X0)
% 7.86/1.47      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.86/1.47      inference(predicate_to_equality,[status(thm)],[c_513]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1990,plain,
% 7.86/1.47      ( k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,X0))) = k1_tops_1(sK0,k2_pre_topc(sK0,X0))
% 7.86/1.47      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1387,c_1394]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_3130,plain,
% 7.86/1.47      ( k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK2))) = k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1411,c_1990]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_3875,plain,
% 7.86/1.47      ( k1_tops_1(sK1,sK3) = sK3
% 7.86/1.47      | k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = k1_tops_1(sK0,sK2) ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_2817,c_3130]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_7,plain,
% 7.86/1.47      ( ~ v4_tops_1(X0,X1)
% 7.86/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.86/1.47      | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
% 7.86/1.47      | ~ l1_pre_topc(X1) ),
% 7.86/1.47      inference(cnf_transformation,[],[f39]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_554,plain,
% 7.86/1.47      ( ~ v4_tops_1(X0,X1)
% 7.86/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.86/1.47      | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
% 7.86/1.47      | sK0 != X1 ),
% 7.86/1.47      inference(resolution_lifted,[status(thm)],[c_7,c_23]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_555,plain,
% 7.86/1.47      ( ~ v4_tops_1(X0,sK0)
% 7.86/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.86/1.47      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X0) ),
% 7.86/1.47      inference(unflattening,[status(thm)],[c_554]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1391,plain,
% 7.86/1.47      ( v4_tops_1(X0,sK0) != iProver_top
% 7.86/1.47      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.86/1.47      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X0) = iProver_top ),
% 7.86/1.47      inference(predicate_to_equality,[status(thm)],[c_555]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_3935,plain,
% 7.86/1.47      ( k1_tops_1(sK1,sK3) = sK3
% 7.86/1.47      | v4_tops_1(sK2,sK0) != iProver_top
% 7.86/1.47      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.86/1.47      | r1_tarski(k1_tops_1(sK0,sK2),sK2) = iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_3875,c_1391]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_29,plain,
% 7.86/1.47      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 7.86/1.47      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_17,negated_conjecture,
% 7.86/1.47      ( ~ v6_tops_1(sK3,sK1) | v6_tops_1(sK2,sK0) ),
% 7.86/1.47      inference(cnf_transformation,[],[f55]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_32,plain,
% 7.86/1.47      ( v6_tops_1(sK3,sK1) != iProver_top
% 7.86/1.47      | v6_tops_1(sK2,sK0) = iProver_top ),
% 7.86/1.47      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_2,plain,
% 7.86/1.47      ( r1_tarski(X0,X0) ),
% 7.86/1.47      inference(cnf_transformation,[],[f60]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_70,plain,
% 7.86/1.47      ( r1_tarski(sK0,sK0) ),
% 7.86/1.47      inference(instantiation,[status(thm)],[c_2]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_0,plain,
% 7.86/1.47      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.86/1.47      inference(cnf_transformation,[],[f36]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_74,plain,
% 7.86/1.47      ( ~ r1_tarski(sK0,sK0) | sK0 = sK0 ),
% 7.86/1.47      inference(instantiation,[status(thm)],[c_0]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_464,plain,
% 7.86/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.86/1.47      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.86/1.47      | sK1 != X1 ),
% 7.86/1.47      inference(resolution_lifted,[status(thm)],[c_3,c_22]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_465,plain,
% 7.86/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.86/1.47      | m1_subset_1(k2_pre_topc(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 7.86/1.47      inference(unflattening,[status(thm)],[c_464]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1504,plain,
% 7.86/1.47      ( m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 7.86/1.47      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 7.86/1.47      inference(instantiation,[status(thm)],[c_465]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1505,plain,
% 7.86/1.47      ( m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 7.86/1.47      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 7.86/1.47      inference(predicate_to_equality,[status(thm)],[c_1504]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_4,plain,
% 7.86/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.86/1.47      | r1_tarski(X0,k2_pre_topc(X1,X0))
% 7.86/1.47      | ~ l1_pre_topc(X1) ),
% 7.86/1.47      inference(cnf_transformation,[],[f38]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_452,plain,
% 7.86/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.86/1.47      | r1_tarski(X0,k2_pre_topc(X1,X0))
% 7.86/1.47      | sK1 != X1 ),
% 7.86/1.47      inference(resolution_lifted,[status(thm)],[c_4,c_22]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_453,plain,
% 7.86/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.86/1.47      | r1_tarski(X0,k2_pre_topc(sK1,X0)) ),
% 7.86/1.47      inference(unflattening,[status(thm)],[c_452]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1522,plain,
% 7.86/1.47      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.86/1.47      | r1_tarski(sK3,k2_pre_topc(sK1,sK3)) ),
% 7.86/1.47      inference(instantiation,[status(thm)],[c_453]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1523,plain,
% 7.86/1.47      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 7.86/1.47      | r1_tarski(sK3,k2_pre_topc(sK1,sK3)) = iProver_top ),
% 7.86/1.47      inference(predicate_to_equality,[status(thm)],[c_1522]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_8,plain,
% 7.86/1.47      ( v6_tops_1(X0,X1)
% 7.86/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.86/1.47      | ~ l1_pre_topc(X1)
% 7.86/1.47      | k1_tops_1(X1,k2_pre_topc(X1,X0)) != X0 ),
% 7.86/1.47      inference(cnf_transformation,[],[f43]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_389,plain,
% 7.86/1.47      ( v6_tops_1(X0,X1)
% 7.86/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.86/1.47      | k1_tops_1(X1,k2_pre_topc(X1,X0)) != X0
% 7.86/1.47      | sK1 != X1 ),
% 7.86/1.47      inference(resolution_lifted,[status(thm)],[c_8,c_22]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_390,plain,
% 7.86/1.47      ( v6_tops_1(X0,sK1)
% 7.86/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.86/1.47      | k1_tops_1(sK1,k2_pre_topc(sK1,X0)) != X0 ),
% 7.86/1.47      inference(unflattening,[status(thm)],[c_389]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1539,plain,
% 7.86/1.47      ( v6_tops_1(sK3,sK1)
% 7.86/1.47      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.86/1.47      | k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) != sK3 ),
% 7.86/1.47      inference(instantiation,[status(thm)],[c_390]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1540,plain,
% 7.86/1.47      ( k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) != sK3
% 7.86/1.47      | v6_tops_1(sK3,sK1) = iProver_top
% 7.86/1.47      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 7.86/1.47      inference(predicate_to_equality,[status(thm)],[c_1539]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1654,plain,
% 7.86/1.47      ( ~ r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3)
% 7.86/1.47      | ~ r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))
% 7.86/1.47      | k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) = sK3 ),
% 7.86/1.47      inference(instantiation,[status(thm)],[c_0]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1655,plain,
% 7.86/1.47      ( k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) = sK3
% 7.86/1.47      | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3) != iProver_top
% 7.86/1.47      | r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) != iProver_top ),
% 7.86/1.47      inference(predicate_to_equality,[status(thm)],[c_1654]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_404,plain,
% 7.86/1.47      ( ~ v4_tops_1(X0,X1)
% 7.86/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.86/1.47      | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
% 7.86/1.47      | sK1 != X1 ),
% 7.86/1.47      inference(resolution_lifted,[status(thm)],[c_7,c_22]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_405,plain,
% 7.86/1.47      ( ~ v4_tops_1(X0,sK1)
% 7.86/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.86/1.47      | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,X0)),X0) ),
% 7.86/1.47      inference(unflattening,[status(thm)],[c_404]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1664,plain,
% 7.86/1.47      ( ~ v4_tops_1(sK3,sK1)
% 7.86/1.47      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.86/1.47      | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3) ),
% 7.86/1.47      inference(instantiation,[status(thm)],[c_405]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1665,plain,
% 7.86/1.47      ( v4_tops_1(sK3,sK1) != iProver_top
% 7.86/1.47      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 7.86/1.47      | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3) = iProver_top ),
% 7.86/1.47      inference(predicate_to_equality,[status(thm)],[c_1664]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_11,plain,
% 7.86/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.86/1.47      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 7.86/1.47      | ~ r1_tarski(X0,X2)
% 7.86/1.47      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 7.86/1.47      | ~ l1_pre_topc(X1) ),
% 7.86/1.47      inference(cnf_transformation,[],[f45]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_344,plain,
% 7.86/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.86/1.47      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 7.86/1.47      | ~ r1_tarski(X0,X2)
% 7.86/1.47      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 7.86/1.47      | sK1 != X1 ),
% 7.86/1.47      inference(resolution_lifted,[status(thm)],[c_11,c_22]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_345,plain,
% 7.86/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.86/1.47      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.86/1.47      | ~ r1_tarski(X0,X1)
% 7.86/1.47      | r1_tarski(k1_tops_1(sK1,X0),k1_tops_1(sK1,X1)) ),
% 7.86/1.47      inference(unflattening,[status(thm)],[c_344]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1569,plain,
% 7.86/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.86/1.47      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.86/1.47      | r1_tarski(k1_tops_1(sK1,sK3),k1_tops_1(sK1,X0))
% 7.86/1.47      | ~ r1_tarski(sK3,X0) ),
% 7.86/1.47      inference(instantiation,[status(thm)],[c_345]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1686,plain,
% 7.86/1.47      ( ~ m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 7.86/1.47      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.86/1.47      | r1_tarski(k1_tops_1(sK1,sK3),k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))
% 7.86/1.47      | ~ r1_tarski(sK3,k2_pre_topc(sK1,sK3)) ),
% 7.86/1.47      inference(instantiation,[status(thm)],[c_1569]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1687,plain,
% 7.86/1.47      ( m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 7.86/1.47      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 7.86/1.47      | r1_tarski(k1_tops_1(sK1,sK3),k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) = iProver_top
% 7.86/1.47      | r1_tarski(sK3,k2_pre_topc(sK1,sK3)) != iProver_top ),
% 7.86/1.47      inference(predicate_to_equality,[status(thm)],[c_1686]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1595,plain,
% 7.86/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.86/1.47      | ~ m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 7.86/1.47      | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),k1_tops_1(sK1,X0))
% 7.86/1.47      | ~ r1_tarski(k2_pre_topc(sK1,sK3),X0) ),
% 7.86/1.47      inference(instantiation,[status(thm)],[c_345]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1825,plain,
% 7.86/1.47      ( ~ m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 7.86/1.47      | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))
% 7.86/1.47      | ~ r1_tarski(k2_pre_topc(sK1,sK3),k2_pre_topc(sK1,sK3)) ),
% 7.86/1.47      inference(instantiation,[status(thm)],[c_1595]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1969,plain,
% 7.86/1.47      ( r1_tarski(sK2,sK2) ),
% 7.86/1.47      inference(instantiation,[status(thm)],[c_2]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1970,plain,
% 7.86/1.47      ( r1_tarski(sK2,sK2) = iProver_top ),
% 7.86/1.47      inference(predicate_to_equality,[status(thm)],[c_1969]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_762,plain,( X0 = X0 ),theory(equality) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_2033,plain,
% 7.86/1.47      ( sK2 = sK2 ),
% 7.86/1.47      inference(instantiation,[status(thm)],[c_762]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_2067,plain,
% 7.86/1.47      ( r1_tarski(k2_pre_topc(sK1,sK3),k2_pre_topc(sK1,sK3)) ),
% 7.86/1.47      inference(instantiation,[status(thm)],[c_2]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_18,negated_conjecture,
% 7.86/1.47      ( v6_tops_1(sK2,sK0) | v4_tops_1(sK3,sK1) ),
% 7.86/1.47      inference(cnf_transformation,[],[f54]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1414,plain,
% 7.86/1.47      ( v6_tops_1(sK2,sK0) = iProver_top
% 7.86/1.47      | v4_tops_1(sK3,sK1) = iProver_top ),
% 7.86/1.47      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_2304,plain,
% 7.86/1.47      ( k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = sK2
% 7.86/1.47      | v4_tops_1(sK3,sK1) = iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1414,c_2297]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_476,plain,
% 7.86/1.47      ( ~ v3_pre_topc(X0,X1)
% 7.86/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.86/1.47      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.86/1.47      | k1_tops_1(X1,X0) = X0
% 7.86/1.47      | sK0 != X1 ),
% 7.86/1.47      inference(resolution_lifted,[status(thm)],[c_295,c_23]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_477,plain,
% 7.86/1.47      ( ~ v3_pre_topc(X0,sK0)
% 7.86/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.86/1.47      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.86/1.47      | k1_tops_1(sK0,X0) = X0 ),
% 7.86/1.47      inference(unflattening,[status(thm)],[c_476]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_757,plain,
% 7.86/1.47      ( ~ v3_pre_topc(X0,sK0)
% 7.86/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.86/1.47      | k1_tops_1(sK0,X0) = X0
% 7.86/1.47      | ~ sP3_iProver_split ),
% 7.86/1.47      inference(splitting,
% 7.86/1.47                [splitting(split),new_symbols(definition,[sP3_iProver_split])],
% 7.86/1.47                [c_477]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1397,plain,
% 7.86/1.47      ( k1_tops_1(sK0,X0) = X0
% 7.86/1.47      | v3_pre_topc(X0,sK0) != iProver_top
% 7.86/1.47      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.86/1.47      | sP3_iProver_split != iProver_top ),
% 7.86/1.47      inference(predicate_to_equality,[status(thm)],[c_757]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_758,plain,
% 7.86/1.47      ( sP3_iProver_split | sP0_iProver_split ),
% 7.86/1.47      inference(splitting,
% 7.86/1.47                [splitting(split),new_symbols(definition,[])],
% 7.86/1.47                [c_477]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_803,plain,
% 7.86/1.47      ( sP3_iProver_split = iProver_top
% 7.86/1.47      | sP0_iProver_split = iProver_top ),
% 7.86/1.47      inference(predicate_to_equality,[status(thm)],[c_758]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_804,plain,
% 7.86/1.47      ( k1_tops_1(sK0,X0) = X0
% 7.86/1.47      | v3_pre_topc(X0,sK0) != iProver_top
% 7.86/1.47      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.86/1.47      | sP3_iProver_split != iProver_top ),
% 7.86/1.47      inference(predicate_to_equality,[status(thm)],[c_757]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_2590,plain,
% 7.86/1.47      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.86/1.47      | v3_pre_topc(X0,sK0) != iProver_top
% 7.86/1.47      | k1_tops_1(sK0,X0) = X0 ),
% 7.86/1.47      inference(global_propositional_subsumption,
% 7.86/1.47                [status(thm)],
% 7.86/1.47                [c_1397,c_28,c_803,c_804,c_1497]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_2591,plain,
% 7.86/1.47      ( k1_tops_1(sK0,X0) = X0
% 7.86/1.47      | v3_pre_topc(X0,sK0) != iProver_top
% 7.86/1.47      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.86/1.47      inference(renaming,[status(thm)],[c_2590]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_2594,plain,
% 7.86/1.47      ( k1_tops_1(sK0,sK2) = sK2 | v3_pre_topc(sK2,sK0) != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1411,c_2591]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_2686,plain,
% 7.86/1.47      ( sK3 = sK3 ),
% 7.86/1.47      inference(instantiation,[status(thm)],[c_762]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_3938,plain,
% 7.86/1.47      ( k1_tops_1(sK1,sK3) = sK3 | k1_tops_1(sK0,sK2) = sK2 ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_3875,c_2817]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_764,plain,
% 7.86/1.47      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.86/1.47      theory(equality) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1960,plain,
% 7.86/1.47      ( ~ r1_tarski(X0,X1)
% 7.86/1.47      | r1_tarski(k1_tops_1(sK0,sK2),sK2)
% 7.86/1.47      | k1_tops_1(sK0,sK2) != X0
% 7.86/1.47      | sK2 != X1 ),
% 7.86/1.47      inference(instantiation,[status(thm)],[c_764]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_3077,plain,
% 7.86/1.47      ( ~ r1_tarski(X0,sK2)
% 7.86/1.47      | r1_tarski(k1_tops_1(sK0,sK2),sK2)
% 7.86/1.47      | k1_tops_1(sK0,sK2) != X0
% 7.86/1.47      | sK2 != sK2 ),
% 7.86/1.47      inference(instantiation,[status(thm)],[c_1960]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_4243,plain,
% 7.86/1.47      ( r1_tarski(k1_tops_1(sK0,sK2),sK2)
% 7.86/1.47      | ~ r1_tarski(sK2,sK2)
% 7.86/1.47      | k1_tops_1(sK0,sK2) != sK2
% 7.86/1.47      | sK2 != sK2 ),
% 7.86/1.47      inference(instantiation,[status(thm)],[c_3077]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_4244,plain,
% 7.86/1.47      ( k1_tops_1(sK0,sK2) != sK2
% 7.86/1.47      | sK2 != sK2
% 7.86/1.47      | r1_tarski(k1_tops_1(sK0,sK2),sK2) = iProver_top
% 7.86/1.47      | r1_tarski(sK2,sK2) != iProver_top ),
% 7.86/1.47      inference(predicate_to_equality,[status(thm)],[c_4243]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_763,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_2081,plain,
% 7.86/1.47      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 7.86/1.47      inference(instantiation,[status(thm)],[c_763]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_3110,plain,
% 7.86/1.47      ( X0 != sK3 | sK3 = X0 | sK3 != sK3 ),
% 7.86/1.47      inference(instantiation,[status(thm)],[c_2081]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_4248,plain,
% 7.86/1.47      ( k1_tops_1(sK1,sK3) != sK3
% 7.86/1.47      | sK3 = k1_tops_1(sK1,sK3)
% 7.86/1.47      | sK3 != sK3 ),
% 7.86/1.47      inference(instantiation,[status(thm)],[c_3110]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1692,plain,
% 7.86/1.47      ( ~ r1_tarski(X0,X1) | r1_tarski(sK3,X2) | X2 != X1 | sK3 != X0 ),
% 7.86/1.47      inference(instantiation,[status(thm)],[c_764]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_4650,plain,
% 7.86/1.47      ( ~ r1_tarski(k1_tops_1(sK1,sK3),X0)
% 7.86/1.47      | r1_tarski(sK3,X1)
% 7.86/1.47      | X1 != X0
% 7.86/1.47      | sK3 != k1_tops_1(sK1,sK3) ),
% 7.86/1.47      inference(instantiation,[status(thm)],[c_1692]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_7380,plain,
% 7.86/1.47      ( ~ r1_tarski(k1_tops_1(sK1,sK3),k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))
% 7.86/1.47      | r1_tarski(sK3,X0)
% 7.86/1.47      | X0 != k1_tops_1(sK1,k2_pre_topc(sK1,sK3))
% 7.86/1.47      | sK3 != k1_tops_1(sK1,sK3) ),
% 7.86/1.47      inference(instantiation,[status(thm)],[c_4650]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_9244,plain,
% 7.86/1.47      ( ~ r1_tarski(k1_tops_1(sK1,sK3),k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))
% 7.86/1.47      | r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))
% 7.86/1.47      | k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) != k1_tops_1(sK1,k2_pre_topc(sK1,sK3))
% 7.86/1.47      | sK3 != k1_tops_1(sK1,sK3) ),
% 7.86/1.47      inference(instantiation,[status(thm)],[c_7380]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_9245,plain,
% 7.86/1.47      ( k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) != k1_tops_1(sK1,k2_pre_topc(sK1,sK3))
% 7.86/1.47      | sK3 != k1_tops_1(sK1,sK3)
% 7.86/1.47      | r1_tarski(k1_tops_1(sK1,sK3),k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) != iProver_top
% 7.86/1.47      | r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) = iProver_top ),
% 7.86/1.47      inference(predicate_to_equality,[status(thm)],[c_9244]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1722,plain,
% 7.86/1.47      ( X0 != X1 | sK2 != X1 | sK2 = X0 ),
% 7.86/1.47      inference(instantiation,[status(thm)],[c_763]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_2129,plain,
% 7.86/1.47      ( X0 != sK2 | sK2 = X0 | sK2 != sK2 ),
% 7.86/1.47      inference(instantiation,[status(thm)],[c_1722]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_12892,plain,
% 7.86/1.47      ( k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) != sK2
% 7.86/1.47      | sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2))
% 7.86/1.47      | sK2 != sK2 ),
% 7.86/1.47      inference(instantiation,[status(thm)],[c_2129]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_753,plain,
% 7.86/1.47      ( v3_pre_topc(X0,sK0)
% 7.86/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.86/1.47      | k1_tops_1(sK0,X0) != X0
% 7.86/1.47      | ~ sP1_iProver_split ),
% 7.86/1.47      inference(splitting,
% 7.86/1.47                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 7.86/1.47                [c_645]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1382,plain,
% 7.86/1.47      ( k1_tops_1(sK0,X0) != X0
% 7.86/1.47      | v3_pre_topc(X0,sK0) = iProver_top
% 7.86/1.47      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.86/1.47      | sP1_iProver_split != iProver_top ),
% 7.86/1.47      inference(predicate_to_equality,[status(thm)],[c_753]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_754,plain,
% 7.86/1.47      ( sP1_iProver_split | sP0_iProver_split ),
% 7.86/1.47      inference(splitting,
% 7.86/1.47                [splitting(split),new_symbols(definition,[])],
% 7.86/1.47                [c_645]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_784,plain,
% 7.86/1.47      ( sP1_iProver_split = iProver_top
% 7.86/1.47      | sP0_iProver_split = iProver_top ),
% 7.86/1.47      inference(predicate_to_equality,[status(thm)],[c_754]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_785,plain,
% 7.86/1.47      ( k1_tops_1(sK0,X0) != X0
% 7.86/1.47      | v3_pre_topc(X0,sK0) = iProver_top
% 7.86/1.47      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.86/1.47      | sP1_iProver_split != iProver_top ),
% 7.86/1.47      inference(predicate_to_equality,[status(thm)],[c_753]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1709,plain,
% 7.86/1.47      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.86/1.47      | v3_pre_topc(X0,sK0) = iProver_top
% 7.86/1.47      | k1_tops_1(sK0,X0) != X0 ),
% 7.86/1.47      inference(global_propositional_subsumption,
% 7.86/1.47                [status(thm)],
% 7.86/1.47                [c_1382,c_28,c_784,c_785,c_1497]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1710,plain,
% 7.86/1.47      ( k1_tops_1(sK0,X0) != X0
% 7.86/1.47      | v3_pre_topc(X0,sK0) = iProver_top
% 7.86/1.47      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.86/1.47      inference(renaming,[status(thm)],[c_1709]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_3138,plain,
% 7.86/1.47      ( v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK0) = iProver_top
% 7.86/1.47      | m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_3130,c_1710]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_3874,plain,
% 7.86/1.47      ( k1_tops_1(sK1,sK3) = sK3
% 7.86/1.47      | v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK0) = iProver_top
% 7.86/1.47      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_2817,c_3138]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_2205,plain,
% 7.86/1.47      ( sK1 = sK1 ),
% 7.86/1.47      inference(instantiation,[status(thm)],[c_762]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_2267,plain,
% 7.86/1.47      ( k1_zfmisc_1(u1_struct_0(sK0)) = k1_zfmisc_1(u1_struct_0(sK0)) ),
% 7.86/1.47      inference(instantiation,[status(thm)],[c_762]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_2277,plain,
% 7.86/1.47      ( k1_zfmisc_1(u1_struct_0(sK1)) = k1_zfmisc_1(u1_struct_0(sK1)) ),
% 7.86/1.47      inference(instantiation,[status(thm)],[c_762]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_768,plain,
% 7.86/1.47      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.86/1.47      theory(equality) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1507,plain,
% 7.86/1.47      ( ~ m1_subset_1(X0,X1)
% 7.86/1.47      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.86/1.47      | X2 != X0
% 7.86/1.47      | k1_zfmisc_1(u1_struct_0(sK1)) != X1 ),
% 7.86/1.47      inference(instantiation,[status(thm)],[c_768]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1869,plain,
% 7.86/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.86/1.47      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.86/1.47      | X1 != X0
% 7.86/1.47      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 7.86/1.47      inference(instantiation,[status(thm)],[c_1507]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_3046,plain,
% 7.86/1.47      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.86/1.47      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.86/1.47      | X0 != sK3
% 7.86/1.47      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 7.86/1.47      inference(instantiation,[status(thm)],[c_1869]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_3488,plain,
% 7.86/1.47      ( m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 7.86/1.47      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.86/1.47      | k1_tops_1(sK1,sK3) != sK3
% 7.86/1.47      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 7.86/1.47      inference(instantiation,[status(thm)],[c_3046]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_3489,plain,
% 7.86/1.47      ( k1_tops_1(sK1,sK3) != sK3
% 7.86/1.47      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
% 7.86/1.47      | m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 7.86/1.47      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 7.86/1.47      inference(predicate_to_equality,[status(thm)],[c_3488]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_769,plain,
% 7.86/1.47      ( ~ v4_tops_1(X0,X1) | v4_tops_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.86/1.47      theory(equality) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_2537,plain,
% 7.86/1.47      ( v4_tops_1(X0,X1) | ~ v4_tops_1(sK3,sK1) | X1 != sK1 | X0 != sK3 ),
% 7.86/1.47      inference(instantiation,[status(thm)],[c_769]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_2669,plain,
% 7.86/1.47      ( v4_tops_1(X0,sK1)
% 7.86/1.47      | ~ v4_tops_1(sK3,sK1)
% 7.86/1.47      | X0 != sK3
% 7.86/1.47      | sK1 != sK1 ),
% 7.86/1.47      inference(instantiation,[status(thm)],[c_2537]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_3682,plain,
% 7.86/1.47      ( v4_tops_1(k1_tops_1(sK1,sK3),sK1)
% 7.86/1.47      | ~ v4_tops_1(sK3,sK1)
% 7.86/1.47      | k1_tops_1(sK1,sK3) != sK3
% 7.86/1.47      | sK1 != sK1 ),
% 7.86/1.47      inference(instantiation,[status(thm)],[c_2669]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_3683,plain,
% 7.86/1.47      ( k1_tops_1(sK1,sK3) != sK3
% 7.86/1.47      | sK1 != sK1
% 7.86/1.47      | v4_tops_1(k1_tops_1(sK1,sK3),sK1) = iProver_top
% 7.86/1.47      | v4_tops_1(sK3,sK1) != iProver_top ),
% 7.86/1.47      inference(predicate_to_equality,[status(thm)],[c_3682]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_4414,plain,
% 7.86/1.47      ( ~ m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 7.86/1.47      | r1_tarski(k1_tops_1(sK1,sK3),k2_pre_topc(sK1,k1_tops_1(sK1,sK3))) ),
% 7.86/1.47      inference(instantiation,[status(thm)],[c_453]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_4421,plain,
% 7.86/1.47      ( m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 7.86/1.47      | r1_tarski(k1_tops_1(sK1,sK3),k2_pre_topc(sK1,k1_tops_1(sK1,sK3))) = iProver_top ),
% 7.86/1.47      inference(predicate_to_equality,[status(thm)],[c_4414]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_4413,plain,
% 7.86/1.47      ( v6_tops_1(k1_tops_1(sK1,sK3),sK1)
% 7.86/1.47      | ~ m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 7.86/1.47      | k1_tops_1(sK1,k2_pre_topc(sK1,k1_tops_1(sK1,sK3))) != k1_tops_1(sK1,sK3) ),
% 7.86/1.47      inference(instantiation,[status(thm)],[c_390]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_4423,plain,
% 7.86/1.47      ( k1_tops_1(sK1,k2_pre_topc(sK1,k1_tops_1(sK1,sK3))) != k1_tops_1(sK1,sK3)
% 7.86/1.47      | v6_tops_1(k1_tops_1(sK1,sK3),sK1) = iProver_top
% 7.86/1.47      | m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 7.86/1.47      inference(predicate_to_equality,[status(thm)],[c_4413]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_362,plain,
% 7.86/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.86/1.47      | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0)
% 7.86/1.47      | sK1 != X1 ),
% 7.86/1.47      inference(resolution_lifted,[status(thm)],[c_10,c_22]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_363,plain,
% 7.86/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.86/1.47      | k1_tops_1(sK1,k1_tops_1(sK1,X0)) = k1_tops_1(sK1,X0) ),
% 7.86/1.47      inference(unflattening,[status(thm)],[c_362]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1406,plain,
% 7.86/1.47      ( k1_tops_1(sK1,k1_tops_1(sK1,X0)) = k1_tops_1(sK1,X0)
% 7.86/1.47      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 7.86/1.47      inference(predicate_to_equality,[status(thm)],[c_363]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_2180,plain,
% 7.86/1.47      ( k1_tops_1(sK1,k1_tops_1(sK1,sK3)) = k1_tops_1(sK1,sK3) ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1412,c_1406]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1399,plain,
% 7.86/1.47      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 7.86/1.47      | m1_subset_1(k2_pre_topc(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 7.86/1.47      inference(predicate_to_equality,[status(thm)],[c_465]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1407,plain,
% 7.86/1.47      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 7.86/1.47      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 7.86/1.47      | r1_tarski(X0,X1) != iProver_top
% 7.86/1.47      | r1_tarski(k1_tops_1(sK1,X0),k1_tops_1(sK1,X1)) = iProver_top ),
% 7.86/1.47      inference(predicate_to_equality,[status(thm)],[c_345]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1403,plain,
% 7.86/1.47      ( v4_tops_1(X0,sK1) != iProver_top
% 7.86/1.47      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 7.86/1.47      | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,X0)),X0) = iProver_top ),
% 7.86/1.47      inference(predicate_to_equality,[status(thm)],[c_405]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1420,plain,
% 7.86/1.47      ( X0 = X1
% 7.86/1.47      | r1_tarski(X0,X1) != iProver_top
% 7.86/1.47      | r1_tarski(X1,X0) != iProver_top ),
% 7.86/1.47      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_2564,plain,
% 7.86/1.47      ( k1_tops_1(sK1,k2_pre_topc(sK1,X0)) = X0
% 7.86/1.47      | v4_tops_1(X0,sK1) != iProver_top
% 7.86/1.47      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 7.86/1.47      | r1_tarski(X0,k1_tops_1(sK1,k2_pre_topc(sK1,X0))) != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1403,c_1420]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_2954,plain,
% 7.86/1.47      ( k1_tops_1(sK1,k2_pre_topc(sK1,k1_tops_1(sK1,X0))) = k1_tops_1(sK1,X0)
% 7.86/1.47      | v4_tops_1(k1_tops_1(sK1,X0),sK1) != iProver_top
% 7.86/1.47      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 7.86/1.47      | m1_subset_1(k1_tops_1(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 7.86/1.47      | m1_subset_1(k2_pre_topc(sK1,k1_tops_1(sK1,X0)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 7.86/1.47      | r1_tarski(X0,k2_pre_topc(sK1,k1_tops_1(sK1,X0))) != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1407,c_2564]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_6909,plain,
% 7.86/1.47      ( k1_tops_1(sK1,k2_pre_topc(sK1,k1_tops_1(sK1,X0))) = k1_tops_1(sK1,X0)
% 7.86/1.47      | v4_tops_1(k1_tops_1(sK1,X0),sK1) != iProver_top
% 7.86/1.47      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 7.86/1.47      | m1_subset_1(k1_tops_1(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 7.86/1.47      | r1_tarski(X0,k2_pre_topc(sK1,k1_tops_1(sK1,X0))) != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_1399,c_2954]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_7763,plain,
% 7.86/1.47      ( k1_tops_1(sK1,k2_pre_topc(sK1,k1_tops_1(sK1,k1_tops_1(sK1,sK3)))) = k1_tops_1(sK1,k1_tops_1(sK1,sK3))
% 7.86/1.47      | v4_tops_1(k1_tops_1(sK1,k1_tops_1(sK1,sK3)),sK1) != iProver_top
% 7.86/1.47      | m1_subset_1(k1_tops_1(sK1,k1_tops_1(sK1,sK3)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 7.86/1.47      | m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 7.86/1.47      | r1_tarski(k1_tops_1(sK1,sK3),k2_pre_topc(sK1,k1_tops_1(sK1,sK3))) != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_2180,c_6909]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_7780,plain,
% 7.86/1.47      ( k1_tops_1(sK1,k2_pre_topc(sK1,k1_tops_1(sK1,sK3))) = k1_tops_1(sK1,sK3)
% 7.86/1.47      | v4_tops_1(k1_tops_1(sK1,sK3),sK1) != iProver_top
% 7.86/1.47      | m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 7.86/1.47      | r1_tarski(k1_tops_1(sK1,sK3),k2_pre_topc(sK1,k1_tops_1(sK1,sK3))) != iProver_top ),
% 7.86/1.47      inference(light_normalisation,[status(thm)],[c_7763,c_2180]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_771,plain,
% 7.86/1.47      ( ~ v6_tops_1(X0,X1) | v6_tops_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.86/1.47      theory(equality) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1534,plain,
% 7.86/1.47      ( ~ v6_tops_1(X0,X1) | v6_tops_1(X2,sK1) | X2 != X0 | sK1 != X1 ),
% 7.86/1.47      inference(instantiation,[status(thm)],[c_771]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1736,plain,
% 7.86/1.47      ( ~ v6_tops_1(X0,sK1) | v6_tops_1(X1,sK1) | X1 != X0 | sK1 != sK1 ),
% 7.86/1.47      inference(instantiation,[status(thm)],[c_1534]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_6393,plain,
% 7.86/1.47      ( v6_tops_1(X0,sK1)
% 7.86/1.47      | ~ v6_tops_1(k1_tops_1(sK1,sK3),sK1)
% 7.86/1.47      | X0 != k1_tops_1(sK1,sK3)
% 7.86/1.47      | sK1 != sK1 ),
% 7.86/1.47      inference(instantiation,[status(thm)],[c_1736]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_9098,plain,
% 7.86/1.47      ( ~ v6_tops_1(k1_tops_1(sK1,sK3),sK1)
% 7.86/1.47      | v6_tops_1(sK3,sK1)
% 7.86/1.47      | sK1 != sK1
% 7.86/1.47      | sK3 != k1_tops_1(sK1,sK3) ),
% 7.86/1.47      inference(instantiation,[status(thm)],[c_6393]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_9099,plain,
% 7.86/1.47      ( sK1 != sK1
% 7.86/1.47      | sK3 != k1_tops_1(sK1,sK3)
% 7.86/1.47      | v6_tops_1(k1_tops_1(sK1,sK3),sK1) != iProver_top
% 7.86/1.47      | v6_tops_1(sK3,sK1) = iProver_top ),
% 7.86/1.47      inference(predicate_to_equality,[status(thm)],[c_9098]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1499,plain,
% 7.86/1.47      ( ~ m1_subset_1(X0,X1)
% 7.86/1.47      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.86/1.47      | X2 != X0
% 7.86/1.47      | k1_zfmisc_1(u1_struct_0(sK0)) != X1 ),
% 7.86/1.47      inference(instantiation,[status(thm)],[c_768]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1847,plain,
% 7.86/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.86/1.47      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.86/1.47      | X1 != X0
% 7.86/1.47      | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0)) ),
% 7.86/1.47      inference(instantiation,[status(thm)],[c_1499]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_3015,plain,
% 7.86/1.47      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.86/1.47      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.86/1.47      | X0 != sK2
% 7.86/1.47      | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0)) ),
% 7.86/1.47      inference(instantiation,[status(thm)],[c_1847]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_12891,plain,
% 7.86/1.47      ( m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
% 7.86/1.47      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.86/1.47      | k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) != sK2
% 7.86/1.47      | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0)) ),
% 7.86/1.47      inference(instantiation,[status(thm)],[c_3015]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_12895,plain,
% 7.86/1.47      ( k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) != sK2
% 7.86/1.47      | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0))
% 7.86/1.47      | m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 7.86/1.47      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.86/1.47      inference(predicate_to_equality,[status(thm)],[c_12891]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_13695,plain,
% 7.86/1.47      ( v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK0) = iProver_top ),
% 7.86/1.47      inference(global_propositional_subsumption,
% 7.86/1.47                [status(thm)],
% 7.86/1.47                [c_3874,c_28,c_29,c_32,c_2205,c_2267,c_2277,c_2297,
% 7.86/1.47                 c_2304,c_2686,c_3138,c_3489,c_3683,c_4248,c_4421,c_4423,
% 7.86/1.47                 c_7780,c_9099,c_12895]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_9239,plain,
% 7.86/1.47      ( ~ r1_tarski(X0,k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))
% 7.86/1.47      | ~ r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),X0)
% 7.86/1.47      | X0 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) ),
% 7.86/1.47      inference(instantiation,[status(thm)],[c_0]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_15287,plain,
% 7.86/1.47      ( ~ r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))
% 7.86/1.47      | k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) = k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) ),
% 7.86/1.47      inference(instantiation,[status(thm)],[c_9239]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_772,plain,
% 7.86/1.47      ( ~ v3_pre_topc(X0,X1) | v3_pre_topc(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.86/1.47      theory(equality) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1489,plain,
% 7.86/1.47      ( ~ v3_pre_topc(X0,X1)
% 7.86/1.47      | v3_pre_topc(sK2,sK0)
% 7.86/1.47      | sK0 != X1
% 7.86/1.47      | sK2 != X0 ),
% 7.86/1.47      inference(instantiation,[status(thm)],[c_772]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_16755,plain,
% 7.86/1.47      ( ~ v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),X0)
% 7.86/1.47      | v3_pre_topc(sK2,sK0)
% 7.86/1.47      | sK0 != X0
% 7.86/1.47      | sK2 != k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) ),
% 7.86/1.47      inference(instantiation,[status(thm)],[c_1489]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_16756,plain,
% 7.86/1.47      ( sK0 != X0
% 7.86/1.47      | sK2 != k1_tops_1(sK0,k2_pre_topc(sK0,sK2))
% 7.86/1.47      | v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),X0) != iProver_top
% 7.86/1.47      | v3_pre_topc(sK2,sK0) = iProver_top ),
% 7.86/1.47      inference(predicate_to_equality,[status(thm)],[c_16755]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_16758,plain,
% 7.86/1.47      ( sK0 != sK0
% 7.86/1.47      | sK2 != k1_tops_1(sK0,k2_pre_topc(sK0,sK2))
% 7.86/1.47      | v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK0) != iProver_top
% 7.86/1.47      | v3_pre_topc(sK2,sK0) = iProver_top ),
% 7.86/1.47      inference(instantiation,[status(thm)],[c_16756]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_17677,plain,
% 7.86/1.47      ( r1_tarski(k1_tops_1(sK0,sK2),sK2) = iProver_top ),
% 7.86/1.47      inference(global_propositional_subsumption,
% 7.86/1.47                [status(thm)],
% 7.86/1.47                [c_3935,c_28,c_20,c_29,c_32,c_70,c_74,c_1504,c_1505,
% 7.86/1.47                 c_1523,c_1540,c_1655,c_1665,c_1687,c_1825,c_1970,c_2033,
% 7.86/1.47                 c_2067,c_2205,c_2267,c_2277,c_2297,c_2304,c_2594,c_2686,
% 7.86/1.47                 c_3138,c_3489,c_3683,c_3874,c_3938,c_4244,c_4248,c_4421,
% 7.86/1.47                 c_4423,c_7780,c_9099,c_9245,c_12892,c_12895,c_15287,
% 7.86/1.47                 c_16758]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_17681,plain,
% 7.86/1.47      ( k1_tops_1(sK0,sK2) = sK2
% 7.86/1.47      | r1_tarski(sK2,k1_tops_1(sK0,sK2)) != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_17677,c_1420]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_17684,plain,
% 7.86/1.47      ( k1_tops_1(sK0,sK2) = sK2 ),
% 7.86/1.47      inference(global_propositional_subsumption,
% 7.86/1.47                [status(thm)],
% 7.86/1.47                [c_17681,c_28,c_20,c_29,c_32,c_70,c_74,c_1504,c_1505,
% 7.86/1.47                 c_1523,c_1540,c_1655,c_1665,c_1687,c_1825,c_2033,c_2067,
% 7.86/1.47                 c_2205,c_2267,c_2277,c_2297,c_2304,c_2594,c_2686,c_3138,
% 7.86/1.47                 c_3489,c_3683,c_3874,c_3938,c_4248,c_4421,c_4423,c_7780,
% 7.86/1.47                 c_9099,c_9245,c_12892,c_12895,c_15287,c_16758]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_5,plain,
% 7.86/1.47      ( v4_tops_1(X0,X1)
% 7.86/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.86/1.47      | ~ r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
% 7.86/1.47      | ~ r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
% 7.86/1.47      | ~ l1_pre_topc(X1) ),
% 7.86/1.47      inference(cnf_transformation,[],[f41]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_584,plain,
% 7.86/1.47      ( v4_tops_1(X0,X1)
% 7.86/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.86/1.47      | ~ r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
% 7.86/1.47      | ~ r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
% 7.86/1.47      | sK0 != X1 ),
% 7.86/1.47      inference(resolution_lifted,[status(thm)],[c_5,c_23]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_585,plain,
% 7.86/1.47      ( v4_tops_1(X0,sK0)
% 7.86/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.86/1.47      | ~ r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,X0)))
% 7.86/1.47      | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X0) ),
% 7.86/1.47      inference(unflattening,[status(thm)],[c_584]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1389,plain,
% 7.86/1.47      ( v4_tops_1(X0,sK0) = iProver_top
% 7.86/1.47      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.86/1.47      | r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,X0))) != iProver_top
% 7.86/1.47      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X0) != iProver_top ),
% 7.86/1.47      inference(predicate_to_equality,[status(thm)],[c_585]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_3873,plain,
% 7.86/1.47      ( k1_tops_1(sK1,sK3) = sK3
% 7.86/1.47      | v4_tops_1(sK2,sK0) = iProver_top
% 7.86/1.47      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.86/1.47      | r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) != iProver_top
% 7.86/1.47      | r1_tarski(sK2,sK2) != iProver_top ),
% 7.86/1.47      inference(superposition,[status(thm)],[c_2817,c_1389]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1588,plain,
% 7.86/1.47      ( v4_tops_1(sK2,sK0)
% 7.86/1.47      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.86/1.47      | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK2)
% 7.86/1.47      | ~ r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) ),
% 7.86/1.47      inference(instantiation,[status(thm)],[c_585]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1589,plain,
% 7.86/1.47      ( v4_tops_1(sK2,sK0) = iProver_top
% 7.86/1.47      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.86/1.47      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK2) != iProver_top
% 7.86/1.47      | r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) != iProver_top ),
% 7.86/1.47      inference(predicate_to_equality,[status(thm)],[c_1588]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1681,plain,
% 7.86/1.47      ( ~ r1_tarski(X0,X1)
% 7.86/1.47      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK2)
% 7.86/1.47      | k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) != X0
% 7.86/1.47      | sK2 != X1 ),
% 7.86/1.47      inference(instantiation,[status(thm)],[c_764]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_2122,plain,
% 7.86/1.47      ( ~ r1_tarski(X0,sK2)
% 7.86/1.47      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK2)
% 7.86/1.47      | k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) != X0
% 7.86/1.47      | sK2 != sK2 ),
% 7.86/1.47      inference(instantiation,[status(thm)],[c_1681]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_2963,plain,
% 7.86/1.47      ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK2)
% 7.86/1.47      | ~ r1_tarski(sK2,sK2)
% 7.86/1.47      | k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) != sK2
% 7.86/1.47      | sK2 != sK2 ),
% 7.86/1.47      inference(instantiation,[status(thm)],[c_2122]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_2964,plain,
% 7.86/1.47      ( k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) != sK2
% 7.86/1.47      | sK2 != sK2
% 7.86/1.47      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK2) = iProver_top
% 7.86/1.47      | r1_tarski(sK2,sK2) != iProver_top ),
% 7.86/1.47      inference(predicate_to_equality,[status(thm)],[c_2963]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_13317,plain,
% 7.86/1.47      ( r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) != iProver_top
% 7.86/1.47      | v4_tops_1(sK2,sK0) = iProver_top ),
% 7.86/1.47      inference(global_propositional_subsumption,
% 7.86/1.47                [status(thm)],
% 7.86/1.47                [c_3873,c_28,c_29,c_32,c_1589,c_1970,c_2033,c_2205,
% 7.86/1.47                 c_2277,c_2297,c_2304,c_2686,c_2964,c_3489,c_3683,c_4248,
% 7.86/1.47                 c_4421,c_4423,c_7780,c_9099]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_13318,plain,
% 7.86/1.47      ( v4_tops_1(sK2,sK0) = iProver_top
% 7.86/1.47      | r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) != iProver_top ),
% 7.86/1.47      inference(renaming,[status(thm)],[c_13317]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_17706,plain,
% 7.86/1.47      ( v4_tops_1(sK2,sK0) = iProver_top
% 7.86/1.47      | r1_tarski(sK2,k2_pre_topc(sK0,sK2)) != iProver_top ),
% 7.86/1.47      inference(demodulation,[status(thm)],[c_17684,c_13318]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1723,plain,
% 7.86/1.47      ( ~ v3_pre_topc(sK3,sK1)
% 7.86/1.47      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.86/1.47      | ~ sP4_iProver_split
% 7.86/1.47      | k1_tops_1(sK1,sK3) = sK3 ),
% 7.86/1.47      inference(instantiation,[status(thm)],[c_759]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1724,plain,
% 7.86/1.47      ( k1_tops_1(sK1,sK3) = sK3
% 7.86/1.47      | v3_pre_topc(sK3,sK1) != iProver_top
% 7.86/1.47      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 7.86/1.47      | sP4_iProver_split != iProver_top ),
% 7.86/1.47      inference(predicate_to_equality,[status(thm)],[c_1723]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_882,plain,
% 7.86/1.47      ( k1_tops_1(sK0,X0) != X0
% 7.86/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.86/1.47      | v3_pre_topc(X0,sK0) ),
% 7.86/1.47      inference(global_propositional_subsumption,
% 7.86/1.47                [status(thm)],
% 7.86/1.47                [c_753,c_754,c_752]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_883,plain,
% 7.86/1.47      ( v3_pre_topc(X0,sK0)
% 7.86/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.86/1.47      | k1_tops_1(sK0,X0) != X0 ),
% 7.86/1.47      inference(renaming,[status(thm)],[c_882]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_889,plain,
% 7.86/1.47      ( k1_tops_1(sK0,X0) != X0
% 7.86/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.86/1.47      | v3_pre_topc(X0,sK0) ),
% 7.86/1.47      inference(global_propositional_subsumption,
% 7.86/1.47                [status(thm)],
% 7.86/1.47                [c_753,c_883]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_890,plain,
% 7.86/1.47      ( v3_pre_topc(X0,sK0)
% 7.86/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.86/1.47      | k1_tops_1(sK0,X0) != X0 ),
% 7.86/1.47      inference(renaming,[status(thm)],[c_889]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1565,plain,
% 7.86/1.47      ( v3_pre_topc(sK2,sK0)
% 7.86/1.47      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.86/1.47      | k1_tops_1(sK0,sK2) != sK2 ),
% 7.86/1.47      inference(instantiation,[status(thm)],[c_890]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1566,plain,
% 7.86/1.47      ( k1_tops_1(sK0,sK2) != sK2
% 7.86/1.47      | v3_pre_topc(sK2,sK0) = iProver_top
% 7.86/1.47      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.86/1.47      inference(predicate_to_equality,[status(thm)],[c_1565]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_602,plain,
% 7.86/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.86/1.47      | r1_tarski(X0,k2_pre_topc(X1,X0))
% 7.86/1.47      | sK0 != X1 ),
% 7.86/1.47      inference(resolution_lifted,[status(thm)],[c_4,c_23]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_603,plain,
% 7.86/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.86/1.47      | r1_tarski(X0,k2_pre_topc(sK0,X0)) ),
% 7.86/1.47      inference(unflattening,[status(thm)],[c_602]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1530,plain,
% 7.86/1.47      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.86/1.47      | r1_tarski(sK2,k2_pre_topc(sK0,sK2)) ),
% 7.86/1.47      inference(instantiation,[status(thm)],[c_603]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_1531,plain,
% 7.86/1.47      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.86/1.47      | r1_tarski(sK2,k2_pre_topc(sK0,sK2)) = iProver_top ),
% 7.86/1.47      inference(predicate_to_equality,[status(thm)],[c_1530]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_14,negated_conjecture,
% 7.86/1.47      ( ~ v3_pre_topc(sK2,sK0)
% 7.86/1.47      | ~ v6_tops_1(sK3,sK1)
% 7.86/1.47      | ~ v4_tops_1(sK2,sK0) ),
% 7.86/1.47      inference(cnf_transformation,[],[f58]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_35,plain,
% 7.86/1.47      ( v3_pre_topc(sK2,sK0) != iProver_top
% 7.86/1.47      | v6_tops_1(sK3,sK1) != iProver_top
% 7.86/1.47      | v4_tops_1(sK2,sK0) != iProver_top ),
% 7.86/1.47      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_15,negated_conjecture,
% 7.86/1.47      ( ~ v3_pre_topc(sK2,sK0)
% 7.86/1.47      | v4_tops_1(sK3,sK1)
% 7.86/1.47      | ~ v4_tops_1(sK2,sK0) ),
% 7.86/1.47      inference(cnf_transformation,[],[f57]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_34,plain,
% 7.86/1.47      ( v3_pre_topc(sK2,sK0) != iProver_top
% 7.86/1.47      | v4_tops_1(sK3,sK1) = iProver_top
% 7.86/1.47      | v4_tops_1(sK2,sK0) != iProver_top ),
% 7.86/1.47      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_16,negated_conjecture,
% 7.86/1.47      ( v3_pre_topc(sK3,sK1)
% 7.86/1.47      | ~ v3_pre_topc(sK2,sK0)
% 7.86/1.47      | ~ v4_tops_1(sK2,sK0) ),
% 7.86/1.47      inference(cnf_transformation,[],[f56]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(c_33,plain,
% 7.86/1.47      ( v3_pre_topc(sK3,sK1) = iProver_top
% 7.86/1.47      | v3_pre_topc(sK2,sK0) != iProver_top
% 7.86/1.47      | v4_tops_1(sK2,sK0) != iProver_top ),
% 7.86/1.47      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.86/1.47  
% 7.86/1.47  cnf(contradiction,plain,
% 7.86/1.47      ( $false ),
% 7.86/1.47      inference(minisat,
% 7.86/1.47                [status(thm)],
% 7.86/1.47                [c_17706,c_17684,c_15287,c_9245,c_4248,c_2686,c_2067,
% 7.86/1.47                 c_1825,c_1724,c_1687,c_1665,c_1655,c_1566,c_1540,c_1531,
% 7.86/1.47                 c_1523,c_1505,c_1504,c_1497,c_815,c_35,c_34,c_33,c_29,
% 7.86/1.48                 c_20,c_28]) ).
% 7.86/1.48  
% 7.86/1.48  
% 7.86/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.86/1.48  
% 7.86/1.48  ------                               Statistics
% 7.86/1.48  
% 7.86/1.48  ------ General
% 7.86/1.48  
% 7.86/1.48  abstr_ref_over_cycles:                  0
% 7.86/1.48  abstr_ref_under_cycles:                 0
% 7.86/1.48  gc_basic_clause_elim:                   0
% 7.86/1.48  forced_gc_time:                         0
% 7.86/1.48  parsing_time:                           0.006
% 7.86/1.48  unif_index_cands_time:                  0.
% 7.86/1.48  unif_index_add_time:                    0.
% 7.86/1.48  orderings_time:                         0.
% 7.86/1.48  out_proof_time:                         0.025
% 7.86/1.48  total_time:                             0.746
% 7.86/1.48  num_of_symbols:                         51
% 7.86/1.48  num_of_terms:                           16332
% 7.86/1.48  
% 7.86/1.48  ------ Preprocessing
% 7.86/1.48  
% 7.86/1.48  num_of_splits:                          8
% 7.86/1.48  num_of_split_atoms:                     5
% 7.86/1.48  num_of_reused_defs:                     3
% 7.86/1.48  num_eq_ax_congr_red:                    2
% 7.86/1.48  num_of_sem_filtered_clauses:            5
% 7.86/1.48  num_of_subtypes:                        0
% 7.86/1.48  monotx_restored_types:                  0
% 7.86/1.48  sat_num_of_epr_types:                   0
% 7.86/1.48  sat_num_of_non_cyclic_types:            0
% 7.86/1.48  sat_guarded_non_collapsed_types:        0
% 7.86/1.48  num_pure_diseq_elim:                    0
% 7.86/1.48  simp_replaced_by:                       0
% 7.86/1.48  res_preprocessed:                       117
% 7.86/1.48  prep_upred:                             0
% 7.86/1.48  prep_unflattend:                        24
% 7.86/1.48  smt_new_axioms:                         0
% 7.86/1.48  pred_elim_cands:                        7
% 7.86/1.48  pred_elim:                              2
% 7.86/1.48  pred_elim_cl:                           -8
% 7.86/1.48  pred_elim_cycles:                       3
% 7.86/1.48  merged_defs:                            0
% 7.86/1.48  merged_defs_ncl:                        0
% 7.86/1.48  bin_hyper_res:                          0
% 7.86/1.48  prep_cycles:                            3
% 7.86/1.48  pred_elim_time:                         0.006
% 7.86/1.48  splitting_time:                         0.
% 7.86/1.48  sem_filter_time:                        0.
% 7.86/1.48  monotx_time:                            0.
% 7.86/1.48  subtype_inf_time:                       0.
% 7.86/1.48  
% 7.86/1.48  ------ Problem properties
% 7.86/1.48  
% 7.86/1.48  clauses:                                40
% 7.86/1.48  conjectures:                            8
% 7.86/1.48  epr:                                    12
% 7.86/1.48  horn:                                   34
% 7.86/1.48  ground:                                 12
% 7.86/1.48  unary:                                  3
% 7.86/1.48  binary:                                 17
% 7.86/1.48  lits:                                   105
% 7.86/1.48  lits_eq:                                11
% 7.86/1.48  fd_pure:                                0
% 7.86/1.48  fd_pseudo:                              0
% 7.86/1.48  fd_cond:                                0
% 7.86/1.48  fd_pseudo_cond:                         1
% 7.86/1.48  ac_symbols:                             0
% 7.86/1.48  
% 7.86/1.48  ------ Propositional Solver
% 7.86/1.48  
% 7.86/1.48  prop_solver_calls:                      30
% 7.86/1.48  prop_fast_solver_calls:                 2020
% 7.86/1.48  smt_solver_calls:                       0
% 7.86/1.48  smt_fast_solver_calls:                  0
% 7.86/1.48  prop_num_of_clauses:                    8845
% 7.86/1.48  prop_preprocess_simplified:             14907
% 7.86/1.48  prop_fo_subsumed:                       71
% 7.86/1.48  prop_solver_time:                       0.
% 7.86/1.48  smt_solver_time:                        0.
% 7.86/1.48  smt_fast_solver_time:                   0.
% 7.86/1.48  prop_fast_solver_time:                  0.
% 7.86/1.48  prop_unsat_core_time:                   0.001
% 7.86/1.48  
% 7.86/1.48  ------ QBF
% 7.86/1.48  
% 7.86/1.48  qbf_q_res:                              0
% 7.86/1.48  qbf_num_tautologies:                    0
% 7.86/1.48  qbf_prep_cycles:                        0
% 7.86/1.48  
% 7.86/1.48  ------ BMC1
% 7.86/1.48  
% 7.86/1.48  bmc1_current_bound:                     -1
% 7.86/1.48  bmc1_last_solved_bound:                 -1
% 7.86/1.48  bmc1_unsat_core_size:                   -1
% 7.86/1.48  bmc1_unsat_core_parents_size:           -1
% 7.86/1.48  bmc1_merge_next_fun:                    0
% 7.86/1.48  bmc1_unsat_core_clauses_time:           0.
% 7.86/1.48  
% 7.86/1.48  ------ Instantiation
% 7.86/1.48  
% 7.86/1.48  inst_num_of_clauses:                    2597
% 7.86/1.48  inst_num_in_passive:                    730
% 7.86/1.48  inst_num_in_active:                     1512
% 7.86/1.48  inst_num_in_unprocessed:                355
% 7.86/1.48  inst_num_of_loops:                      1660
% 7.86/1.48  inst_num_of_learning_restarts:          0
% 7.86/1.48  inst_num_moves_active_passive:          142
% 7.86/1.48  inst_lit_activity:                      0
% 7.86/1.48  inst_lit_activity_moves:                0
% 7.86/1.48  inst_num_tautologies:                   0
% 7.86/1.48  inst_num_prop_implied:                  0
% 7.86/1.48  inst_num_existing_simplified:           0
% 7.86/1.48  inst_num_eq_res_simplified:             0
% 7.86/1.48  inst_num_child_elim:                    0
% 7.86/1.48  inst_num_of_dismatching_blockings:      751
% 7.86/1.48  inst_num_of_non_proper_insts:           3460
% 7.86/1.48  inst_num_of_duplicates:                 0
% 7.86/1.48  inst_inst_num_from_inst_to_res:         0
% 7.86/1.48  inst_dismatching_checking_time:         0.
% 7.86/1.48  
% 7.86/1.48  ------ Resolution
% 7.86/1.48  
% 7.86/1.48  res_num_of_clauses:                     0
% 7.86/1.48  res_num_in_passive:                     0
% 7.86/1.48  res_num_in_active:                      0
% 7.86/1.48  res_num_of_loops:                       120
% 7.86/1.48  res_forward_subset_subsumed:            250
% 7.86/1.48  res_backward_subset_subsumed:           0
% 7.86/1.48  res_forward_subsumed:                   0
% 7.86/1.48  res_backward_subsumed:                  0
% 7.86/1.48  res_forward_subsumption_resolution:     0
% 7.86/1.48  res_backward_subsumption_resolution:    0
% 7.86/1.48  res_clause_to_clause_subsumption:       4378
% 7.86/1.48  res_orphan_elimination:                 0
% 7.86/1.48  res_tautology_del:                      328
% 7.86/1.48  res_num_eq_res_simplified:              0
% 7.86/1.48  res_num_sel_changes:                    0
% 7.86/1.48  res_moves_from_active_to_pass:          0
% 7.86/1.48  
% 7.86/1.48  ------ Superposition
% 7.86/1.48  
% 7.86/1.48  sup_time_total:                         0.
% 7.86/1.48  sup_time_generating:                    0.
% 7.86/1.48  sup_time_sim_full:                      0.
% 7.86/1.48  sup_time_sim_immed:                     0.
% 7.86/1.48  
% 7.86/1.48  sup_num_of_clauses:                     668
% 7.86/1.48  sup_num_in_active:                      280
% 7.86/1.48  sup_num_in_passive:                     388
% 7.86/1.48  sup_num_of_loops:                       331
% 7.86/1.48  sup_fw_superposition:                   610
% 7.86/1.48  sup_bw_superposition:                   523
% 7.86/1.48  sup_immediate_simplified:               643
% 7.86/1.48  sup_given_eliminated:                   2
% 7.86/1.48  comparisons_done:                       0
% 7.86/1.48  comparisons_avoided:                    36
% 7.86/1.48  
% 7.86/1.48  ------ Simplifications
% 7.86/1.48  
% 7.86/1.48  
% 7.86/1.48  sim_fw_subset_subsumed:                 38
% 7.86/1.48  sim_bw_subset_subsumed:                 55
% 7.86/1.48  sim_fw_subsumed:                        276
% 7.86/1.48  sim_bw_subsumed:                        6
% 7.86/1.48  sim_fw_subsumption_res:                 0
% 7.86/1.48  sim_bw_subsumption_res:                 0
% 7.86/1.48  sim_tautology_del:                      5
% 7.86/1.48  sim_eq_tautology_del:                   38
% 7.86/1.48  sim_eq_res_simp:                        0
% 7.86/1.48  sim_fw_demodulated:                     332
% 7.86/1.48  sim_bw_demodulated:                     44
% 7.86/1.48  sim_light_normalised:                   217
% 7.86/1.48  sim_joinable_taut:                      0
% 7.86/1.48  sim_joinable_simp:                      0
% 7.86/1.48  sim_ac_normalised:                      0
% 7.86/1.48  sim_smt_subsumption:                    0
% 7.86/1.48  
%------------------------------------------------------------------------------
