%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1284+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:20 EST 2020

% Result     : Theorem 3.43s
% Output     : CNFRefutation 3.43s
% Verified   : 
% Statistics : Number of formulae       :  233 (27457 expanded)
%              Number of clauses        :  175 (7683 expanded)
%              Number of leaves         :   15 (9047 expanded)
%              Depth                    :   43
%              Number of atoms          :  848 (239442 expanded)
%              Number of equality atoms :  363 (12665 expanded)
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

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_tops_1(X1,X0)
              | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1 )
            & ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
              | ~ v5_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
      | ~ v5_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f49,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f53,plain,
    ( v5_tops_1(sK2,sK0)
    | v4_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f52,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f33])).

fof(f8,axiom,(
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

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f50,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

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

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f16,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f48,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_tops_1(X1,X0)
          <=> ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_tops_1(X1,X0)
          <=> ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

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
    inference(nnf_transformation,[],[f11])).

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

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
      | ~ v4_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f56,plain,
    ( ~ v4_tops_1(sK2,sK0)
    | ~ v4_pre_topc(sK2,sK0)
    | v4_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f55,plain,
    ( v5_tops_1(sK2,sK0)
    | ~ v5_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v5_tops_1(X1,X0)
      | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v4_tops_1(X1,X0)
      | ~ r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
      | ~ r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f37,plain,(
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

fof(f47,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

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

cnf(c_7,plain,
    ( ~ v5_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k1_tops_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_23,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_502,plain,
    ( ~ v5_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,k1_tops_1(X1,X0)) = X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_23])).

cnf(c_503,plain,
    ( ~ v5_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k1_tops_1(sK0,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_502])).

cnf(c_1180,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,X0)) = X0
    | v5_tops_1(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_503])).

cnf(c_2371,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = sK2
    | v5_tops_1(sK2,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1196,c_1180])).

cnf(c_2430,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = sK2
    | v4_tops_1(sK3,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1199,c_2371])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_490,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_23])).

cnf(c_491,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_490])).

cnf(c_1181,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_491])).

cnf(c_19,negated_conjecture,
    ( v4_pre_topc(sK3,sK1)
    | v5_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1198,plain,
    ( v4_pre_topc(sK3,sK1) = iProver_top
    | v5_tops_1(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1197,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_13,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_22,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_310,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,X0) = X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_22])).

cnf(c_311,plain,
    ( ~ v4_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_310])).

cnf(c_1193,plain,
    ( k2_pre_topc(sK1,X0) = X0
    | v4_pre_topc(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_311])).

cnf(c_2224,plain,
    ( k2_pre_topc(sK1,sK3) = sK3
    | v4_pre_topc(sK3,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1197,c_1193])).

cnf(c_2290,plain,
    ( k2_pre_topc(sK1,sK3) = sK3
    | v5_tops_1(sK2,sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1198,c_2224])).

cnf(c_2664,plain,
    ( k2_pre_topc(sK1,sK3) = sK3
    | k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_2290,c_2371])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k2_pre_topc(X1,X0),k2_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_460,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k2_pre_topc(X1,X0),k2_pre_topc(X1,X2))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_23])).

cnf(c_461,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,X1)
    | r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,X1)) ),
    inference(unflattening,[status(thm)],[c_460])).

cnf(c_1183,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_461])).

cnf(c_3587,plain,
    ( k2_pre_topc(sK1,sK3) = sK3
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK2),X0) != iProver_top
    | r1_tarski(sK2,k2_pre_topc(sK0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2664,c_1183])).

cnf(c_28,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1441,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_491])).

cnf(c_1442,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1441])).

cnf(c_6921,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | k2_pre_topc(sK1,sK3) = sK3
    | r1_tarski(k1_tops_1(sK0,sK2),X0) != iProver_top
    | r1_tarski(sK2,k2_pre_topc(sK0,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3587,c_28,c_1442])).

cnf(c_6922,plain,
    ( k2_pre_topc(sK1,sK3) = sK3
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK2),X0) != iProver_top
    | r1_tarski(sK2,k2_pre_topc(sK0,X0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_6921])).

cnf(c_6932,plain,
    ( k2_pre_topc(sK1,sK3) = sK3
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,X0)) != iProver_top
    | r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1181,c_6922])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1685,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1688,plain,
    ( r1_tarski(sK2,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1685])).

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

cnf(c_2874,plain,
    ( k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1183,c_1205])).

cnf(c_3586,plain,
    ( k2_pre_topc(sK1,sK3) = sK3
    | k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = k2_pre_topc(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,X0),sK2) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK2),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2664,c_2874])).

cnf(c_6058,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = k2_pre_topc(sK0,X0)
    | k2_pre_topc(sK1,sK3) = sK3
    | r1_tarski(k2_pre_topc(sK0,X0),sK2) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK2),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3586,c_28,c_1442])).

cnf(c_6059,plain,
    ( k2_pre_topc(sK1,sK3) = sK3
    | k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = k2_pre_topc(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,X0),sK2) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK2),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6058])).

cnf(c_6069,plain,
    ( k2_pre_topc(sK1,sK3) = sK3
    | k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = k2_pre_topc(sK0,sK2)
    | r1_tarski(k2_pre_topc(sK0,sK2),sK2) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK2),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1196,c_6059])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_478,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_23])).

cnf(c_479,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,X0),X0) ),
    inference(unflattening,[status(thm)],[c_478])).

cnf(c_1447,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    inference(instantiation,[status(thm)],[c_479])).

cnf(c_3585,plain,
    ( k2_pre_topc(sK1,sK3) = sK3
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k1_tops_1(sK0,sK2)) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,X0),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2664,c_1183])).

cnf(c_5213,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | k2_pre_topc(sK1,sK3) = sK3
    | r1_tarski(X0,k1_tops_1(sK0,sK2)) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,X0),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3585,c_28,c_1442])).

cnf(c_5214,plain,
    ( k2_pre_topc(sK1,sK3) = sK3
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k1_tops_1(sK0,sK2)) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,X0),sK2) = iProver_top ),
    inference(renaming,[status(thm)],[c_5213])).

cnf(c_5223,plain,
    ( k2_pre_topc(sK1,sK3) = sK3
    | r1_tarski(k2_pre_topc(sK0,sK2),sK2) = iProver_top
    | r1_tarski(sK2,k1_tops_1(sK0,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1196,c_5214])).

cnf(c_653,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1701,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_653])).

cnf(c_445,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,X0) = X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_23])).

cnf(c_446,plain,
    ( ~ v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_445])).

cnf(c_1184,plain,
    ( k2_pre_topc(sK0,X0) = X0
    | v4_pre_topc(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_446])).

cnf(c_1983,plain,
    ( k2_pre_topc(sK0,sK2) = sK2
    | v4_pre_topc(sK2,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1196,c_1184])).

cnf(c_9,plain,
    ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_24,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_264,plain,
    ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_24])).

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

cnf(c_1892,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,k1_tops_1(sK0,X0)),sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1181,c_1195])).

cnf(c_3592,plain,
    ( k2_pre_topc(sK1,sK3) = sK3
    | v4_pre_topc(sK2,sK0) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2664,c_1892])).

cnf(c_655,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1833,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_pre_topc(sK0,sK2),sK2)
    | k2_pre_topc(sK0,sK2) != X0
    | sK2 != X1 ),
    inference(instantiation,[status(thm)],[c_655])).

cnf(c_2672,plain,
    ( ~ r1_tarski(X0,sK2)
    | r1_tarski(k2_pre_topc(sK0,sK2),sK2)
    | k2_pre_topc(sK0,sK2) != X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1833])).

cnf(c_3830,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK2),sK2)
    | ~ r1_tarski(sK2,sK2)
    | k2_pre_topc(sK0,sK2) != sK2
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_2672])).

cnf(c_3831,plain,
    ( k2_pre_topc(sK0,sK2) != sK2
    | sK2 != sK2
    | r1_tarski(k2_pre_topc(sK0,sK2),sK2) = iProver_top
    | r1_tarski(sK2,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3830])).

cnf(c_5244,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK2),sK2) = iProver_top
    | k2_pre_topc(sK1,sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5223,c_28,c_1688,c_1701,c_1983,c_3592,c_3831])).

cnf(c_5245,plain,
    ( k2_pre_topc(sK1,sK3) = sK3
    | r1_tarski(k2_pre_topc(sK0,sK2),sK2) = iProver_top ),
    inference(renaming,[status(thm)],[c_5244])).

cnf(c_5246,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK2),sK2)
    | k2_pre_topc(sK1,sK3) = sK3 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5245])).

cnf(c_6089,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,sK2),sK2)
    | ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | k2_pre_topc(sK1,sK3) = sK3
    | k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = k2_pre_topc(sK0,sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6069])).

cnf(c_6167,plain,
    ( k2_pre_topc(sK1,sK3) = sK3
    | k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = k2_pre_topc(sK0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6069,c_28,c_1448,c_5245])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_tops_1(X0,X1)
    | r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_547,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_tops_1(X0,X1)
    | r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_23])).

cnf(c_548,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_tops_1(X0,sK0)
    | r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,X0))) ),
    inference(unflattening,[status(thm)],[c_547])).

cnf(c_1177,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v4_tops_1(X0,sK0) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_548])).

cnf(c_6185,plain,
    ( k2_pre_topc(sK1,sK3) = sK3
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v4_tops_1(sK2,sK0) != iProver_top
    | r1_tarski(sK2,k2_pre_topc(sK0,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6167,c_1177])).

cnf(c_16,negated_conjecture,
    ( v4_pre_topc(sK3,sK1)
    | ~ v4_pre_topc(sK2,sK0)
    | ~ v4_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_33,plain,
    ( v4_pre_topc(sK3,sK1) = iProver_top
    | v4_pre_topc(sK2,sK0) != iProver_top
    | v4_tops_1(sK2,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_6573,plain,
    ( v4_tops_1(sK2,sK0) != iProver_top
    | k2_pre_topc(sK1,sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6185,c_28,c_33,c_2224,c_3592])).

cnf(c_6574,plain,
    ( k2_pre_topc(sK1,sK3) = sK3
    | v4_tops_1(sK2,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6573])).

cnf(c_355,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_22])).

cnf(c_356,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k1_tops_1(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_355])).

cnf(c_1190,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k1_tops_1(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_356])).

cnf(c_5250,plain,
    ( k2_pre_topc(sK1,sK3) = sK3
    | k2_pre_topc(sK0,sK2) = sK2
    | r1_tarski(sK2,k2_pre_topc(sK0,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5245,c_1205])).

cnf(c_5296,plain,
    ( k2_pre_topc(sK0,sK2) = sK2
    | k2_pre_topc(sK1,sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5250,c_28,c_1983,c_3592])).

cnf(c_5297,plain,
    ( k2_pre_topc(sK1,sK3) = sK3
    | k2_pre_topc(sK0,sK2) = sK2 ),
    inference(renaming,[status(thm)],[c_5296])).

cnf(c_325,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k2_pre_topc(X1,X0),k2_pre_topc(X1,X2))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_22])).

cnf(c_326,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X0,X1)
    | r1_tarski(k2_pre_topc(sK1,X0),k2_pre_topc(sK1,X1)) ),
    inference(unflattening,[status(thm)],[c_325])).

cnf(c_1192,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_pre_topc(sK1,X0),k2_pre_topc(sK1,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_326])).

cnf(c_5308,plain,
    ( k2_pre_topc(sK0,sK2) = sK2
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(k2_pre_topc(sK1,X0),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_5297,c_1192])).

cnf(c_29,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_6663,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | k2_pre_topc(sK0,sK2) = sK2
    | r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(k2_pre_topc(sK1,X0),sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5308,c_29])).

cnf(c_6664,plain,
    ( k2_pre_topc(sK0,sK2) = sK2
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(k2_pre_topc(sK1,X0),sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_6663])).

cnf(c_6674,plain,
    ( k2_pre_topc(sK0,sK2) = sK2
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(k2_pre_topc(sK1,k1_tops_1(sK1,X0)),sK3) = iProver_top
    | r1_tarski(k1_tops_1(sK1,X0),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1190,c_6664])).

cnf(c_412,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_tops_1(X0,X1)
    | r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_22])).

cnf(c_413,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v4_tops_1(X0,sK1)
    | r1_tarski(X0,k2_pre_topc(sK1,k1_tops_1(sK1,X0))) ),
    inference(unflattening,[status(thm)],[c_412])).

cnf(c_1186,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v4_tops_1(X0,sK1) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK1,k1_tops_1(sK1,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_413])).

cnf(c_2776,plain,
    ( k2_pre_topc(sK1,k1_tops_1(sK1,X0)) = X0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v4_tops_1(X0,sK1) != iProver_top
    | r1_tarski(k2_pre_topc(sK1,k1_tops_1(sK1,X0)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1186,c_1205])).

cnf(c_6752,plain,
    ( k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) = sK3
    | k2_pre_topc(sK0,sK2) = sK2
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v4_tops_1(sK3,sK1) != iProver_top
    | r1_tarski(k1_tops_1(sK1,sK3),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6674,c_2776])).

cnf(c_343,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_22])).

cnf(c_344,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(k1_tops_1(sK1,X0),X0) ),
    inference(unflattening,[status(thm)],[c_343])).

cnf(c_1444,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(k1_tops_1(sK1,sK3),sK3) ),
    inference(instantiation,[status(thm)],[c_344])).

cnf(c_1445,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(k1_tops_1(sK1,sK3),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1444])).

cnf(c_7185,plain,
    ( v4_tops_1(sK3,sK1) != iProver_top
    | k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) = sK3
    | k2_pre_topc(sK0,sK2) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6752,c_29,c_1445])).

cnf(c_7186,plain,
    ( k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) = sK3
    | k2_pre_topc(sK0,sK2) = sK2
    | v4_tops_1(sK3,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_7185])).

cnf(c_7192,plain,
    ( k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) = sK3
    | k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = sK2
    | k2_pre_topc(sK0,sK2) = sK2 ),
    inference(superposition,[status(thm)],[c_2430,c_7186])).

cnf(c_17,negated_conjecture,
    ( ~ v5_tops_1(sK3,sK1)
    | v5_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_32,plain,
    ( v5_tops_1(sK3,sK1) != iProver_top
    | v5_tops_1(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_6,plain,
    ( v5_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k1_tops_1(X1,X0)) != X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_382,plain,
    ( v5_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,k1_tops_1(X1,X0)) != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_22])).

cnf(c_383,plain,
    ( v5_tops_1(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,k1_tops_1(sK1,X0)) != X0 ),
    inference(unflattening,[status(thm)],[c_382])).

cnf(c_1453,plain,
    ( v5_tops_1(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) != sK3 ),
    inference(instantiation,[status(thm)],[c_383])).

cnf(c_1454,plain,
    ( k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) != sK3
    | v5_tops_1(sK3,sK1) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1453])).

cnf(c_7193,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = sK2
    | k2_pre_topc(sK0,sK2) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7192,c_29,c_32,c_1445,c_1454,c_2371,c_2430,c_6752])).

cnf(c_517,plain,
    ( v5_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,k1_tops_1(X1,X0)) != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_23])).

cnf(c_518,plain,
    ( v5_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k1_tops_1(sK0,X0)) != X0 ),
    inference(unflattening,[status(thm)],[c_517])).

cnf(c_1179,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,X0)) != X0
    | v5_tops_1(X0,sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_518])).

cnf(c_7209,plain,
    ( k2_pre_topc(sK0,sK2) = sK2
    | v5_tops_1(sK2,sK0) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7193,c_1179])).

cnf(c_7208,plain,
    ( k2_pre_topc(sK0,sK2) = sK2
    | v4_pre_topc(sK2,sK0) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7193,c_1892])).

cnf(c_7368,plain,
    ( k2_pre_topc(sK0,sK2) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7209,c_28,c_1983,c_7208])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v4_tops_1(X0,X1)
    | ~ r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
    | ~ r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_562,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v4_tops_1(X0,X1)
    | ~ r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
    | ~ r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_23])).

cnf(c_563,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_tops_1(X0,sK0)
    | ~ r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,X0)))
    | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X0) ),
    inference(unflattening,[status(thm)],[c_562])).

cnf(c_1176,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v4_tops_1(X0,sK0) = iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,X0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_563])).

cnf(c_7440,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v4_tops_1(sK2,sK0) = iProver_top
    | r1_tarski(k1_tops_1(sK0,sK2),sK2) != iProver_top
    | r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7368,c_1176])).

cnf(c_1448,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK2),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1447])).

cnf(c_8139,plain,
    ( v4_tops_1(sK2,sK0) = iProver_top
    | r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7440,c_28,c_1448])).

cnf(c_8148,plain,
    ( k2_pre_topc(sK1,sK3) = sK3
    | v4_tops_1(sK2,sK0) = iProver_top
    | r1_tarski(sK2,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2664,c_8139])).

cnf(c_8164,plain,
    ( k2_pre_topc(sK1,sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6932,c_1688,c_6574,c_8148])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_tops_1(X0,X1)
    | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_397,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_tops_1(X0,X1)
    | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_22])).

cnf(c_398,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v4_tops_1(X0,sK1)
    | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,X0)),X0) ),
    inference(unflattening,[status(thm)],[c_397])).

cnf(c_1187,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v4_tops_1(X0,sK1) != iProver_top
    | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,X0)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_398])).

cnf(c_3188,plain,
    ( k2_pre_topc(sK1,k1_tops_1(sK1,k2_pre_topc(sK1,X0))) = k2_pre_topc(sK1,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k1_tops_1(sK1,k2_pre_topc(sK1,X0)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v4_tops_1(k2_pre_topc(sK1,X0),sK1) != iProver_top
    | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,X0)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1192,c_2776])).

cnf(c_5040,plain,
    ( k2_pre_topc(sK1,k1_tops_1(sK1,k2_pre_topc(sK1,X0))) = k2_pre_topc(sK1,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v4_tops_1(k2_pre_topc(sK1,X0),sK1) != iProver_top
    | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,X0)),X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3188,c_1190])).

cnf(c_5044,plain,
    ( k2_pre_topc(sK1,k1_tops_1(sK1,k2_pre_topc(sK1,X0))) = k2_pre_topc(sK1,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v4_tops_1(X0,sK1) != iProver_top
    | v4_tops_1(k2_pre_topc(sK1,X0),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1187,c_5040])).

cnf(c_8209,plain,
    ( k2_pre_topc(sK1,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) = k2_pre_topc(sK1,sK3)
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v4_tops_1(k2_pre_topc(sK1,sK3),sK1) != iProver_top
    | v4_tops_1(sK3,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_8164,c_5044])).

cnf(c_8283,plain,
    ( k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) = sK3
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v4_tops_1(sK3,sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8209,c_8164])).

cnf(c_9447,plain,
    ( k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) = sK3
    | v4_tops_1(sK3,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8283,c_29])).

cnf(c_9453,plain,
    ( k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) = sK3
    | k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_2430,c_9447])).

cnf(c_2383,plain,
    ( ~ v5_tops_1(sK2,sK0)
    | k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = sK2 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2371])).

cnf(c_9526,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9453,c_20,c_17,c_1453,c_2383])).

cnf(c_9530,plain,
    ( v4_tops_1(sK2,sK0) = iProver_top
    | r1_tarski(sK2,sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9526,c_8139])).

cnf(c_532,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_tops_1(X0,X1)
    | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_23])).

cnf(c_533,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_tops_1(X0,sK0)
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X0) ),
    inference(unflattening,[status(thm)],[c_532])).

cnf(c_1178,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v4_tops_1(X0,sK0) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_533])).

cnf(c_2099,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,X0)) = X0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v4_tops_1(X0,sK0) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,X0)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1177,c_1205])).

cnf(c_2875,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,X0))) = k2_pre_topc(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v4_tops_1(k2_pre_topc(sK0,X0),sK0) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1183,c_2099])).

cnf(c_4402,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,X0))) = k2_pre_topc(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v4_tops_1(k2_pre_topc(sK0,X0),sK0) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2875,c_1181])).

cnf(c_4406,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,X0))) = k2_pre_topc(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v4_tops_1(X0,sK0) != iProver_top
    | v4_tops_1(k2_pre_topc(sK0,X0),sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1178,c_4402])).

cnf(c_7433,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK2))) = k2_pre_topc(sK0,sK2)
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v4_tops_1(k2_pre_topc(sK0,sK2),sK0) != iProver_top
    | v4_tops_1(sK2,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7368,c_4406])).

cnf(c_7487,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = sK2
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v4_tops_1(sK2,sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7433,c_7368])).

cnf(c_15,negated_conjecture,
    ( ~ v4_pre_topc(sK2,sK0)
    | v4_tops_1(sK3,sK1)
    | ~ v4_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_34,plain,
    ( v4_pre_topc(sK2,sK0) != iProver_top
    | v4_tops_1(sK3,sK1) = iProver_top
    | v4_tops_1(sK2,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_14,negated_conjecture,
    ( ~ v4_pre_topc(sK2,sK0)
    | ~ v5_tops_1(sK3,sK1)
    | ~ v4_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_35,plain,
    ( v4_pre_topc(sK2,sK0) != iProver_top
    | v5_tops_1(sK3,sK1) != iProver_top
    | v4_tops_1(sK2,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_12,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_282,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_24])).

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

cnf(c_9348,plain,
    ( v4_tops_1(sK2,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7487,c_28,c_29,c_34,c_35,c_1451,c_1454,c_1983,c_7208,c_8283])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9530,c_9348,c_1688])).


%------------------------------------------------------------------------------
