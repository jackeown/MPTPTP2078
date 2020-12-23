%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:15:51 EST 2020

% Result     : Theorem 19.24s
% Output     : CNFRefutation 19.85s
% Verified   : 
% Statistics : Number of formulae       :  235 (3405 expanded)
%              Number of clauses        :  167 ( 975 expanded)
%              Number of leaves         :   20 (1084 expanded)
%              Depth                    :   23
%              Number of atoms          :  792 (28234 expanded)
%              Number of equality atoms :  258 (1346 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
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

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f40,plain,(
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

fof(f39,plain,(
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

fof(f38,plain,(
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

fof(f37,plain,
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

fof(f41,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f31,f40,f39,f38,f37])).

fof(f63,plain,
    ( v5_tops_1(sK2,sK0)
    | v4_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f62,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f41])).

fof(f10,axiom,(
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

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X2),X1)
              | ~ r1_tarski(X2,X1)
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X2),X1)
              | ~ r1_tarski(X2,X1)
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_pre_topc(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f60,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f70,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f42])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f44,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f61,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f41])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_tops_1(X1,X0)
              | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1 )
            & ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
              | ~ v5_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
      | ~ v5_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f59,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,k1_tops_1(X0,X1)) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,k1_tops_1(X0,X1)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,k1_tops_1(X0,X1))))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,k1_tops_1(X0,X1))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f66,plain,
    ( ~ v4_tops_1(sK2,sK0)
    | ~ v4_pre_topc(sK2,sK0)
    | v4_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f58,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_tops_1(X1,X0)
          <=> ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_tops_1(X1,X0)
          <=> ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v4_tops_1(X1,X0)
      | ~ r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
      | ~ r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)
      | ~ v4_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
      | ~ v4_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f64,plain,
    ( v5_tops_1(sK2,sK0)
    | v4_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v5_tops_1(X1,X0)
      | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f68,plain,
    ( ~ v4_tops_1(sK2,sK0)
    | ~ v4_pre_topc(sK2,sK0)
    | ~ v5_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f67,plain,
    ( ~ v4_tops_1(sK2,sK0)
    | ~ v4_pre_topc(sK2,sK0)
    | v4_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f65,plain,
    ( v5_tops_1(sK2,sK0)
    | ~ v5_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_763,plain,
    ( ~ v4_tops_1(X0,X1)
    | v4_tops_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_55763,plain,
    ( ~ v4_tops_1(X0,X1)
    | v4_tops_1(sK2,sK0)
    | sK0 != X1
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_763])).

cnf(c_60634,plain,
    ( ~ v4_tops_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),X0)
    | v4_tops_1(sK2,sK0)
    | sK0 != X0
    | sK2 != k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_55763])).

cnf(c_60636,plain,
    ( ~ v4_tops_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),sK0)
    | v4_tops_1(sK2,sK0)
    | sK0 != sK0
    | sK2 != k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_60634])).

cnf(c_21,negated_conjecture,
    ( v4_pre_topc(sK3,sK1)
    | v5_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1381,plain,
    ( v4_pre_topc(sK3,sK1) = iProver_top
    | v5_tops_1(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1380,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_14,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | r1_tarski(k2_pre_topc(X1,X2),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_319,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | r1_tarski(k2_pre_topc(X1,X2),X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_24])).

cnf(c_320,plain,
    ( ~ v4_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X1,X0)
    | r1_tarski(k2_pre_topc(sK1,X1),X0) ),
    inference(unflattening,[status(thm)],[c_319])).

cnf(c_1376,plain,
    ( v4_pre_topc(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(k2_pre_topc(sK1,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_320])).

cnf(c_4328,plain,
    ( v4_pre_topc(sK3,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(k2_pre_topc(sK1,X0),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1380,c_1376])).

cnf(c_4460,plain,
    ( v4_pre_topc(sK3,sK1) != iProver_top
    | r1_tarski(k2_pre_topc(sK1,sK3),sK3) = iProver_top
    | r1_tarski(sK3,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1380,c_4328])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2238,plain,
    ( r1_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2239,plain,
    ( r1_tarski(sK3,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2238])).

cnf(c_4471,plain,
    ( r1_tarski(k2_pre_topc(sK1,sK3),sK3) = iProver_top
    | v4_pre_topc(sK3,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4460,c_2239])).

cnf(c_4472,plain,
    ( v4_pre_topc(sK3,sK1) != iProver_top
    | r1_tarski(k2_pre_topc(sK1,sK3),sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_4471])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_448,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_24])).

cnf(c_449,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(X0,k2_pre_topc(sK1,X0)) ),
    inference(unflattening,[status(thm)],[c_448])).

cnf(c_1368,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_449])).

cnf(c_1950,plain,
    ( r1_tarski(sK3,k2_pre_topc(sK1,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1380,c_1368])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1388,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1983,plain,
    ( k2_pre_topc(sK1,sK3) = sK3
    | r1_tarski(k2_pre_topc(sK1,sK3),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1950,c_1388])).

cnf(c_4476,plain,
    ( k2_pre_topc(sK1,sK3) = sK3
    | v4_pre_topc(sK3,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4472,c_1983])).

cnf(c_4582,plain,
    ( k2_pre_topc(sK1,sK3) = sK3
    | v5_tops_1(sK2,sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1381,c_4476])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1379,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_11,plain,
    ( ~ v5_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k1_tops_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_25,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_529,plain,
    ( ~ v5_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,k1_tops_1(X1,X0)) = X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_25])).

cnf(c_530,plain,
    ( ~ v5_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k1_tops_1(sK0,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_529])).

cnf(c_1362,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,X0)) = X0
    | v5_tops_1(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_530])).

cnf(c_2784,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = sK2
    | v5_tops_1(sK2,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1379,c_1362])).

cnf(c_4585,plain,
    ( k2_pre_topc(sK1,sK3) = sK3
    | k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_4582,c_2784])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_517,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_25])).

cnf(c_518,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_517])).

cnf(c_1363,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_518])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_637,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_25])).

cnf(c_638,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) = k2_pre_topc(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_637])).

cnf(c_1355,plain,
    ( k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) = k2_pre_topc(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_638])).

cnf(c_2225,plain,
    ( k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,X0))) = k2_pre_topc(sK0,k1_tops_1(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1363,c_1355])).

cnf(c_5550,plain,
    ( k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) = k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) ),
    inference(superposition,[status(thm)],[c_1379,c_2225])).

cnf(c_5559,plain,
    ( k2_pre_topc(sK1,sK3) = sK3
    | k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = k2_pre_topc(sK0,sK2) ),
    inference(superposition,[status(thm)],[c_4585,c_5550])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k1_tops_1(X1,k2_pre_topc(X1,k1_tops_1(X1,X0)))) = k2_pre_topc(X1,k1_tops_1(X1,X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_484,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,k1_tops_1(X1,k2_pre_topc(X1,k1_tops_1(X1,X0)))) = k2_pre_topc(X1,k1_tops_1(X1,X0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_25])).

cnf(c_485,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,X0)))) = k2_pre_topc(sK0,k1_tops_1(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_484])).

cnf(c_1365,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,X0)))) = k2_pre_topc(sK0,k1_tops_1(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_485])).

cnf(c_3210,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2)))) = k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) ),
    inference(superposition,[status(thm)],[c_1379,c_1365])).

cnf(c_6014,plain,
    ( k2_pre_topc(sK1,sK3) = sK3
    | k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK2))) = k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) ),
    inference(superposition,[status(thm)],[c_5559,c_3210])).

cnf(c_625,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_25])).

cnf(c_626,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,k2_pre_topc(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_625])).

cnf(c_1356,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_626])).

cnf(c_2227,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),k2_pre_topc(sK0,k1_tops_1(sK0,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1363,c_1356])).

cnf(c_5318,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,X0)) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,X0)),k1_tops_1(sK0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2227,c_1388])).

cnf(c_7138,plain,
    ( k2_pre_topc(sK1,sK3) = sK3
    | k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK2))) = k1_tops_1(sK0,k2_pre_topc(sK0,sK2))
    | m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_pre_topc(sK0,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6014,c_5318])).

cnf(c_18,negated_conjecture,
    ( v4_pre_topc(sK3,sK1)
    | ~ v4_pre_topc(sK2,sK0)
    | ~ v4_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_35,plain,
    ( v4_pre_topc(sK3,sK1) = iProver_top
    | v4_pre_topc(sK2,sK0) != iProver_top
    | v4_tops_1(sK2,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_13,plain,
    ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_26,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_286,plain,
    ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_26])).

cnf(c_287,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_286])).

cnf(c_291,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(k2_pre_topc(sK0,X0),sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_287,c_25])).

cnf(c_292,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(renaming,[status(thm)],[c_291])).

cnf(c_1378,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,X0),sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_292])).

cnf(c_2226,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,k1_tops_1(sK0,X0)),sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1363,c_1378])).

cnf(c_5136,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),sK0) = iProver_top
    | m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3210,c_2226])).

cnf(c_30,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1486,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_518])).

cnf(c_1487,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1486])).

cnf(c_1653,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),sK0)
    | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_292])).

cnf(c_1654,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),sK0) = iProver_top
    | m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1653])).

cnf(c_6379,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5136,c_30,c_1487,c_1654])).

cnf(c_6384,plain,
    ( k2_pre_topc(sK1,sK3) = sK3
    | v4_pre_topc(sK2,sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4585,c_6379])).

cnf(c_7,plain,
    ( v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
    | ~ r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_589,plain,
    ( v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
    | ~ r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_25])).

cnf(c_590,plain,
    ( v4_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,X0)))
    | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X0) ),
    inference(unflattening,[status(thm)],[c_589])).

cnf(c_1358,plain,
    ( v4_tops_1(X0,sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,X0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_590])).

cnf(c_5567,plain,
    ( v4_tops_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),sK0) = iProver_top
    | m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))),k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5550,c_1358])).

cnf(c_5574,plain,
    ( v4_tops_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),sK0) = iProver_top
    | m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))),k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5567,c_3210])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_649,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_25])).

cnf(c_650,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_649])).

cnf(c_1651,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_650])).

cnf(c_1658,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1651])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k2_pre_topc(X1,X0),k2_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_607,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k2_pre_topc(X1,X0),k2_pre_topc(X1,X2))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_25])).

cnf(c_608,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,X1)
    | r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,X1)) ),
    inference(unflattening,[status(thm)],[c_607])).

cnf(c_1645,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k1_tops_1(sK0,sK2),X0)
    | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),k2_pre_topc(sK0,X0)) ),
    inference(instantiation,[status(thm)],[c_608])).

cnf(c_2475,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK2))
    | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) ),
    inference(instantiation,[status(thm)],[c_1645])).

cnf(c_2476,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK2)) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2475])).

cnf(c_3612,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_3613,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3612])).

cnf(c_5317,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))),k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3210,c_2227])).

cnf(c_53705,plain,
    ( v4_tops_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5574,c_30,c_1487,c_1658,c_2476,c_3613,c_5317])).

cnf(c_53710,plain,
    ( k2_pre_topc(sK1,sK3) = sK3
    | v4_tops_1(sK2,sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4585,c_53705])).

cnf(c_53734,plain,
    ( k2_pre_topc(sK1,sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7138,c_35,c_4476,c_6384,c_53710])).

cnf(c_460,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_24])).

cnf(c_461,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,k2_pre_topc(sK1,X0)) = k2_pre_topc(sK1,X0) ),
    inference(unflattening,[status(thm)],[c_460])).

cnf(c_1367,plain,
    ( k2_pre_topc(sK1,k2_pre_topc(sK1,X0)) = k2_pre_topc(sK1,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_461])).

cnf(c_2500,plain,
    ( k2_pre_topc(sK1,k2_pre_topc(sK1,sK3)) = k2_pre_topc(sK1,sK3) ),
    inference(superposition,[status(thm)],[c_1380,c_1367])).

cnf(c_9,plain,
    ( ~ v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_382,plain,
    ( ~ v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_24])).

cnf(c_383,plain,
    ( ~ v4_tops_1(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,X0)),X0) ),
    inference(unflattening,[status(thm)],[c_382])).

cnf(c_1372,plain,
    ( v4_tops_1(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,X0)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_383])).

cnf(c_430,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k2_pre_topc(X1,X0),k2_pre_topc(X1,X2))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_24])).

cnf(c_431,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X0,X1)
    | r1_tarski(k2_pre_topc(sK1,X0),k2_pre_topc(sK1,X1)) ),
    inference(unflattening,[status(thm)],[c_430])).

cnf(c_1369,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_pre_topc(sK1,X0),k2_pre_topc(sK1,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_431])).

cnf(c_8,plain,
    ( ~ v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_397,plain,
    ( ~ v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_24])).

cnf(c_398,plain,
    ( ~ v4_tops_1(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(X0,k2_pre_topc(sK1,k1_tops_1(sK1,X0))) ),
    inference(unflattening,[status(thm)],[c_397])).

cnf(c_1371,plain,
    ( v4_tops_1(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK1,k1_tops_1(sK1,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_398])).

cnf(c_3600,plain,
    ( k2_pre_topc(sK1,k1_tops_1(sK1,X0)) = X0
    | v4_tops_1(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(k2_pre_topc(sK1,k1_tops_1(sK1,X0)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1371,c_1388])).

cnf(c_4809,plain,
    ( k2_pre_topc(sK1,k1_tops_1(sK1,k2_pre_topc(sK1,X0))) = k2_pre_topc(sK1,X0)
    | v4_tops_1(k2_pre_topc(sK1,X0),sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k1_tops_1(sK1,k2_pre_topc(sK1,X0)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,X0)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1369,c_3600])).

cnf(c_472,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_24])).

cnf(c_473,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k2_pre_topc(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_472])).

cnf(c_474,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_473])).

cnf(c_340,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_24])).

cnf(c_341,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k1_tops_1(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_340])).

cnf(c_21792,plain,
    ( m1_subset_1(k1_tops_1(sK1,k2_pre_topc(sK1,X0)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k2_pre_topc(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_341])).

cnf(c_21793,plain,
    ( m1_subset_1(k1_tops_1(sK1,k2_pre_topc(sK1,X0)),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(k2_pre_topc(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21792])).

cnf(c_38575,plain,
    ( k2_pre_topc(sK1,k1_tops_1(sK1,k2_pre_topc(sK1,X0))) = k2_pre_topc(sK1,X0)
    | v4_tops_1(k2_pre_topc(sK1,X0),sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,X0)),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4809,c_474,c_21793])).

cnf(c_38581,plain,
    ( k2_pre_topc(sK1,k1_tops_1(sK1,k2_pre_topc(sK1,X0))) = k2_pre_topc(sK1,X0)
    | v4_tops_1(X0,sK1) != iProver_top
    | v4_tops_1(k2_pre_topc(sK1,X0),sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1372,c_38575])).

cnf(c_39186,plain,
    ( k2_pre_topc(sK1,k1_tops_1(sK1,k2_pre_topc(sK1,k2_pre_topc(sK1,sK3)))) = k2_pre_topc(sK1,k2_pre_topc(sK1,sK3))
    | v4_tops_1(k2_pre_topc(sK1,sK3),sK1) != iProver_top
    | m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2500,c_38581])).

cnf(c_39213,plain,
    ( k2_pre_topc(sK1,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) = k2_pre_topc(sK1,sK3)
    | v4_tops_1(k2_pre_topc(sK1,sK3),sK1) != iProver_top
    | m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_39186,c_2500])).

cnf(c_31,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1482,plain,
    ( m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_473])).

cnf(c_1483,plain,
    ( m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1482])).

cnf(c_3606,plain,
    ( v4_tops_1(k2_pre_topc(sK1,sK3),sK1) != iProver_top
    | m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),k2_pre_topc(sK1,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2500,c_1372])).

cnf(c_38583,plain,
    ( k2_pre_topc(sK1,k1_tops_1(sK1,k2_pre_topc(sK1,k2_pre_topc(sK1,sK3)))) = k2_pre_topc(sK1,k2_pre_topc(sK1,sK3))
    | v4_tops_1(k2_pre_topc(sK1,k2_pre_topc(sK1,sK3)),sK1) != iProver_top
    | m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),k2_pre_topc(sK1,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2500,c_38575])).

cnf(c_38610,plain,
    ( k2_pre_topc(sK1,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) = k2_pre_topc(sK1,sK3)
    | v4_tops_1(k2_pre_topc(sK1,sK3),sK1) != iProver_top
    | m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),k2_pre_topc(sK1,sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_38583,c_2500])).

cnf(c_39217,plain,
    ( v4_tops_1(k2_pre_topc(sK1,sK3),sK1) != iProver_top
    | k2_pre_topc(sK1,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) = k2_pre_topc(sK1,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_39213,c_31,c_1483,c_3606,c_38610])).

cnf(c_39218,plain,
    ( k2_pre_topc(sK1,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) = k2_pre_topc(sK1,sK3)
    | v4_tops_1(k2_pre_topc(sK1,sK3),sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_39217])).

cnf(c_53758,plain,
    ( k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) = sK3
    | v4_tops_1(sK3,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_53734,c_39218])).

cnf(c_53794,plain,
    ( ~ v4_tops_1(sK3,sK1)
    | k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) = sK3 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_53758])).

cnf(c_766,plain,
    ( ~ v4_pre_topc(X0,X1)
    | v4_pre_topc(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1457,plain,
    ( ~ v4_pre_topc(X0,X1)
    | v4_pre_topc(sK2,sK0)
    | sK0 != X1
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_766])).

cnf(c_6439,plain,
    ( ~ v4_pre_topc(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),X0)
    | v4_pre_topc(sK2,sK0)
    | sK0 != X0
    | sK2 != k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_1457])).

cnf(c_6441,plain,
    ( ~ v4_pre_topc(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),sK0)
    | v4_pre_topc(sK2,sK0)
    | sK0 != sK0
    | sK2 != k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_6439])).

cnf(c_5588,plain,
    ( v4_tops_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),sK0)
    | ~ m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))),k2_pre_topc(sK0,k1_tops_1(sK0,sK2)))
    | ~ r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5574])).

cnf(c_5320,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))),k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5317])).

cnf(c_20,negated_conjecture,
    ( v5_tops_1(sK2,sK0)
    | v4_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1382,plain,
    ( v5_tops_1(sK2,sK0) = iProver_top
    | v4_tops_1(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2915,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = sK2
    | v4_tops_1(sK3,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1382,c_2784])).

cnf(c_757,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1745,plain,
    ( X0 != X1
    | sK2 != X1
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_757])).

cnf(c_2254,plain,
    ( X0 != sK2
    | sK2 = X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1745])).

cnf(c_2643,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) != sK2
    | sK2 = k2_pre_topc(sK0,k1_tops_1(sK0,sK2))
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_2254])).

cnf(c_756,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1993,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_756])).

cnf(c_1535,plain,
    ( ~ v5_tops_1(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_530])).

cnf(c_10,plain,
    ( v5_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k1_tops_1(X1,X0)) != X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_367,plain,
    ( v5_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,k1_tops_1(X1,X0)) != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_24])).

cnf(c_368,plain,
    ( v5_tops_1(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,k1_tops_1(sK1,X0)) != X0 ),
    inference(unflattening,[status(thm)],[c_367])).

cnf(c_1525,plain,
    ( v5_tops_1(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) != sK3 ),
    inference(instantiation,[status(thm)],[c_368])).

cnf(c_82,plain,
    ( ~ r1_tarski(sK0,sK0)
    | sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_78,plain,
    ( r1_tarski(sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_16,negated_conjecture,
    ( ~ v4_pre_topc(sK2,sK0)
    | ~ v5_tops_1(sK3,sK1)
    | ~ v4_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_17,negated_conjecture,
    ( ~ v4_pre_topc(sK2,sK0)
    | v4_tops_1(sK3,sK1)
    | ~ v4_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_19,negated_conjecture,
    ( ~ v5_tops_1(sK3,sK1)
    | v5_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f65])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_60636,c_53794,c_53758,c_6441,c_5588,c_5320,c_3612,c_2915,c_2643,c_2475,c_1993,c_1651,c_1653,c_1535,c_1525,c_1486,c_82,c_78,c_16,c_17,c_19,c_22,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:57:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 19.24/2.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.24/2.99  
% 19.24/2.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.24/2.99  
% 19.24/2.99  ------  iProver source info
% 19.24/2.99  
% 19.24/2.99  git: date: 2020-06-30 10:37:57 +0100
% 19.24/2.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.24/2.99  git: non_committed_changes: false
% 19.24/2.99  git: last_make_outside_of_git: false
% 19.24/2.99  
% 19.24/2.99  ------ 
% 19.24/2.99  
% 19.24/2.99  ------ Input Options
% 19.24/2.99  
% 19.24/2.99  --out_options                           all
% 19.24/2.99  --tptp_safe_out                         true
% 19.24/2.99  --problem_path                          ""
% 19.24/2.99  --include_path                          ""
% 19.24/2.99  --clausifier                            res/vclausify_rel
% 19.24/2.99  --clausifier_options                    ""
% 19.24/2.99  --stdin                                 false
% 19.24/2.99  --stats_out                             all
% 19.24/2.99  
% 19.24/2.99  ------ General Options
% 19.24/2.99  
% 19.24/2.99  --fof                                   false
% 19.24/2.99  --time_out_real                         305.
% 19.24/2.99  --time_out_virtual                      -1.
% 19.24/2.99  --symbol_type_check                     false
% 19.24/2.99  --clausify_out                          false
% 19.24/2.99  --sig_cnt_out                           false
% 19.24/2.99  --trig_cnt_out                          false
% 19.24/2.99  --trig_cnt_out_tolerance                1.
% 19.24/2.99  --trig_cnt_out_sk_spl                   false
% 19.24/2.99  --abstr_cl_out                          false
% 19.24/2.99  
% 19.24/2.99  ------ Global Options
% 19.24/2.99  
% 19.24/2.99  --schedule                              default
% 19.24/2.99  --add_important_lit                     false
% 19.24/2.99  --prop_solver_per_cl                    1000
% 19.24/2.99  --min_unsat_core                        false
% 19.24/2.99  --soft_assumptions                      false
% 19.24/2.99  --soft_lemma_size                       3
% 19.24/2.99  --prop_impl_unit_size                   0
% 19.24/2.99  --prop_impl_unit                        []
% 19.24/2.99  --share_sel_clauses                     true
% 19.24/2.99  --reset_solvers                         false
% 19.24/2.99  --bc_imp_inh                            [conj_cone]
% 19.24/2.99  --conj_cone_tolerance                   3.
% 19.24/2.99  --extra_neg_conj                        none
% 19.24/2.99  --large_theory_mode                     true
% 19.24/2.99  --prolific_symb_bound                   200
% 19.24/2.99  --lt_threshold                          2000
% 19.24/2.99  --clause_weak_htbl                      true
% 19.24/2.99  --gc_record_bc_elim                     false
% 19.24/2.99  
% 19.24/2.99  ------ Preprocessing Options
% 19.24/2.99  
% 19.24/2.99  --preprocessing_flag                    true
% 19.24/2.99  --time_out_prep_mult                    0.1
% 19.24/2.99  --splitting_mode                        input
% 19.24/2.99  --splitting_grd                         true
% 19.24/2.99  --splitting_cvd                         false
% 19.24/2.99  --splitting_cvd_svl                     false
% 19.24/2.99  --splitting_nvd                         32
% 19.24/2.99  --sub_typing                            true
% 19.24/2.99  --prep_gs_sim                           true
% 19.24/2.99  --prep_unflatten                        true
% 19.24/2.99  --prep_res_sim                          true
% 19.24/2.99  --prep_upred                            true
% 19.24/2.99  --prep_sem_filter                       exhaustive
% 19.24/2.99  --prep_sem_filter_out                   false
% 19.24/2.99  --pred_elim                             true
% 19.24/2.99  --res_sim_input                         true
% 19.24/2.99  --eq_ax_congr_red                       true
% 19.24/2.99  --pure_diseq_elim                       true
% 19.24/2.99  --brand_transform                       false
% 19.24/2.99  --non_eq_to_eq                          false
% 19.24/2.99  --prep_def_merge                        true
% 19.24/2.99  --prep_def_merge_prop_impl              false
% 19.24/2.99  --prep_def_merge_mbd                    true
% 19.24/2.99  --prep_def_merge_tr_red                 false
% 19.24/2.99  --prep_def_merge_tr_cl                  false
% 19.24/2.99  --smt_preprocessing                     true
% 19.24/2.99  --smt_ac_axioms                         fast
% 19.24/2.99  --preprocessed_out                      false
% 19.24/2.99  --preprocessed_stats                    false
% 19.24/2.99  
% 19.24/2.99  ------ Abstraction refinement Options
% 19.24/2.99  
% 19.24/2.99  --abstr_ref                             []
% 19.24/2.99  --abstr_ref_prep                        false
% 19.24/2.99  --abstr_ref_until_sat                   false
% 19.24/2.99  --abstr_ref_sig_restrict                funpre
% 19.24/2.99  --abstr_ref_af_restrict_to_split_sk     false
% 19.24/2.99  --abstr_ref_under                       []
% 19.24/2.99  
% 19.24/2.99  ------ SAT Options
% 19.24/2.99  
% 19.24/2.99  --sat_mode                              false
% 19.24/2.99  --sat_fm_restart_options                ""
% 19.24/2.99  --sat_gr_def                            false
% 19.24/2.99  --sat_epr_types                         true
% 19.24/2.99  --sat_non_cyclic_types                  false
% 19.24/2.99  --sat_finite_models                     false
% 19.24/2.99  --sat_fm_lemmas                         false
% 19.24/2.99  --sat_fm_prep                           false
% 19.24/2.99  --sat_fm_uc_incr                        true
% 19.24/2.99  --sat_out_model                         small
% 19.24/2.99  --sat_out_clauses                       false
% 19.24/2.99  
% 19.24/2.99  ------ QBF Options
% 19.24/2.99  
% 19.24/2.99  --qbf_mode                              false
% 19.24/2.99  --qbf_elim_univ                         false
% 19.24/2.99  --qbf_dom_inst                          none
% 19.24/2.99  --qbf_dom_pre_inst                      false
% 19.24/2.99  --qbf_sk_in                             false
% 19.24/2.99  --qbf_pred_elim                         true
% 19.24/2.99  --qbf_split                             512
% 19.24/2.99  
% 19.24/2.99  ------ BMC1 Options
% 19.24/2.99  
% 19.24/2.99  --bmc1_incremental                      false
% 19.24/2.99  --bmc1_axioms                           reachable_all
% 19.24/2.99  --bmc1_min_bound                        0
% 19.24/2.99  --bmc1_max_bound                        -1
% 19.24/2.99  --bmc1_max_bound_default                -1
% 19.24/2.99  --bmc1_symbol_reachability              true
% 19.24/2.99  --bmc1_property_lemmas                  false
% 19.24/2.99  --bmc1_k_induction                      false
% 19.24/2.99  --bmc1_non_equiv_states                 false
% 19.24/2.99  --bmc1_deadlock                         false
% 19.24/2.99  --bmc1_ucm                              false
% 19.24/2.99  --bmc1_add_unsat_core                   none
% 19.24/2.99  --bmc1_unsat_core_children              false
% 19.24/2.99  --bmc1_unsat_core_extrapolate_axioms    false
% 19.24/2.99  --bmc1_out_stat                         full
% 19.24/2.99  --bmc1_ground_init                      false
% 19.24/2.99  --bmc1_pre_inst_next_state              false
% 19.24/2.99  --bmc1_pre_inst_state                   false
% 19.24/2.99  --bmc1_pre_inst_reach_state             false
% 19.24/2.99  --bmc1_out_unsat_core                   false
% 19.24/2.99  --bmc1_aig_witness_out                  false
% 19.24/2.99  --bmc1_verbose                          false
% 19.24/2.99  --bmc1_dump_clauses_tptp                false
% 19.24/2.99  --bmc1_dump_unsat_core_tptp             false
% 19.24/2.99  --bmc1_dump_file                        -
% 19.24/2.99  --bmc1_ucm_expand_uc_limit              128
% 19.24/2.99  --bmc1_ucm_n_expand_iterations          6
% 19.24/2.99  --bmc1_ucm_extend_mode                  1
% 19.24/2.99  --bmc1_ucm_init_mode                    2
% 19.24/2.99  --bmc1_ucm_cone_mode                    none
% 19.24/2.99  --bmc1_ucm_reduced_relation_type        0
% 19.24/2.99  --bmc1_ucm_relax_model                  4
% 19.24/2.99  --bmc1_ucm_full_tr_after_sat            true
% 19.24/2.99  --bmc1_ucm_expand_neg_assumptions       false
% 19.24/2.99  --bmc1_ucm_layered_model                none
% 19.24/2.99  --bmc1_ucm_max_lemma_size               10
% 19.24/2.99  
% 19.24/2.99  ------ AIG Options
% 19.24/2.99  
% 19.24/2.99  --aig_mode                              false
% 19.24/2.99  
% 19.24/2.99  ------ Instantiation Options
% 19.24/2.99  
% 19.24/2.99  --instantiation_flag                    true
% 19.24/2.99  --inst_sos_flag                         true
% 19.24/2.99  --inst_sos_phase                        true
% 19.24/2.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.24/2.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.24/2.99  --inst_lit_sel_side                     num_symb
% 19.24/2.99  --inst_solver_per_active                1400
% 19.24/2.99  --inst_solver_calls_frac                1.
% 19.24/2.99  --inst_passive_queue_type               priority_queues
% 19.24/2.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.24/2.99  --inst_passive_queues_freq              [25;2]
% 19.24/2.99  --inst_dismatching                      true
% 19.24/2.99  --inst_eager_unprocessed_to_passive     true
% 19.24/2.99  --inst_prop_sim_given                   true
% 19.24/2.99  --inst_prop_sim_new                     false
% 19.24/2.99  --inst_subs_new                         false
% 19.24/2.99  --inst_eq_res_simp                      false
% 19.24/2.99  --inst_subs_given                       false
% 19.24/2.99  --inst_orphan_elimination               true
% 19.24/2.99  --inst_learning_loop_flag               true
% 19.24/2.99  --inst_learning_start                   3000
% 19.24/2.99  --inst_learning_factor                  2
% 19.24/2.99  --inst_start_prop_sim_after_learn       3
% 19.24/2.99  --inst_sel_renew                        solver
% 19.24/2.99  --inst_lit_activity_flag                true
% 19.24/2.99  --inst_restr_to_given                   false
% 19.24/2.99  --inst_activity_threshold               500
% 19.24/2.99  --inst_out_proof                        true
% 19.24/2.99  
% 19.24/2.99  ------ Resolution Options
% 19.24/2.99  
% 19.24/2.99  --resolution_flag                       true
% 19.24/2.99  --res_lit_sel                           adaptive
% 19.24/2.99  --res_lit_sel_side                      none
% 19.24/2.99  --res_ordering                          kbo
% 19.24/2.99  --res_to_prop_solver                    active
% 19.24/2.99  --res_prop_simpl_new                    false
% 19.24/2.99  --res_prop_simpl_given                  true
% 19.24/2.99  --res_passive_queue_type                priority_queues
% 19.24/2.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.24/2.99  --res_passive_queues_freq               [15;5]
% 19.24/2.99  --res_forward_subs                      full
% 19.24/2.99  --res_backward_subs                     full
% 19.24/2.99  --res_forward_subs_resolution           true
% 19.24/2.99  --res_backward_subs_resolution          true
% 19.24/2.99  --res_orphan_elimination                true
% 19.24/2.99  --res_time_limit                        2.
% 19.24/2.99  --res_out_proof                         true
% 19.24/2.99  
% 19.24/2.99  ------ Superposition Options
% 19.24/2.99  
% 19.24/2.99  --superposition_flag                    true
% 19.24/2.99  --sup_passive_queue_type                priority_queues
% 19.24/2.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.24/2.99  --sup_passive_queues_freq               [8;1;4]
% 19.24/2.99  --demod_completeness_check              fast
% 19.24/2.99  --demod_use_ground                      true
% 19.24/2.99  --sup_to_prop_solver                    passive
% 19.24/2.99  --sup_prop_simpl_new                    true
% 19.24/2.99  --sup_prop_simpl_given                  true
% 19.24/2.99  --sup_fun_splitting                     true
% 19.24/2.99  --sup_smt_interval                      50000
% 19.24/2.99  
% 19.24/2.99  ------ Superposition Simplification Setup
% 19.24/2.99  
% 19.24/2.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.24/2.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.24/2.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.24/2.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 19.24/2.99  --sup_full_triv                         [TrivRules;PropSubs]
% 19.24/2.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.24/2.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.24/2.99  --sup_immed_triv                        [TrivRules]
% 19.24/2.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.24/2.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.24/2.99  --sup_immed_bw_main                     []
% 19.24/2.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.24/2.99  --sup_input_triv                        [Unflattening;TrivRules]
% 19.24/2.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.24/2.99  --sup_input_bw                          []
% 19.24/2.99  
% 19.24/2.99  ------ Combination Options
% 19.24/2.99  
% 19.24/2.99  --comb_res_mult                         3
% 19.24/2.99  --comb_sup_mult                         2
% 19.24/2.99  --comb_inst_mult                        10
% 19.24/2.99  
% 19.24/2.99  ------ Debug Options
% 19.24/2.99  
% 19.24/2.99  --dbg_backtrace                         false
% 19.24/2.99  --dbg_dump_prop_clauses                 false
% 19.24/2.99  --dbg_dump_prop_clauses_file            -
% 19.24/2.99  --dbg_out_stat                          false
% 19.24/2.99  ------ Parsing...
% 19.24/2.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.24/2.99  
% 19.24/2.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 19.24/2.99  
% 19.24/2.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.24/2.99  
% 19.24/2.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.24/2.99  ------ Proving...
% 19.24/2.99  ------ Problem Properties 
% 19.24/2.99  
% 19.24/2.99  
% 19.24/2.99  clauses                                 35
% 19.24/2.99  conjectures                             8
% 19.24/2.99  EPR                                     8
% 19.24/2.99  Horn                                    33
% 19.24/2.99  unary                                   3
% 19.24/2.99  binary                                  14
% 19.24/2.99  lits                                    93
% 19.24/2.99  lits eq                                 9
% 19.24/2.99  fd_pure                                 0
% 19.24/2.99  fd_pseudo                               0
% 19.24/2.99  fd_cond                                 0
% 19.24/2.99  fd_pseudo_cond                          1
% 19.24/2.99  AC symbols                              0
% 19.24/2.99  
% 19.24/2.99  ------ Schedule dynamic 5 is on 
% 19.24/2.99  
% 19.24/2.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 19.24/2.99  
% 19.24/2.99  
% 19.24/2.99  ------ 
% 19.24/2.99  Current options:
% 19.24/2.99  ------ 
% 19.24/2.99  
% 19.24/2.99  ------ Input Options
% 19.24/2.99  
% 19.24/2.99  --out_options                           all
% 19.24/2.99  --tptp_safe_out                         true
% 19.24/2.99  --problem_path                          ""
% 19.24/2.99  --include_path                          ""
% 19.24/2.99  --clausifier                            res/vclausify_rel
% 19.24/2.99  --clausifier_options                    ""
% 19.24/2.99  --stdin                                 false
% 19.24/2.99  --stats_out                             all
% 19.24/2.99  
% 19.24/2.99  ------ General Options
% 19.24/2.99  
% 19.24/2.99  --fof                                   false
% 19.24/2.99  --time_out_real                         305.
% 19.24/2.99  --time_out_virtual                      -1.
% 19.24/2.99  --symbol_type_check                     false
% 19.24/2.99  --clausify_out                          false
% 19.24/2.99  --sig_cnt_out                           false
% 19.24/2.99  --trig_cnt_out                          false
% 19.24/2.99  --trig_cnt_out_tolerance                1.
% 19.24/2.99  --trig_cnt_out_sk_spl                   false
% 19.24/2.99  --abstr_cl_out                          false
% 19.24/2.99  
% 19.24/2.99  ------ Global Options
% 19.24/2.99  
% 19.24/2.99  --schedule                              default
% 19.24/2.99  --add_important_lit                     false
% 19.24/2.99  --prop_solver_per_cl                    1000
% 19.24/2.99  --min_unsat_core                        false
% 19.24/2.99  --soft_assumptions                      false
% 19.24/2.99  --soft_lemma_size                       3
% 19.24/2.99  --prop_impl_unit_size                   0
% 19.24/2.99  --prop_impl_unit                        []
% 19.24/2.99  --share_sel_clauses                     true
% 19.24/2.99  --reset_solvers                         false
% 19.24/2.99  --bc_imp_inh                            [conj_cone]
% 19.24/2.99  --conj_cone_tolerance                   3.
% 19.24/2.99  --extra_neg_conj                        none
% 19.24/2.99  --large_theory_mode                     true
% 19.24/2.99  --prolific_symb_bound                   200
% 19.24/2.99  --lt_threshold                          2000
% 19.24/2.99  --clause_weak_htbl                      true
% 19.24/2.99  --gc_record_bc_elim                     false
% 19.24/2.99  
% 19.24/2.99  ------ Preprocessing Options
% 19.24/2.99  
% 19.24/2.99  --preprocessing_flag                    true
% 19.24/2.99  --time_out_prep_mult                    0.1
% 19.24/2.99  --splitting_mode                        input
% 19.24/2.99  --splitting_grd                         true
% 19.24/2.99  --splitting_cvd                         false
% 19.24/2.99  --splitting_cvd_svl                     false
% 19.24/2.99  --splitting_nvd                         32
% 19.24/2.99  --sub_typing                            true
% 19.24/2.99  --prep_gs_sim                           true
% 19.24/2.99  --prep_unflatten                        true
% 19.24/2.99  --prep_res_sim                          true
% 19.24/2.99  --prep_upred                            true
% 19.24/2.99  --prep_sem_filter                       exhaustive
% 19.24/2.99  --prep_sem_filter_out                   false
% 19.24/2.99  --pred_elim                             true
% 19.24/2.99  --res_sim_input                         true
% 19.24/2.99  --eq_ax_congr_red                       true
% 19.24/2.99  --pure_diseq_elim                       true
% 19.24/2.99  --brand_transform                       false
% 19.24/2.99  --non_eq_to_eq                          false
% 19.24/2.99  --prep_def_merge                        true
% 19.24/2.99  --prep_def_merge_prop_impl              false
% 19.24/2.99  --prep_def_merge_mbd                    true
% 19.24/2.99  --prep_def_merge_tr_red                 false
% 19.24/2.99  --prep_def_merge_tr_cl                  false
% 19.24/2.99  --smt_preprocessing                     true
% 19.24/2.99  --smt_ac_axioms                         fast
% 19.24/2.99  --preprocessed_out                      false
% 19.24/2.99  --preprocessed_stats                    false
% 19.24/2.99  
% 19.24/2.99  ------ Abstraction refinement Options
% 19.24/2.99  
% 19.24/2.99  --abstr_ref                             []
% 19.24/2.99  --abstr_ref_prep                        false
% 19.24/2.99  --abstr_ref_until_sat                   false
% 19.24/2.99  --abstr_ref_sig_restrict                funpre
% 19.24/2.99  --abstr_ref_af_restrict_to_split_sk     false
% 19.24/2.99  --abstr_ref_under                       []
% 19.24/2.99  
% 19.24/2.99  ------ SAT Options
% 19.24/2.99  
% 19.24/2.99  --sat_mode                              false
% 19.24/2.99  --sat_fm_restart_options                ""
% 19.24/2.99  --sat_gr_def                            false
% 19.24/2.99  --sat_epr_types                         true
% 19.24/2.99  --sat_non_cyclic_types                  false
% 19.24/2.99  --sat_finite_models                     false
% 19.24/2.99  --sat_fm_lemmas                         false
% 19.24/2.99  --sat_fm_prep                           false
% 19.24/2.99  --sat_fm_uc_incr                        true
% 19.24/2.99  --sat_out_model                         small
% 19.24/2.99  --sat_out_clauses                       false
% 19.24/2.99  
% 19.24/2.99  ------ QBF Options
% 19.24/2.99  
% 19.24/2.99  --qbf_mode                              false
% 19.24/2.99  --qbf_elim_univ                         false
% 19.24/2.99  --qbf_dom_inst                          none
% 19.24/2.99  --qbf_dom_pre_inst                      false
% 19.24/2.99  --qbf_sk_in                             false
% 19.24/2.99  --qbf_pred_elim                         true
% 19.24/2.99  --qbf_split                             512
% 19.24/2.99  
% 19.24/2.99  ------ BMC1 Options
% 19.24/2.99  
% 19.24/2.99  --bmc1_incremental                      false
% 19.24/2.99  --bmc1_axioms                           reachable_all
% 19.24/2.99  --bmc1_min_bound                        0
% 19.24/2.99  --bmc1_max_bound                        -1
% 19.24/2.99  --bmc1_max_bound_default                -1
% 19.24/2.99  --bmc1_symbol_reachability              true
% 19.24/2.99  --bmc1_property_lemmas                  false
% 19.24/2.99  --bmc1_k_induction                      false
% 19.24/2.99  --bmc1_non_equiv_states                 false
% 19.24/2.99  --bmc1_deadlock                         false
% 19.24/2.99  --bmc1_ucm                              false
% 19.24/2.99  --bmc1_add_unsat_core                   none
% 19.24/2.99  --bmc1_unsat_core_children              false
% 19.24/2.99  --bmc1_unsat_core_extrapolate_axioms    false
% 19.24/2.99  --bmc1_out_stat                         full
% 19.24/2.99  --bmc1_ground_init                      false
% 19.24/2.99  --bmc1_pre_inst_next_state              false
% 19.24/2.99  --bmc1_pre_inst_state                   false
% 19.24/2.99  --bmc1_pre_inst_reach_state             false
% 19.24/2.99  --bmc1_out_unsat_core                   false
% 19.24/2.99  --bmc1_aig_witness_out                  false
% 19.24/2.99  --bmc1_verbose                          false
% 19.24/2.99  --bmc1_dump_clauses_tptp                false
% 19.24/2.99  --bmc1_dump_unsat_core_tptp             false
% 19.24/2.99  --bmc1_dump_file                        -
% 19.24/2.99  --bmc1_ucm_expand_uc_limit              128
% 19.24/2.99  --bmc1_ucm_n_expand_iterations          6
% 19.24/2.99  --bmc1_ucm_extend_mode                  1
% 19.24/2.99  --bmc1_ucm_init_mode                    2
% 19.24/2.99  --bmc1_ucm_cone_mode                    none
% 19.24/2.99  --bmc1_ucm_reduced_relation_type        0
% 19.24/2.99  --bmc1_ucm_relax_model                  4
% 19.24/2.99  --bmc1_ucm_full_tr_after_sat            true
% 19.24/2.99  --bmc1_ucm_expand_neg_assumptions       false
% 19.24/2.99  --bmc1_ucm_layered_model                none
% 19.24/2.99  --bmc1_ucm_max_lemma_size               10
% 19.24/2.99  
% 19.24/2.99  ------ AIG Options
% 19.24/2.99  
% 19.24/2.99  --aig_mode                              false
% 19.24/2.99  
% 19.24/2.99  ------ Instantiation Options
% 19.24/2.99  
% 19.24/2.99  --instantiation_flag                    true
% 19.24/2.99  --inst_sos_flag                         true
% 19.24/2.99  --inst_sos_phase                        true
% 19.24/2.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.24/2.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.24/2.99  --inst_lit_sel_side                     none
% 19.24/2.99  --inst_solver_per_active                1400
% 19.24/2.99  --inst_solver_calls_frac                1.
% 19.24/2.99  --inst_passive_queue_type               priority_queues
% 19.24/2.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.24/2.99  --inst_passive_queues_freq              [25;2]
% 19.24/2.99  --inst_dismatching                      true
% 19.24/2.99  --inst_eager_unprocessed_to_passive     true
% 19.24/2.99  --inst_prop_sim_given                   true
% 19.24/2.99  --inst_prop_sim_new                     false
% 19.24/2.99  --inst_subs_new                         false
% 19.24/2.99  --inst_eq_res_simp                      false
% 19.24/2.99  --inst_subs_given                       false
% 19.24/2.99  --inst_orphan_elimination               true
% 19.24/2.99  --inst_learning_loop_flag               true
% 19.24/2.99  --inst_learning_start                   3000
% 19.24/2.99  --inst_learning_factor                  2
% 19.24/2.99  --inst_start_prop_sim_after_learn       3
% 19.24/2.99  --inst_sel_renew                        solver
% 19.24/2.99  --inst_lit_activity_flag                true
% 19.24/2.99  --inst_restr_to_given                   false
% 19.24/2.99  --inst_activity_threshold               500
% 19.24/2.99  --inst_out_proof                        true
% 19.24/2.99  
% 19.24/2.99  ------ Resolution Options
% 19.24/2.99  
% 19.24/2.99  --resolution_flag                       false
% 19.24/2.99  --res_lit_sel                           adaptive
% 19.24/2.99  --res_lit_sel_side                      none
% 19.24/2.99  --res_ordering                          kbo
% 19.24/2.99  --res_to_prop_solver                    active
% 19.24/2.99  --res_prop_simpl_new                    false
% 19.24/2.99  --res_prop_simpl_given                  true
% 19.24/2.99  --res_passive_queue_type                priority_queues
% 19.24/2.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.24/2.99  --res_passive_queues_freq               [15;5]
% 19.24/2.99  --res_forward_subs                      full
% 19.24/2.99  --res_backward_subs                     full
% 19.24/2.99  --res_forward_subs_resolution           true
% 19.24/2.99  --res_backward_subs_resolution          true
% 19.24/2.99  --res_orphan_elimination                true
% 19.24/2.99  --res_time_limit                        2.
% 19.24/2.99  --res_out_proof                         true
% 19.24/2.99  
% 19.24/2.99  ------ Superposition Options
% 19.24/2.99  
% 19.24/2.99  --superposition_flag                    true
% 19.24/2.99  --sup_passive_queue_type                priority_queues
% 19.24/2.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.24/2.99  --sup_passive_queues_freq               [8;1;4]
% 19.24/2.99  --demod_completeness_check              fast
% 19.24/2.99  --demod_use_ground                      true
% 19.24/2.99  --sup_to_prop_solver                    passive
% 19.24/2.99  --sup_prop_simpl_new                    true
% 19.24/2.99  --sup_prop_simpl_given                  true
% 19.24/2.99  --sup_fun_splitting                     true
% 19.24/2.99  --sup_smt_interval                      50000
% 19.24/2.99  
% 19.24/2.99  ------ Superposition Simplification Setup
% 19.24/2.99  
% 19.24/2.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.24/2.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.24/2.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.24/2.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 19.24/2.99  --sup_full_triv                         [TrivRules;PropSubs]
% 19.24/2.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.24/2.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.24/2.99  --sup_immed_triv                        [TrivRules]
% 19.24/2.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.24/2.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.24/2.99  --sup_immed_bw_main                     []
% 19.24/2.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.24/2.99  --sup_input_triv                        [Unflattening;TrivRules]
% 19.24/2.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.24/2.99  --sup_input_bw                          []
% 19.24/2.99  
% 19.24/2.99  ------ Combination Options
% 19.24/2.99  
% 19.24/2.99  --comb_res_mult                         3
% 19.24/2.99  --comb_sup_mult                         2
% 19.24/2.99  --comb_inst_mult                        10
% 19.24/2.99  
% 19.24/2.99  ------ Debug Options
% 19.24/2.99  
% 19.24/2.99  --dbg_backtrace                         false
% 19.24/2.99  --dbg_dump_prop_clauses                 false
% 19.24/2.99  --dbg_dump_prop_clauses_file            -
% 19.24/2.99  --dbg_out_stat                          false
% 19.24/2.99  
% 19.24/2.99  
% 19.24/2.99  
% 19.24/2.99  
% 19.24/2.99  ------ Proving...
% 19.24/2.99  
% 19.24/2.99  
% 19.24/2.99  % SZS status Theorem for theBenchmark.p
% 19.24/2.99  
% 19.24/2.99  % SZS output start CNFRefutation for theBenchmark.p
% 19.24/2.99  
% 19.24/2.99  fof(f12,conjecture,(
% 19.24/2.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v5_tops_1(X2,X0) => (v4_tops_1(X2,X0) & v4_pre_topc(X2,X0))) & ((v4_tops_1(X3,X1) & v4_pre_topc(X3,X1)) => v5_tops_1(X3,X1)))))))),
% 19.24/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.24/2.99  
% 19.24/2.99  fof(f13,negated_conjecture,(
% 19.24/2.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v5_tops_1(X2,X0) => (v4_tops_1(X2,X0) & v4_pre_topc(X2,X0))) & ((v4_tops_1(X3,X1) & v4_pre_topc(X3,X1)) => v5_tops_1(X3,X1)))))))),
% 19.24/2.99    inference(negated_conjecture,[],[f12])).
% 19.24/2.99  
% 19.24/2.99  fof(f30,plain,(
% 19.24/2.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v4_pre_topc(X2,X0)) & v5_tops_1(X2,X0)) | (~v5_tops_1(X3,X1) & (v4_tops_1(X3,X1) & v4_pre_topc(X3,X1)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 19.24/2.99    inference(ennf_transformation,[],[f13])).
% 19.24/2.99  
% 19.24/2.99  fof(f31,plain,(
% 19.24/2.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v4_pre_topc(X2,X0)) & v5_tops_1(X2,X0)) | (~v5_tops_1(X3,X1) & v4_tops_1(X3,X1) & v4_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 19.24/2.99    inference(flattening,[],[f30])).
% 19.24/2.99  
% 19.24/2.99  fof(f40,plain,(
% 19.24/2.99    ( ! [X2,X0,X1] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v4_pre_topc(X2,X0)) & v5_tops_1(X2,X0)) | (~v5_tops_1(X3,X1) & v4_tops_1(X3,X1) & v4_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => ((((~v4_tops_1(X2,X0) | ~v4_pre_topc(X2,X0)) & v5_tops_1(X2,X0)) | (~v5_tops_1(sK3,X1) & v4_tops_1(sK3,X1) & v4_pre_topc(sK3,X1))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X1))))) )),
% 19.24/2.99    introduced(choice_axiom,[])).
% 19.24/2.99  
% 19.24/2.99  fof(f39,plain,(
% 19.24/2.99    ( ! [X0,X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v4_pre_topc(X2,X0)) & v5_tops_1(X2,X0)) | (~v5_tops_1(X3,X1) & v4_tops_1(X3,X1) & v4_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X3] : ((((~v4_tops_1(sK2,X0) | ~v4_pre_topc(sK2,X0)) & v5_tops_1(sK2,X0)) | (~v5_tops_1(X3,X1) & v4_tops_1(X3,X1) & v4_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 19.24/2.99    introduced(choice_axiom,[])).
% 19.24/2.99  
% 19.24/2.99  fof(f38,plain,(
% 19.24/2.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v4_pre_topc(X2,X0)) & v5_tops_1(X2,X0)) | (~v5_tops_1(X3,X1) & v4_tops_1(X3,X1) & v4_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) => (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v4_pre_topc(X2,X0)) & v5_tops_1(X2,X0)) | (~v5_tops_1(X3,sK1) & v4_tops_1(X3,sK1) & v4_pre_topc(X3,sK1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(sK1))) )),
% 19.24/2.99    introduced(choice_axiom,[])).
% 19.24/2.99  
% 19.24/2.99  fof(f37,plain,(
% 19.24/2.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v4_pre_topc(X2,X0)) & v5_tops_1(X2,X0)) | (~v5_tops_1(X3,X1) & v4_tops_1(X3,X1) & v4_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,sK0) | ~v4_pre_topc(X2,sK0)) & v5_tops_1(X2,sK0)) | (~v5_tops_1(X3,X1) & v4_tops_1(X3,X1) & v4_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 19.24/2.99    introduced(choice_axiom,[])).
% 19.24/2.99  
% 19.24/2.99  fof(f41,plain,(
% 19.24/2.99    ((((((~v4_tops_1(sK2,sK0) | ~v4_pre_topc(sK2,sK0)) & v5_tops_1(sK2,sK0)) | (~v5_tops_1(sK3,sK1) & v4_tops_1(sK3,sK1) & v4_pre_topc(sK3,sK1))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 19.24/2.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f31,f40,f39,f38,f37])).
% 19.24/2.99  
% 19.24/2.99  fof(f63,plain,(
% 19.24/2.99    v5_tops_1(sK2,sK0) | v4_pre_topc(sK3,sK1)),
% 19.24/2.99    inference(cnf_transformation,[],[f41])).
% 19.24/2.99  
% 19.24/2.99  fof(f62,plain,(
% 19.24/2.99    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 19.24/2.99    inference(cnf_transformation,[],[f41])).
% 19.24/2.99  
% 19.24/2.99  fof(f10,axiom,(
% 19.24/2.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X2,X1) & v4_pre_topc(X1,X0)) => r1_tarski(k2_pre_topc(X0,X2),X1)))))),
% 19.24/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.24/2.99  
% 19.24/2.99  fof(f27,plain,(
% 19.24/2.99    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k2_pre_topc(X0,X2),X1) | (~r1_tarski(X2,X1) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 19.24/2.99    inference(ennf_transformation,[],[f10])).
% 19.24/2.99  
% 19.24/2.99  fof(f28,plain,(
% 19.24/2.99    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k2_pre_topc(X0,X2),X1) | ~r1_tarski(X2,X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 19.24/2.99    inference(flattening,[],[f27])).
% 19.24/2.99  
% 19.24/2.99  fof(f56,plain,(
% 19.24/2.99    ( ! [X2,X0,X1] : (r1_tarski(k2_pre_topc(X0,X2),X1) | ~r1_tarski(X2,X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 19.24/2.99    inference(cnf_transformation,[],[f28])).
% 19.24/2.99  
% 19.24/2.99  fof(f60,plain,(
% 19.24/2.99    l1_pre_topc(sK1)),
% 19.24/2.99    inference(cnf_transformation,[],[f41])).
% 19.24/2.99  
% 19.24/2.99  fof(f1,axiom,(
% 19.24/2.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 19.24/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.24/2.99  
% 19.24/2.99  fof(f32,plain,(
% 19.24/2.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 19.24/2.99    inference(nnf_transformation,[],[f1])).
% 19.24/2.99  
% 19.24/2.99  fof(f33,plain,(
% 19.24/2.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 19.24/2.99    inference(flattening,[],[f32])).
% 19.24/2.99  
% 19.24/2.99  fof(f42,plain,(
% 19.24/2.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 19.24/2.99    inference(cnf_transformation,[],[f33])).
% 19.24/2.99  
% 19.24/2.99  fof(f70,plain,(
% 19.24/2.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 19.24/2.99    inference(equality_resolution,[],[f42])).
% 19.24/2.99  
% 19.24/2.99  fof(f4,axiom,(
% 19.24/2.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 19.24/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.24/2.99  
% 19.24/2.99  fof(f18,plain,(
% 19.24/2.99    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 19.24/2.99    inference(ennf_transformation,[],[f4])).
% 19.24/2.99  
% 19.24/2.99  fof(f47,plain,(
% 19.24/2.99    ( ! [X0,X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 19.24/2.99    inference(cnf_transformation,[],[f18])).
% 19.24/2.99  
% 19.24/2.99  fof(f44,plain,(
% 19.24/2.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 19.24/2.99    inference(cnf_transformation,[],[f33])).
% 19.24/2.99  
% 19.24/2.99  fof(f61,plain,(
% 19.24/2.99    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 19.24/2.99    inference(cnf_transformation,[],[f41])).
% 19.24/2.99  
% 19.24/2.99  fof(f7,axiom,(
% 19.24/2.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1)))),
% 19.24/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.24/2.99  
% 19.24/2.99  fof(f22,plain,(
% 19.24/2.99    ! [X0] : (! [X1] : ((v5_tops_1(X1,X0) <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 19.24/2.99    inference(ennf_transformation,[],[f7])).
% 19.24/2.99  
% 19.24/2.99  fof(f36,plain,(
% 19.24/2.99    ! [X0] : (! [X1] : (((v5_tops_1(X1,X0) | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1) & (k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 | ~v5_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 19.24/2.99    inference(nnf_transformation,[],[f22])).
% 19.24/2.99  
% 19.24/2.99  fof(f52,plain,(
% 19.24/2.99    ( ! [X0,X1] : (k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 | ~v5_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 19.24/2.99    inference(cnf_transformation,[],[f36])).
% 19.24/2.99  
% 19.24/2.99  fof(f59,plain,(
% 19.24/2.99    l1_pre_topc(sK0)),
% 19.24/2.99    inference(cnf_transformation,[],[f41])).
% 19.24/2.99  
% 19.24/2.99  fof(f8,axiom,(
% 19.24/2.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 19.24/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.85/2.99  
% 19.85/2.99  fof(f23,plain,(
% 19.85/2.99    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 19.85/2.99    inference(ennf_transformation,[],[f8])).
% 19.85/2.99  
% 19.85/2.99  fof(f24,plain,(
% 19.85/2.99    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 19.85/2.99    inference(flattening,[],[f23])).
% 19.85/2.99  
% 19.85/2.99  fof(f54,plain,(
% 19.85/2.99    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 19.85/2.99    inference(cnf_transformation,[],[f24])).
% 19.85/2.99  
% 19.85/2.99  fof(f3,axiom,(
% 19.85/2.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)))),
% 19.85/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.85/2.99  
% 19.85/2.99  fof(f16,plain,(
% 19.85/2.99    ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 19.85/2.99    inference(ennf_transformation,[],[f3])).
% 19.85/2.99  
% 19.85/2.99  fof(f17,plain,(
% 19.85/2.99    ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 19.85/2.99    inference(flattening,[],[f16])).
% 19.85/2.99  
% 19.85/2.99  fof(f46,plain,(
% 19.85/2.99    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 19.85/2.99    inference(cnf_transformation,[],[f17])).
% 19.85/2.99  
% 19.85/2.99  fof(f11,axiom,(
% 19.85/2.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,k1_tops_1(X0,X1)) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,k1_tops_1(X0,X1))))))),
% 19.85/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.85/2.99  
% 19.85/2.99  fof(f29,plain,(
% 19.85/2.99    ! [X0] : (! [X1] : (k2_pre_topc(X0,k1_tops_1(X0,X1)) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,k1_tops_1(X0,X1)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 19.85/2.99    inference(ennf_transformation,[],[f11])).
% 19.85/2.99  
% 19.85/2.99  fof(f57,plain,(
% 19.85/2.99    ( ! [X0,X1] : (k2_pre_topc(X0,k1_tops_1(X0,X1)) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,k1_tops_1(X0,X1)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 19.85/2.99    inference(cnf_transformation,[],[f29])).
% 19.85/2.99  
% 19.85/2.99  fof(f66,plain,(
% 19.85/2.99    ~v4_tops_1(sK2,sK0) | ~v4_pre_topc(sK2,sK0) | v4_pre_topc(sK3,sK1)),
% 19.85/2.99    inference(cnf_transformation,[],[f41])).
% 19.85/2.99  
% 19.85/2.99  fof(f9,axiom,(
% 19.85/2.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 19.85/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.85/2.99  
% 19.85/2.99  fof(f25,plain,(
% 19.85/2.99    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 19.85/2.99    inference(ennf_transformation,[],[f9])).
% 19.85/2.99  
% 19.85/2.99  fof(f26,plain,(
% 19.85/2.99    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 19.85/2.99    inference(flattening,[],[f25])).
% 19.85/2.99  
% 19.85/2.99  fof(f55,plain,(
% 19.85/2.99    ( ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 19.85/2.99    inference(cnf_transformation,[],[f26])).
% 19.85/2.99  
% 19.85/2.99  fof(f58,plain,(
% 19.85/2.99    v2_pre_topc(sK0)),
% 19.85/2.99    inference(cnf_transformation,[],[f41])).
% 19.85/2.99  
% 19.85/2.99  fof(f6,axiom,(
% 19.85/2.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)))))),
% 19.85/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.85/2.99  
% 19.85/2.99  fof(f21,plain,(
% 19.85/2.99    ! [X0] : (! [X1] : ((v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 19.85/2.99    inference(ennf_transformation,[],[f6])).
% 19.85/2.99  
% 19.85/2.99  fof(f34,plain,(
% 19.85/2.99    ! [X0] : (! [X1] : (((v4_tops_1(X1,X0) | (~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1))) & ((r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) | ~v4_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 19.85/2.99    inference(nnf_transformation,[],[f21])).
% 19.85/2.99  
% 19.85/2.99  fof(f35,plain,(
% 19.85/2.99    ! [X0] : (! [X1] : (((v4_tops_1(X1,X0) | ~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) & ((r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) | ~v4_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 19.85/2.99    inference(flattening,[],[f34])).
% 19.85/2.99  
% 19.85/2.99  fof(f51,plain,(
% 19.85/2.99    ( ! [X0,X1] : (v4_tops_1(X1,X0) | ~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 19.85/2.99    inference(cnf_transformation,[],[f35])).
% 19.85/2.99  
% 19.85/2.99  fof(f2,axiom,(
% 19.85/2.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 19.85/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.85/2.99  
% 19.85/2.99  fof(f14,plain,(
% 19.85/2.99    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 19.85/2.99    inference(ennf_transformation,[],[f2])).
% 19.85/2.99  
% 19.85/2.99  fof(f15,plain,(
% 19.85/2.99    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 19.85/2.99    inference(flattening,[],[f14])).
% 19.85/2.99  
% 19.85/2.99  fof(f45,plain,(
% 19.85/2.99    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 19.85/2.99    inference(cnf_transformation,[],[f15])).
% 19.85/2.99  
% 19.85/2.99  fof(f5,axiom,(
% 19.85/2.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 19.85/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.85/2.99  
% 19.85/2.99  fof(f19,plain,(
% 19.85/2.99    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 19.85/2.99    inference(ennf_transformation,[],[f5])).
% 19.85/2.99  
% 19.85/2.99  fof(f20,plain,(
% 19.85/2.99    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 19.85/2.99    inference(flattening,[],[f19])).
% 19.85/2.99  
% 19.85/2.99  fof(f48,plain,(
% 19.85/2.99    ( ! [X2,X0,X1] : (r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 19.85/2.99    inference(cnf_transformation,[],[f20])).
% 19.85/2.99  
% 19.85/2.99  fof(f49,plain,(
% 19.85/2.99    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) | ~v4_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 19.85/2.99    inference(cnf_transformation,[],[f35])).
% 19.85/2.99  
% 19.85/2.99  fof(f50,plain,(
% 19.85/2.99    ( ! [X0,X1] : (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~v4_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 19.85/2.99    inference(cnf_transformation,[],[f35])).
% 19.85/2.99  
% 19.85/2.99  fof(f64,plain,(
% 19.85/2.99    v5_tops_1(sK2,sK0) | v4_tops_1(sK3,sK1)),
% 19.85/2.99    inference(cnf_transformation,[],[f41])).
% 19.85/2.99  
% 19.85/2.99  fof(f53,plain,(
% 19.85/2.99    ( ! [X0,X1] : (v5_tops_1(X1,X0) | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 19.85/2.99    inference(cnf_transformation,[],[f36])).
% 19.85/2.99  
% 19.85/2.99  fof(f68,plain,(
% 19.85/2.99    ~v4_tops_1(sK2,sK0) | ~v4_pre_topc(sK2,sK0) | ~v5_tops_1(sK3,sK1)),
% 19.85/2.99    inference(cnf_transformation,[],[f41])).
% 19.85/2.99  
% 19.85/2.99  fof(f67,plain,(
% 19.85/2.99    ~v4_tops_1(sK2,sK0) | ~v4_pre_topc(sK2,sK0) | v4_tops_1(sK3,sK1)),
% 19.85/2.99    inference(cnf_transformation,[],[f41])).
% 19.85/2.99  
% 19.85/2.99  fof(f65,plain,(
% 19.85/2.99    v5_tops_1(sK2,sK0) | ~v5_tops_1(sK3,sK1)),
% 19.85/2.99    inference(cnf_transformation,[],[f41])).
% 19.85/2.99  
% 19.85/2.99  cnf(c_763,plain,
% 19.85/2.99      ( ~ v4_tops_1(X0,X1) | v4_tops_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 19.85/2.99      theory(equality) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_55763,plain,
% 19.85/2.99      ( ~ v4_tops_1(X0,X1) | v4_tops_1(sK2,sK0) | sK0 != X1 | sK2 != X0 ),
% 19.85/2.99      inference(instantiation,[status(thm)],[c_763]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_60634,plain,
% 19.85/2.99      ( ~ v4_tops_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),X0)
% 19.85/2.99      | v4_tops_1(sK2,sK0)
% 19.85/2.99      | sK0 != X0
% 19.85/2.99      | sK2 != k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) ),
% 19.85/2.99      inference(instantiation,[status(thm)],[c_55763]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_60636,plain,
% 19.85/2.99      ( ~ v4_tops_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),sK0)
% 19.85/2.99      | v4_tops_1(sK2,sK0)
% 19.85/2.99      | sK0 != sK0
% 19.85/2.99      | sK2 != k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) ),
% 19.85/2.99      inference(instantiation,[status(thm)],[c_60634]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_21,negated_conjecture,
% 19.85/2.99      ( v4_pre_topc(sK3,sK1) | v5_tops_1(sK2,sK0) ),
% 19.85/2.99      inference(cnf_transformation,[],[f63]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_1381,plain,
% 19.85/2.99      ( v4_pre_topc(sK3,sK1) = iProver_top
% 19.85/2.99      | v5_tops_1(sK2,sK0) = iProver_top ),
% 19.85/2.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_22,negated_conjecture,
% 19.85/2.99      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 19.85/2.99      inference(cnf_transformation,[],[f62]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_1380,plain,
% 19.85/2.99      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 19.85/2.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_14,plain,
% 19.85/2.99      ( ~ v4_pre_topc(X0,X1)
% 19.85/2.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.85/2.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 19.85/2.99      | ~ r1_tarski(X2,X0)
% 19.85/2.99      | r1_tarski(k2_pre_topc(X1,X2),X0)
% 19.85/2.99      | ~ l1_pre_topc(X1) ),
% 19.85/2.99      inference(cnf_transformation,[],[f56]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_24,negated_conjecture,
% 19.85/2.99      ( l1_pre_topc(sK1) ),
% 19.85/2.99      inference(cnf_transformation,[],[f60]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_319,plain,
% 19.85/2.99      ( ~ v4_pre_topc(X0,X1)
% 19.85/2.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.85/2.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 19.85/2.99      | ~ r1_tarski(X2,X0)
% 19.85/2.99      | r1_tarski(k2_pre_topc(X1,X2),X0)
% 19.85/2.99      | sK1 != X1 ),
% 19.85/2.99      inference(resolution_lifted,[status(thm)],[c_14,c_24]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_320,plain,
% 19.85/2.99      ( ~ v4_pre_topc(X0,sK1)
% 19.85/2.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 19.85/2.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 19.85/2.99      | ~ r1_tarski(X1,X0)
% 19.85/2.99      | r1_tarski(k2_pre_topc(sK1,X1),X0) ),
% 19.85/2.99      inference(unflattening,[status(thm)],[c_319]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_1376,plain,
% 19.85/2.99      ( v4_pre_topc(X0,sK1) != iProver_top
% 19.85/2.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 19.85/2.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 19.85/2.99      | r1_tarski(X1,X0) != iProver_top
% 19.85/2.99      | r1_tarski(k2_pre_topc(sK1,X1),X0) = iProver_top ),
% 19.85/2.99      inference(predicate_to_equality,[status(thm)],[c_320]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_4328,plain,
% 19.85/2.99      ( v4_pre_topc(sK3,sK1) != iProver_top
% 19.85/2.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 19.85/2.99      | r1_tarski(X0,sK3) != iProver_top
% 19.85/2.99      | r1_tarski(k2_pre_topc(sK1,X0),sK3) = iProver_top ),
% 19.85/2.99      inference(superposition,[status(thm)],[c_1380,c_1376]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_4460,plain,
% 19.85/2.99      ( v4_pre_topc(sK3,sK1) != iProver_top
% 19.85/2.99      | r1_tarski(k2_pre_topc(sK1,sK3),sK3) = iProver_top
% 19.85/2.99      | r1_tarski(sK3,sK3) != iProver_top ),
% 19.85/2.99      inference(superposition,[status(thm)],[c_1380,c_4328]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_2,plain,
% 19.85/2.99      ( r1_tarski(X0,X0) ),
% 19.85/2.99      inference(cnf_transformation,[],[f70]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_2238,plain,
% 19.85/2.99      ( r1_tarski(sK3,sK3) ),
% 19.85/2.99      inference(instantiation,[status(thm)],[c_2]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_2239,plain,
% 19.85/2.99      ( r1_tarski(sK3,sK3) = iProver_top ),
% 19.85/2.99      inference(predicate_to_equality,[status(thm)],[c_2238]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_4471,plain,
% 19.85/2.99      ( r1_tarski(k2_pre_topc(sK1,sK3),sK3) = iProver_top
% 19.85/2.99      | v4_pre_topc(sK3,sK1) != iProver_top ),
% 19.85/2.99      inference(global_propositional_subsumption,
% 19.85/2.99                [status(thm)],
% 19.85/2.99                [c_4460,c_2239]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_4472,plain,
% 19.85/2.99      ( v4_pre_topc(sK3,sK1) != iProver_top
% 19.85/2.99      | r1_tarski(k2_pre_topc(sK1,sK3),sK3) = iProver_top ),
% 19.85/2.99      inference(renaming,[status(thm)],[c_4471]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_5,plain,
% 19.85/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.85/2.99      | r1_tarski(X0,k2_pre_topc(X1,X0))
% 19.85/2.99      | ~ l1_pre_topc(X1) ),
% 19.85/2.99      inference(cnf_transformation,[],[f47]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_448,plain,
% 19.85/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.85/2.99      | r1_tarski(X0,k2_pre_topc(X1,X0))
% 19.85/2.99      | sK1 != X1 ),
% 19.85/2.99      inference(resolution_lifted,[status(thm)],[c_5,c_24]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_449,plain,
% 19.85/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 19.85/2.99      | r1_tarski(X0,k2_pre_topc(sK1,X0)) ),
% 19.85/2.99      inference(unflattening,[status(thm)],[c_448]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_1368,plain,
% 19.85/2.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 19.85/2.99      | r1_tarski(X0,k2_pre_topc(sK1,X0)) = iProver_top ),
% 19.85/2.99      inference(predicate_to_equality,[status(thm)],[c_449]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_1950,plain,
% 19.85/2.99      ( r1_tarski(sK3,k2_pre_topc(sK1,sK3)) = iProver_top ),
% 19.85/2.99      inference(superposition,[status(thm)],[c_1380,c_1368]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_0,plain,
% 19.85/2.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 19.85/2.99      inference(cnf_transformation,[],[f44]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_1388,plain,
% 19.85/2.99      ( X0 = X1
% 19.85/2.99      | r1_tarski(X0,X1) != iProver_top
% 19.85/2.99      | r1_tarski(X1,X0) != iProver_top ),
% 19.85/2.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_1983,plain,
% 19.85/2.99      ( k2_pre_topc(sK1,sK3) = sK3
% 19.85/2.99      | r1_tarski(k2_pre_topc(sK1,sK3),sK3) != iProver_top ),
% 19.85/2.99      inference(superposition,[status(thm)],[c_1950,c_1388]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_4476,plain,
% 19.85/2.99      ( k2_pre_topc(sK1,sK3) = sK3
% 19.85/2.99      | v4_pre_topc(sK3,sK1) != iProver_top ),
% 19.85/2.99      inference(superposition,[status(thm)],[c_4472,c_1983]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_4582,plain,
% 19.85/2.99      ( k2_pre_topc(sK1,sK3) = sK3 | v5_tops_1(sK2,sK0) = iProver_top ),
% 19.85/2.99      inference(superposition,[status(thm)],[c_1381,c_4476]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_23,negated_conjecture,
% 19.85/2.99      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 19.85/2.99      inference(cnf_transformation,[],[f61]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_1379,plain,
% 19.85/2.99      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 19.85/2.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_11,plain,
% 19.85/2.99      ( ~ v5_tops_1(X0,X1)
% 19.85/2.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.85/2.99      | ~ l1_pre_topc(X1)
% 19.85/2.99      | k2_pre_topc(X1,k1_tops_1(X1,X0)) = X0 ),
% 19.85/2.99      inference(cnf_transformation,[],[f52]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_25,negated_conjecture,
% 19.85/2.99      ( l1_pre_topc(sK0) ),
% 19.85/2.99      inference(cnf_transformation,[],[f59]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_529,plain,
% 19.85/2.99      ( ~ v5_tops_1(X0,X1)
% 19.85/2.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.85/2.99      | k2_pre_topc(X1,k1_tops_1(X1,X0)) = X0
% 19.85/2.99      | sK0 != X1 ),
% 19.85/2.99      inference(resolution_lifted,[status(thm)],[c_11,c_25]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_530,plain,
% 19.85/2.99      ( ~ v5_tops_1(X0,sK0)
% 19.85/2.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.85/2.99      | k2_pre_topc(sK0,k1_tops_1(sK0,X0)) = X0 ),
% 19.85/2.99      inference(unflattening,[status(thm)],[c_529]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_1362,plain,
% 19.85/2.99      ( k2_pre_topc(sK0,k1_tops_1(sK0,X0)) = X0
% 19.85/2.99      | v5_tops_1(X0,sK0) != iProver_top
% 19.85/2.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 19.85/2.99      inference(predicate_to_equality,[status(thm)],[c_530]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_2784,plain,
% 19.85/2.99      ( k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = sK2
% 19.85/2.99      | v5_tops_1(sK2,sK0) != iProver_top ),
% 19.85/2.99      inference(superposition,[status(thm)],[c_1379,c_1362]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_4585,plain,
% 19.85/2.99      ( k2_pre_topc(sK1,sK3) = sK3
% 19.85/2.99      | k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = sK2 ),
% 19.85/2.99      inference(superposition,[status(thm)],[c_4582,c_2784]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_12,plain,
% 19.85/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.85/2.99      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 19.85/2.99      | ~ l1_pre_topc(X1) ),
% 19.85/2.99      inference(cnf_transformation,[],[f54]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_517,plain,
% 19.85/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.85/2.99      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 19.85/2.99      | sK0 != X1 ),
% 19.85/2.99      inference(resolution_lifted,[status(thm)],[c_12,c_25]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_518,plain,
% 19.85/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.85/2.99      | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 19.85/2.99      inference(unflattening,[status(thm)],[c_517]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_1363,plain,
% 19.85/2.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 19.85/2.99      | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 19.85/2.99      inference(predicate_to_equality,[status(thm)],[c_518]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_4,plain,
% 19.85/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.85/2.99      | ~ l1_pre_topc(X1)
% 19.85/2.99      | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0) ),
% 19.85/2.99      inference(cnf_transformation,[],[f46]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_637,plain,
% 19.85/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.85/2.99      | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0)
% 19.85/2.99      | sK0 != X1 ),
% 19.85/2.99      inference(resolution_lifted,[status(thm)],[c_4,c_25]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_638,plain,
% 19.85/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.85/2.99      | k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) = k2_pre_topc(sK0,X0) ),
% 19.85/2.99      inference(unflattening,[status(thm)],[c_637]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_1355,plain,
% 19.85/2.99      ( k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) = k2_pre_topc(sK0,X0)
% 19.85/2.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 19.85/2.99      inference(predicate_to_equality,[status(thm)],[c_638]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_2225,plain,
% 19.85/2.99      ( k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,X0))) = k2_pre_topc(sK0,k1_tops_1(sK0,X0))
% 19.85/2.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 19.85/2.99      inference(superposition,[status(thm)],[c_1363,c_1355]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_5550,plain,
% 19.85/2.99      ( k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) = k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) ),
% 19.85/2.99      inference(superposition,[status(thm)],[c_1379,c_2225]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_5559,plain,
% 19.85/2.99      ( k2_pre_topc(sK1,sK3) = sK3
% 19.85/2.99      | k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = k2_pre_topc(sK0,sK2) ),
% 19.85/2.99      inference(superposition,[status(thm)],[c_4585,c_5550]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_15,plain,
% 19.85/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.85/2.99      | ~ l1_pre_topc(X1)
% 19.85/2.99      | k2_pre_topc(X1,k1_tops_1(X1,k2_pre_topc(X1,k1_tops_1(X1,X0)))) = k2_pre_topc(X1,k1_tops_1(X1,X0)) ),
% 19.85/2.99      inference(cnf_transformation,[],[f57]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_484,plain,
% 19.85/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.85/2.99      | k2_pre_topc(X1,k1_tops_1(X1,k2_pre_topc(X1,k1_tops_1(X1,X0)))) = k2_pre_topc(X1,k1_tops_1(X1,X0))
% 19.85/2.99      | sK0 != X1 ),
% 19.85/2.99      inference(resolution_lifted,[status(thm)],[c_15,c_25]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_485,plain,
% 19.85/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.85/2.99      | k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,X0)))) = k2_pre_topc(sK0,k1_tops_1(sK0,X0)) ),
% 19.85/2.99      inference(unflattening,[status(thm)],[c_484]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_1365,plain,
% 19.85/2.99      ( k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,X0)))) = k2_pre_topc(sK0,k1_tops_1(sK0,X0))
% 19.85/2.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 19.85/2.99      inference(predicate_to_equality,[status(thm)],[c_485]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_3210,plain,
% 19.85/2.99      ( k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2)))) = k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) ),
% 19.85/2.99      inference(superposition,[status(thm)],[c_1379,c_1365]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_6014,plain,
% 19.85/2.99      ( k2_pre_topc(sK1,sK3) = sK3
% 19.85/2.99      | k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK2))) = k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) ),
% 19.85/2.99      inference(superposition,[status(thm)],[c_5559,c_3210]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_625,plain,
% 19.85/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.85/2.99      | r1_tarski(X0,k2_pre_topc(X1,X0))
% 19.85/2.99      | sK0 != X1 ),
% 19.85/2.99      inference(resolution_lifted,[status(thm)],[c_5,c_25]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_626,plain,
% 19.85/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.85/2.99      | r1_tarski(X0,k2_pre_topc(sK0,X0)) ),
% 19.85/2.99      inference(unflattening,[status(thm)],[c_625]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_1356,plain,
% 19.85/2.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 19.85/2.99      | r1_tarski(X0,k2_pre_topc(sK0,X0)) = iProver_top ),
% 19.85/2.99      inference(predicate_to_equality,[status(thm)],[c_626]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_2227,plain,
% 19.85/2.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 19.85/2.99      | r1_tarski(k1_tops_1(sK0,X0),k2_pre_topc(sK0,k1_tops_1(sK0,X0))) = iProver_top ),
% 19.85/2.99      inference(superposition,[status(thm)],[c_1363,c_1356]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_5318,plain,
% 19.85/2.99      ( k2_pre_topc(sK0,k1_tops_1(sK0,X0)) = k1_tops_1(sK0,X0)
% 19.85/2.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 19.85/2.99      | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,X0)),k1_tops_1(sK0,X0)) != iProver_top ),
% 19.85/2.99      inference(superposition,[status(thm)],[c_2227,c_1388]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_7138,plain,
% 19.85/2.99      ( k2_pre_topc(sK1,sK3) = sK3
% 19.85/2.99      | k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK2))) = k1_tops_1(sK0,k2_pre_topc(sK0,sK2))
% 19.85/2.99      | m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 19.85/2.99      | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_pre_topc(sK0,sK2))) != iProver_top ),
% 19.85/2.99      inference(superposition,[status(thm)],[c_6014,c_5318]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_18,negated_conjecture,
% 19.85/2.99      ( v4_pre_topc(sK3,sK1)
% 19.85/2.99      | ~ v4_pre_topc(sK2,sK0)
% 19.85/2.99      | ~ v4_tops_1(sK2,sK0) ),
% 19.85/2.99      inference(cnf_transformation,[],[f66]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_35,plain,
% 19.85/2.99      ( v4_pre_topc(sK3,sK1) = iProver_top
% 19.85/2.99      | v4_pre_topc(sK2,sK0) != iProver_top
% 19.85/2.99      | v4_tops_1(sK2,sK0) != iProver_top ),
% 19.85/2.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_13,plain,
% 19.85/2.99      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
% 19.85/2.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 19.85/2.99      | ~ v2_pre_topc(X0)
% 19.85/2.99      | ~ l1_pre_topc(X0) ),
% 19.85/2.99      inference(cnf_transformation,[],[f55]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_26,negated_conjecture,
% 19.85/2.99      ( v2_pre_topc(sK0) ),
% 19.85/2.99      inference(cnf_transformation,[],[f58]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_286,plain,
% 19.85/2.99      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
% 19.85/2.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 19.85/2.99      | ~ l1_pre_topc(X0)
% 19.85/2.99      | sK0 != X0 ),
% 19.85/2.99      inference(resolution_lifted,[status(thm)],[c_13,c_26]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_287,plain,
% 19.85/2.99      ( v4_pre_topc(k2_pre_topc(sK0,X0),sK0)
% 19.85/2.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.85/2.99      | ~ l1_pre_topc(sK0) ),
% 19.85/2.99      inference(unflattening,[status(thm)],[c_286]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_291,plain,
% 19.85/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.85/2.99      | v4_pre_topc(k2_pre_topc(sK0,X0),sK0) ),
% 19.85/2.99      inference(global_propositional_subsumption,
% 19.85/2.99                [status(thm)],
% 19.85/2.99                [c_287,c_25]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_292,plain,
% 19.85/2.99      ( v4_pre_topc(k2_pre_topc(sK0,X0),sK0)
% 19.85/2.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 19.85/2.99      inference(renaming,[status(thm)],[c_291]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_1378,plain,
% 19.85/2.99      ( v4_pre_topc(k2_pre_topc(sK0,X0),sK0) = iProver_top
% 19.85/2.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 19.85/2.99      inference(predicate_to_equality,[status(thm)],[c_292]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_2226,plain,
% 19.85/2.99      ( v4_pre_topc(k2_pre_topc(sK0,k1_tops_1(sK0,X0)),sK0) = iProver_top
% 19.85/2.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 19.85/2.99      inference(superposition,[status(thm)],[c_1363,c_1378]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_5136,plain,
% 19.85/2.99      ( v4_pre_topc(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),sK0) = iProver_top
% 19.85/2.99      | m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 19.85/2.99      inference(superposition,[status(thm)],[c_3210,c_2226]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_30,plain,
% 19.85/2.99      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 19.85/2.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_1486,plain,
% 19.85/2.99      ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 19.85/2.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 19.85/2.99      inference(instantiation,[status(thm)],[c_518]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_1487,plain,
% 19.85/2.99      ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 19.85/2.99      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 19.85/2.99      inference(predicate_to_equality,[status(thm)],[c_1486]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_1653,plain,
% 19.85/2.99      ( v4_pre_topc(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),sK0)
% 19.85/2.99      | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 19.85/2.99      inference(instantiation,[status(thm)],[c_292]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_1654,plain,
% 19.85/2.99      ( v4_pre_topc(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),sK0) = iProver_top
% 19.85/2.99      | m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 19.85/2.99      inference(predicate_to_equality,[status(thm)],[c_1653]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_6379,plain,
% 19.85/2.99      ( v4_pre_topc(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),sK0) = iProver_top ),
% 19.85/2.99      inference(global_propositional_subsumption,
% 19.85/2.99                [status(thm)],
% 19.85/2.99                [c_5136,c_30,c_1487,c_1654]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_6384,plain,
% 19.85/2.99      ( k2_pre_topc(sK1,sK3) = sK3 | v4_pre_topc(sK2,sK0) = iProver_top ),
% 19.85/2.99      inference(superposition,[status(thm)],[c_4585,c_6379]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_7,plain,
% 19.85/2.99      ( v4_tops_1(X0,X1)
% 19.85/2.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.85/2.99      | ~ r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
% 19.85/2.99      | ~ r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
% 19.85/2.99      | ~ l1_pre_topc(X1) ),
% 19.85/2.99      inference(cnf_transformation,[],[f51]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_589,plain,
% 19.85/2.99      ( v4_tops_1(X0,X1)
% 19.85/2.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.85/2.99      | ~ r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
% 19.85/2.99      | ~ r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
% 19.85/2.99      | sK0 != X1 ),
% 19.85/2.99      inference(resolution_lifted,[status(thm)],[c_7,c_25]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_590,plain,
% 19.85/2.99      ( v4_tops_1(X0,sK0)
% 19.85/2.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.85/2.99      | ~ r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,X0)))
% 19.85/2.99      | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X0) ),
% 19.85/2.99      inference(unflattening,[status(thm)],[c_589]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_1358,plain,
% 19.85/2.99      ( v4_tops_1(X0,sK0) = iProver_top
% 19.85/2.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 19.85/2.99      | r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,X0))) != iProver_top
% 19.85/2.99      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X0) != iProver_top ),
% 19.85/2.99      inference(predicate_to_equality,[status(thm)],[c_590]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_5567,plain,
% 19.85/2.99      ( v4_tops_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),sK0) = iProver_top
% 19.85/2.99      | m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 19.85/2.99      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))),k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) != iProver_top
% 19.85/2.99      | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))))) != iProver_top ),
% 19.85/2.99      inference(superposition,[status(thm)],[c_5550,c_1358]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_5574,plain,
% 19.85/2.99      ( v4_tops_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),sK0) = iProver_top
% 19.85/2.99      | m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 19.85/2.99      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))),k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) != iProver_top
% 19.85/2.99      | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) != iProver_top ),
% 19.85/2.99      inference(light_normalisation,[status(thm)],[c_5567,c_3210]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_3,plain,
% 19.85/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.85/2.99      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 19.85/2.99      | ~ l1_pre_topc(X1) ),
% 19.85/2.99      inference(cnf_transformation,[],[f45]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_649,plain,
% 19.85/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.85/2.99      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 19.85/2.99      | sK0 != X1 ),
% 19.85/2.99      inference(resolution_lifted,[status(thm)],[c_3,c_25]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_650,plain,
% 19.85/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.85/2.99      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 19.85/2.99      inference(unflattening,[status(thm)],[c_649]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_1651,plain,
% 19.85/2.99      ( ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 19.85/2.99      | m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 19.85/2.99      inference(instantiation,[status(thm)],[c_650]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_1658,plain,
% 19.85/2.99      ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 19.85/2.99      | m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 19.85/2.99      inference(predicate_to_equality,[status(thm)],[c_1651]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_6,plain,
% 19.85/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.85/2.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 19.85/2.99      | ~ r1_tarski(X0,X2)
% 19.85/2.99      | r1_tarski(k2_pre_topc(X1,X0),k2_pre_topc(X1,X2))
% 19.85/2.99      | ~ l1_pre_topc(X1) ),
% 19.85/2.99      inference(cnf_transformation,[],[f48]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_607,plain,
% 19.85/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.85/2.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 19.85/2.99      | ~ r1_tarski(X0,X2)
% 19.85/2.99      | r1_tarski(k2_pre_topc(X1,X0),k2_pre_topc(X1,X2))
% 19.85/2.99      | sK0 != X1 ),
% 19.85/2.99      inference(resolution_lifted,[status(thm)],[c_6,c_25]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_608,plain,
% 19.85/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.85/2.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.85/2.99      | ~ r1_tarski(X0,X1)
% 19.85/2.99      | r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,X1)) ),
% 19.85/2.99      inference(unflattening,[status(thm)],[c_607]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_1645,plain,
% 19.85/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.85/2.99      | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 19.85/2.99      | ~ r1_tarski(k1_tops_1(sK0,sK2),X0)
% 19.85/2.99      | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),k2_pre_topc(sK0,X0)) ),
% 19.85/2.99      inference(instantiation,[status(thm)],[c_608]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_2475,plain,
% 19.85/2.99      ( ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 19.85/2.99      | ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK2))
% 19.85/2.99      | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) ),
% 19.85/2.99      inference(instantiation,[status(thm)],[c_1645]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_2476,plain,
% 19.85/2.99      ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 19.85/2.99      | r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK2)) != iProver_top
% 19.85/2.99      | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) = iProver_top ),
% 19.85/2.99      inference(predicate_to_equality,[status(thm)],[c_2475]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_3612,plain,
% 19.85/2.99      ( r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK2)) ),
% 19.85/2.99      inference(instantiation,[status(thm)],[c_2]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_3613,plain,
% 19.85/2.99      ( r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK2)) = iProver_top ),
% 19.85/2.99      inference(predicate_to_equality,[status(thm)],[c_3612]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_5317,plain,
% 19.85/2.99      ( m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 19.85/2.99      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))),k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) = iProver_top ),
% 19.85/2.99      inference(superposition,[status(thm)],[c_3210,c_2227]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_53705,plain,
% 19.85/2.99      ( v4_tops_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),sK0) = iProver_top ),
% 19.85/2.99      inference(global_propositional_subsumption,
% 19.85/2.99                [status(thm)],
% 19.85/2.99                [c_5574,c_30,c_1487,c_1658,c_2476,c_3613,c_5317]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_53710,plain,
% 19.85/2.99      ( k2_pre_topc(sK1,sK3) = sK3 | v4_tops_1(sK2,sK0) = iProver_top ),
% 19.85/2.99      inference(superposition,[status(thm)],[c_4585,c_53705]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_53734,plain,
% 19.85/2.99      ( k2_pre_topc(sK1,sK3) = sK3 ),
% 19.85/2.99      inference(global_propositional_subsumption,
% 19.85/2.99                [status(thm)],
% 19.85/2.99                [c_7138,c_35,c_4476,c_6384,c_53710]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_460,plain,
% 19.85/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.85/2.99      | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0)
% 19.85/2.99      | sK1 != X1 ),
% 19.85/2.99      inference(resolution_lifted,[status(thm)],[c_4,c_24]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_461,plain,
% 19.85/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 19.85/2.99      | k2_pre_topc(sK1,k2_pre_topc(sK1,X0)) = k2_pre_topc(sK1,X0) ),
% 19.85/2.99      inference(unflattening,[status(thm)],[c_460]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_1367,plain,
% 19.85/2.99      ( k2_pre_topc(sK1,k2_pre_topc(sK1,X0)) = k2_pre_topc(sK1,X0)
% 19.85/2.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 19.85/2.99      inference(predicate_to_equality,[status(thm)],[c_461]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_2500,plain,
% 19.85/2.99      ( k2_pre_topc(sK1,k2_pre_topc(sK1,sK3)) = k2_pre_topc(sK1,sK3) ),
% 19.85/2.99      inference(superposition,[status(thm)],[c_1380,c_1367]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_9,plain,
% 19.85/2.99      ( ~ v4_tops_1(X0,X1)
% 19.85/2.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.85/2.99      | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
% 19.85/2.99      | ~ l1_pre_topc(X1) ),
% 19.85/2.99      inference(cnf_transformation,[],[f49]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_382,plain,
% 19.85/2.99      ( ~ v4_tops_1(X0,X1)
% 19.85/2.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.85/2.99      | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
% 19.85/2.99      | sK1 != X1 ),
% 19.85/2.99      inference(resolution_lifted,[status(thm)],[c_9,c_24]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_383,plain,
% 19.85/2.99      ( ~ v4_tops_1(X0,sK1)
% 19.85/2.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 19.85/2.99      | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,X0)),X0) ),
% 19.85/2.99      inference(unflattening,[status(thm)],[c_382]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_1372,plain,
% 19.85/2.99      ( v4_tops_1(X0,sK1) != iProver_top
% 19.85/2.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 19.85/2.99      | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,X0)),X0) = iProver_top ),
% 19.85/2.99      inference(predicate_to_equality,[status(thm)],[c_383]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_430,plain,
% 19.85/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.85/2.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 19.85/2.99      | ~ r1_tarski(X0,X2)
% 19.85/2.99      | r1_tarski(k2_pre_topc(X1,X0),k2_pre_topc(X1,X2))
% 19.85/2.99      | sK1 != X1 ),
% 19.85/2.99      inference(resolution_lifted,[status(thm)],[c_6,c_24]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_431,plain,
% 19.85/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 19.85/2.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 19.85/2.99      | ~ r1_tarski(X0,X1)
% 19.85/2.99      | r1_tarski(k2_pre_topc(sK1,X0),k2_pre_topc(sK1,X1)) ),
% 19.85/2.99      inference(unflattening,[status(thm)],[c_430]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_1369,plain,
% 19.85/2.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 19.85/2.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 19.85/2.99      | r1_tarski(X0,X1) != iProver_top
% 19.85/2.99      | r1_tarski(k2_pre_topc(sK1,X0),k2_pre_topc(sK1,X1)) = iProver_top ),
% 19.85/2.99      inference(predicate_to_equality,[status(thm)],[c_431]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_8,plain,
% 19.85/2.99      ( ~ v4_tops_1(X0,X1)
% 19.85/2.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.85/2.99      | r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
% 19.85/2.99      | ~ l1_pre_topc(X1) ),
% 19.85/2.99      inference(cnf_transformation,[],[f50]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_397,plain,
% 19.85/2.99      ( ~ v4_tops_1(X0,X1)
% 19.85/2.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.85/2.99      | r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
% 19.85/2.99      | sK1 != X1 ),
% 19.85/2.99      inference(resolution_lifted,[status(thm)],[c_8,c_24]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_398,plain,
% 19.85/2.99      ( ~ v4_tops_1(X0,sK1)
% 19.85/2.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 19.85/2.99      | r1_tarski(X0,k2_pre_topc(sK1,k1_tops_1(sK1,X0))) ),
% 19.85/2.99      inference(unflattening,[status(thm)],[c_397]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_1371,plain,
% 19.85/2.99      ( v4_tops_1(X0,sK1) != iProver_top
% 19.85/2.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 19.85/2.99      | r1_tarski(X0,k2_pre_topc(sK1,k1_tops_1(sK1,X0))) = iProver_top ),
% 19.85/2.99      inference(predicate_to_equality,[status(thm)],[c_398]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_3600,plain,
% 19.85/2.99      ( k2_pre_topc(sK1,k1_tops_1(sK1,X0)) = X0
% 19.85/2.99      | v4_tops_1(X0,sK1) != iProver_top
% 19.85/2.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 19.85/2.99      | r1_tarski(k2_pre_topc(sK1,k1_tops_1(sK1,X0)),X0) != iProver_top ),
% 19.85/2.99      inference(superposition,[status(thm)],[c_1371,c_1388]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_4809,plain,
% 19.85/2.99      ( k2_pre_topc(sK1,k1_tops_1(sK1,k2_pre_topc(sK1,X0))) = k2_pre_topc(sK1,X0)
% 19.85/2.99      | v4_tops_1(k2_pre_topc(sK1,X0),sK1) != iProver_top
% 19.85/2.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 19.85/2.99      | m1_subset_1(k1_tops_1(sK1,k2_pre_topc(sK1,X0)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 19.85/2.99      | m1_subset_1(k2_pre_topc(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 19.85/2.99      | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,X0)),X0) != iProver_top ),
% 19.85/2.99      inference(superposition,[status(thm)],[c_1369,c_3600]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_472,plain,
% 19.85/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.85/2.99      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 19.85/2.99      | sK1 != X1 ),
% 19.85/2.99      inference(resolution_lifted,[status(thm)],[c_3,c_24]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_473,plain,
% 19.85/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 19.85/2.99      | m1_subset_1(k2_pre_topc(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 19.85/2.99      inference(unflattening,[status(thm)],[c_472]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_474,plain,
% 19.85/2.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 19.85/2.99      | m1_subset_1(k2_pre_topc(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 19.85/2.99      inference(predicate_to_equality,[status(thm)],[c_473]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_340,plain,
% 19.85/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.85/2.99      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 19.85/2.99      | sK1 != X1 ),
% 19.85/2.99      inference(resolution_lifted,[status(thm)],[c_12,c_24]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_341,plain,
% 19.85/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 19.85/2.99      | m1_subset_1(k1_tops_1(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 19.85/2.99      inference(unflattening,[status(thm)],[c_340]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_21792,plain,
% 19.85/2.99      ( m1_subset_1(k1_tops_1(sK1,k2_pre_topc(sK1,X0)),k1_zfmisc_1(u1_struct_0(sK1)))
% 19.85/2.99      | ~ m1_subset_1(k2_pre_topc(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 19.85/2.99      inference(instantiation,[status(thm)],[c_341]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_21793,plain,
% 19.85/2.99      ( m1_subset_1(k1_tops_1(sK1,k2_pre_topc(sK1,X0)),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 19.85/2.99      | m1_subset_1(k2_pre_topc(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 19.85/3.00      inference(predicate_to_equality,[status(thm)],[c_21792]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_38575,plain,
% 19.85/3.00      ( k2_pre_topc(sK1,k1_tops_1(sK1,k2_pre_topc(sK1,X0))) = k2_pre_topc(sK1,X0)
% 19.85/3.00      | v4_tops_1(k2_pre_topc(sK1,X0),sK1) != iProver_top
% 19.85/3.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 19.85/3.00      | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,X0)),X0) != iProver_top ),
% 19.85/3.00      inference(global_propositional_subsumption,
% 19.85/3.00                [status(thm)],
% 19.85/3.00                [c_4809,c_474,c_21793]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_38581,plain,
% 19.85/3.00      ( k2_pre_topc(sK1,k1_tops_1(sK1,k2_pre_topc(sK1,X0))) = k2_pre_topc(sK1,X0)
% 19.85/3.00      | v4_tops_1(X0,sK1) != iProver_top
% 19.85/3.00      | v4_tops_1(k2_pre_topc(sK1,X0),sK1) != iProver_top
% 19.85/3.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 19.85/3.00      inference(superposition,[status(thm)],[c_1372,c_38575]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_39186,plain,
% 19.85/3.00      ( k2_pre_topc(sK1,k1_tops_1(sK1,k2_pre_topc(sK1,k2_pre_topc(sK1,sK3)))) = k2_pre_topc(sK1,k2_pre_topc(sK1,sK3))
% 19.85/3.00      | v4_tops_1(k2_pre_topc(sK1,sK3),sK1) != iProver_top
% 19.85/3.00      | m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 19.85/3.00      inference(superposition,[status(thm)],[c_2500,c_38581]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_39213,plain,
% 19.85/3.00      ( k2_pre_topc(sK1,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) = k2_pre_topc(sK1,sK3)
% 19.85/3.00      | v4_tops_1(k2_pre_topc(sK1,sK3),sK1) != iProver_top
% 19.85/3.00      | m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 19.85/3.00      inference(light_normalisation,[status(thm)],[c_39186,c_2500]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_31,plain,
% 19.85/3.00      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 19.85/3.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_1482,plain,
% 19.85/3.00      ( m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 19.85/3.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 19.85/3.00      inference(instantiation,[status(thm)],[c_473]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_1483,plain,
% 19.85/3.00      ( m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 19.85/3.00      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 19.85/3.00      inference(predicate_to_equality,[status(thm)],[c_1482]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_3606,plain,
% 19.85/3.00      ( v4_tops_1(k2_pre_topc(sK1,sK3),sK1) != iProver_top
% 19.85/3.00      | m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 19.85/3.00      | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),k2_pre_topc(sK1,sK3)) = iProver_top ),
% 19.85/3.00      inference(superposition,[status(thm)],[c_2500,c_1372]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_38583,plain,
% 19.85/3.00      ( k2_pre_topc(sK1,k1_tops_1(sK1,k2_pre_topc(sK1,k2_pre_topc(sK1,sK3)))) = k2_pre_topc(sK1,k2_pre_topc(sK1,sK3))
% 19.85/3.00      | v4_tops_1(k2_pre_topc(sK1,k2_pre_topc(sK1,sK3)),sK1) != iProver_top
% 19.85/3.00      | m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 19.85/3.00      | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),k2_pre_topc(sK1,sK3)) != iProver_top ),
% 19.85/3.00      inference(superposition,[status(thm)],[c_2500,c_38575]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_38610,plain,
% 19.85/3.00      ( k2_pre_topc(sK1,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) = k2_pre_topc(sK1,sK3)
% 19.85/3.00      | v4_tops_1(k2_pre_topc(sK1,sK3),sK1) != iProver_top
% 19.85/3.00      | m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 19.85/3.00      | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),k2_pre_topc(sK1,sK3)) != iProver_top ),
% 19.85/3.00      inference(light_normalisation,[status(thm)],[c_38583,c_2500]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_39217,plain,
% 19.85/3.00      ( v4_tops_1(k2_pre_topc(sK1,sK3),sK1) != iProver_top
% 19.85/3.00      | k2_pre_topc(sK1,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) = k2_pre_topc(sK1,sK3) ),
% 19.85/3.00      inference(global_propositional_subsumption,
% 19.85/3.00                [status(thm)],
% 19.85/3.00                [c_39213,c_31,c_1483,c_3606,c_38610]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_39218,plain,
% 19.85/3.00      ( k2_pre_topc(sK1,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) = k2_pre_topc(sK1,sK3)
% 19.85/3.00      | v4_tops_1(k2_pre_topc(sK1,sK3),sK1) != iProver_top ),
% 19.85/3.00      inference(renaming,[status(thm)],[c_39217]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_53758,plain,
% 19.85/3.00      ( k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) = sK3
% 19.85/3.00      | v4_tops_1(sK3,sK1) != iProver_top ),
% 19.85/3.00      inference(demodulation,[status(thm)],[c_53734,c_39218]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_53794,plain,
% 19.85/3.00      ( ~ v4_tops_1(sK3,sK1)
% 19.85/3.00      | k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) = sK3 ),
% 19.85/3.00      inference(predicate_to_equality_rev,[status(thm)],[c_53758]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_766,plain,
% 19.85/3.00      ( ~ v4_pre_topc(X0,X1) | v4_pre_topc(X2,X3) | X2 != X0 | X3 != X1 ),
% 19.85/3.00      theory(equality) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_1457,plain,
% 19.85/3.00      ( ~ v4_pre_topc(X0,X1)
% 19.85/3.00      | v4_pre_topc(sK2,sK0)
% 19.85/3.00      | sK0 != X1
% 19.85/3.00      | sK2 != X0 ),
% 19.85/3.00      inference(instantiation,[status(thm)],[c_766]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_6439,plain,
% 19.85/3.00      ( ~ v4_pre_topc(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),X0)
% 19.85/3.00      | v4_pre_topc(sK2,sK0)
% 19.85/3.00      | sK0 != X0
% 19.85/3.00      | sK2 != k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) ),
% 19.85/3.00      inference(instantiation,[status(thm)],[c_1457]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_6441,plain,
% 19.85/3.00      ( ~ v4_pre_topc(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),sK0)
% 19.85/3.00      | v4_pre_topc(sK2,sK0)
% 19.85/3.00      | sK0 != sK0
% 19.85/3.00      | sK2 != k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) ),
% 19.85/3.00      inference(instantiation,[status(thm)],[c_6439]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_5588,plain,
% 19.85/3.00      ( v4_tops_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),sK0)
% 19.85/3.00      | ~ m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
% 19.85/3.00      | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))),k2_pre_topc(sK0,k1_tops_1(sK0,sK2)))
% 19.85/3.00      | ~ r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) ),
% 19.85/3.00      inference(predicate_to_equality_rev,[status(thm)],[c_5574]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_5320,plain,
% 19.85/3.00      ( ~ m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
% 19.85/3.00      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))),k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) ),
% 19.85/3.00      inference(predicate_to_equality_rev,[status(thm)],[c_5317]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_20,negated_conjecture,
% 19.85/3.00      ( v5_tops_1(sK2,sK0) | v4_tops_1(sK3,sK1) ),
% 19.85/3.00      inference(cnf_transformation,[],[f64]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_1382,plain,
% 19.85/3.00      ( v5_tops_1(sK2,sK0) = iProver_top
% 19.85/3.00      | v4_tops_1(sK3,sK1) = iProver_top ),
% 19.85/3.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_2915,plain,
% 19.85/3.00      ( k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = sK2
% 19.85/3.00      | v4_tops_1(sK3,sK1) = iProver_top ),
% 19.85/3.00      inference(superposition,[status(thm)],[c_1382,c_2784]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_757,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_1745,plain,
% 19.85/3.00      ( X0 != X1 | sK2 != X1 | sK2 = X0 ),
% 19.85/3.00      inference(instantiation,[status(thm)],[c_757]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_2254,plain,
% 19.85/3.00      ( X0 != sK2 | sK2 = X0 | sK2 != sK2 ),
% 19.85/3.00      inference(instantiation,[status(thm)],[c_1745]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_2643,plain,
% 19.85/3.00      ( k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) != sK2
% 19.85/3.00      | sK2 = k2_pre_topc(sK0,k1_tops_1(sK0,sK2))
% 19.85/3.00      | sK2 != sK2 ),
% 19.85/3.00      inference(instantiation,[status(thm)],[c_2254]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_756,plain,( X0 = X0 ),theory(equality) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_1993,plain,
% 19.85/3.00      ( sK2 = sK2 ),
% 19.85/3.00      inference(instantiation,[status(thm)],[c_756]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_1535,plain,
% 19.85/3.00      ( ~ v5_tops_1(sK2,sK0)
% 19.85/3.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.85/3.00      | k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = sK2 ),
% 19.85/3.00      inference(instantiation,[status(thm)],[c_530]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_10,plain,
% 19.85/3.00      ( v5_tops_1(X0,X1)
% 19.85/3.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.85/3.00      | ~ l1_pre_topc(X1)
% 19.85/3.00      | k2_pre_topc(X1,k1_tops_1(X1,X0)) != X0 ),
% 19.85/3.00      inference(cnf_transformation,[],[f53]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_367,plain,
% 19.85/3.00      ( v5_tops_1(X0,X1)
% 19.85/3.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.85/3.00      | k2_pre_topc(X1,k1_tops_1(X1,X0)) != X0
% 19.85/3.00      | sK1 != X1 ),
% 19.85/3.00      inference(resolution_lifted,[status(thm)],[c_10,c_24]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_368,plain,
% 19.85/3.00      ( v5_tops_1(X0,sK1)
% 19.85/3.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 19.85/3.00      | k2_pre_topc(sK1,k1_tops_1(sK1,X0)) != X0 ),
% 19.85/3.00      inference(unflattening,[status(thm)],[c_367]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_1525,plain,
% 19.85/3.00      ( v5_tops_1(sK3,sK1)
% 19.85/3.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 19.85/3.00      | k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) != sK3 ),
% 19.85/3.00      inference(instantiation,[status(thm)],[c_368]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_82,plain,
% 19.85/3.00      ( ~ r1_tarski(sK0,sK0) | sK0 = sK0 ),
% 19.85/3.00      inference(instantiation,[status(thm)],[c_0]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_78,plain,
% 19.85/3.00      ( r1_tarski(sK0,sK0) ),
% 19.85/3.00      inference(instantiation,[status(thm)],[c_2]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_16,negated_conjecture,
% 19.85/3.00      ( ~ v4_pre_topc(sK2,sK0)
% 19.85/3.00      | ~ v5_tops_1(sK3,sK1)
% 19.85/3.00      | ~ v4_tops_1(sK2,sK0) ),
% 19.85/3.00      inference(cnf_transformation,[],[f68]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_17,negated_conjecture,
% 19.85/3.00      ( ~ v4_pre_topc(sK2,sK0)
% 19.85/3.00      | v4_tops_1(sK3,sK1)
% 19.85/3.00      | ~ v4_tops_1(sK2,sK0) ),
% 19.85/3.00      inference(cnf_transformation,[],[f67]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_19,negated_conjecture,
% 19.85/3.00      ( ~ v5_tops_1(sK3,sK1) | v5_tops_1(sK2,sK0) ),
% 19.85/3.00      inference(cnf_transformation,[],[f65]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(contradiction,plain,
% 19.85/3.00      ( $false ),
% 19.85/3.00      inference(minisat,
% 19.85/3.00                [status(thm)],
% 19.85/3.00                [c_60636,c_53794,c_53758,c_6441,c_5588,c_5320,c_3612,
% 19.85/3.00                 c_2915,c_2643,c_2475,c_1993,c_1651,c_1653,c_1535,c_1525,
% 19.85/3.00                 c_1486,c_82,c_78,c_16,c_17,c_19,c_22,c_23]) ).
% 19.85/3.00  
% 19.85/3.00  
% 19.85/3.00  % SZS output end CNFRefutation for theBenchmark.p
% 19.85/3.00  
% 19.85/3.00  ------                               Statistics
% 19.85/3.00  
% 19.85/3.00  ------ General
% 19.85/3.00  
% 19.85/3.00  abstr_ref_over_cycles:                  0
% 19.85/3.00  abstr_ref_under_cycles:                 0
% 19.85/3.00  gc_basic_clause_elim:                   0
% 19.85/3.00  forced_gc_time:                         0
% 19.85/3.00  parsing_time:                           0.019
% 19.85/3.00  unif_index_cands_time:                  0.
% 19.85/3.00  unif_index_add_time:                    0.
% 19.85/3.00  orderings_time:                         0.
% 19.85/3.00  out_proof_time:                         0.021
% 19.85/3.00  total_time:                             2.133
% 19.85/3.00  num_of_symbols:                         46
% 19.85/3.00  num_of_terms:                           82033
% 19.85/3.00  
% 19.85/3.00  ------ Preprocessing
% 19.85/3.00  
% 19.85/3.00  num_of_splits:                          0
% 19.85/3.00  num_of_split_atoms:                     0
% 19.85/3.00  num_of_reused_defs:                     0
% 19.85/3.00  num_eq_ax_congr_red:                    2
% 19.85/3.00  num_of_sem_filtered_clauses:            1
% 19.85/3.00  num_of_subtypes:                        0
% 19.85/3.00  monotx_restored_types:                  0
% 19.85/3.00  sat_num_of_epr_types:                   0
% 19.85/3.00  sat_num_of_non_cyclic_types:            0
% 19.85/3.00  sat_guarded_non_collapsed_types:        0
% 19.85/3.00  num_pure_diseq_elim:                    0
% 19.85/3.00  simp_replaced_by:                       0
% 19.85/3.00  res_preprocessed:                       119
% 19.85/3.00  prep_upred:                             0
% 19.85/3.00  prep_unflattend:                        25
% 19.85/3.00  smt_new_axioms:                         0
% 19.85/3.00  pred_elim_cands:                        7
% 19.85/3.00  pred_elim:                              2
% 19.85/3.00  pred_elim_cl:                           -9
% 19.85/3.00  pred_elim_cycles:                       3
% 19.85/3.00  merged_defs:                            0
% 19.85/3.00  merged_defs_ncl:                        0
% 19.85/3.00  bin_hyper_res:                          0
% 19.85/3.00  prep_cycles:                            3
% 19.85/3.00  pred_elim_time:                         0.008
% 19.85/3.00  splitting_time:                         0.
% 19.85/3.00  sem_filter_time:                        0.
% 19.85/3.00  monotx_time:                            0.001
% 19.85/3.00  subtype_inf_time:                       0.
% 19.85/3.00  
% 19.85/3.00  ------ Problem properties
% 19.85/3.00  
% 19.85/3.00  clauses:                                35
% 19.85/3.00  conjectures:                            8
% 19.85/3.00  epr:                                    8
% 19.85/3.00  horn:                                   33
% 19.85/3.00  ground:                                 8
% 19.85/3.00  unary:                                  3
% 19.85/3.00  binary:                                 14
% 19.85/3.00  lits:                                   93
% 19.85/3.00  lits_eq:                                9
% 19.85/3.00  fd_pure:                                0
% 19.85/3.00  fd_pseudo:                              0
% 19.85/3.00  fd_cond:                                0
% 19.85/3.00  fd_pseudo_cond:                         1
% 19.85/3.00  ac_symbols:                             0
% 19.85/3.00  
% 19.85/3.00  ------ Propositional Solver
% 19.85/3.00  
% 19.85/3.00  prop_solver_calls:                      37
% 19.85/3.00  prop_fast_solver_calls:                 2997
% 19.85/3.00  smt_solver_calls:                       0
% 19.85/3.00  smt_fast_solver_calls:                  0
% 19.85/3.00  prop_num_of_clauses:                    21408
% 19.85/3.00  prop_preprocess_simplified:             37178
% 19.85/3.00  prop_fo_subsumed:                       179
% 19.85/3.00  prop_solver_time:                       0.
% 19.85/3.00  smt_solver_time:                        0.
% 19.85/3.00  smt_fast_solver_time:                   0.
% 19.85/3.00  prop_fast_solver_time:                  0.
% 19.85/3.00  prop_unsat_core_time:                   0.003
% 19.85/3.00  
% 19.85/3.00  ------ QBF
% 19.85/3.00  
% 19.85/3.00  qbf_q_res:                              0
% 19.85/3.00  qbf_num_tautologies:                    0
% 19.85/3.00  qbf_prep_cycles:                        0
% 19.85/3.00  
% 19.85/3.00  ------ BMC1
% 19.85/3.00  
% 19.85/3.00  bmc1_current_bound:                     -1
% 19.85/3.00  bmc1_last_solved_bound:                 -1
% 19.85/3.00  bmc1_unsat_core_size:                   -1
% 19.85/3.00  bmc1_unsat_core_parents_size:           -1
% 19.85/3.00  bmc1_merge_next_fun:                    0
% 19.85/3.00  bmc1_unsat_core_clauses_time:           0.
% 19.85/3.00  
% 19.85/3.00  ------ Instantiation
% 19.85/3.00  
% 19.85/3.00  inst_num_of_clauses:                    1183
% 19.85/3.00  inst_num_in_passive:                    89
% 19.85/3.00  inst_num_in_active:                     3393
% 19.85/3.00  inst_num_in_unprocessed:                593
% 19.85/3.00  inst_num_of_loops:                      3505
% 19.85/3.00  inst_num_of_learning_restarts:          1
% 19.85/3.00  inst_num_moves_active_passive:          107
% 19.85/3.00  inst_lit_activity:                      0
% 19.85/3.00  inst_lit_activity_moves:                4
% 19.85/3.00  inst_num_tautologies:                   0
% 19.85/3.00  inst_num_prop_implied:                  0
% 19.85/3.00  inst_num_existing_simplified:           0
% 19.85/3.00  inst_num_eq_res_simplified:             0
% 19.85/3.00  inst_num_child_elim:                    0
% 19.85/3.00  inst_num_of_dismatching_blockings:      16055
% 19.85/3.00  inst_num_of_non_proper_insts:           7920
% 19.85/3.00  inst_num_of_duplicates:                 0
% 19.85/3.00  inst_inst_num_from_inst_to_res:         0
% 19.85/3.00  inst_dismatching_checking_time:         0.
% 19.85/3.00  
% 19.85/3.00  ------ Resolution
% 19.85/3.00  
% 19.85/3.00  res_num_of_clauses:                     46
% 19.85/3.00  res_num_in_passive:                     46
% 19.85/3.00  res_num_in_active:                      0
% 19.85/3.00  res_num_of_loops:                       122
% 19.85/3.00  res_forward_subset_subsumed:            95
% 19.85/3.00  res_backward_subset_subsumed:           0
% 19.85/3.00  res_forward_subsumed:                   0
% 19.85/3.00  res_backward_subsumed:                  0
% 19.85/3.00  res_forward_subsumption_resolution:     0
% 19.85/3.00  res_backward_subsumption_resolution:    0
% 19.85/3.00  res_clause_to_clause_subsumption:       15843
% 19.85/3.00  res_orphan_elimination:                 0
% 19.85/3.00  res_tautology_del:                      325
% 19.85/3.00  res_num_eq_res_simplified:              0
% 19.85/3.00  res_num_sel_changes:                    0
% 19.85/3.00  res_moves_from_active_to_pass:          0
% 19.85/3.00  
% 19.85/3.00  ------ Superposition
% 19.85/3.00  
% 19.85/3.00  sup_time_total:                         0.
% 19.85/3.00  sup_time_generating:                    0.
% 19.85/3.00  sup_time_sim_full:                      0.
% 19.85/3.00  sup_time_sim_immed:                     0.
% 19.85/3.00  
% 19.85/3.00  sup_num_of_clauses:                     2094
% 19.85/3.00  sup_num_in_active:                      605
% 19.85/3.00  sup_num_in_passive:                     1489
% 19.85/3.00  sup_num_of_loops:                       700
% 19.85/3.00  sup_fw_superposition:                   4472
% 19.85/3.00  sup_bw_superposition:                   1759
% 19.85/3.00  sup_immediate_simplified:               3902
% 19.85/3.00  sup_given_eliminated:                   0
% 19.85/3.00  comparisons_done:                       0
% 19.85/3.00  comparisons_avoided:                    39
% 19.85/3.00  
% 19.85/3.00  ------ Simplifications
% 19.85/3.00  
% 19.85/3.00  
% 19.85/3.00  sim_fw_subset_subsumed:                 190
% 19.85/3.00  sim_bw_subset_subsumed:                 177
% 19.85/3.00  sim_fw_subsumed:                        611
% 19.85/3.00  sim_bw_subsumed:                        16
% 19.85/3.00  sim_fw_subsumption_res:                 0
% 19.85/3.00  sim_bw_subsumption_res:                 0
% 19.85/3.00  sim_tautology_del:                      252
% 19.85/3.00  sim_eq_tautology_del:                   2258
% 19.85/3.00  sim_eq_res_simp:                        0
% 19.85/3.00  sim_fw_demodulated:                     644
% 19.85/3.00  sim_bw_demodulated:                     56
% 19.85/3.00  sim_light_normalised:                   2979
% 19.85/3.00  sim_joinable_taut:                      0
% 19.85/3.00  sim_joinable_simp:                      0
% 19.85/3.00  sim_ac_normalised:                      0
% 19.85/3.00  sim_smt_subsumption:                    0
% 19.85/3.00  
%------------------------------------------------------------------------------
