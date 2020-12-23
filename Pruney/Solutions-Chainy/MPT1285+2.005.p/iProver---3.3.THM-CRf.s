%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:15:53 EST 2020

% Result     : Theorem 3.92s
% Output     : CNFRefutation 4.10s
% Verified   : 
% Statistics : Number of formulae       :  198 (4799 expanded)
%              Number of clauses        :  123 (1348 expanded)
%              Number of leaves         :   20 (1541 expanded)
%              Depth                    :   33
%              Number of atoms          :  722 (40809 expanded)
%              Number of equality atoms :  265 (2671 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
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

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f46,plain,(
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

fof(f45,plain,(
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

fof(f44,plain,(
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

fof(f43,plain,
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

fof(f47,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f34,f46,f45,f44,f43])).

fof(f72,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f47])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v6_tops_1(X1,X0)
          <=> v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v6_tops_1(X1,X0)
          <=> v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v6_tops_1(X1,X0)
              | ~ v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v6_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v6_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_tops_1(X1,X0)
              | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1 )
            & ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
              | ~ v5_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
      | ~ v5_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f70,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v6_tops_1(X1,X0)
          <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v6_tops_1(X1,X0)
          <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v6_tops_1(X1,X0)
              | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1 )
            & ( k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1
              | ~ v6_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v6_tops_1(X1,X0)
      | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f74,plain,
    ( v6_tops_1(sK2,sK0)
    | v3_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_tops_1(X1,X0)
          <=> ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_tops_1(X1,X0)
          <=> ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)
      | ~ v4_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f73,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f47])).

fof(f13,axiom,(
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

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f71,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f50,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f75,plain,
    ( v6_tops_1(sK2,sK0)
    | v4_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1
      | ~ v6_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f76,plain,
    ( v6_tops_1(sK2,sK0)
    | ~ v6_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f47])).

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

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

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

fof(f62,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f69,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f77,plain,
    ( ~ v4_tops_1(sK2,sK0)
    | ~ v3_pre_topc(sK2,sK0)
    | v3_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v4_tops_1(X1,X0)
      | ~ r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
      | ~ r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f81,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f48])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f78,plain,
    ( ~ v4_tops_1(sK2,sK0)
    | ~ v3_pre_topc(sK2,sK0)
    | v4_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f79,plain,
    ( ~ v4_tops_1(sK2,sK0)
    | ~ v3_pre_topc(sK2,sK0)
    | ~ v6_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_982,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_17,plain,
    ( ~ v6_tops_1(X0,X1)
    | v5_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_993,plain,
    ( v6_tops_1(X0,X1) != iProver_top
    | v5_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1007,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_10,plain,
    ( ~ v5_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k1_tops_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1000,plain,
    ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
    | v5_tops_1(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3876,plain,
    ( k2_pre_topc(X0,k1_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))) = k3_subset_1(u1_struct_0(X0),X1)
    | v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1007,c_1000])).

cnf(c_12660,plain,
    ( k2_pre_topc(X0,k1_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))) = k3_subset_1(u1_struct_0(X0),X1)
    | v6_tops_1(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_993,c_3876])).

cnf(c_12958,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK2))) = k3_subset_1(u1_struct_0(sK0),sK2)
    | v6_tops_1(sK2,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_982,c_12660])).

cnf(c_30,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1300,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1360,plain,
    ( ~ v6_tops_1(sK2,sK0)
    | v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK2),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_2229,plain,
    ( ~ v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK2),sK0)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK2))) = k3_subset_1(u1_struct_0(sK0),sK2) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_11,plain,
    ( v6_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,k2_pre_topc(X1,X0)) != X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2240,plain,
    ( v6_tops_1(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) != sK2 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_26,negated_conjecture,
    ( v3_pre_topc(sK3,sK1)
    | v6_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_984,plain,
    ( v3_pre_topc(sK3,sK1) = iProver_top
    | v6_tops_1(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_8,plain,
    ( ~ v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1002,plain,
    ( v4_tops_1(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1006,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_983,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_20,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_990,plain,
    ( v3_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,k1_tops_1(X1,X2)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2442,plain,
    ( v3_pre_topc(sK3,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top
    | r1_tarski(sK3,k1_tops_1(sK1,X0)) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_983,c_990])).

cnf(c_29,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_34,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_36,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_1741,plain,
    ( ~ v3_pre_topc(sK3,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(sK3,X0)
    | r1_tarski(sK3,k1_tops_1(sK1,X0))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_1750,plain,
    ( v3_pre_topc(sK3,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top
    | r1_tarski(sK3,k1_tops_1(sK1,X0)) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1741])).

cnf(c_3386,plain,
    ( r1_tarski(sK3,k1_tops_1(sK1,X0)) = iProver_top
    | r1_tarski(sK3,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v3_pre_topc(sK3,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2442,c_34,c_36,c_1750])).

cnf(c_3387,plain,
    ( v3_pre_topc(sK3,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top
    | r1_tarski(sK3,k1_tops_1(sK1,X0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_3386])).

cnf(c_3397,plain,
    ( v3_pre_topc(sK3,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,X0))) = iProver_top
    | r1_tarski(sK3,k2_pre_topc(sK1,X0)) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1006,c_3387])).

cnf(c_5549,plain,
    ( r1_tarski(sK3,k2_pre_topc(sK1,X0)) != iProver_top
    | r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,X0))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v3_pre_topc(sK3,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3397,c_34])).

cnf(c_5550,plain,
    ( v3_pre_topc(sK3,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,X0))) = iProver_top
    | r1_tarski(sK3,k2_pre_topc(sK1,X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5549])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1009,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_5559,plain,
    ( k1_tops_1(sK1,k2_pre_topc(sK1,X0)) = sK3
    | v3_pre_topc(sK3,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,X0)),sK3) != iProver_top
    | r1_tarski(sK3,k2_pre_topc(sK1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5550,c_1009])).

cnf(c_6162,plain,
    ( k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) = sK3
    | v3_pre_topc(sK3,sK1) != iProver_top
    | v4_tops_1(sK3,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(sK3,k2_pre_topc(sK1,sK3)) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1002,c_5559])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1309,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(sK3,k2_pre_topc(sK1,sK3))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1310,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(sK3,k2_pre_topc(sK1,sK3)) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1309])).

cnf(c_6917,plain,
    ( v4_tops_1(sK3,sK1) != iProver_top
    | v3_pre_topc(sK3,sK1) != iProver_top
    | k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6162,c_34,c_36,c_1310])).

cnf(c_6918,plain,
    ( k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) = sK3
    | v3_pre_topc(sK3,sK1) != iProver_top
    | v4_tops_1(sK3,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_6917])).

cnf(c_6924,plain,
    ( k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) = sK3
    | v6_tops_1(sK2,sK0) = iProver_top
    | v4_tops_1(sK3,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_984,c_6918])).

cnf(c_37,plain,
    ( v3_pre_topc(sK3,sK1) = iProver_top
    | v6_tops_1(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_25,negated_conjecture,
    ( v6_tops_1(sK2,sK0)
    | v4_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_38,plain,
    ( v6_tops_1(sK2,sK0) = iProver_top
    | v4_tops_1(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_7007,plain,
    ( v6_tops_1(sK2,sK0) = iProver_top
    | k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6924,c_38])).

cnf(c_7008,plain,
    ( k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) = sK3
    | v6_tops_1(sK2,sK0) = iProver_top ),
    inference(renaming,[status(thm)],[c_7007])).

cnf(c_12,plain,
    ( ~ v6_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,k2_pre_topc(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_998,plain,
    ( k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1
    | v6_tops_1(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2894,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = sK2
    | v6_tops_1(sK2,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_982,c_998])).

cnf(c_33,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_3377,plain,
    ( v6_tops_1(sK2,sK0) != iProver_top
    | k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2894,c_33])).

cnf(c_3378,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = sK2
    | v6_tops_1(sK2,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3377])).

cnf(c_7013,plain,
    ( k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) = sK3
    | k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_7008,c_3378])).

cnf(c_999,plain,
    ( k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1
    | v6_tops_1(X1,X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_7534,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = sK2
    | v6_tops_1(sK3,sK1) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_7013,c_999])).

cnf(c_24,negated_conjecture,
    ( ~ v6_tops_1(sK3,sK1)
    | v6_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_39,plain,
    ( v6_tops_1(sK3,sK1) != iProver_top
    | v6_tops_1(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_7750,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7534,c_34,c_36,c_39,c_3378])).

cnf(c_13173,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK2))) = k3_subset_1(u1_struct_0(sK0),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12958,c_30,c_34,c_28,c_36,c_39,c_1300,c_1360,c_2229,c_2240,c_3378,c_7534])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_997,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_14,plain,
    ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_996,plain,
    ( v4_pre_topc(k2_pre_topc(X0,X1),X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2706,plain,
    ( v4_pre_topc(k2_pre_topc(X0,k1_tops_1(X0,X1)),X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_997,c_996])).

cnf(c_13188,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK2),sK0) = iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_13173,c_2706])).

cnf(c_31,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_32,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_35,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_1301,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1300])).

cnf(c_13859,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK2),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13188,c_32,c_33,c_35,c_1301])).

cnf(c_18,plain,
    ( v3_pre_topc(X0,X1)
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0(X1),X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_992,plain,
    ( v3_pre_topc(X0,X1) = iProver_top
    | v4_pre_topc(k3_subset_1(u1_struct_0(X1),X0),X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_13864,plain,
    ( v3_pre_topc(sK2,sK0) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_13859,c_992])).

cnf(c_14025,plain,
    ( v3_pre_topc(sK2,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13864,c_33,c_35])).

cnf(c_23,negated_conjecture,
    ( v3_pre_topc(sK3,sK1)
    | ~ v3_pre_topc(sK2,sK0)
    | ~ v4_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_987,plain,
    ( v3_pre_topc(sK3,sK1) = iProver_top
    | v3_pre_topc(sK2,sK0) != iProver_top
    | v4_tops_1(sK2,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_14031,plain,
    ( v3_pre_topc(sK3,sK1) = iProver_top
    | v4_tops_1(sK2,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_14025,c_987])).

cnf(c_40,plain,
    ( v3_pre_topc(sK3,sK1) = iProver_top
    | v3_pre_topc(sK2,sK0) != iProver_top
    | v4_tops_1(sK2,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_6,plain,
    ( v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
    | ~ r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1004,plain,
    ( v4_tops_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0))) != iProver_top
    | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_7759,plain,
    ( v4_tops_1(sK2,sK0) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) != iProver_top
    | r1_tarski(sK2,sK2) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7750,c_1004])).

cnf(c_428,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1773,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_428])).

cnf(c_430,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1465,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_tops_1(X2,k2_pre_topc(X2,X3)),X3)
    | X3 != X1
    | k1_tops_1(X2,k2_pre_topc(X2,X3)) != X0 ),
    inference(instantiation,[status(thm)],[c_430])).

cnf(c_3475,plain,
    ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK2)
    | ~ r1_tarski(sK2,X0)
    | k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) != sK2
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_1465])).

cnf(c_3994,plain,
    ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK2)
    | ~ r1_tarski(sK2,sK2)
    | k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) != sK2
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_3475])).

cnf(c_3996,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) != sK2
    | sK2 != sK2
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK2) = iProver_top
    | r1_tarski(sK2,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3994])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_3995,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_3998,plain,
    ( r1_tarski(sK2,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3995])).

cnf(c_7168,plain,
    ( v4_tops_1(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK2)
    | ~ r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2)))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_7169,plain,
    ( v4_tops_1(sK2,sK0) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK2) != iProver_top
    | r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7168])).

cnf(c_9106,plain,
    ( v4_tops_1(sK2,sK0) = iProver_top
    | r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7759,c_33,c_34,c_35,c_36,c_39,c_1773,c_3378,c_3996,c_3998,c_7169,c_7534])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_995,plain,
    ( k1_tops_1(X0,k1_tops_1(X0,X1)) = k1_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2665,plain,
    ( k1_tops_1(X0,k1_tops_1(X0,k2_pre_topc(X0,X1))) = k1_tops_1(X0,k2_pre_topc(X0,X1))
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1006,c_995])).

cnf(c_8453,plain,
    ( k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK2))) = k1_tops_1(sK0,k2_pre_topc(sK0,sK2))
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_982,c_2665])).

cnf(c_8456,plain,
    ( k1_tops_1(sK0,sK2) = sK2
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8453,c_7750])).

cnf(c_8802,plain,
    ( k1_tops_1(sK0,sK2) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8456,c_33])).

cnf(c_9110,plain,
    ( v4_tops_1(sK2,sK0) = iProver_top
    | r1_tarski(sK2,k2_pre_topc(sK0,sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9106,c_8802])).

cnf(c_1005,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(X1,X0)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1942,plain,
    ( r1_tarski(sK2,k2_pre_topc(sK0,sK2)) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_982,c_1005])).

cnf(c_1312,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK2,k2_pre_topc(sK0,sK2))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1313,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK2,k2_pre_topc(sK0,sK2)) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1312])).

cnf(c_2200,plain,
    ( r1_tarski(sK2,k2_pre_topc(sK0,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1942,c_33,c_35,c_1313])).

cnf(c_9113,plain,
    ( v4_tops_1(sK2,sK0) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_9110,c_2200])).

cnf(c_14141,plain,
    ( v3_pre_topc(sK3,sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14031,c_33,c_35,c_40,c_9113,c_13864])).

cnf(c_14146,plain,
    ( k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) = sK3
    | v4_tops_1(sK3,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_14141,c_6918])).

cnf(c_22,negated_conjecture,
    ( ~ v3_pre_topc(sK2,sK0)
    | v4_tops_1(sK3,sK1)
    | ~ v4_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_41,plain,
    ( v3_pre_topc(sK2,sK0) != iProver_top
    | v4_tops_1(sK3,sK1) = iProver_top
    | v4_tops_1(sK2,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_14258,plain,
    ( k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_14146,c_33,c_34,c_35,c_36,c_40,c_41,c_1310,c_6162,c_9113,c_13864])).

cnf(c_14276,plain,
    ( v6_tops_1(sK3,sK1) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_14258,c_999])).

cnf(c_21,negated_conjecture,
    ( ~ v3_pre_topc(sK2,sK0)
    | ~ v6_tops_1(sK3,sK1)
    | ~ v4_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_42,plain,
    ( v3_pre_topc(sK2,sK0) != iProver_top
    | v6_tops_1(sK3,sK1) != iProver_top
    | v4_tops_1(sK2,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14276,c_13864,c_9113,c_42,c_36,c_35,c_34,c_33])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : iproveropt_run.sh %d %s
% 0.11/0.32  % Computer   : n001.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 11:51:29 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  % Running in FOF mode
% 3.92/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.92/0.99  
% 3.92/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.92/0.99  
% 3.92/0.99  ------  iProver source info
% 3.92/0.99  
% 3.92/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.92/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.92/0.99  git: non_committed_changes: false
% 3.92/0.99  git: last_make_outside_of_git: false
% 3.92/0.99  
% 3.92/0.99  ------ 
% 3.92/0.99  ------ Parsing...
% 3.92/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.92/0.99  
% 3.92/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.92/0.99  
% 3.92/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.92/0.99  
% 3.92/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.92/0.99  ------ Proving...
% 3.92/0.99  ------ Problem Properties 
% 3.92/0.99  
% 3.92/0.99  
% 3.92/0.99  clauses                                 31
% 3.92/0.99  conjectures                             11
% 3.92/0.99  EPR                                     11
% 3.92/0.99  Horn                                    29
% 3.92/0.99  unary                                   6
% 3.92/0.99  binary                                  4
% 3.92/0.99  lits                                    93
% 3.92/0.99  lits eq                                 6
% 3.92/0.99  fd_pure                                 0
% 3.92/0.99  fd_pseudo                               0
% 3.92/0.99  fd_cond                                 0
% 3.92/0.99  fd_pseudo_cond                          1
% 3.92/0.99  AC symbols                              0
% 3.92/0.99  
% 3.92/0.99  ------ Input Options Time Limit: Unbounded
% 3.92/0.99  
% 3.92/0.99  
% 3.92/0.99  ------ 
% 3.92/0.99  Current options:
% 3.92/0.99  ------ 
% 3.92/0.99  
% 3.92/0.99  
% 3.92/0.99  
% 3.92/0.99  
% 3.92/0.99  ------ Proving...
% 3.92/0.99  
% 3.92/0.99  
% 3.92/0.99  % SZS status Theorem for theBenchmark.p
% 3.92/0.99  
% 3.92/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.92/0.99  
% 3.92/0.99  fof(f14,conjecture,(
% 3.92/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v6_tops_1(X2,X0) => (v4_tops_1(X2,X0) & v3_pre_topc(X2,X0))) & ((v4_tops_1(X3,X1) & v3_pre_topc(X3,X1)) => v6_tops_1(X3,X1)))))))),
% 3.92/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.92/0.99  
% 3.92/0.99  fof(f15,negated_conjecture,(
% 3.92/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v6_tops_1(X2,X0) => (v4_tops_1(X2,X0) & v3_pre_topc(X2,X0))) & ((v4_tops_1(X3,X1) & v3_pre_topc(X3,X1)) => v6_tops_1(X3,X1)))))))),
% 3.92/0.99    inference(negated_conjecture,[],[f14])).
% 3.92/0.99  
% 3.92/0.99  fof(f33,plain,(
% 3.92/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(X3,X1) & (v4_tops_1(X3,X1) & v3_pre_topc(X3,X1)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.92/0.99    inference(ennf_transformation,[],[f15])).
% 3.92/0.99  
% 3.92/0.99  fof(f34,plain,(
% 3.92/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.92/0.99    inference(flattening,[],[f33])).
% 3.92/0.99  
% 3.92/0.99  fof(f46,plain,(
% 3.92/0.99    ( ! [X2,X0,X1] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(sK3,X1) & v4_tops_1(sK3,X1) & v3_pre_topc(sK3,X1))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X1))))) )),
% 3.92/0.99    introduced(choice_axiom,[])).
% 3.92/0.99  
% 3.92/0.99  fof(f45,plain,(
% 3.92/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X3] : ((((~v4_tops_1(sK2,X0) | ~v3_pre_topc(sK2,X0)) & v6_tops_1(sK2,X0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.92/0.99    introduced(choice_axiom,[])).
% 3.92/0.99  
% 3.92/0.99  fof(f44,plain,(
% 3.92/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) => (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(X3,sK1) & v4_tops_1(X3,sK1) & v3_pre_topc(X3,sK1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(sK1))) )),
% 3.92/0.99    introduced(choice_axiom,[])).
% 3.92/0.99  
% 3.92/0.99  fof(f43,plain,(
% 3.92/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,sK0) | ~v3_pre_topc(X2,sK0)) & v6_tops_1(X2,sK0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 3.92/0.99    introduced(choice_axiom,[])).
% 3.92/0.99  
% 3.92/0.99  fof(f47,plain,(
% 3.92/0.99    ((((((~v4_tops_1(sK2,sK0) | ~v3_pre_topc(sK2,sK0)) & v6_tops_1(sK2,sK0)) | (~v6_tops_1(sK3,sK1) & v4_tops_1(sK3,sK1) & v3_pre_topc(sK3,sK1))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 3.92/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f34,f46,f45,f44,f43])).
% 3.92/0.99  
% 3.92/0.99  fof(f72,plain,(
% 3.92/0.99    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.92/0.99    inference(cnf_transformation,[],[f47])).
% 3.92/0.99  
% 3.92/0.99  fof(f11,axiom,(
% 3.92/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v6_tops_1(X1,X0) <=> v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 3.92/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.92/0.99  
% 3.92/0.99  fof(f29,plain,(
% 3.92/0.99    ! [X0] : (! [X1] : ((v6_tops_1(X1,X0) <=> v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.92/0.99    inference(ennf_transformation,[],[f11])).
% 3.92/0.99  
% 3.92/0.99  fof(f41,plain,(
% 3.92/0.99    ! [X0] : (! [X1] : (((v6_tops_1(X1,X0) | ~v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v6_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.92/0.99    inference(nnf_transformation,[],[f29])).
% 3.92/0.99  
% 3.92/0.99  fof(f64,plain,(
% 3.92/0.99    ( ! [X0,X1] : (v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v6_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.92/0.99    inference(cnf_transformation,[],[f41])).
% 3.92/0.99  
% 3.92/0.99  fof(f2,axiom,(
% 3.92/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 3.92/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.92/0.99  
% 3.92/0.99  fof(f16,plain,(
% 3.92/0.99    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.92/0.99    inference(ennf_transformation,[],[f2])).
% 3.92/0.99  
% 3.92/0.99  fof(f51,plain,(
% 3.92/0.99    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.92/0.99    inference(cnf_transformation,[],[f16])).
% 3.92/0.99  
% 3.92/0.99  fof(f6,axiom,(
% 3.92/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1)))),
% 3.92/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.92/0.99  
% 3.92/0.99  fof(f21,plain,(
% 3.92/0.99    ! [X0] : (! [X1] : ((v5_tops_1(X1,X0) <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.92/0.99    inference(ennf_transformation,[],[f6])).
% 3.92/0.99  
% 3.92/0.99  fof(f39,plain,(
% 3.92/0.99    ! [X0] : (! [X1] : (((v5_tops_1(X1,X0) | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1) & (k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 | ~v5_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.92/0.99    inference(nnf_transformation,[],[f21])).
% 3.92/0.99  
% 3.92/0.99  fof(f57,plain,(
% 3.92/0.99    ( ! [X0,X1] : (k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 | ~v5_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.92/0.99    inference(cnf_transformation,[],[f39])).
% 3.92/0.99  
% 3.92/0.99  fof(f70,plain,(
% 3.92/0.99    l1_pre_topc(sK0)),
% 3.92/0.99    inference(cnf_transformation,[],[f47])).
% 3.92/0.99  
% 3.92/0.99  fof(f7,axiom,(
% 3.92/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v6_tops_1(X1,X0) <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1)))),
% 3.92/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.92/0.99  
% 3.92/0.99  fof(f22,plain,(
% 3.92/0.99    ! [X0] : (! [X1] : ((v6_tops_1(X1,X0) <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.92/0.99    inference(ennf_transformation,[],[f7])).
% 3.92/0.99  
% 3.92/0.99  fof(f40,plain,(
% 3.92/0.99    ! [X0] : (! [X1] : (((v6_tops_1(X1,X0) | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1) & (k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 | ~v6_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.92/0.99    inference(nnf_transformation,[],[f22])).
% 3.92/0.99  
% 3.92/0.99  fof(f60,plain,(
% 3.92/0.99    ( ! [X0,X1] : (v6_tops_1(X1,X0) | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.92/0.99    inference(cnf_transformation,[],[f40])).
% 3.92/0.99  
% 3.92/0.99  fof(f74,plain,(
% 3.92/0.99    v6_tops_1(sK2,sK0) | v3_pre_topc(sK3,sK1)),
% 3.92/0.99    inference(cnf_transformation,[],[f47])).
% 3.92/0.99  
% 3.92/0.99  fof(f5,axiom,(
% 3.92/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)))))),
% 3.92/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.92/0.99  
% 3.92/0.99  fof(f20,plain,(
% 3.92/0.99    ! [X0] : (! [X1] : ((v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.92/0.99    inference(ennf_transformation,[],[f5])).
% 3.92/0.99  
% 3.92/0.99  fof(f37,plain,(
% 3.92/0.99    ! [X0] : (! [X1] : (((v4_tops_1(X1,X0) | (~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1))) & ((r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) | ~v4_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.92/0.99    inference(nnf_transformation,[],[f20])).
% 3.92/0.99  
% 3.92/0.99  fof(f38,plain,(
% 3.92/0.99    ! [X0] : (! [X1] : (((v4_tops_1(X1,X0) | ~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) & ((r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) | ~v4_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.92/0.99    inference(flattening,[],[f37])).
% 3.92/0.99  
% 3.92/0.99  fof(f54,plain,(
% 3.92/0.99    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) | ~v4_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.92/0.99    inference(cnf_transformation,[],[f38])).
% 3.92/0.99  
% 3.92/0.99  fof(f3,axiom,(
% 3.92/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.92/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.92/0.99  
% 3.92/0.99  fof(f17,plain,(
% 3.92/0.99    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.92/0.99    inference(ennf_transformation,[],[f3])).
% 3.92/0.99  
% 3.92/0.99  fof(f18,plain,(
% 3.92/0.99    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.92/0.99    inference(flattening,[],[f17])).
% 3.92/0.99  
% 3.92/0.99  fof(f52,plain,(
% 3.92/0.99    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.92/0.99    inference(cnf_transformation,[],[f18])).
% 3.92/0.99  
% 3.92/0.99  fof(f73,plain,(
% 3.92/0.99    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 3.92/0.99    inference(cnf_transformation,[],[f47])).
% 3.92/0.99  
% 3.92/0.99  fof(f13,axiom,(
% 3.92/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 3.92/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.92/0.99  
% 3.92/0.99  fof(f31,plain,(
% 3.92/0.99    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.92/0.99    inference(ennf_transformation,[],[f13])).
% 3.92/0.99  
% 3.92/0.99  fof(f32,plain,(
% 3.92/0.99    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.92/0.99    inference(flattening,[],[f31])).
% 3.92/0.99  
% 3.92/0.99  fof(f68,plain,(
% 3.92/0.99    ( ! [X2,X0,X1] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.92/0.99    inference(cnf_transformation,[],[f32])).
% 3.92/0.99  
% 3.92/0.99  fof(f71,plain,(
% 3.92/0.99    l1_pre_topc(sK1)),
% 3.92/0.99    inference(cnf_transformation,[],[f47])).
% 3.92/0.99  
% 3.92/0.99  fof(f1,axiom,(
% 3.92/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.92/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.92/0.99  
% 3.92/0.99  fof(f35,plain,(
% 3.92/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.92/0.99    inference(nnf_transformation,[],[f1])).
% 3.92/0.99  
% 3.92/0.99  fof(f36,plain,(
% 3.92/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.92/0.99    inference(flattening,[],[f35])).
% 3.92/0.99  
% 3.92/0.99  fof(f50,plain,(
% 3.92/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.92/0.99    inference(cnf_transformation,[],[f36])).
% 3.92/0.99  
% 3.92/0.99  fof(f4,axiom,(
% 3.92/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 3.92/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.92/0.99  
% 3.92/0.99  fof(f19,plain,(
% 3.92/0.99    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.92/0.99    inference(ennf_transformation,[],[f4])).
% 3.92/0.99  
% 3.92/0.99  fof(f53,plain,(
% 3.92/0.99    ( ! [X0,X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.92/0.99    inference(cnf_transformation,[],[f19])).
% 3.92/0.99  
% 3.92/0.99  fof(f75,plain,(
% 3.92/0.99    v6_tops_1(sK2,sK0) | v4_tops_1(sK3,sK1)),
% 3.92/0.99    inference(cnf_transformation,[],[f47])).
% 3.92/0.99  
% 3.92/0.99  fof(f59,plain,(
% 3.92/0.99    ( ! [X0,X1] : (k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 | ~v6_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.92/0.99    inference(cnf_transformation,[],[f40])).
% 3.92/0.99  
% 3.92/0.99  fof(f76,plain,(
% 3.92/0.99    v6_tops_1(sK2,sK0) | ~v6_tops_1(sK3,sK1)),
% 3.92/0.99    inference(cnf_transformation,[],[f47])).
% 3.92/0.99  
% 3.92/0.99  fof(f8,axiom,(
% 3.92/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.92/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.92/0.99  
% 3.92/0.99  fof(f23,plain,(
% 3.92/0.99    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.92/0.99    inference(ennf_transformation,[],[f8])).
% 3.92/0.99  
% 3.92/0.99  fof(f24,plain,(
% 3.92/0.99    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.92/0.99    inference(flattening,[],[f23])).
% 3.92/0.99  
% 3.92/0.99  fof(f61,plain,(
% 3.92/0.99    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.92/0.99    inference(cnf_transformation,[],[f24])).
% 3.92/0.99  
% 3.92/0.99  fof(f9,axiom,(
% 3.92/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 3.92/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.92/0.99  
% 3.92/0.99  fof(f25,plain,(
% 3.92/0.99    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.92/0.99    inference(ennf_transformation,[],[f9])).
% 3.92/0.99  
% 3.92/0.99  fof(f26,plain,(
% 3.92/0.99    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.92/0.99    inference(flattening,[],[f25])).
% 3.92/0.99  
% 3.92/0.99  fof(f62,plain,(
% 3.92/0.99    ( ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 4.10/0.99    inference(cnf_transformation,[],[f26])).
% 4.10/0.99  
% 4.10/0.99  fof(f69,plain,(
% 4.10/0.99    v2_pre_topc(sK0)),
% 4.10/0.99    inference(cnf_transformation,[],[f47])).
% 4.10/0.99  
% 4.10/0.99  fof(f12,axiom,(
% 4.10/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 4.10/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.10/0.99  
% 4.10/0.99  fof(f30,plain,(
% 4.10/0.99    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.10/0.99    inference(ennf_transformation,[],[f12])).
% 4.10/0.99  
% 4.10/0.99  fof(f42,plain,(
% 4.10/0.99    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.10/0.99    inference(nnf_transformation,[],[f30])).
% 4.10/0.99  
% 4.10/0.99  fof(f67,plain,(
% 4.10/0.99    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.10/0.99    inference(cnf_transformation,[],[f42])).
% 4.10/0.99  
% 4.10/0.99  fof(f77,plain,(
% 4.10/0.99    ~v4_tops_1(sK2,sK0) | ~v3_pre_topc(sK2,sK0) | v3_pre_topc(sK3,sK1)),
% 4.10/0.99    inference(cnf_transformation,[],[f47])).
% 4.10/0.99  
% 4.10/0.99  fof(f56,plain,(
% 4.10/0.99    ( ! [X0,X1] : (v4_tops_1(X1,X0) | ~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.10/0.99    inference(cnf_transformation,[],[f38])).
% 4.10/0.99  
% 4.10/0.99  fof(f48,plain,(
% 4.10/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 4.10/0.99    inference(cnf_transformation,[],[f36])).
% 4.10/0.99  
% 4.10/0.99  fof(f81,plain,(
% 4.10/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 4.10/0.99    inference(equality_resolution,[],[f48])).
% 4.10/0.99  
% 4.10/0.99  fof(f10,axiom,(
% 4.10/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)))),
% 4.10/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.10/0.99  
% 4.10/0.99  fof(f27,plain,(
% 4.10/0.99    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 4.10/0.99    inference(ennf_transformation,[],[f10])).
% 4.10/0.99  
% 4.10/0.99  fof(f28,plain,(
% 4.10/0.99    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 4.10/0.99    inference(flattening,[],[f27])).
% 4.10/0.99  
% 4.10/0.99  fof(f63,plain,(
% 4.10/0.99    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.10/0.99    inference(cnf_transformation,[],[f28])).
% 4.10/0.99  
% 4.10/0.99  fof(f78,plain,(
% 4.10/0.99    ~v4_tops_1(sK2,sK0) | ~v3_pre_topc(sK2,sK0) | v4_tops_1(sK3,sK1)),
% 4.10/0.99    inference(cnf_transformation,[],[f47])).
% 4.10/0.99  
% 4.10/0.99  fof(f79,plain,(
% 4.10/0.99    ~v4_tops_1(sK2,sK0) | ~v3_pre_topc(sK2,sK0) | ~v6_tops_1(sK3,sK1)),
% 4.10/0.99    inference(cnf_transformation,[],[f47])).
% 4.10/0.99  
% 4.10/0.99  cnf(c_28,negated_conjecture,
% 4.10/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 4.10/0.99      inference(cnf_transformation,[],[f72]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_982,plain,
% 4.10/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 4.10/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_17,plain,
% 4.10/0.99      ( ~ v6_tops_1(X0,X1)
% 4.10/0.99      | v5_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1)
% 4.10/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.10/0.99      | ~ l1_pre_topc(X1) ),
% 4.10/0.99      inference(cnf_transformation,[],[f64]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_993,plain,
% 4.10/0.99      ( v6_tops_1(X0,X1) != iProver_top
% 4.10/0.99      | v5_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1) = iProver_top
% 4.10/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 4.10/0.99      | l1_pre_topc(X1) != iProver_top ),
% 4.10/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_3,plain,
% 4.10/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 4.10/0.99      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 4.10/0.99      inference(cnf_transformation,[],[f51]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_1007,plain,
% 4.10/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 4.10/0.99      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 4.10/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_10,plain,
% 4.10/0.99      ( ~ v5_tops_1(X0,X1)
% 4.10/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.10/0.99      | ~ l1_pre_topc(X1)
% 4.10/0.99      | k2_pre_topc(X1,k1_tops_1(X1,X0)) = X0 ),
% 4.10/0.99      inference(cnf_transformation,[],[f57]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_1000,plain,
% 4.10/0.99      ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
% 4.10/0.99      | v5_tops_1(X1,X0) != iProver_top
% 4.10/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 4.10/0.99      | l1_pre_topc(X0) != iProver_top ),
% 4.10/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_3876,plain,
% 4.10/0.99      ( k2_pre_topc(X0,k1_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))) = k3_subset_1(u1_struct_0(X0),X1)
% 4.10/0.99      | v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) != iProver_top
% 4.10/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 4.10/0.99      | l1_pre_topc(X0) != iProver_top ),
% 4.10/0.99      inference(superposition,[status(thm)],[c_1007,c_1000]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_12660,plain,
% 4.10/0.99      ( k2_pre_topc(X0,k1_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))) = k3_subset_1(u1_struct_0(X0),X1)
% 4.10/0.99      | v6_tops_1(X1,X0) != iProver_top
% 4.10/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 4.10/0.99      | l1_pre_topc(X0) != iProver_top ),
% 4.10/0.99      inference(superposition,[status(thm)],[c_993,c_3876]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_12958,plain,
% 4.10/0.99      ( k2_pre_topc(sK0,k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK2))) = k3_subset_1(u1_struct_0(sK0),sK2)
% 4.10/0.99      | v6_tops_1(sK2,sK0) != iProver_top
% 4.10/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 4.10/0.99      inference(superposition,[status(thm)],[c_982,c_12660]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_30,negated_conjecture,
% 4.10/0.99      ( l1_pre_topc(sK0) ),
% 4.10/0.99      inference(cnf_transformation,[],[f70]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_1300,plain,
% 4.10/0.99      ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 4.10/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 4.10/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_1360,plain,
% 4.10/0.99      ( ~ v6_tops_1(sK2,sK0)
% 4.10/0.99      | v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK2),sK0)
% 4.10/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 4.10/0.99      | ~ l1_pre_topc(sK0) ),
% 4.10/0.99      inference(instantiation,[status(thm)],[c_17]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_2229,plain,
% 4.10/0.99      ( ~ v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK2),sK0)
% 4.10/0.99      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 4.10/0.99      | ~ l1_pre_topc(sK0)
% 4.10/0.99      | k2_pre_topc(sK0,k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK2))) = k3_subset_1(u1_struct_0(sK0),sK2) ),
% 4.10/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_11,plain,
% 4.10/0.99      ( v6_tops_1(X0,X1)
% 4.10/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.10/0.99      | ~ l1_pre_topc(X1)
% 4.10/0.99      | k1_tops_1(X1,k2_pre_topc(X1,X0)) != X0 ),
% 4.10/0.99      inference(cnf_transformation,[],[f60]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_2240,plain,
% 4.10/0.99      ( v6_tops_1(sK2,sK0)
% 4.10/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 4.10/0.99      | ~ l1_pre_topc(sK0)
% 4.10/0.99      | k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) != sK2 ),
% 4.10/0.99      inference(instantiation,[status(thm)],[c_11]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_26,negated_conjecture,
% 4.10/0.99      ( v3_pre_topc(sK3,sK1) | v6_tops_1(sK2,sK0) ),
% 4.10/0.99      inference(cnf_transformation,[],[f74]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_984,plain,
% 4.10/0.99      ( v3_pre_topc(sK3,sK1) = iProver_top
% 4.10/0.99      | v6_tops_1(sK2,sK0) = iProver_top ),
% 4.10/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_8,plain,
% 4.10/0.99      ( ~ v4_tops_1(X0,X1)
% 4.10/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.10/0.99      | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
% 4.10/0.99      | ~ l1_pre_topc(X1) ),
% 4.10/0.99      inference(cnf_transformation,[],[f54]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_1002,plain,
% 4.10/0.99      ( v4_tops_1(X0,X1) != iProver_top
% 4.10/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 4.10/0.99      | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0) = iProver_top
% 4.10/0.99      | l1_pre_topc(X1) != iProver_top ),
% 4.10/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_4,plain,
% 4.10/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.10/0.99      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 4.10/0.99      | ~ l1_pre_topc(X1) ),
% 4.10/0.99      inference(cnf_transformation,[],[f52]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_1006,plain,
% 4.10/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 4.10/0.99      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 4.10/0.99      | l1_pre_topc(X1) != iProver_top ),
% 4.10/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_27,negated_conjecture,
% 4.10/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 4.10/0.99      inference(cnf_transformation,[],[f73]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_983,plain,
% 4.10/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 4.10/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_20,plain,
% 4.10/0.99      ( ~ v3_pre_topc(X0,X1)
% 4.10/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.10/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 4.10/0.99      | ~ r1_tarski(X0,X2)
% 4.10/0.99      | r1_tarski(X0,k1_tops_1(X1,X2))
% 4.10/0.99      | ~ l1_pre_topc(X1) ),
% 4.10/0.99      inference(cnf_transformation,[],[f68]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_990,plain,
% 4.10/0.99      ( v3_pre_topc(X0,X1) != iProver_top
% 4.10/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 4.10/0.99      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 4.10/0.99      | r1_tarski(X0,X2) != iProver_top
% 4.10/0.99      | r1_tarski(X0,k1_tops_1(X1,X2)) = iProver_top
% 4.10/0.99      | l1_pre_topc(X1) != iProver_top ),
% 4.10/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_2442,plain,
% 4.10/0.99      ( v3_pre_topc(sK3,sK1) != iProver_top
% 4.10/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 4.10/0.99      | r1_tarski(sK3,X0) != iProver_top
% 4.10/0.99      | r1_tarski(sK3,k1_tops_1(sK1,X0)) = iProver_top
% 4.10/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 4.10/0.99      inference(superposition,[status(thm)],[c_983,c_990]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_29,negated_conjecture,
% 4.10/0.99      ( l1_pre_topc(sK1) ),
% 4.10/0.99      inference(cnf_transformation,[],[f71]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_34,plain,
% 4.10/0.99      ( l1_pre_topc(sK1) = iProver_top ),
% 4.10/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_36,plain,
% 4.10/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 4.10/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_1741,plain,
% 4.10/0.99      ( ~ v3_pre_topc(sK3,sK1)
% 4.10/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 4.10/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 4.10/0.99      | ~ r1_tarski(sK3,X0)
% 4.10/0.99      | r1_tarski(sK3,k1_tops_1(sK1,X0))
% 4.10/0.99      | ~ l1_pre_topc(sK1) ),
% 4.10/0.99      inference(instantiation,[status(thm)],[c_20]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_1750,plain,
% 4.10/0.99      ( v3_pre_topc(sK3,sK1) != iProver_top
% 4.10/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 4.10/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 4.10/0.99      | r1_tarski(sK3,X0) != iProver_top
% 4.10/0.99      | r1_tarski(sK3,k1_tops_1(sK1,X0)) = iProver_top
% 4.10/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 4.10/0.99      inference(predicate_to_equality,[status(thm)],[c_1741]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_3386,plain,
% 4.10/0.99      ( r1_tarski(sK3,k1_tops_1(sK1,X0)) = iProver_top
% 4.10/0.99      | r1_tarski(sK3,X0) != iProver_top
% 4.10/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 4.10/0.99      | v3_pre_topc(sK3,sK1) != iProver_top ),
% 4.10/0.99      inference(global_propositional_subsumption,
% 4.10/0.99                [status(thm)],
% 4.10/0.99                [c_2442,c_34,c_36,c_1750]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_3387,plain,
% 4.10/0.99      ( v3_pre_topc(sK3,sK1) != iProver_top
% 4.10/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 4.10/0.99      | r1_tarski(sK3,X0) != iProver_top
% 4.10/0.99      | r1_tarski(sK3,k1_tops_1(sK1,X0)) = iProver_top ),
% 4.10/0.99      inference(renaming,[status(thm)],[c_3386]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_3397,plain,
% 4.10/0.99      ( v3_pre_topc(sK3,sK1) != iProver_top
% 4.10/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 4.10/0.99      | r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,X0))) = iProver_top
% 4.10/0.99      | r1_tarski(sK3,k2_pre_topc(sK1,X0)) != iProver_top
% 4.10/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 4.10/0.99      inference(superposition,[status(thm)],[c_1006,c_3387]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_5549,plain,
% 4.10/0.99      ( r1_tarski(sK3,k2_pre_topc(sK1,X0)) != iProver_top
% 4.10/0.99      | r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,X0))) = iProver_top
% 4.10/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 4.10/0.99      | v3_pre_topc(sK3,sK1) != iProver_top ),
% 4.10/0.99      inference(global_propositional_subsumption,
% 4.10/0.99                [status(thm)],
% 4.10/0.99                [c_3397,c_34]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_5550,plain,
% 4.10/0.99      ( v3_pre_topc(sK3,sK1) != iProver_top
% 4.10/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 4.10/0.99      | r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,X0))) = iProver_top
% 4.10/0.99      | r1_tarski(sK3,k2_pre_topc(sK1,X0)) != iProver_top ),
% 4.10/0.99      inference(renaming,[status(thm)],[c_5549]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_0,plain,
% 4.10/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 4.10/0.99      inference(cnf_transformation,[],[f50]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_1009,plain,
% 4.10/0.99      ( X0 = X1
% 4.10/0.99      | r1_tarski(X0,X1) != iProver_top
% 4.10/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 4.10/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_5559,plain,
% 4.10/0.99      ( k1_tops_1(sK1,k2_pre_topc(sK1,X0)) = sK3
% 4.10/0.99      | v3_pre_topc(sK3,sK1) != iProver_top
% 4.10/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 4.10/0.99      | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,X0)),sK3) != iProver_top
% 4.10/0.99      | r1_tarski(sK3,k2_pre_topc(sK1,X0)) != iProver_top ),
% 4.10/0.99      inference(superposition,[status(thm)],[c_5550,c_1009]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_6162,plain,
% 4.10/0.99      ( k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) = sK3
% 4.10/0.99      | v3_pre_topc(sK3,sK1) != iProver_top
% 4.10/0.99      | v4_tops_1(sK3,sK1) != iProver_top
% 4.10/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 4.10/0.99      | r1_tarski(sK3,k2_pre_topc(sK1,sK3)) != iProver_top
% 4.10/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 4.10/0.99      inference(superposition,[status(thm)],[c_1002,c_5559]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_5,plain,
% 4.10/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.10/0.99      | r1_tarski(X0,k2_pre_topc(X1,X0))
% 4.10/0.99      | ~ l1_pre_topc(X1) ),
% 4.10/0.99      inference(cnf_transformation,[],[f53]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_1309,plain,
% 4.10/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 4.10/0.99      | r1_tarski(sK3,k2_pre_topc(sK1,sK3))
% 4.10/0.99      | ~ l1_pre_topc(sK1) ),
% 4.10/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_1310,plain,
% 4.10/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 4.10/0.99      | r1_tarski(sK3,k2_pre_topc(sK1,sK3)) = iProver_top
% 4.10/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 4.10/0.99      inference(predicate_to_equality,[status(thm)],[c_1309]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_6917,plain,
% 4.10/0.99      ( v4_tops_1(sK3,sK1) != iProver_top
% 4.10/0.99      | v3_pre_topc(sK3,sK1) != iProver_top
% 4.10/0.99      | k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) = sK3 ),
% 4.10/0.99      inference(global_propositional_subsumption,
% 4.10/0.99                [status(thm)],
% 4.10/0.99                [c_6162,c_34,c_36,c_1310]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_6918,plain,
% 4.10/0.99      ( k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) = sK3
% 4.10/0.99      | v3_pre_topc(sK3,sK1) != iProver_top
% 4.10/0.99      | v4_tops_1(sK3,sK1) != iProver_top ),
% 4.10/0.99      inference(renaming,[status(thm)],[c_6917]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_6924,plain,
% 4.10/0.99      ( k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) = sK3
% 4.10/0.99      | v6_tops_1(sK2,sK0) = iProver_top
% 4.10/0.99      | v4_tops_1(sK3,sK1) != iProver_top ),
% 4.10/0.99      inference(superposition,[status(thm)],[c_984,c_6918]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_37,plain,
% 4.10/0.99      ( v3_pre_topc(sK3,sK1) = iProver_top
% 4.10/0.99      | v6_tops_1(sK2,sK0) = iProver_top ),
% 4.10/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_25,negated_conjecture,
% 4.10/0.99      ( v6_tops_1(sK2,sK0) | v4_tops_1(sK3,sK1) ),
% 4.10/0.99      inference(cnf_transformation,[],[f75]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_38,plain,
% 4.10/0.99      ( v6_tops_1(sK2,sK0) = iProver_top
% 4.10/0.99      | v4_tops_1(sK3,sK1) = iProver_top ),
% 4.10/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_7007,plain,
% 4.10/0.99      ( v6_tops_1(sK2,sK0) = iProver_top
% 4.10/0.99      | k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) = sK3 ),
% 4.10/0.99      inference(global_propositional_subsumption,
% 4.10/0.99                [status(thm)],
% 4.10/0.99                [c_6924,c_38]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_7008,plain,
% 4.10/0.99      ( k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) = sK3
% 4.10/0.99      | v6_tops_1(sK2,sK0) = iProver_top ),
% 4.10/0.99      inference(renaming,[status(thm)],[c_7007]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_12,plain,
% 4.10/0.99      ( ~ v6_tops_1(X0,X1)
% 4.10/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.10/0.99      | ~ l1_pre_topc(X1)
% 4.10/0.99      | k1_tops_1(X1,k2_pre_topc(X1,X0)) = X0 ),
% 4.10/0.99      inference(cnf_transformation,[],[f59]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_998,plain,
% 4.10/0.99      ( k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1
% 4.10/0.99      | v6_tops_1(X1,X0) != iProver_top
% 4.10/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 4.10/0.99      | l1_pre_topc(X0) != iProver_top ),
% 4.10/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_2894,plain,
% 4.10/0.99      ( k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = sK2
% 4.10/0.99      | v6_tops_1(sK2,sK0) != iProver_top
% 4.10/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 4.10/0.99      inference(superposition,[status(thm)],[c_982,c_998]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_33,plain,
% 4.10/0.99      ( l1_pre_topc(sK0) = iProver_top ),
% 4.10/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_3377,plain,
% 4.10/0.99      ( v6_tops_1(sK2,sK0) != iProver_top
% 4.10/0.99      | k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = sK2 ),
% 4.10/0.99      inference(global_propositional_subsumption,
% 4.10/0.99                [status(thm)],
% 4.10/0.99                [c_2894,c_33]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_3378,plain,
% 4.10/0.99      ( k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = sK2
% 4.10/0.99      | v6_tops_1(sK2,sK0) != iProver_top ),
% 4.10/0.99      inference(renaming,[status(thm)],[c_3377]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_7013,plain,
% 4.10/0.99      ( k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) = sK3
% 4.10/0.99      | k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = sK2 ),
% 4.10/0.99      inference(superposition,[status(thm)],[c_7008,c_3378]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_999,plain,
% 4.10/0.99      ( k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1
% 4.10/0.99      | v6_tops_1(X1,X0) = iProver_top
% 4.10/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 4.10/0.99      | l1_pre_topc(X0) != iProver_top ),
% 4.10/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_7534,plain,
% 4.10/0.99      ( k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = sK2
% 4.10/0.99      | v6_tops_1(sK3,sK1) = iProver_top
% 4.10/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 4.10/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 4.10/0.99      inference(superposition,[status(thm)],[c_7013,c_999]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_24,negated_conjecture,
% 4.10/0.99      ( ~ v6_tops_1(sK3,sK1) | v6_tops_1(sK2,sK0) ),
% 4.10/0.99      inference(cnf_transformation,[],[f76]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_39,plain,
% 4.10/0.99      ( v6_tops_1(sK3,sK1) != iProver_top
% 4.10/0.99      | v6_tops_1(sK2,sK0) = iProver_top ),
% 4.10/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_7750,plain,
% 4.10/0.99      ( k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = sK2 ),
% 4.10/0.99      inference(global_propositional_subsumption,
% 4.10/0.99                [status(thm)],
% 4.10/0.99                [c_7534,c_34,c_36,c_39,c_3378]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_13173,plain,
% 4.10/0.99      ( k2_pre_topc(sK0,k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK2))) = k3_subset_1(u1_struct_0(sK0),sK2) ),
% 4.10/0.99      inference(global_propositional_subsumption,
% 4.10/0.99                [status(thm)],
% 4.10/0.99                [c_12958,c_30,c_34,c_28,c_36,c_39,c_1300,c_1360,c_2229,
% 4.10/0.99                 c_2240,c_3378,c_7534]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_13,plain,
% 4.10/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.10/0.99      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 4.10/0.99      | ~ l1_pre_topc(X1) ),
% 4.10/0.99      inference(cnf_transformation,[],[f61]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_997,plain,
% 4.10/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 4.10/0.99      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 4.10/0.99      | l1_pre_topc(X1) != iProver_top ),
% 4.10/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_14,plain,
% 4.10/0.99      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
% 4.10/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 4.10/0.99      | ~ v2_pre_topc(X0)
% 4.10/0.99      | ~ l1_pre_topc(X0) ),
% 4.10/0.99      inference(cnf_transformation,[],[f62]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_996,plain,
% 4.10/0.99      ( v4_pre_topc(k2_pre_topc(X0,X1),X0) = iProver_top
% 4.10/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 4.10/0.99      | v2_pre_topc(X0) != iProver_top
% 4.10/0.99      | l1_pre_topc(X0) != iProver_top ),
% 4.10/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_2706,plain,
% 4.10/0.99      ( v4_pre_topc(k2_pre_topc(X0,k1_tops_1(X0,X1)),X0) = iProver_top
% 4.10/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 4.10/0.99      | v2_pre_topc(X0) != iProver_top
% 4.10/0.99      | l1_pre_topc(X0) != iProver_top ),
% 4.10/0.99      inference(superposition,[status(thm)],[c_997,c_996]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_13188,plain,
% 4.10/0.99      ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK2),sK0) = iProver_top
% 4.10/0.99      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.10/0.99      | v2_pre_topc(sK0) != iProver_top
% 4.10/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 4.10/0.99      inference(superposition,[status(thm)],[c_13173,c_2706]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_31,negated_conjecture,
% 4.10/0.99      ( v2_pre_topc(sK0) ),
% 4.10/0.99      inference(cnf_transformation,[],[f69]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_32,plain,
% 4.10/0.99      ( v2_pre_topc(sK0) = iProver_top ),
% 4.10/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_35,plain,
% 4.10/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 4.10/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_1301,plain,
% 4.10/0.99      ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 4.10/0.99      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 4.10/0.99      inference(predicate_to_equality,[status(thm)],[c_1300]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_13859,plain,
% 4.10/0.99      ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK2),sK0) = iProver_top ),
% 4.10/0.99      inference(global_propositional_subsumption,
% 4.10/0.99                [status(thm)],
% 4.10/0.99                [c_13188,c_32,c_33,c_35,c_1301]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_18,plain,
% 4.10/0.99      ( v3_pre_topc(X0,X1)
% 4.10/0.99      | ~ v4_pre_topc(k3_subset_1(u1_struct_0(X1),X0),X1)
% 4.10/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.10/0.99      | ~ l1_pre_topc(X1) ),
% 4.10/0.99      inference(cnf_transformation,[],[f67]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_992,plain,
% 4.10/0.99      ( v3_pre_topc(X0,X1) = iProver_top
% 4.10/0.99      | v4_pre_topc(k3_subset_1(u1_struct_0(X1),X0),X1) != iProver_top
% 4.10/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 4.10/0.99      | l1_pre_topc(X1) != iProver_top ),
% 4.10/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_13864,plain,
% 4.10/0.99      ( v3_pre_topc(sK2,sK0) = iProver_top
% 4.10/0.99      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.10/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 4.10/0.99      inference(superposition,[status(thm)],[c_13859,c_992]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_14025,plain,
% 4.10/0.99      ( v3_pre_topc(sK2,sK0) = iProver_top ),
% 4.10/0.99      inference(global_propositional_subsumption,
% 4.10/0.99                [status(thm)],
% 4.10/0.99                [c_13864,c_33,c_35]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_23,negated_conjecture,
% 4.10/0.99      ( v3_pre_topc(sK3,sK1)
% 4.10/0.99      | ~ v3_pre_topc(sK2,sK0)
% 4.10/0.99      | ~ v4_tops_1(sK2,sK0) ),
% 4.10/0.99      inference(cnf_transformation,[],[f77]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_987,plain,
% 4.10/0.99      ( v3_pre_topc(sK3,sK1) = iProver_top
% 4.10/0.99      | v3_pre_topc(sK2,sK0) != iProver_top
% 4.10/0.99      | v4_tops_1(sK2,sK0) != iProver_top ),
% 4.10/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_14031,plain,
% 4.10/0.99      ( v3_pre_topc(sK3,sK1) = iProver_top
% 4.10/0.99      | v4_tops_1(sK2,sK0) != iProver_top ),
% 4.10/0.99      inference(superposition,[status(thm)],[c_14025,c_987]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_40,plain,
% 4.10/0.99      ( v3_pre_topc(sK3,sK1) = iProver_top
% 4.10/0.99      | v3_pre_topc(sK2,sK0) != iProver_top
% 4.10/0.99      | v4_tops_1(sK2,sK0) != iProver_top ),
% 4.10/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_6,plain,
% 4.10/0.99      ( v4_tops_1(X0,X1)
% 4.10/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.10/0.99      | ~ r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
% 4.10/0.99      | ~ r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
% 4.10/0.99      | ~ l1_pre_topc(X1) ),
% 4.10/0.99      inference(cnf_transformation,[],[f56]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_1004,plain,
% 4.10/0.99      ( v4_tops_1(X0,X1) = iProver_top
% 4.10/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 4.10/0.99      | r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0))) != iProver_top
% 4.10/0.99      | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0) != iProver_top
% 4.10/0.99      | l1_pre_topc(X1) != iProver_top ),
% 4.10/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_7759,plain,
% 4.10/0.99      ( v4_tops_1(sK2,sK0) = iProver_top
% 4.10/0.99      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.10/0.99      | r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) != iProver_top
% 4.10/0.99      | r1_tarski(sK2,sK2) != iProver_top
% 4.10/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 4.10/0.99      inference(superposition,[status(thm)],[c_7750,c_1004]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_428,plain,( X0 = X0 ),theory(equality) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_1773,plain,
% 4.10/0.99      ( sK2 = sK2 ),
% 4.10/0.99      inference(instantiation,[status(thm)],[c_428]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_430,plain,
% 4.10/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 4.10/0.99      theory(equality) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_1465,plain,
% 4.10/0.99      ( ~ r1_tarski(X0,X1)
% 4.10/0.99      | r1_tarski(k1_tops_1(X2,k2_pre_topc(X2,X3)),X3)
% 4.10/0.99      | X3 != X1
% 4.10/0.99      | k1_tops_1(X2,k2_pre_topc(X2,X3)) != X0 ),
% 4.10/0.99      inference(instantiation,[status(thm)],[c_430]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_3475,plain,
% 4.10/0.99      ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK2)
% 4.10/0.99      | ~ r1_tarski(sK2,X0)
% 4.10/0.99      | k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) != sK2
% 4.10/0.99      | sK2 != X0 ),
% 4.10/0.99      inference(instantiation,[status(thm)],[c_1465]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_3994,plain,
% 4.10/0.99      ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK2)
% 4.10/0.99      | ~ r1_tarski(sK2,sK2)
% 4.10/0.99      | k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) != sK2
% 4.10/0.99      | sK2 != sK2 ),
% 4.10/0.99      inference(instantiation,[status(thm)],[c_3475]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_3996,plain,
% 4.10/0.99      ( k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) != sK2
% 4.10/0.99      | sK2 != sK2
% 4.10/0.99      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK2) = iProver_top
% 4.10/0.99      | r1_tarski(sK2,sK2) != iProver_top ),
% 4.10/0.99      inference(predicate_to_equality,[status(thm)],[c_3994]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_2,plain,
% 4.10/0.99      ( r1_tarski(X0,X0) ),
% 4.10/0.99      inference(cnf_transformation,[],[f81]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_3995,plain,
% 4.10/0.99      ( r1_tarski(sK2,sK2) ),
% 4.10/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_3998,plain,
% 4.10/0.99      ( r1_tarski(sK2,sK2) = iProver_top ),
% 4.10/0.99      inference(predicate_to_equality,[status(thm)],[c_3995]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_7168,plain,
% 4.10/0.99      ( v4_tops_1(sK2,sK0)
% 4.10/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 4.10/0.99      | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK2)
% 4.10/0.99      | ~ r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2)))
% 4.10/0.99      | ~ l1_pre_topc(sK0) ),
% 4.10/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_7169,plain,
% 4.10/0.99      ( v4_tops_1(sK2,sK0) = iProver_top
% 4.10/0.99      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.10/0.99      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK2) != iProver_top
% 4.10/0.99      | r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) != iProver_top
% 4.10/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 4.10/0.99      inference(predicate_to_equality,[status(thm)],[c_7168]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_9106,plain,
% 4.10/0.99      ( v4_tops_1(sK2,sK0) = iProver_top
% 4.10/0.99      | r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) != iProver_top ),
% 4.10/0.99      inference(global_propositional_subsumption,
% 4.10/0.99                [status(thm)],
% 4.10/0.99                [c_7759,c_33,c_34,c_35,c_36,c_39,c_1773,c_3378,c_3996,
% 4.10/0.99                 c_3998,c_7169,c_7534]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_15,plain,
% 4.10/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.10/0.99      | ~ l1_pre_topc(X1)
% 4.10/0.99      | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
% 4.10/0.99      inference(cnf_transformation,[],[f63]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_995,plain,
% 4.10/0.99      ( k1_tops_1(X0,k1_tops_1(X0,X1)) = k1_tops_1(X0,X1)
% 4.10/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 4.10/0.99      | l1_pre_topc(X0) != iProver_top ),
% 4.10/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_2665,plain,
% 4.10/0.99      ( k1_tops_1(X0,k1_tops_1(X0,k2_pre_topc(X0,X1))) = k1_tops_1(X0,k2_pre_topc(X0,X1))
% 4.10/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 4.10/0.99      | l1_pre_topc(X0) != iProver_top ),
% 4.10/0.99      inference(superposition,[status(thm)],[c_1006,c_995]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_8453,plain,
% 4.10/0.99      ( k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK2))) = k1_tops_1(sK0,k2_pre_topc(sK0,sK2))
% 4.10/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 4.10/0.99      inference(superposition,[status(thm)],[c_982,c_2665]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_8456,plain,
% 4.10/0.99      ( k1_tops_1(sK0,sK2) = sK2 | l1_pre_topc(sK0) != iProver_top ),
% 4.10/0.99      inference(light_normalisation,[status(thm)],[c_8453,c_7750]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_8802,plain,
% 4.10/0.99      ( k1_tops_1(sK0,sK2) = sK2 ),
% 4.10/0.99      inference(global_propositional_subsumption,
% 4.10/0.99                [status(thm)],
% 4.10/0.99                [c_8456,c_33]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_9110,plain,
% 4.10/0.99      ( v4_tops_1(sK2,sK0) = iProver_top
% 4.10/0.99      | r1_tarski(sK2,k2_pre_topc(sK0,sK2)) != iProver_top ),
% 4.10/0.99      inference(light_normalisation,[status(thm)],[c_9106,c_8802]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_1005,plain,
% 4.10/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 4.10/0.99      | r1_tarski(X0,k2_pre_topc(X1,X0)) = iProver_top
% 4.10/0.99      | l1_pre_topc(X1) != iProver_top ),
% 4.10/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_1942,plain,
% 4.10/0.99      ( r1_tarski(sK2,k2_pre_topc(sK0,sK2)) = iProver_top
% 4.10/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 4.10/0.99      inference(superposition,[status(thm)],[c_982,c_1005]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_1312,plain,
% 4.10/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 4.10/0.99      | r1_tarski(sK2,k2_pre_topc(sK0,sK2))
% 4.10/0.99      | ~ l1_pre_topc(sK0) ),
% 4.10/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_1313,plain,
% 4.10/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.10/0.99      | r1_tarski(sK2,k2_pre_topc(sK0,sK2)) = iProver_top
% 4.10/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 4.10/0.99      inference(predicate_to_equality,[status(thm)],[c_1312]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_2200,plain,
% 4.10/0.99      ( r1_tarski(sK2,k2_pre_topc(sK0,sK2)) = iProver_top ),
% 4.10/0.99      inference(global_propositional_subsumption,
% 4.10/0.99                [status(thm)],
% 4.10/0.99                [c_1942,c_33,c_35,c_1313]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_9113,plain,
% 4.10/0.99      ( v4_tops_1(sK2,sK0) = iProver_top ),
% 4.10/0.99      inference(forward_subsumption_resolution,
% 4.10/0.99                [status(thm)],
% 4.10/0.99                [c_9110,c_2200]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_14141,plain,
% 4.10/0.99      ( v3_pre_topc(sK3,sK1) = iProver_top ),
% 4.10/0.99      inference(global_propositional_subsumption,
% 4.10/0.99                [status(thm)],
% 4.10/0.99                [c_14031,c_33,c_35,c_40,c_9113,c_13864]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_14146,plain,
% 4.10/0.99      ( k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) = sK3
% 4.10/0.99      | v4_tops_1(sK3,sK1) != iProver_top ),
% 4.10/0.99      inference(superposition,[status(thm)],[c_14141,c_6918]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_22,negated_conjecture,
% 4.10/0.99      ( ~ v3_pre_topc(sK2,sK0)
% 4.10/0.99      | v4_tops_1(sK3,sK1)
% 4.10/0.99      | ~ v4_tops_1(sK2,sK0) ),
% 4.10/0.99      inference(cnf_transformation,[],[f78]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_41,plain,
% 4.10/0.99      ( v3_pre_topc(sK2,sK0) != iProver_top
% 4.10/0.99      | v4_tops_1(sK3,sK1) = iProver_top
% 4.10/0.99      | v4_tops_1(sK2,sK0) != iProver_top ),
% 4.10/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_14258,plain,
% 4.10/0.99      ( k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) = sK3 ),
% 4.10/0.99      inference(global_propositional_subsumption,
% 4.10/0.99                [status(thm)],
% 4.10/0.99                [c_14146,c_33,c_34,c_35,c_36,c_40,c_41,c_1310,c_6162,
% 4.10/0.99                 c_9113,c_13864]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_14276,plain,
% 4.10/0.99      ( v6_tops_1(sK3,sK1) = iProver_top
% 4.10/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 4.10/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 4.10/0.99      inference(superposition,[status(thm)],[c_14258,c_999]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_21,negated_conjecture,
% 4.10/0.99      ( ~ v3_pre_topc(sK2,sK0)
% 4.10/0.99      | ~ v6_tops_1(sK3,sK1)
% 4.10/0.99      | ~ v4_tops_1(sK2,sK0) ),
% 4.10/0.99      inference(cnf_transformation,[],[f79]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_42,plain,
% 4.10/0.99      ( v3_pre_topc(sK2,sK0) != iProver_top
% 4.10/0.99      | v6_tops_1(sK3,sK1) != iProver_top
% 4.10/0.99      | v4_tops_1(sK2,sK0) != iProver_top ),
% 4.10/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(contradiction,plain,
% 4.10/0.99      ( $false ),
% 4.10/0.99      inference(minisat,
% 4.10/0.99                [status(thm)],
% 4.10/0.99                [c_14276,c_13864,c_9113,c_42,c_36,c_35,c_34,c_33]) ).
% 4.10/0.99  
% 4.10/0.99  
% 4.10/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 4.10/0.99  
% 4.10/0.99  ------                               Statistics
% 4.10/0.99  
% 4.10/0.99  ------ Selected
% 4.10/0.99  
% 4.10/0.99  total_time:                             0.439
% 4.10/0.99  
%------------------------------------------------------------------------------
