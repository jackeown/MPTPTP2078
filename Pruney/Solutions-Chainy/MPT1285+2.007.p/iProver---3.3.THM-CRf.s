%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:15:54 EST 2020

% Result     : Theorem 7.49s
% Output     : CNFRefutation 7.49s
% Verified   : 
% Statistics : Number of formulae       :  271 (5174 expanded)
%              Number of clauses        :  209 (1476 expanded)
%              Number of leaves         :   21 (1748 expanded)
%              Depth                    :   25
%              Number of atoms          :  981 (47789 expanded)
%              Number of equality atoms :  378 (2345 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    5 (   2 average)

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
                 => ( ( v6_tops_1(X2,X0)
                     => ( v4_tops_1(X2,X0)
                        & v3_pre_topc(X2,X0) ) )
                    & ( ( v4_tops_1(X3,X1)
                        & v3_pre_topc(X3,X1) )
                     => v6_tops_1(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
                   => ( ( v6_tops_1(X2,X0)
                       => ( v4_tops_1(X2,X0)
                          & v3_pre_topc(X2,X0) ) )
                      & ( ( v4_tops_1(X3,X1)
                          & v3_pre_topc(X3,X1) )
                       => v6_tops_1(X3,X1) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f35,plain,(
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

fof(f34,plain,(
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

fof(f33,plain,(
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

fof(f32,plain,
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

fof(f36,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f26,f35,f34,f33,f32])).

fof(f57,plain,
    ( v6_tops_1(sK2,sK0)
    | v3_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f56,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f36])).

fof(f9,axiom,(
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

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f52,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f53,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f54,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f55,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f36])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X2,X0)
      | k1_tops_1(X0,X2) != X2
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f4,axiom,(
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
    inference(ennf_transformation,[],[f4])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v6_tops_1(X1,X0)
              | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1 )
            & ( k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1
              | ~ v6_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1
      | ~ v6_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f59,plain,
    ( v6_tops_1(sK2,sK0)
    | ~ v6_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f64,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f37])).

fof(f39,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f58,plain,
    ( v6_tops_1(sK2,sK0)
    | v4_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v6_tops_1(X1,X0)
      | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
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
    inference(ennf_transformation,[],[f3])).

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
    inference(nnf_transformation,[],[f14])).

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

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)
      | ~ v4_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
      | ~ v4_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v4_tops_1(X1,X0)
      | ~ r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
      | ~ r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f61,plain,
    ( ~ v4_tops_1(sK2,sK0)
    | ~ v3_pre_topc(sK2,sK0)
    | v4_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f60,plain,
    ( ~ v4_tops_1(sK2,sK0)
    | ~ v3_pre_topc(sK2,sK0)
    | v3_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f62,plain,
    ( ~ v4_tops_1(sK2,sK0)
    | ~ v3_pre_topc(sK2,sK0)
    | ~ v6_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_20,negated_conjecture,
    ( v3_pre_topc(sK3,sK1)
    | v6_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1462,plain,
    ( v3_pre_topc(sK3,sK1) = iProver_top
    | v6_tops_1(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1461,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_14,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_25,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_318,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X1,X0) = X0
    | sK0 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_25])).

cnf(c_319,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK0)
    | k1_tops_1(X1,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_318])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_323,plain,
    ( ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X0,X1)
    | k1_tops_1(X1,X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_319,c_24])).

cnf(c_324,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = X0 ),
    inference(renaming,[status(thm)],[c_323])).

cnf(c_23,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_358,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(X1,X0) = X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_324,c_23])).

cnf(c_359,plain,
    ( ~ v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK1,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_358])).

cnf(c_791,plain,
    ( ~ v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,X0) = X0
    | ~ sP4_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP4_iProver_split])],[c_359])).

cnf(c_1457,plain,
    ( k1_tops_1(sK1,X0) = X0
    | v3_pre_topc(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | sP4_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_791])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_29,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_792,plain,
    ( sP4_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_359])).

cnf(c_847,plain,
    ( sP4_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_792])).

cnf(c_848,plain,
    ( k1_tops_1(sK1,X0) = X0
    | v3_pre_topc(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | sP4_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_791])).

cnf(c_13,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_293,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X1,X0) != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_25])).

cnf(c_294,plain,
    ( v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(sK0)
    | k1_tops_1(sK0,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_293])).

cnf(c_298,plain,
    ( ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | v3_pre_topc(X0,sK0)
    | k1_tops_1(sK0,X0) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_294,c_24])).

cnf(c_299,plain,
    ( v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(X2)
    | k1_tops_1(sK0,X0) != X0 ),
    inference(renaming,[status(thm)],[c_298])).

cnf(c_676,plain,
    ( v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) != X0
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_299])).

cnf(c_677,plain,
    ( v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_676])).

cnf(c_784,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_677])).

cnf(c_1547,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ sP0_iProver_split ),
    inference(instantiation,[status(thm)],[c_784])).

cnf(c_1548,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1547])).

cnf(c_2856,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v3_pre_topc(X0,sK1) != iProver_top
    | k1_tops_1(sK1,X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1457,c_29,c_847,c_848,c_1548])).

cnf(c_2857,plain,
    ( k1_tops_1(sK1,X0) = X0
    | v3_pre_topc(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2856])).

cnf(c_2862,plain,
    ( k1_tops_1(sK1,sK3) = sK3
    | v3_pre_topc(sK3,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1461,c_2857])).

cnf(c_2931,plain,
    ( k1_tops_1(sK1,sK3) = sK3
    | v6_tops_1(sK2,sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1462,c_2862])).

cnf(c_1460,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_8,plain,
    ( ~ v6_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,k2_pre_topc(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_568,plain,
    ( ~ v6_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,k2_pre_topc(X1,X0)) = X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_24])).

cnf(c_569,plain,
    ( ~ v6_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,k2_pre_topc(sK0,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_568])).

cnf(c_1440,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,X0)) = X0
    | v6_tops_1(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_569])).

cnf(c_2375,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = sK2
    | v6_tops_1(sK2,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1460,c_1440])).

cnf(c_3021,plain,
    ( k1_tops_1(sK1,sK3) = sK3
    | k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_2931,c_2375])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_646,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_24])).

cnf(c_647,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_646])).

cnf(c_1435,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_647])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_556,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_24])).

cnf(c_557,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,k1_tops_1(sK0,X0)) = k1_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_556])).

cnf(c_1441,plain,
    ( k1_tops_1(sK0,k1_tops_1(sK0,X0)) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_557])).

cnf(c_2177,plain,
    ( k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,X0))) = k1_tops_1(sK0,k2_pre_topc(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1435,c_1441])).

cnf(c_3467,plain,
    ( k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK2))) = k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) ),
    inference(superposition,[status(thm)],[c_1460,c_2177])).

cnf(c_4130,plain,
    ( k1_tops_1(sK1,sK3) = sK3
    | k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = k1_tops_1(sK0,sK2) ),
    inference(superposition,[status(thm)],[c_3021,c_3467])).

cnf(c_4186,plain,
    ( k1_tops_1(sK1,sK3) = sK3
    | k1_tops_1(sK0,sK2) = sK2 ),
    inference(superposition,[status(thm)],[c_4130,c_3021])).

cnf(c_18,negated_conjecture,
    ( ~ v6_tops_1(sK3,sK1)
    | v6_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_74,plain,
    ( r1_tarski(sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_78,plain,
    ( ~ r1_tarski(sK0,sK0)
    | sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1569,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_647])).

cnf(c_9,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_275,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_25])).

cnf(c_276,plain,
    ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_275])).

cnf(c_280,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(k1_tops_1(sK0,X0),sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_276,c_24])).

cnf(c_281,plain,
    ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(renaming,[status(thm)],[c_280])).

cnf(c_1679,plain,
    ( v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK0)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_281])).

cnf(c_794,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2102,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_794])).

cnf(c_2295,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_794])).

cnf(c_2377,plain,
    ( ~ v6_tops_1(sK2,sK0)
    | k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = sK2 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2375])).

cnf(c_2428,plain,
    ( k1_zfmisc_1(u1_struct_0(sK1)) = k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_794])).

cnf(c_19,negated_conjecture,
    ( v6_tops_1(sK2,sK0)
    | v4_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1463,plain,
    ( v6_tops_1(sK2,sK0) = iProver_top
    | v4_tops_1(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2448,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = sK2
    | v4_tops_1(sK3,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1463,c_2375])).

cnf(c_2449,plain,
    ( v4_tops_1(sK3,sK1)
    | k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = sK2 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2448])).

cnf(c_508,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(X1,X0) = X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_324,c_24])).

cnf(c_509,plain,
    ( ~ v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_508])).

cnf(c_789,plain,
    ( ~ v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) = X0
    | ~ sP3_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP3_iProver_split])],[c_509])).

cnf(c_1445,plain,
    ( k1_tops_1(sK0,X0) = X0
    | v3_pre_topc(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | sP3_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_789])).

cnf(c_790,plain,
    ( sP3_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_509])).

cnf(c_835,plain,
    ( sP3_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_790])).

cnf(c_836,plain,
    ( k1_tops_1(sK0,X0) = X0
    | v3_pre_topc(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | sP3_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_789])).

cnf(c_2800,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v3_pre_topc(X0,sK0) != iProver_top
    | k1_tops_1(sK0,X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1445,c_29,c_835,c_836,c_1548])).

cnf(c_2801,plain,
    ( k1_tops_1(sK0,X0) = X0
    | v3_pre_topc(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2800])).

cnf(c_2804,plain,
    ( k1_tops_1(sK0,sK2) = sK2
    | v3_pre_topc(sK2,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1460,c_2801])).

cnf(c_2806,plain,
    ( ~ v3_pre_topc(sK2,sK0)
    | k1_tops_1(sK0,sK2) = sK2 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2804])).

cnf(c_2847,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_794])).

cnf(c_800,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1564,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | X2 != X0
    | k1_zfmisc_1(u1_struct_0(sK1)) != X1 ),
    inference(instantiation,[status(thm)],[c_800])).

cnf(c_1927,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | X1 != X0
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1564])).

cnf(c_3369,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | X0 != sK3
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1927])).

cnf(c_3880,plain,
    ( m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,sK3) != sK3
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_3369])).

cnf(c_801,plain,
    ( ~ v4_tops_1(X0,X1)
    | v4_tops_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1598,plain,
    ( ~ v4_tops_1(X0,X1)
    | v4_tops_1(X2,sK1)
    | X2 != X0
    | sK1 != X1 ),
    inference(instantiation,[status(thm)],[c_801])).

cnf(c_1937,plain,
    ( ~ v4_tops_1(X0,sK1)
    | v4_tops_1(X1,sK1)
    | X1 != X0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1598])).

cnf(c_3535,plain,
    ( v4_tops_1(X0,sK1)
    | ~ v4_tops_1(sK3,sK1)
    | X0 != sK3
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1937])).

cnf(c_3886,plain,
    ( v4_tops_1(k1_tops_1(sK1,sK3),sK1)
    | ~ v4_tops_1(sK3,sK1)
    | k1_tops_1(sK1,sK3) != sK3
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_3535])).

cnf(c_7,plain,
    ( v6_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,k2_pre_topc(X1,X0)) != X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_433,plain,
    ( v6_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,k2_pre_topc(X1,X0)) != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_23])).

cnf(c_434,plain,
    ( v6_tops_1(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,k2_pre_topc(sK1,X0)) != X0 ),
    inference(unflattening,[status(thm)],[c_433])).

cnf(c_4553,plain,
    ( v6_tops_1(k1_tops_1(sK1,sK3),sK1)
    | ~ m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,k2_pre_topc(sK1,k1_tops_1(sK1,sK3))) != k1_tops_1(sK1,sK3) ),
    inference(instantiation,[status(thm)],[c_434])).

cnf(c_795,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2171,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_795])).

cnf(c_3447,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2171])).

cnf(c_5859,plain,
    ( k1_tops_1(sK1,sK3) != sK3
    | sK3 = k1_tops_1(sK1,sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_3447])).

cnf(c_406,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_23])).

cnf(c_407,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,k1_tops_1(sK1,X0)) = k1_tops_1(sK1,X0) ),
    inference(unflattening,[status(thm)],[c_406])).

cnf(c_1453,plain,
    ( k1_tops_1(sK1,k1_tops_1(sK1,X0)) = k1_tops_1(sK1,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_407])).

cnf(c_2312,plain,
    ( k1_tops_1(sK1,k1_tops_1(sK1,sK3)) = k1_tops_1(sK1,sK3) ),
    inference(superposition,[status(thm)],[c_1461,c_1453])).

cnf(c_496,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_23])).

cnf(c_497,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k2_pre_topc(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_496])).

cnf(c_1447,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_497])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_376,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_23])).

cnf(c_377,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X0,X1)
    | r1_tarski(k1_tops_1(sK1,X0),k1_tops_1(sK1,X1)) ),
    inference(unflattening,[status(thm)],[c_376])).

cnf(c_1455,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_tops_1(sK1,X0),k1_tops_1(sK1,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_377])).

cnf(c_6,plain,
    ( ~ v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_448,plain,
    ( ~ v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_23])).

cnf(c_449,plain,
    ( ~ v4_tops_1(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,X0)),X0) ),
    inference(unflattening,[status(thm)],[c_448])).

cnf(c_1450,plain,
    ( v4_tops_1(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,X0)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_449])).

cnf(c_1469,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2795,plain,
    ( k1_tops_1(sK1,k2_pre_topc(sK1,X0)) = X0
    | v4_tops_1(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X0,k1_tops_1(sK1,k2_pre_topc(sK1,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1450,c_1469])).

cnf(c_3127,plain,
    ( k1_tops_1(sK1,k2_pre_topc(sK1,k1_tops_1(sK1,X0))) = k1_tops_1(sK1,X0)
    | v4_tops_1(k1_tops_1(sK1,X0),sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k1_tops_1(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK1,k1_tops_1(sK1,X0)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK1,k1_tops_1(sK1,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1455,c_2795])).

cnf(c_7066,plain,
    ( k1_tops_1(sK1,k2_pre_topc(sK1,k1_tops_1(sK1,X0))) = k1_tops_1(sK1,X0)
    | v4_tops_1(k1_tops_1(sK1,X0),sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k1_tops_1(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK1,k1_tops_1(sK1,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1447,c_3127])).

cnf(c_8871,plain,
    ( k1_tops_1(sK1,k2_pre_topc(sK1,k1_tops_1(sK1,k1_tops_1(sK1,sK3)))) = k1_tops_1(sK1,k1_tops_1(sK1,sK3))
    | v4_tops_1(k1_tops_1(sK1,k1_tops_1(sK1,sK3)),sK1) != iProver_top
    | m1_subset_1(k1_tops_1(sK1,k1_tops_1(sK1,sK3)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(k1_tops_1(sK1,sK3),k2_pre_topc(sK1,k1_tops_1(sK1,sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2312,c_7066])).

cnf(c_8888,plain,
    ( k1_tops_1(sK1,k2_pre_topc(sK1,k1_tops_1(sK1,sK3))) = k1_tops_1(sK1,sK3)
    | v4_tops_1(k1_tops_1(sK1,sK3),sK1) != iProver_top
    | m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(k1_tops_1(sK1,sK3),k2_pre_topc(sK1,k1_tops_1(sK1,sK3))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8871,c_2312])).

cnf(c_5,plain,
    ( ~ v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_463,plain,
    ( ~ v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_23])).

cnf(c_464,plain,
    ( ~ v4_tops_1(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(X0,k2_pre_topc(sK1,k1_tops_1(sK1,X0))) ),
    inference(unflattening,[status(thm)],[c_463])).

cnf(c_1449,plain,
    ( v4_tops_1(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK1,k1_tops_1(sK1,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_464])).

cnf(c_2767,plain,
    ( v4_tops_1(k1_tops_1(sK1,sK3),sK1) != iProver_top
    | m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(k1_tops_1(sK1,sK3),k2_pre_topc(sK1,k1_tops_1(sK1,sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2312,c_1449])).

cnf(c_8902,plain,
    ( m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v4_tops_1(k1_tops_1(sK1,sK3),sK1) != iProver_top
    | k1_tops_1(sK1,k2_pre_topc(sK1,k1_tops_1(sK1,sK3))) = k1_tops_1(sK1,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8888,c_2767])).

cnf(c_8903,plain,
    ( k1_tops_1(sK1,k2_pre_topc(sK1,k1_tops_1(sK1,sK3))) = k1_tops_1(sK1,sK3)
    | v4_tops_1(k1_tops_1(sK1,sK3),sK1) != iProver_top
    | m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_8902])).

cnf(c_8904,plain,
    ( ~ v4_tops_1(k1_tops_1(sK1,sK3),sK1)
    | ~ m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,k2_pre_topc(sK1,k1_tops_1(sK1,sK3))) = k1_tops_1(sK1,sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_8903])).

cnf(c_803,plain,
    ( ~ v6_tops_1(X0,X1)
    | v6_tops_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1589,plain,
    ( ~ v6_tops_1(X0,X1)
    | v6_tops_1(X2,sK1)
    | X2 != X0
    | sK1 != X1 ),
    inference(instantiation,[status(thm)],[c_803])).

cnf(c_1785,plain,
    ( ~ v6_tops_1(X0,sK1)
    | v6_tops_1(X1,sK1)
    | X1 != X0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1589])).

cnf(c_6928,plain,
    ( v6_tops_1(X0,sK1)
    | ~ v6_tops_1(k1_tops_1(sK1,sK3),sK1)
    | X0 != k1_tops_1(sK1,sK3)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1785])).

cnf(c_9297,plain,
    ( ~ v6_tops_1(k1_tops_1(sK1,sK3),sK1)
    | v6_tops_1(sK3,sK1)
    | sK1 != sK1
    | sK3 != k1_tops_1(sK1,sK3) ),
    inference(instantiation,[status(thm)],[c_6928])).

cnf(c_1779,plain,
    ( X0 != X1
    | sK2 != X1
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_795])).

cnf(c_2243,plain,
    ( X0 != sK2
    | sK2 = X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1779])).

cnf(c_13824,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) != sK2
    | sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2))
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_2243])).

cnf(c_804,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v3_pre_topc(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1540,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v3_pre_topc(sK2,sK0)
    | sK0 != X1
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_804])).

cnf(c_16840,plain,
    ( ~ v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),X0)
    | v3_pre_topc(sK2,sK0)
    | sK0 != X0
    | sK2 != k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_1540])).

cnf(c_16842,plain,
    ( ~ v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK0)
    | v3_pre_topc(sK2,sK0)
    | sK0 != sK0
    | sK2 != k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_16840])).

cnf(c_19395,plain,
    ( k1_tops_1(sK0,sK2) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4186,c_22,c_21,c_18,c_74,c_78,c_1569,c_1679,c_2102,c_2295,c_2377,c_2428,c_2449,c_2806,c_2847,c_3021,c_3880,c_3886,c_4553,c_5859,c_8904,c_9297,c_13824,c_16842])).

cnf(c_4,plain,
    ( v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
    | ~ r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_628,plain,
    ( v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
    | ~ r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_24])).

cnf(c_629,plain,
    ( v4_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,X0)))
    | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X0) ),
    inference(unflattening,[status(thm)],[c_628])).

cnf(c_1436,plain,
    ( v4_tops_1(X0,sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,X0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_629])).

cnf(c_4127,plain,
    ( k1_tops_1(sK1,sK3) = sK3
    | v4_tops_1(sK2,sK0) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) != iProver_top
    | r1_tarski(sK2,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3021,c_1436])).

cnf(c_1645,plain,
    ( v4_tops_1(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK2)
    | ~ r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) ),
    inference(instantiation,[status(thm)],[c_629])).

cnf(c_1646,plain,
    ( v4_tops_1(sK2,sK0) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK2) != iProver_top
    | r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1645])).

cnf(c_2013,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2014,plain,
    ( r1_tarski(sK2,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2013])).

cnf(c_796,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1744,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK2)
    | k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) != X0
    | sK2 != X1 ),
    inference(instantiation,[status(thm)],[c_796])).

cnf(c_2236,plain,
    ( ~ r1_tarski(X0,sK2)
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK2)
    | k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) != X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1744])).

cnf(c_3244,plain,
    ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK2)
    | ~ r1_tarski(sK2,sK2)
    | k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) != sK2
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_2236])).

cnf(c_3245,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) != sK2
    | sK2 != sK2
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK2) = iProver_top
    | r1_tarski(sK2,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3244])).

cnf(c_14018,plain,
    ( r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) != iProver_top
    | v4_tops_1(sK2,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4127,c_29,c_21,c_18,c_1646,c_2014,c_2102,c_2295,c_2377,c_2428,c_2449,c_2847,c_3021,c_3245,c_3880,c_3886,c_4553,c_5859,c_8904,c_9297])).

cnf(c_14019,plain,
    ( v4_tops_1(sK2,sK0) = iProver_top
    | r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_14018])).

cnf(c_19426,plain,
    ( v4_tops_1(sK2,sK0) = iProver_top
    | r1_tarski(sK2,k2_pre_topc(sK0,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_19395,c_14019])).

cnf(c_3650,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,k2_pre_topc(sK0,sK2))
    | X2 != X0
    | k2_pre_topc(sK0,sK2) != X1 ),
    inference(instantiation,[status(thm)],[c_796])).

cnf(c_6849,plain,
    ( ~ r1_tarski(X0,k2_pre_topc(sK0,sK2))
    | r1_tarski(X1,k2_pre_topc(sK0,sK2))
    | X1 != X0
    | k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_3650])).

cnf(c_13002,plain,
    ( r1_tarski(X0,k2_pre_topc(sK0,sK2))
    | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,sK2))
    | X0 != k1_tops_1(sK0,k2_pre_topc(sK0,sK2))
    | k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_6849])).

cnf(c_19169,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,sK2))
    | r1_tarski(sK2,k2_pre_topc(sK0,sK2))
    | k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,sK2)
    | sK2 != k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_13002])).

cnf(c_19170,plain,
    ( k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,sK2)
    | sK2 != k1_tops_1(sK0,k2_pre_topc(sK0,sK2))
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,sK2)) != iProver_top
    | r1_tarski(sK2,k2_pre_topc(sK0,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19169])).

cnf(c_785,plain,
    ( v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) != X0
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_677])).

cnf(c_1430,plain,
    ( k1_tops_1(sK0,X0) != X0
    | v3_pre_topc(X0,sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_785])).

cnf(c_786,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_677])).

cnf(c_816,plain,
    ( sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_786])).

cnf(c_817,plain,
    ( k1_tops_1(sK0,X0) != X0
    | v3_pre_topc(X0,sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_785])).

cnf(c_1750,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v3_pre_topc(X0,sK0) = iProver_top
    | k1_tops_1(sK0,X0) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1430,c_29,c_816,c_817,c_1548])).

cnf(c_1751,plain,
    ( k1_tops_1(sK0,X0) != X0
    | v3_pre_topc(X0,sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1750])).

cnf(c_3476,plain,
    ( v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK0) = iProver_top
    | m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3467,c_1751])).

cnf(c_1570,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1569])).

cnf(c_1683,plain,
    ( v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK0) = iProver_top
    | m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1679])).

cnf(c_3678,plain,
    ( v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3476,c_29,c_1570,c_1683])).

cnf(c_4129,plain,
    ( k1_tops_1(sK1,sK3) = sK3
    | v3_pre_topc(sK2,sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3021,c_3678])).

cnf(c_16,negated_conjecture,
    ( ~ v3_pre_topc(sK2,sK0)
    | v4_tops_1(sK3,sK1)
    | ~ v4_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1466,plain,
    ( v3_pre_topc(sK2,sK0) != iProver_top
    | v4_tops_1(sK3,sK1) = iProver_top
    | v4_tops_1(sK2,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_14695,plain,
    ( k1_tops_1(sK1,sK3) = sK3
    | v4_tops_1(sK3,sK1) = iProver_top
    | v4_tops_1(sK2,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4129,c_1466])).

cnf(c_17,negated_conjecture,
    ( v3_pre_topc(sK3,sK1)
    | ~ v3_pre_topc(sK2,sK0)
    | ~ v4_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1465,plain,
    ( v3_pre_topc(sK3,sK1) = iProver_top
    | v3_pre_topc(sK2,sK0) != iProver_top
    | v4_tops_1(sK2,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_14696,plain,
    ( k1_tops_1(sK1,sK3) = sK3
    | v3_pre_topc(sK3,sK1) = iProver_top
    | v4_tops_1(sK2,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4129,c_1465])).

cnf(c_14713,plain,
    ( k1_tops_1(sK1,sK3) = sK3
    | v4_tops_1(sK2,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14695,c_2862,c_14696])).

cnf(c_9298,plain,
    ( sK1 != sK1
    | sK3 != k1_tops_1(sK1,sK3)
    | v6_tops_1(k1_tops_1(sK1,sK3),sK1) != iProver_top
    | v6_tops_1(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9297])).

cnf(c_4563,plain,
    ( k1_tops_1(sK1,k2_pre_topc(sK1,k1_tops_1(sK1,sK3))) != k1_tops_1(sK1,sK3)
    | v6_tops_1(k1_tops_1(sK1,sK3),sK1) = iProver_top
    | m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4553])).

cnf(c_3887,plain,
    ( k1_tops_1(sK1,sK3) != sK3
    | sK1 != sK1
    | v4_tops_1(k1_tops_1(sK1,sK3),sK1) = iProver_top
    | v4_tops_1(sK3,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3886])).

cnf(c_3881,plain,
    ( k1_tops_1(sK1,sK3) != sK3
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
    | m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3880])).

cnf(c_3593,plain,
    ( k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_794])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_544,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_24])).

cnf(c_545,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,X0),X0) ),
    inference(unflattening,[status(thm)],[c_544])).

cnf(c_1677,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_545])).

cnf(c_1687,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1677])).

cnf(c_916,plain,
    ( k1_tops_1(sK0,X0) != X0
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(X0,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_785,c_786,c_784])).

cnf(c_917,plain,
    ( v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) != X0 ),
    inference(renaming,[status(thm)],[c_916])).

cnf(c_923,plain,
    ( k1_tops_1(sK0,X0) != X0
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(X0,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_785,c_917])).

cnf(c_924,plain,
    ( v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) != X0 ),
    inference(renaming,[status(thm)],[c_923])).

cnf(c_1632,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,sK2) != sK2 ),
    inference(instantiation,[status(thm)],[c_924])).

cnf(c_1633,plain,
    ( k1_tops_1(sK0,sK2) != sK2
    | v3_pre_topc(sK2,sK0) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1632])).

cnf(c_15,negated_conjecture,
    ( ~ v3_pre_topc(sK2,sK0)
    | ~ v6_tops_1(sK3,sK1)
    | ~ v4_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_36,plain,
    ( v3_pre_topc(sK2,sK0) != iProver_top
    | v6_tops_1(sK3,sK1) != iProver_top
    | v4_tops_1(sK2,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_35,plain,
    ( v3_pre_topc(sK2,sK0) != iProver_top
    | v4_tops_1(sK3,sK1) = iProver_top
    | v4_tops_1(sK2,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_30,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_19426,c_19170,c_16842,c_14713,c_13824,c_9298,c_9297,c_8904,c_8903,c_5859,c_4563,c_4553,c_3887,c_3886,c_3881,c_3880,c_3593,c_3021,c_2847,c_2806,c_2449,c_2428,c_2377,c_2295,c_2102,c_1687,c_1679,c_1633,c_1570,c_1569,c_78,c_74,c_36,c_35,c_18,c_30,c_21,c_29,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:47:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.49/1.52  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.49/1.52  
% 7.49/1.52  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.49/1.52  
% 7.49/1.52  ------  iProver source info
% 7.49/1.52  
% 7.49/1.52  git: date: 2020-06-30 10:37:57 +0100
% 7.49/1.52  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.49/1.52  git: non_committed_changes: false
% 7.49/1.52  git: last_make_outside_of_git: false
% 7.49/1.52  
% 7.49/1.52  ------ 
% 7.49/1.52  
% 7.49/1.52  ------ Input Options
% 7.49/1.52  
% 7.49/1.52  --out_options                           all
% 7.49/1.52  --tptp_safe_out                         true
% 7.49/1.52  --problem_path                          ""
% 7.49/1.52  --include_path                          ""
% 7.49/1.52  --clausifier                            res/vclausify_rel
% 7.49/1.52  --clausifier_options                    ""
% 7.49/1.52  --stdin                                 false
% 7.49/1.52  --stats_out                             all
% 7.49/1.52  
% 7.49/1.52  ------ General Options
% 7.49/1.52  
% 7.49/1.52  --fof                                   false
% 7.49/1.52  --time_out_real                         305.
% 7.49/1.52  --time_out_virtual                      -1.
% 7.49/1.52  --symbol_type_check                     false
% 7.49/1.52  --clausify_out                          false
% 7.49/1.52  --sig_cnt_out                           false
% 7.49/1.52  --trig_cnt_out                          false
% 7.49/1.52  --trig_cnt_out_tolerance                1.
% 7.49/1.52  --trig_cnt_out_sk_spl                   false
% 7.49/1.52  --abstr_cl_out                          false
% 7.49/1.52  
% 7.49/1.52  ------ Global Options
% 7.49/1.52  
% 7.49/1.52  --schedule                              default
% 7.49/1.52  --add_important_lit                     false
% 7.49/1.52  --prop_solver_per_cl                    1000
% 7.49/1.52  --min_unsat_core                        false
% 7.49/1.52  --soft_assumptions                      false
% 7.49/1.52  --soft_lemma_size                       3
% 7.49/1.52  --prop_impl_unit_size                   0
% 7.49/1.52  --prop_impl_unit                        []
% 7.49/1.52  --share_sel_clauses                     true
% 7.49/1.52  --reset_solvers                         false
% 7.49/1.52  --bc_imp_inh                            [conj_cone]
% 7.49/1.52  --conj_cone_tolerance                   3.
% 7.49/1.52  --extra_neg_conj                        none
% 7.49/1.52  --large_theory_mode                     true
% 7.49/1.52  --prolific_symb_bound                   200
% 7.49/1.52  --lt_threshold                          2000
% 7.49/1.52  --clause_weak_htbl                      true
% 7.49/1.52  --gc_record_bc_elim                     false
% 7.49/1.52  
% 7.49/1.52  ------ Preprocessing Options
% 7.49/1.52  
% 7.49/1.52  --preprocessing_flag                    true
% 7.49/1.52  --time_out_prep_mult                    0.1
% 7.49/1.52  --splitting_mode                        input
% 7.49/1.52  --splitting_grd                         true
% 7.49/1.52  --splitting_cvd                         false
% 7.49/1.52  --splitting_cvd_svl                     false
% 7.49/1.52  --splitting_nvd                         32
% 7.49/1.52  --sub_typing                            true
% 7.49/1.52  --prep_gs_sim                           true
% 7.49/1.52  --prep_unflatten                        true
% 7.49/1.52  --prep_res_sim                          true
% 7.49/1.52  --prep_upred                            true
% 7.49/1.52  --prep_sem_filter                       exhaustive
% 7.49/1.52  --prep_sem_filter_out                   false
% 7.49/1.52  --pred_elim                             true
% 7.49/1.52  --res_sim_input                         true
% 7.49/1.52  --eq_ax_congr_red                       true
% 7.49/1.52  --pure_diseq_elim                       true
% 7.49/1.52  --brand_transform                       false
% 7.49/1.52  --non_eq_to_eq                          false
% 7.49/1.52  --prep_def_merge                        true
% 7.49/1.52  --prep_def_merge_prop_impl              false
% 7.49/1.52  --prep_def_merge_mbd                    true
% 7.49/1.52  --prep_def_merge_tr_red                 false
% 7.49/1.52  --prep_def_merge_tr_cl                  false
% 7.49/1.52  --smt_preprocessing                     true
% 7.49/1.52  --smt_ac_axioms                         fast
% 7.49/1.52  --preprocessed_out                      false
% 7.49/1.52  --preprocessed_stats                    false
% 7.49/1.52  
% 7.49/1.52  ------ Abstraction refinement Options
% 7.49/1.52  
% 7.49/1.52  --abstr_ref                             []
% 7.49/1.52  --abstr_ref_prep                        false
% 7.49/1.52  --abstr_ref_until_sat                   false
% 7.49/1.52  --abstr_ref_sig_restrict                funpre
% 7.49/1.52  --abstr_ref_af_restrict_to_split_sk     false
% 7.49/1.52  --abstr_ref_under                       []
% 7.49/1.52  
% 7.49/1.52  ------ SAT Options
% 7.49/1.52  
% 7.49/1.52  --sat_mode                              false
% 7.49/1.52  --sat_fm_restart_options                ""
% 7.49/1.52  --sat_gr_def                            false
% 7.49/1.52  --sat_epr_types                         true
% 7.49/1.52  --sat_non_cyclic_types                  false
% 7.49/1.52  --sat_finite_models                     false
% 7.49/1.52  --sat_fm_lemmas                         false
% 7.49/1.52  --sat_fm_prep                           false
% 7.49/1.52  --sat_fm_uc_incr                        true
% 7.49/1.52  --sat_out_model                         small
% 7.49/1.52  --sat_out_clauses                       false
% 7.49/1.52  
% 7.49/1.52  ------ QBF Options
% 7.49/1.52  
% 7.49/1.52  --qbf_mode                              false
% 7.49/1.52  --qbf_elim_univ                         false
% 7.49/1.52  --qbf_dom_inst                          none
% 7.49/1.52  --qbf_dom_pre_inst                      false
% 7.49/1.52  --qbf_sk_in                             false
% 7.49/1.52  --qbf_pred_elim                         true
% 7.49/1.52  --qbf_split                             512
% 7.49/1.52  
% 7.49/1.52  ------ BMC1 Options
% 7.49/1.52  
% 7.49/1.52  --bmc1_incremental                      false
% 7.49/1.52  --bmc1_axioms                           reachable_all
% 7.49/1.52  --bmc1_min_bound                        0
% 7.49/1.52  --bmc1_max_bound                        -1
% 7.49/1.52  --bmc1_max_bound_default                -1
% 7.49/1.52  --bmc1_symbol_reachability              true
% 7.49/1.52  --bmc1_property_lemmas                  false
% 7.49/1.52  --bmc1_k_induction                      false
% 7.49/1.52  --bmc1_non_equiv_states                 false
% 7.49/1.52  --bmc1_deadlock                         false
% 7.49/1.52  --bmc1_ucm                              false
% 7.49/1.52  --bmc1_add_unsat_core                   none
% 7.49/1.52  --bmc1_unsat_core_children              false
% 7.49/1.52  --bmc1_unsat_core_extrapolate_axioms    false
% 7.49/1.52  --bmc1_out_stat                         full
% 7.49/1.52  --bmc1_ground_init                      false
% 7.49/1.52  --bmc1_pre_inst_next_state              false
% 7.49/1.52  --bmc1_pre_inst_state                   false
% 7.49/1.52  --bmc1_pre_inst_reach_state             false
% 7.49/1.52  --bmc1_out_unsat_core                   false
% 7.49/1.52  --bmc1_aig_witness_out                  false
% 7.49/1.52  --bmc1_verbose                          false
% 7.49/1.52  --bmc1_dump_clauses_tptp                false
% 7.49/1.52  --bmc1_dump_unsat_core_tptp             false
% 7.49/1.52  --bmc1_dump_file                        -
% 7.49/1.52  --bmc1_ucm_expand_uc_limit              128
% 7.49/1.52  --bmc1_ucm_n_expand_iterations          6
% 7.49/1.52  --bmc1_ucm_extend_mode                  1
% 7.49/1.52  --bmc1_ucm_init_mode                    2
% 7.49/1.52  --bmc1_ucm_cone_mode                    none
% 7.49/1.52  --bmc1_ucm_reduced_relation_type        0
% 7.49/1.52  --bmc1_ucm_relax_model                  4
% 7.49/1.52  --bmc1_ucm_full_tr_after_sat            true
% 7.49/1.52  --bmc1_ucm_expand_neg_assumptions       false
% 7.49/1.52  --bmc1_ucm_layered_model                none
% 7.49/1.52  --bmc1_ucm_max_lemma_size               10
% 7.49/1.52  
% 7.49/1.52  ------ AIG Options
% 7.49/1.52  
% 7.49/1.52  --aig_mode                              false
% 7.49/1.52  
% 7.49/1.52  ------ Instantiation Options
% 7.49/1.52  
% 7.49/1.52  --instantiation_flag                    true
% 7.49/1.52  --inst_sos_flag                         true
% 7.49/1.52  --inst_sos_phase                        true
% 7.49/1.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.49/1.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.49/1.52  --inst_lit_sel_side                     num_symb
% 7.49/1.52  --inst_solver_per_active                1400
% 7.49/1.52  --inst_solver_calls_frac                1.
% 7.49/1.52  --inst_passive_queue_type               priority_queues
% 7.49/1.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.49/1.52  --inst_passive_queues_freq              [25;2]
% 7.49/1.52  --inst_dismatching                      true
% 7.49/1.52  --inst_eager_unprocessed_to_passive     true
% 7.49/1.52  --inst_prop_sim_given                   true
% 7.49/1.52  --inst_prop_sim_new                     false
% 7.49/1.52  --inst_subs_new                         false
% 7.49/1.52  --inst_eq_res_simp                      false
% 7.49/1.52  --inst_subs_given                       false
% 7.49/1.52  --inst_orphan_elimination               true
% 7.49/1.52  --inst_learning_loop_flag               true
% 7.49/1.52  --inst_learning_start                   3000
% 7.49/1.52  --inst_learning_factor                  2
% 7.49/1.52  --inst_start_prop_sim_after_learn       3
% 7.49/1.52  --inst_sel_renew                        solver
% 7.49/1.52  --inst_lit_activity_flag                true
% 7.49/1.52  --inst_restr_to_given                   false
% 7.49/1.52  --inst_activity_threshold               500
% 7.49/1.52  --inst_out_proof                        true
% 7.49/1.52  
% 7.49/1.52  ------ Resolution Options
% 7.49/1.52  
% 7.49/1.52  --resolution_flag                       true
% 7.49/1.52  --res_lit_sel                           adaptive
% 7.49/1.52  --res_lit_sel_side                      none
% 7.49/1.52  --res_ordering                          kbo
% 7.49/1.52  --res_to_prop_solver                    active
% 7.49/1.52  --res_prop_simpl_new                    false
% 7.49/1.52  --res_prop_simpl_given                  true
% 7.49/1.52  --res_passive_queue_type                priority_queues
% 7.49/1.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.49/1.52  --res_passive_queues_freq               [15;5]
% 7.49/1.52  --res_forward_subs                      full
% 7.49/1.52  --res_backward_subs                     full
% 7.49/1.52  --res_forward_subs_resolution           true
% 7.49/1.52  --res_backward_subs_resolution          true
% 7.49/1.52  --res_orphan_elimination                true
% 7.49/1.52  --res_time_limit                        2.
% 7.49/1.52  --res_out_proof                         true
% 7.49/1.52  
% 7.49/1.52  ------ Superposition Options
% 7.49/1.52  
% 7.49/1.52  --superposition_flag                    true
% 7.49/1.52  --sup_passive_queue_type                priority_queues
% 7.49/1.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.49/1.52  --sup_passive_queues_freq               [8;1;4]
% 7.49/1.52  --demod_completeness_check              fast
% 7.49/1.52  --demod_use_ground                      true
% 7.49/1.52  --sup_to_prop_solver                    passive
% 7.49/1.52  --sup_prop_simpl_new                    true
% 7.49/1.52  --sup_prop_simpl_given                  true
% 7.49/1.52  --sup_fun_splitting                     true
% 7.49/1.52  --sup_smt_interval                      50000
% 7.49/1.52  
% 7.49/1.52  ------ Superposition Simplification Setup
% 7.49/1.52  
% 7.49/1.52  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.49/1.52  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.49/1.52  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.49/1.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.49/1.52  --sup_full_triv                         [TrivRules;PropSubs]
% 7.49/1.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.49/1.52  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.49/1.52  --sup_immed_triv                        [TrivRules]
% 7.49/1.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.49/1.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.49/1.52  --sup_immed_bw_main                     []
% 7.49/1.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.49/1.52  --sup_input_triv                        [Unflattening;TrivRules]
% 7.49/1.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.49/1.52  --sup_input_bw                          []
% 7.49/1.52  
% 7.49/1.52  ------ Combination Options
% 7.49/1.52  
% 7.49/1.52  --comb_res_mult                         3
% 7.49/1.52  --comb_sup_mult                         2
% 7.49/1.52  --comb_inst_mult                        10
% 7.49/1.52  
% 7.49/1.52  ------ Debug Options
% 7.49/1.52  
% 7.49/1.52  --dbg_backtrace                         false
% 7.49/1.52  --dbg_dump_prop_clauses                 false
% 7.49/1.52  --dbg_dump_prop_clauses_file            -
% 7.49/1.52  --dbg_out_stat                          false
% 7.49/1.52  ------ Parsing...
% 7.49/1.52  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.49/1.52  
% 7.49/1.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 7.49/1.52  
% 7.49/1.52  ------ Preprocessing... gs_s  sp: 8 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.49/1.52  
% 7.49/1.52  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.49/1.52  ------ Proving...
% 7.49/1.52  ------ Problem Properties 
% 7.49/1.52  
% 7.49/1.52  
% 7.49/1.52  clauses                                 41
% 7.49/1.52  conjectures                             8
% 7.49/1.52  EPR                                     12
% 7.49/1.52  Horn                                    35
% 7.49/1.52  unary                                   3
% 7.49/1.52  binary                                  18
% 7.49/1.52  lits                                    107
% 7.49/1.52  lits eq                                 11
% 7.49/1.52  fd_pure                                 0
% 7.49/1.52  fd_pseudo                               0
% 7.49/1.52  fd_cond                                 0
% 7.49/1.52  fd_pseudo_cond                          1
% 7.49/1.52  AC symbols                              0
% 7.49/1.52  
% 7.49/1.52  ------ Schedule dynamic 5 is on 
% 7.49/1.52  
% 7.49/1.52  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.49/1.52  
% 7.49/1.52  
% 7.49/1.52  ------ 
% 7.49/1.52  Current options:
% 7.49/1.52  ------ 
% 7.49/1.52  
% 7.49/1.52  ------ Input Options
% 7.49/1.52  
% 7.49/1.52  --out_options                           all
% 7.49/1.52  --tptp_safe_out                         true
% 7.49/1.52  --problem_path                          ""
% 7.49/1.52  --include_path                          ""
% 7.49/1.52  --clausifier                            res/vclausify_rel
% 7.49/1.52  --clausifier_options                    ""
% 7.49/1.52  --stdin                                 false
% 7.49/1.52  --stats_out                             all
% 7.49/1.52  
% 7.49/1.52  ------ General Options
% 7.49/1.52  
% 7.49/1.52  --fof                                   false
% 7.49/1.52  --time_out_real                         305.
% 7.49/1.52  --time_out_virtual                      -1.
% 7.49/1.52  --symbol_type_check                     false
% 7.49/1.52  --clausify_out                          false
% 7.49/1.52  --sig_cnt_out                           false
% 7.49/1.52  --trig_cnt_out                          false
% 7.49/1.52  --trig_cnt_out_tolerance                1.
% 7.49/1.52  --trig_cnt_out_sk_spl                   false
% 7.49/1.52  --abstr_cl_out                          false
% 7.49/1.52  
% 7.49/1.52  ------ Global Options
% 7.49/1.52  
% 7.49/1.52  --schedule                              default
% 7.49/1.52  --add_important_lit                     false
% 7.49/1.52  --prop_solver_per_cl                    1000
% 7.49/1.52  --min_unsat_core                        false
% 7.49/1.52  --soft_assumptions                      false
% 7.49/1.52  --soft_lemma_size                       3
% 7.49/1.52  --prop_impl_unit_size                   0
% 7.49/1.52  --prop_impl_unit                        []
% 7.49/1.52  --share_sel_clauses                     true
% 7.49/1.52  --reset_solvers                         false
% 7.49/1.52  --bc_imp_inh                            [conj_cone]
% 7.49/1.52  --conj_cone_tolerance                   3.
% 7.49/1.52  --extra_neg_conj                        none
% 7.49/1.52  --large_theory_mode                     true
% 7.49/1.52  --prolific_symb_bound                   200
% 7.49/1.52  --lt_threshold                          2000
% 7.49/1.52  --clause_weak_htbl                      true
% 7.49/1.52  --gc_record_bc_elim                     false
% 7.49/1.52  
% 7.49/1.52  ------ Preprocessing Options
% 7.49/1.52  
% 7.49/1.52  --preprocessing_flag                    true
% 7.49/1.52  --time_out_prep_mult                    0.1
% 7.49/1.52  --splitting_mode                        input
% 7.49/1.52  --splitting_grd                         true
% 7.49/1.52  --splitting_cvd                         false
% 7.49/1.52  --splitting_cvd_svl                     false
% 7.49/1.52  --splitting_nvd                         32
% 7.49/1.52  --sub_typing                            true
% 7.49/1.52  --prep_gs_sim                           true
% 7.49/1.52  --prep_unflatten                        true
% 7.49/1.52  --prep_res_sim                          true
% 7.49/1.52  --prep_upred                            true
% 7.49/1.52  --prep_sem_filter                       exhaustive
% 7.49/1.52  --prep_sem_filter_out                   false
% 7.49/1.52  --pred_elim                             true
% 7.49/1.52  --res_sim_input                         true
% 7.49/1.52  --eq_ax_congr_red                       true
% 7.49/1.52  --pure_diseq_elim                       true
% 7.49/1.52  --brand_transform                       false
% 7.49/1.52  --non_eq_to_eq                          false
% 7.49/1.52  --prep_def_merge                        true
% 7.49/1.52  --prep_def_merge_prop_impl              false
% 7.49/1.52  --prep_def_merge_mbd                    true
% 7.49/1.52  --prep_def_merge_tr_red                 false
% 7.49/1.52  --prep_def_merge_tr_cl                  false
% 7.49/1.52  --smt_preprocessing                     true
% 7.49/1.52  --smt_ac_axioms                         fast
% 7.49/1.52  --preprocessed_out                      false
% 7.49/1.52  --preprocessed_stats                    false
% 7.49/1.52  
% 7.49/1.52  ------ Abstraction refinement Options
% 7.49/1.52  
% 7.49/1.52  --abstr_ref                             []
% 7.49/1.52  --abstr_ref_prep                        false
% 7.49/1.52  --abstr_ref_until_sat                   false
% 7.49/1.52  --abstr_ref_sig_restrict                funpre
% 7.49/1.52  --abstr_ref_af_restrict_to_split_sk     false
% 7.49/1.52  --abstr_ref_under                       []
% 7.49/1.52  
% 7.49/1.52  ------ SAT Options
% 7.49/1.52  
% 7.49/1.52  --sat_mode                              false
% 7.49/1.52  --sat_fm_restart_options                ""
% 7.49/1.52  --sat_gr_def                            false
% 7.49/1.52  --sat_epr_types                         true
% 7.49/1.52  --sat_non_cyclic_types                  false
% 7.49/1.52  --sat_finite_models                     false
% 7.49/1.52  --sat_fm_lemmas                         false
% 7.49/1.52  --sat_fm_prep                           false
% 7.49/1.52  --sat_fm_uc_incr                        true
% 7.49/1.52  --sat_out_model                         small
% 7.49/1.52  --sat_out_clauses                       false
% 7.49/1.52  
% 7.49/1.52  ------ QBF Options
% 7.49/1.52  
% 7.49/1.52  --qbf_mode                              false
% 7.49/1.52  --qbf_elim_univ                         false
% 7.49/1.52  --qbf_dom_inst                          none
% 7.49/1.52  --qbf_dom_pre_inst                      false
% 7.49/1.52  --qbf_sk_in                             false
% 7.49/1.52  --qbf_pred_elim                         true
% 7.49/1.52  --qbf_split                             512
% 7.49/1.52  
% 7.49/1.52  ------ BMC1 Options
% 7.49/1.52  
% 7.49/1.52  --bmc1_incremental                      false
% 7.49/1.52  --bmc1_axioms                           reachable_all
% 7.49/1.52  --bmc1_min_bound                        0
% 7.49/1.52  --bmc1_max_bound                        -1
% 7.49/1.52  --bmc1_max_bound_default                -1
% 7.49/1.52  --bmc1_symbol_reachability              true
% 7.49/1.52  --bmc1_property_lemmas                  false
% 7.49/1.52  --bmc1_k_induction                      false
% 7.49/1.52  --bmc1_non_equiv_states                 false
% 7.49/1.52  --bmc1_deadlock                         false
% 7.49/1.52  --bmc1_ucm                              false
% 7.49/1.52  --bmc1_add_unsat_core                   none
% 7.49/1.52  --bmc1_unsat_core_children              false
% 7.49/1.52  --bmc1_unsat_core_extrapolate_axioms    false
% 7.49/1.52  --bmc1_out_stat                         full
% 7.49/1.52  --bmc1_ground_init                      false
% 7.49/1.52  --bmc1_pre_inst_next_state              false
% 7.49/1.52  --bmc1_pre_inst_state                   false
% 7.49/1.52  --bmc1_pre_inst_reach_state             false
% 7.49/1.52  --bmc1_out_unsat_core                   false
% 7.49/1.52  --bmc1_aig_witness_out                  false
% 7.49/1.52  --bmc1_verbose                          false
% 7.49/1.52  --bmc1_dump_clauses_tptp                false
% 7.49/1.52  --bmc1_dump_unsat_core_tptp             false
% 7.49/1.52  --bmc1_dump_file                        -
% 7.49/1.52  --bmc1_ucm_expand_uc_limit              128
% 7.49/1.52  --bmc1_ucm_n_expand_iterations          6
% 7.49/1.52  --bmc1_ucm_extend_mode                  1
% 7.49/1.52  --bmc1_ucm_init_mode                    2
% 7.49/1.52  --bmc1_ucm_cone_mode                    none
% 7.49/1.52  --bmc1_ucm_reduced_relation_type        0
% 7.49/1.52  --bmc1_ucm_relax_model                  4
% 7.49/1.52  --bmc1_ucm_full_tr_after_sat            true
% 7.49/1.52  --bmc1_ucm_expand_neg_assumptions       false
% 7.49/1.52  --bmc1_ucm_layered_model                none
% 7.49/1.52  --bmc1_ucm_max_lemma_size               10
% 7.49/1.52  
% 7.49/1.52  ------ AIG Options
% 7.49/1.52  
% 7.49/1.52  --aig_mode                              false
% 7.49/1.52  
% 7.49/1.52  ------ Instantiation Options
% 7.49/1.52  
% 7.49/1.52  --instantiation_flag                    true
% 7.49/1.52  --inst_sos_flag                         true
% 7.49/1.52  --inst_sos_phase                        true
% 7.49/1.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.49/1.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.49/1.52  --inst_lit_sel_side                     none
% 7.49/1.52  --inst_solver_per_active                1400
% 7.49/1.52  --inst_solver_calls_frac                1.
% 7.49/1.52  --inst_passive_queue_type               priority_queues
% 7.49/1.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.49/1.52  --inst_passive_queues_freq              [25;2]
% 7.49/1.52  --inst_dismatching                      true
% 7.49/1.52  --inst_eager_unprocessed_to_passive     true
% 7.49/1.52  --inst_prop_sim_given                   true
% 7.49/1.52  --inst_prop_sim_new                     false
% 7.49/1.52  --inst_subs_new                         false
% 7.49/1.52  --inst_eq_res_simp                      false
% 7.49/1.52  --inst_subs_given                       false
% 7.49/1.52  --inst_orphan_elimination               true
% 7.49/1.52  --inst_learning_loop_flag               true
% 7.49/1.52  --inst_learning_start                   3000
% 7.49/1.52  --inst_learning_factor                  2
% 7.49/1.52  --inst_start_prop_sim_after_learn       3
% 7.49/1.52  --inst_sel_renew                        solver
% 7.49/1.52  --inst_lit_activity_flag                true
% 7.49/1.52  --inst_restr_to_given                   false
% 7.49/1.52  --inst_activity_threshold               500
% 7.49/1.52  --inst_out_proof                        true
% 7.49/1.52  
% 7.49/1.52  ------ Resolution Options
% 7.49/1.52  
% 7.49/1.52  --resolution_flag                       false
% 7.49/1.52  --res_lit_sel                           adaptive
% 7.49/1.52  --res_lit_sel_side                      none
% 7.49/1.52  --res_ordering                          kbo
% 7.49/1.52  --res_to_prop_solver                    active
% 7.49/1.52  --res_prop_simpl_new                    false
% 7.49/1.52  --res_prop_simpl_given                  true
% 7.49/1.52  --res_passive_queue_type                priority_queues
% 7.49/1.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.49/1.52  --res_passive_queues_freq               [15;5]
% 7.49/1.52  --res_forward_subs                      full
% 7.49/1.52  --res_backward_subs                     full
% 7.49/1.52  --res_forward_subs_resolution           true
% 7.49/1.52  --res_backward_subs_resolution          true
% 7.49/1.52  --res_orphan_elimination                true
% 7.49/1.52  --res_time_limit                        2.
% 7.49/1.52  --res_out_proof                         true
% 7.49/1.52  
% 7.49/1.52  ------ Superposition Options
% 7.49/1.52  
% 7.49/1.52  --superposition_flag                    true
% 7.49/1.52  --sup_passive_queue_type                priority_queues
% 7.49/1.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.49/1.52  --sup_passive_queues_freq               [8;1;4]
% 7.49/1.52  --demod_completeness_check              fast
% 7.49/1.52  --demod_use_ground                      true
% 7.49/1.52  --sup_to_prop_solver                    passive
% 7.49/1.52  --sup_prop_simpl_new                    true
% 7.49/1.52  --sup_prop_simpl_given                  true
% 7.49/1.52  --sup_fun_splitting                     true
% 7.49/1.52  --sup_smt_interval                      50000
% 7.49/1.52  
% 7.49/1.52  ------ Superposition Simplification Setup
% 7.49/1.52  
% 7.49/1.52  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.49/1.52  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.49/1.52  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.49/1.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.49/1.52  --sup_full_triv                         [TrivRules;PropSubs]
% 7.49/1.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.49/1.52  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.49/1.52  --sup_immed_triv                        [TrivRules]
% 7.49/1.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.49/1.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.49/1.52  --sup_immed_bw_main                     []
% 7.49/1.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.49/1.52  --sup_input_triv                        [Unflattening;TrivRules]
% 7.49/1.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.49/1.52  --sup_input_bw                          []
% 7.49/1.52  
% 7.49/1.52  ------ Combination Options
% 7.49/1.52  
% 7.49/1.52  --comb_res_mult                         3
% 7.49/1.52  --comb_sup_mult                         2
% 7.49/1.52  --comb_inst_mult                        10
% 7.49/1.52  
% 7.49/1.52  ------ Debug Options
% 7.49/1.52  
% 7.49/1.52  --dbg_backtrace                         false
% 7.49/1.52  --dbg_dump_prop_clauses                 false
% 7.49/1.52  --dbg_dump_prop_clauses_file            -
% 7.49/1.52  --dbg_out_stat                          false
% 7.49/1.52  
% 7.49/1.52  
% 7.49/1.52  
% 7.49/1.52  
% 7.49/1.52  ------ Proving...
% 7.49/1.52  
% 7.49/1.52  
% 7.49/1.52  % SZS status Theorem for theBenchmark.p
% 7.49/1.52  
% 7.49/1.52  % SZS output start CNFRefutation for theBenchmark.p
% 7.49/1.52  
% 7.49/1.52  fof(f10,conjecture,(
% 7.49/1.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v6_tops_1(X2,X0) => (v4_tops_1(X2,X0) & v3_pre_topc(X2,X0))) & ((v4_tops_1(X3,X1) & v3_pre_topc(X3,X1)) => v6_tops_1(X3,X1)))))))),
% 7.49/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.52  
% 7.49/1.52  fof(f11,negated_conjecture,(
% 7.49/1.52    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v6_tops_1(X2,X0) => (v4_tops_1(X2,X0) & v3_pre_topc(X2,X0))) & ((v4_tops_1(X3,X1) & v3_pre_topc(X3,X1)) => v6_tops_1(X3,X1)))))))),
% 7.49/1.52    inference(negated_conjecture,[],[f10])).
% 7.49/1.52  
% 7.49/1.52  fof(f25,plain,(
% 7.49/1.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(X3,X1) & (v4_tops_1(X3,X1) & v3_pre_topc(X3,X1)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 7.49/1.52    inference(ennf_transformation,[],[f11])).
% 7.49/1.52  
% 7.49/1.52  fof(f26,plain,(
% 7.49/1.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.49/1.52    inference(flattening,[],[f25])).
% 7.49/1.52  
% 7.49/1.52  fof(f35,plain,(
% 7.49/1.52    ( ! [X2,X0,X1] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(sK3,X1) & v4_tops_1(sK3,X1) & v3_pre_topc(sK3,X1))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X1))))) )),
% 7.49/1.52    introduced(choice_axiom,[])).
% 7.49/1.52  
% 7.49/1.52  fof(f34,plain,(
% 7.49/1.52    ( ! [X0,X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X3] : ((((~v4_tops_1(sK2,X0) | ~v3_pre_topc(sK2,X0)) & v6_tops_1(sK2,X0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 7.49/1.52    introduced(choice_axiom,[])).
% 7.49/1.52  
% 7.49/1.52  fof(f33,plain,(
% 7.49/1.52    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) => (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(X3,sK1) & v4_tops_1(X3,sK1) & v3_pre_topc(X3,sK1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(sK1))) )),
% 7.49/1.52    introduced(choice_axiom,[])).
% 7.49/1.52  
% 7.49/1.52  fof(f32,plain,(
% 7.49/1.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,sK0) | ~v3_pre_topc(X2,sK0)) & v6_tops_1(X2,sK0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 7.49/1.52    introduced(choice_axiom,[])).
% 7.49/1.52  
% 7.49/1.52  fof(f36,plain,(
% 7.49/1.52    ((((((~v4_tops_1(sK2,sK0) | ~v3_pre_topc(sK2,sK0)) & v6_tops_1(sK2,sK0)) | (~v6_tops_1(sK3,sK1) & v4_tops_1(sK3,sK1) & v3_pre_topc(sK3,sK1))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 7.49/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f26,f35,f34,f33,f32])).
% 7.49/1.52  
% 7.49/1.52  fof(f57,plain,(
% 7.49/1.52    v6_tops_1(sK2,sK0) | v3_pre_topc(sK3,sK1)),
% 7.49/1.52    inference(cnf_transformation,[],[f36])).
% 7.49/1.52  
% 7.49/1.52  fof(f56,plain,(
% 7.49/1.52    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 7.49/1.52    inference(cnf_transformation,[],[f36])).
% 7.49/1.52  
% 7.49/1.52  fof(f9,axiom,(
% 7.49/1.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 7.49/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.52  
% 7.49/1.52  fof(f23,plain,(
% 7.49/1.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.49/1.52    inference(ennf_transformation,[],[f9])).
% 7.49/1.52  
% 7.49/1.52  fof(f24,plain,(
% 7.49/1.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.49/1.52    inference(flattening,[],[f23])).
% 7.49/1.52  
% 7.49/1.52  fof(f50,plain,(
% 7.49/1.52    ( ! [X2,X0,X3,X1] : (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.49/1.52    inference(cnf_transformation,[],[f24])).
% 7.49/1.52  
% 7.49/1.52  fof(f52,plain,(
% 7.49/1.52    v2_pre_topc(sK0)),
% 7.49/1.52    inference(cnf_transformation,[],[f36])).
% 7.49/1.52  
% 7.49/1.52  fof(f53,plain,(
% 7.49/1.52    l1_pre_topc(sK0)),
% 7.49/1.52    inference(cnf_transformation,[],[f36])).
% 7.49/1.52  
% 7.49/1.52  fof(f54,plain,(
% 7.49/1.52    l1_pre_topc(sK1)),
% 7.49/1.52    inference(cnf_transformation,[],[f36])).
% 7.49/1.52  
% 7.49/1.52  fof(f55,plain,(
% 7.49/1.52    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 7.49/1.52    inference(cnf_transformation,[],[f36])).
% 7.49/1.52  
% 7.49/1.52  fof(f51,plain,(
% 7.49/1.52    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.49/1.52    inference(cnf_transformation,[],[f24])).
% 7.49/1.52  
% 7.49/1.52  fof(f4,axiom,(
% 7.49/1.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v6_tops_1(X1,X0) <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1)))),
% 7.49/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.52  
% 7.49/1.52  fof(f15,plain,(
% 7.49/1.52    ! [X0] : (! [X1] : ((v6_tops_1(X1,X0) <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.49/1.52    inference(ennf_transformation,[],[f4])).
% 7.49/1.52  
% 7.49/1.52  fof(f31,plain,(
% 7.49/1.52    ! [X0] : (! [X1] : (((v6_tops_1(X1,X0) | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1) & (k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 | ~v6_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.49/1.52    inference(nnf_transformation,[],[f15])).
% 7.49/1.52  
% 7.49/1.52  fof(f44,plain,(
% 7.49/1.52    ( ! [X0,X1] : (k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 | ~v6_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.49/1.52    inference(cnf_transformation,[],[f31])).
% 7.49/1.52  
% 7.49/1.52  fof(f2,axiom,(
% 7.49/1.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 7.49/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.52  
% 7.49/1.52  fof(f12,plain,(
% 7.49/1.52    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 7.49/1.52    inference(ennf_transformation,[],[f2])).
% 7.49/1.52  
% 7.49/1.52  fof(f13,plain,(
% 7.49/1.52    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 7.49/1.52    inference(flattening,[],[f12])).
% 7.49/1.52  
% 7.49/1.52  fof(f40,plain,(
% 7.49/1.52    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.49/1.52    inference(cnf_transformation,[],[f13])).
% 7.49/1.52  
% 7.49/1.52  fof(f6,axiom,(
% 7.49/1.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)))),
% 7.49/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.52  
% 7.49/1.52  fof(f18,plain,(
% 7.49/1.52    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 7.49/1.52    inference(ennf_transformation,[],[f6])).
% 7.49/1.52  
% 7.49/1.52  fof(f19,plain,(
% 7.49/1.52    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 7.49/1.52    inference(flattening,[],[f18])).
% 7.49/1.52  
% 7.49/1.52  fof(f47,plain,(
% 7.49/1.52    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.49/1.52    inference(cnf_transformation,[],[f19])).
% 7.49/1.52  
% 7.49/1.52  fof(f59,plain,(
% 7.49/1.52    v6_tops_1(sK2,sK0) | ~v6_tops_1(sK3,sK1)),
% 7.49/1.52    inference(cnf_transformation,[],[f36])).
% 7.49/1.52  
% 7.49/1.52  fof(f1,axiom,(
% 7.49/1.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.49/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.52  
% 7.49/1.52  fof(f27,plain,(
% 7.49/1.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.49/1.52    inference(nnf_transformation,[],[f1])).
% 7.49/1.52  
% 7.49/1.52  fof(f28,plain,(
% 7.49/1.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.49/1.52    inference(flattening,[],[f27])).
% 7.49/1.52  
% 7.49/1.52  fof(f37,plain,(
% 7.49/1.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.49/1.52    inference(cnf_transformation,[],[f28])).
% 7.49/1.52  
% 7.49/1.52  fof(f64,plain,(
% 7.49/1.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.49/1.52    inference(equality_resolution,[],[f37])).
% 7.49/1.52  
% 7.49/1.52  fof(f39,plain,(
% 7.49/1.52    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.49/1.52    inference(cnf_transformation,[],[f28])).
% 7.49/1.52  
% 7.49/1.52  fof(f5,axiom,(
% 7.49/1.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 7.49/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.52  
% 7.49/1.52  fof(f16,plain,(
% 7.49/1.52    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.49/1.52    inference(ennf_transformation,[],[f5])).
% 7.49/1.52  
% 7.49/1.52  fof(f17,plain,(
% 7.49/1.52    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.49/1.52    inference(flattening,[],[f16])).
% 7.49/1.52  
% 7.49/1.52  fof(f46,plain,(
% 7.49/1.52    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.49/1.52    inference(cnf_transformation,[],[f17])).
% 7.49/1.52  
% 7.49/1.52  fof(f58,plain,(
% 7.49/1.52    v6_tops_1(sK2,sK0) | v4_tops_1(sK3,sK1)),
% 7.49/1.52    inference(cnf_transformation,[],[f36])).
% 7.49/1.52  
% 7.49/1.52  fof(f45,plain,(
% 7.49/1.52    ( ! [X0,X1] : (v6_tops_1(X1,X0) | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.49/1.52    inference(cnf_transformation,[],[f31])).
% 7.49/1.52  
% 7.49/1.52  fof(f8,axiom,(
% 7.49/1.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 7.49/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.52  
% 7.49/1.52  fof(f21,plain,(
% 7.49/1.52    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.49/1.52    inference(ennf_transformation,[],[f8])).
% 7.49/1.52  
% 7.49/1.52  fof(f22,plain,(
% 7.49/1.52    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.49/1.52    inference(flattening,[],[f21])).
% 7.49/1.52  
% 7.49/1.52  fof(f49,plain,(
% 7.49/1.52    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.49/1.52    inference(cnf_transformation,[],[f22])).
% 7.49/1.52  
% 7.49/1.52  fof(f3,axiom,(
% 7.49/1.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)))))),
% 7.49/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.52  
% 7.49/1.52  fof(f14,plain,(
% 7.49/1.52    ! [X0] : (! [X1] : ((v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.49/1.52    inference(ennf_transformation,[],[f3])).
% 7.49/1.52  
% 7.49/1.52  fof(f29,plain,(
% 7.49/1.52    ! [X0] : (! [X1] : (((v4_tops_1(X1,X0) | (~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1))) & ((r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) | ~v4_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.49/1.52    inference(nnf_transformation,[],[f14])).
% 7.49/1.52  
% 7.49/1.52  fof(f30,plain,(
% 7.49/1.52    ! [X0] : (! [X1] : (((v4_tops_1(X1,X0) | ~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) & ((r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) | ~v4_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.49/1.52    inference(flattening,[],[f29])).
% 7.49/1.52  
% 7.49/1.52  fof(f41,plain,(
% 7.49/1.52    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) | ~v4_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.49/1.52    inference(cnf_transformation,[],[f30])).
% 7.49/1.52  
% 7.49/1.52  fof(f42,plain,(
% 7.49/1.52    ( ! [X0,X1] : (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~v4_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.49/1.52    inference(cnf_transformation,[],[f30])).
% 7.49/1.52  
% 7.49/1.52  fof(f43,plain,(
% 7.49/1.52    ( ! [X0,X1] : (v4_tops_1(X1,X0) | ~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.49/1.52    inference(cnf_transformation,[],[f30])).
% 7.49/1.52  
% 7.49/1.52  fof(f61,plain,(
% 7.49/1.52    ~v4_tops_1(sK2,sK0) | ~v3_pre_topc(sK2,sK0) | v4_tops_1(sK3,sK1)),
% 7.49/1.52    inference(cnf_transformation,[],[f36])).
% 7.49/1.52  
% 7.49/1.52  fof(f60,plain,(
% 7.49/1.52    ~v4_tops_1(sK2,sK0) | ~v3_pre_topc(sK2,sK0) | v3_pre_topc(sK3,sK1)),
% 7.49/1.52    inference(cnf_transformation,[],[f36])).
% 7.49/1.52  
% 7.49/1.52  fof(f7,axiom,(
% 7.49/1.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 7.49/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.52  
% 7.49/1.52  fof(f20,plain,(
% 7.49/1.52    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.49/1.52    inference(ennf_transformation,[],[f7])).
% 7.49/1.52  
% 7.49/1.52  fof(f48,plain,(
% 7.49/1.52    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.49/1.52    inference(cnf_transformation,[],[f20])).
% 7.49/1.52  
% 7.49/1.52  fof(f62,plain,(
% 7.49/1.52    ~v4_tops_1(sK2,sK0) | ~v3_pre_topc(sK2,sK0) | ~v6_tops_1(sK3,sK1)),
% 7.49/1.52    inference(cnf_transformation,[],[f36])).
% 7.49/1.52  
% 7.49/1.52  cnf(c_20,negated_conjecture,
% 7.49/1.52      ( v3_pre_topc(sK3,sK1) | v6_tops_1(sK2,sK0) ),
% 7.49/1.52      inference(cnf_transformation,[],[f57]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_1462,plain,
% 7.49/1.52      ( v3_pre_topc(sK3,sK1) = iProver_top
% 7.49/1.52      | v6_tops_1(sK2,sK0) = iProver_top ),
% 7.49/1.52      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_21,negated_conjecture,
% 7.49/1.52      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 7.49/1.52      inference(cnf_transformation,[],[f56]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_1461,plain,
% 7.49/1.52      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 7.49/1.52      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_14,plain,
% 7.49/1.52      ( ~ v3_pre_topc(X0,X1)
% 7.49/1.52      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 7.49/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.49/1.52      | ~ v2_pre_topc(X3)
% 7.49/1.52      | ~ l1_pre_topc(X3)
% 7.49/1.52      | ~ l1_pre_topc(X1)
% 7.49/1.52      | k1_tops_1(X1,X0) = X0 ),
% 7.49/1.52      inference(cnf_transformation,[],[f50]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_25,negated_conjecture,
% 7.49/1.52      ( v2_pre_topc(sK0) ),
% 7.49/1.52      inference(cnf_transformation,[],[f52]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_318,plain,
% 7.49/1.52      ( ~ v3_pre_topc(X0,X1)
% 7.49/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.49/1.52      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 7.49/1.52      | ~ l1_pre_topc(X1)
% 7.49/1.52      | ~ l1_pre_topc(X3)
% 7.49/1.52      | k1_tops_1(X1,X0) = X0
% 7.49/1.52      | sK0 != X3 ),
% 7.49/1.52      inference(resolution_lifted,[status(thm)],[c_14,c_25]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_319,plain,
% 7.49/1.52      ( ~ v3_pre_topc(X0,X1)
% 7.49/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.49/1.52      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.49/1.52      | ~ l1_pre_topc(X1)
% 7.49/1.52      | ~ l1_pre_topc(sK0)
% 7.49/1.52      | k1_tops_1(X1,X0) = X0 ),
% 7.49/1.52      inference(unflattening,[status(thm)],[c_318]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_24,negated_conjecture,
% 7.49/1.52      ( l1_pre_topc(sK0) ),
% 7.49/1.52      inference(cnf_transformation,[],[f53]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_323,plain,
% 7.49/1.52      ( ~ l1_pre_topc(X1)
% 7.49/1.52      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.49/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.49/1.52      | ~ v3_pre_topc(X0,X1)
% 7.49/1.52      | k1_tops_1(X1,X0) = X0 ),
% 7.49/1.52      inference(global_propositional_subsumption,
% 7.49/1.52                [status(thm)],
% 7.49/1.52                [c_319,c_24]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_324,plain,
% 7.49/1.52      ( ~ v3_pre_topc(X0,X1)
% 7.49/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.49/1.52      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.49/1.52      | ~ l1_pre_topc(X1)
% 7.49/1.52      | k1_tops_1(X1,X0) = X0 ),
% 7.49/1.52      inference(renaming,[status(thm)],[c_323]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_23,negated_conjecture,
% 7.49/1.52      ( l1_pre_topc(sK1) ),
% 7.49/1.52      inference(cnf_transformation,[],[f54]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_358,plain,
% 7.49/1.52      ( ~ v3_pre_topc(X0,X1)
% 7.49/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.49/1.52      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.49/1.52      | k1_tops_1(X1,X0) = X0
% 7.49/1.52      | sK1 != X1 ),
% 7.49/1.52      inference(resolution_lifted,[status(thm)],[c_324,c_23]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_359,plain,
% 7.49/1.52      ( ~ v3_pre_topc(X0,sK1)
% 7.49/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.49/1.52      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.49/1.52      | k1_tops_1(sK1,X0) = X0 ),
% 7.49/1.52      inference(unflattening,[status(thm)],[c_358]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_791,plain,
% 7.49/1.52      ( ~ v3_pre_topc(X0,sK1)
% 7.49/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.49/1.52      | k1_tops_1(sK1,X0) = X0
% 7.49/1.52      | ~ sP4_iProver_split ),
% 7.49/1.52      inference(splitting,
% 7.49/1.52                [splitting(split),new_symbols(definition,[sP4_iProver_split])],
% 7.49/1.52                [c_359]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_1457,plain,
% 7.49/1.52      ( k1_tops_1(sK1,X0) = X0
% 7.49/1.52      | v3_pre_topc(X0,sK1) != iProver_top
% 7.49/1.52      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 7.49/1.52      | sP4_iProver_split != iProver_top ),
% 7.49/1.52      inference(predicate_to_equality,[status(thm)],[c_791]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_22,negated_conjecture,
% 7.49/1.52      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.49/1.52      inference(cnf_transformation,[],[f55]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_29,plain,
% 7.49/1.52      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.49/1.52      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_792,plain,
% 7.49/1.52      ( sP4_iProver_split | sP0_iProver_split ),
% 7.49/1.52      inference(splitting,
% 7.49/1.52                [splitting(split),new_symbols(definition,[])],
% 7.49/1.52                [c_359]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_847,plain,
% 7.49/1.52      ( sP4_iProver_split = iProver_top
% 7.49/1.52      | sP0_iProver_split = iProver_top ),
% 7.49/1.52      inference(predicate_to_equality,[status(thm)],[c_792]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_848,plain,
% 7.49/1.52      ( k1_tops_1(sK1,X0) = X0
% 7.49/1.52      | v3_pre_topc(X0,sK1) != iProver_top
% 7.49/1.52      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 7.49/1.52      | sP4_iProver_split != iProver_top ),
% 7.49/1.52      inference(predicate_to_equality,[status(thm)],[c_791]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_13,plain,
% 7.49/1.52      ( v3_pre_topc(X0,X1)
% 7.49/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.49/1.52      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 7.49/1.52      | ~ v2_pre_topc(X1)
% 7.49/1.52      | ~ l1_pre_topc(X1)
% 7.49/1.52      | ~ l1_pre_topc(X3)
% 7.49/1.52      | k1_tops_1(X1,X0) != X0 ),
% 7.49/1.52      inference(cnf_transformation,[],[f51]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_293,plain,
% 7.49/1.52      ( v3_pre_topc(X0,X1)
% 7.49/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.49/1.52      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 7.49/1.52      | ~ l1_pre_topc(X1)
% 7.49/1.52      | ~ l1_pre_topc(X3)
% 7.49/1.52      | k1_tops_1(X1,X0) != X0
% 7.49/1.52      | sK0 != X1 ),
% 7.49/1.52      inference(resolution_lifted,[status(thm)],[c_13,c_25]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_294,plain,
% 7.49/1.52      ( v3_pre_topc(X0,sK0)
% 7.49/1.52      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 7.49/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.49/1.52      | ~ l1_pre_topc(X2)
% 7.49/1.52      | ~ l1_pre_topc(sK0)
% 7.49/1.52      | k1_tops_1(sK0,X0) != X0 ),
% 7.49/1.52      inference(unflattening,[status(thm)],[c_293]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_298,plain,
% 7.49/1.52      ( ~ l1_pre_topc(X2)
% 7.49/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.49/1.52      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 7.49/1.52      | v3_pre_topc(X0,sK0)
% 7.49/1.52      | k1_tops_1(sK0,X0) != X0 ),
% 7.49/1.52      inference(global_propositional_subsumption,
% 7.49/1.52                [status(thm)],
% 7.49/1.52                [c_294,c_24]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_299,plain,
% 7.49/1.52      ( v3_pre_topc(X0,sK0)
% 7.49/1.52      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 7.49/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.49/1.52      | ~ l1_pre_topc(X2)
% 7.49/1.52      | k1_tops_1(sK0,X0) != X0 ),
% 7.49/1.52      inference(renaming,[status(thm)],[c_298]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_676,plain,
% 7.49/1.52      ( v3_pre_topc(X0,sK0)
% 7.49/1.52      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 7.49/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.49/1.52      | k1_tops_1(sK0,X0) != X0
% 7.49/1.52      | sK0 != X2 ),
% 7.49/1.52      inference(resolution_lifted,[status(thm)],[c_24,c_299]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_677,plain,
% 7.49/1.52      ( v3_pre_topc(X0,sK0)
% 7.49/1.52      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.49/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.49/1.52      | k1_tops_1(sK0,X0) != X0 ),
% 7.49/1.52      inference(unflattening,[status(thm)],[c_676]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_784,plain,
% 7.49/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.49/1.52      | ~ sP0_iProver_split ),
% 7.49/1.52      inference(splitting,
% 7.49/1.52                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 7.49/1.52                [c_677]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_1547,plain,
% 7.49/1.52      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.49/1.52      | ~ sP0_iProver_split ),
% 7.49/1.52      inference(instantiation,[status(thm)],[c_784]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_1548,plain,
% 7.49/1.52      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.49/1.52      | sP0_iProver_split != iProver_top ),
% 7.49/1.52      inference(predicate_to_equality,[status(thm)],[c_1547]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_2856,plain,
% 7.49/1.52      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 7.49/1.52      | v3_pre_topc(X0,sK1) != iProver_top
% 7.49/1.52      | k1_tops_1(sK1,X0) = X0 ),
% 7.49/1.52      inference(global_propositional_subsumption,
% 7.49/1.52                [status(thm)],
% 7.49/1.52                [c_1457,c_29,c_847,c_848,c_1548]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_2857,plain,
% 7.49/1.52      ( k1_tops_1(sK1,X0) = X0
% 7.49/1.52      | v3_pre_topc(X0,sK1) != iProver_top
% 7.49/1.52      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 7.49/1.52      inference(renaming,[status(thm)],[c_2856]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_2862,plain,
% 7.49/1.52      ( k1_tops_1(sK1,sK3) = sK3 | v3_pre_topc(sK3,sK1) != iProver_top ),
% 7.49/1.52      inference(superposition,[status(thm)],[c_1461,c_2857]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_2931,plain,
% 7.49/1.52      ( k1_tops_1(sK1,sK3) = sK3 | v6_tops_1(sK2,sK0) = iProver_top ),
% 7.49/1.52      inference(superposition,[status(thm)],[c_1462,c_2862]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_1460,plain,
% 7.49/1.52      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.49/1.52      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_8,plain,
% 7.49/1.52      ( ~ v6_tops_1(X0,X1)
% 7.49/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.49/1.52      | ~ l1_pre_topc(X1)
% 7.49/1.52      | k1_tops_1(X1,k2_pre_topc(X1,X0)) = X0 ),
% 7.49/1.52      inference(cnf_transformation,[],[f44]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_568,plain,
% 7.49/1.52      ( ~ v6_tops_1(X0,X1)
% 7.49/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.49/1.52      | k1_tops_1(X1,k2_pre_topc(X1,X0)) = X0
% 7.49/1.52      | sK0 != X1 ),
% 7.49/1.52      inference(resolution_lifted,[status(thm)],[c_8,c_24]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_569,plain,
% 7.49/1.52      ( ~ v6_tops_1(X0,sK0)
% 7.49/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.49/1.52      | k1_tops_1(sK0,k2_pre_topc(sK0,X0)) = X0 ),
% 7.49/1.52      inference(unflattening,[status(thm)],[c_568]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_1440,plain,
% 7.49/1.52      ( k1_tops_1(sK0,k2_pre_topc(sK0,X0)) = X0
% 7.49/1.52      | v6_tops_1(X0,sK0) != iProver_top
% 7.49/1.52      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.49/1.52      inference(predicate_to_equality,[status(thm)],[c_569]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_2375,plain,
% 7.49/1.52      ( k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = sK2
% 7.49/1.52      | v6_tops_1(sK2,sK0) != iProver_top ),
% 7.49/1.52      inference(superposition,[status(thm)],[c_1460,c_1440]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_3021,plain,
% 7.49/1.52      ( k1_tops_1(sK1,sK3) = sK3
% 7.49/1.52      | k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = sK2 ),
% 7.49/1.52      inference(superposition,[status(thm)],[c_2931,c_2375]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_3,plain,
% 7.49/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.49/1.52      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.49/1.52      | ~ l1_pre_topc(X1) ),
% 7.49/1.52      inference(cnf_transformation,[],[f40]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_646,plain,
% 7.49/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.49/1.52      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.49/1.52      | sK0 != X1 ),
% 7.49/1.52      inference(resolution_lifted,[status(thm)],[c_3,c_24]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_647,plain,
% 7.49/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.49/1.52      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.49/1.52      inference(unflattening,[status(thm)],[c_646]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_1435,plain,
% 7.49/1.52      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.49/1.52      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.49/1.52      inference(predicate_to_equality,[status(thm)],[c_647]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_10,plain,
% 7.49/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.49/1.52      | ~ l1_pre_topc(X1)
% 7.49/1.52      | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
% 7.49/1.52      inference(cnf_transformation,[],[f47]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_556,plain,
% 7.49/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.49/1.52      | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0)
% 7.49/1.52      | sK0 != X1 ),
% 7.49/1.52      inference(resolution_lifted,[status(thm)],[c_10,c_24]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_557,plain,
% 7.49/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.49/1.52      | k1_tops_1(sK0,k1_tops_1(sK0,X0)) = k1_tops_1(sK0,X0) ),
% 7.49/1.52      inference(unflattening,[status(thm)],[c_556]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_1441,plain,
% 7.49/1.52      ( k1_tops_1(sK0,k1_tops_1(sK0,X0)) = k1_tops_1(sK0,X0)
% 7.49/1.52      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.49/1.52      inference(predicate_to_equality,[status(thm)],[c_557]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_2177,plain,
% 7.49/1.52      ( k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,X0))) = k1_tops_1(sK0,k2_pre_topc(sK0,X0))
% 7.49/1.52      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.49/1.52      inference(superposition,[status(thm)],[c_1435,c_1441]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_3467,plain,
% 7.49/1.52      ( k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK2))) = k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) ),
% 7.49/1.52      inference(superposition,[status(thm)],[c_1460,c_2177]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_4130,plain,
% 7.49/1.52      ( k1_tops_1(sK1,sK3) = sK3
% 7.49/1.52      | k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = k1_tops_1(sK0,sK2) ),
% 7.49/1.52      inference(superposition,[status(thm)],[c_3021,c_3467]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_4186,plain,
% 7.49/1.52      ( k1_tops_1(sK1,sK3) = sK3 | k1_tops_1(sK0,sK2) = sK2 ),
% 7.49/1.52      inference(superposition,[status(thm)],[c_4130,c_3021]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_18,negated_conjecture,
% 7.49/1.52      ( ~ v6_tops_1(sK3,sK1) | v6_tops_1(sK2,sK0) ),
% 7.49/1.52      inference(cnf_transformation,[],[f59]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_2,plain,
% 7.49/1.52      ( r1_tarski(X0,X0) ),
% 7.49/1.52      inference(cnf_transformation,[],[f64]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_74,plain,
% 7.49/1.52      ( r1_tarski(sK0,sK0) ),
% 7.49/1.52      inference(instantiation,[status(thm)],[c_2]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_0,plain,
% 7.49/1.52      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.49/1.52      inference(cnf_transformation,[],[f39]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_78,plain,
% 7.49/1.52      ( ~ r1_tarski(sK0,sK0) | sK0 = sK0 ),
% 7.49/1.52      inference(instantiation,[status(thm)],[c_0]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_1569,plain,
% 7.49/1.52      ( m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 7.49/1.52      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.49/1.52      inference(instantiation,[status(thm)],[c_647]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_9,plain,
% 7.49/1.52      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 7.49/1.52      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 7.49/1.52      | ~ v2_pre_topc(X0)
% 7.49/1.52      | ~ l1_pre_topc(X0) ),
% 7.49/1.52      inference(cnf_transformation,[],[f46]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_275,plain,
% 7.49/1.52      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 7.49/1.52      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 7.49/1.52      | ~ l1_pre_topc(X0)
% 7.49/1.52      | sK0 != X0 ),
% 7.49/1.52      inference(resolution_lifted,[status(thm)],[c_9,c_25]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_276,plain,
% 7.49/1.52      ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
% 7.49/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.49/1.52      | ~ l1_pre_topc(sK0) ),
% 7.49/1.52      inference(unflattening,[status(thm)],[c_275]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_280,plain,
% 7.49/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.49/1.52      | v3_pre_topc(k1_tops_1(sK0,X0),sK0) ),
% 7.49/1.52      inference(global_propositional_subsumption,
% 7.49/1.52                [status(thm)],
% 7.49/1.52                [c_276,c_24]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_281,plain,
% 7.49/1.52      ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
% 7.49/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.49/1.52      inference(renaming,[status(thm)],[c_280]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_1679,plain,
% 7.49/1.52      ( v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK0)
% 7.49/1.52      | ~ m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.49/1.52      inference(instantiation,[status(thm)],[c_281]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_794,plain,( X0 = X0 ),theory(equality) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_2102,plain,
% 7.49/1.52      ( sK2 = sK2 ),
% 7.49/1.52      inference(instantiation,[status(thm)],[c_794]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_2295,plain,
% 7.49/1.52      ( sK1 = sK1 ),
% 7.49/1.52      inference(instantiation,[status(thm)],[c_794]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_2377,plain,
% 7.49/1.52      ( ~ v6_tops_1(sK2,sK0)
% 7.49/1.52      | k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = sK2 ),
% 7.49/1.52      inference(predicate_to_equality_rev,[status(thm)],[c_2375]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_2428,plain,
% 7.49/1.52      ( k1_zfmisc_1(u1_struct_0(sK1)) = k1_zfmisc_1(u1_struct_0(sK1)) ),
% 7.49/1.52      inference(instantiation,[status(thm)],[c_794]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_19,negated_conjecture,
% 7.49/1.52      ( v6_tops_1(sK2,sK0) | v4_tops_1(sK3,sK1) ),
% 7.49/1.52      inference(cnf_transformation,[],[f58]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_1463,plain,
% 7.49/1.52      ( v6_tops_1(sK2,sK0) = iProver_top
% 7.49/1.52      | v4_tops_1(sK3,sK1) = iProver_top ),
% 7.49/1.52      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_2448,plain,
% 7.49/1.52      ( k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = sK2
% 7.49/1.52      | v4_tops_1(sK3,sK1) = iProver_top ),
% 7.49/1.52      inference(superposition,[status(thm)],[c_1463,c_2375]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_2449,plain,
% 7.49/1.52      ( v4_tops_1(sK3,sK1) | k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = sK2 ),
% 7.49/1.52      inference(predicate_to_equality_rev,[status(thm)],[c_2448]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_508,plain,
% 7.49/1.52      ( ~ v3_pre_topc(X0,X1)
% 7.49/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.49/1.52      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.49/1.52      | k1_tops_1(X1,X0) = X0
% 7.49/1.52      | sK0 != X1 ),
% 7.49/1.52      inference(resolution_lifted,[status(thm)],[c_324,c_24]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_509,plain,
% 7.49/1.52      ( ~ v3_pre_topc(X0,sK0)
% 7.49/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.49/1.52      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.49/1.52      | k1_tops_1(sK0,X0) = X0 ),
% 7.49/1.52      inference(unflattening,[status(thm)],[c_508]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_789,plain,
% 7.49/1.52      ( ~ v3_pre_topc(X0,sK0)
% 7.49/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.49/1.52      | k1_tops_1(sK0,X0) = X0
% 7.49/1.52      | ~ sP3_iProver_split ),
% 7.49/1.52      inference(splitting,
% 7.49/1.52                [splitting(split),new_symbols(definition,[sP3_iProver_split])],
% 7.49/1.52                [c_509]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_1445,plain,
% 7.49/1.52      ( k1_tops_1(sK0,X0) = X0
% 7.49/1.52      | v3_pre_topc(X0,sK0) != iProver_top
% 7.49/1.52      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.49/1.52      | sP3_iProver_split != iProver_top ),
% 7.49/1.52      inference(predicate_to_equality,[status(thm)],[c_789]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_790,plain,
% 7.49/1.52      ( sP3_iProver_split | sP0_iProver_split ),
% 7.49/1.52      inference(splitting,
% 7.49/1.52                [splitting(split),new_symbols(definition,[])],
% 7.49/1.52                [c_509]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_835,plain,
% 7.49/1.52      ( sP3_iProver_split = iProver_top
% 7.49/1.52      | sP0_iProver_split = iProver_top ),
% 7.49/1.52      inference(predicate_to_equality,[status(thm)],[c_790]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_836,plain,
% 7.49/1.52      ( k1_tops_1(sK0,X0) = X0
% 7.49/1.52      | v3_pre_topc(X0,sK0) != iProver_top
% 7.49/1.52      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.49/1.52      | sP3_iProver_split != iProver_top ),
% 7.49/1.52      inference(predicate_to_equality,[status(thm)],[c_789]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_2800,plain,
% 7.49/1.52      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.49/1.52      | v3_pre_topc(X0,sK0) != iProver_top
% 7.49/1.52      | k1_tops_1(sK0,X0) = X0 ),
% 7.49/1.52      inference(global_propositional_subsumption,
% 7.49/1.52                [status(thm)],
% 7.49/1.52                [c_1445,c_29,c_835,c_836,c_1548]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_2801,plain,
% 7.49/1.52      ( k1_tops_1(sK0,X0) = X0
% 7.49/1.52      | v3_pre_topc(X0,sK0) != iProver_top
% 7.49/1.52      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.49/1.52      inference(renaming,[status(thm)],[c_2800]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_2804,plain,
% 7.49/1.52      ( k1_tops_1(sK0,sK2) = sK2 | v3_pre_topc(sK2,sK0) != iProver_top ),
% 7.49/1.52      inference(superposition,[status(thm)],[c_1460,c_2801]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_2806,plain,
% 7.49/1.52      ( ~ v3_pre_topc(sK2,sK0) | k1_tops_1(sK0,sK2) = sK2 ),
% 7.49/1.52      inference(predicate_to_equality_rev,[status(thm)],[c_2804]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_2847,plain,
% 7.49/1.52      ( sK3 = sK3 ),
% 7.49/1.52      inference(instantiation,[status(thm)],[c_794]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_800,plain,
% 7.49/1.52      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.49/1.52      theory(equality) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_1564,plain,
% 7.49/1.52      ( ~ m1_subset_1(X0,X1)
% 7.49/1.52      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.49/1.52      | X2 != X0
% 7.49/1.52      | k1_zfmisc_1(u1_struct_0(sK1)) != X1 ),
% 7.49/1.52      inference(instantiation,[status(thm)],[c_800]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_1927,plain,
% 7.49/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.49/1.52      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.49/1.52      | X1 != X0
% 7.49/1.52      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 7.49/1.52      inference(instantiation,[status(thm)],[c_1564]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_3369,plain,
% 7.49/1.52      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.49/1.52      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.49/1.52      | X0 != sK3
% 7.49/1.52      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 7.49/1.52      inference(instantiation,[status(thm)],[c_1927]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_3880,plain,
% 7.49/1.52      ( m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 7.49/1.52      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.49/1.52      | k1_tops_1(sK1,sK3) != sK3
% 7.49/1.52      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 7.49/1.52      inference(instantiation,[status(thm)],[c_3369]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_801,plain,
% 7.49/1.52      ( ~ v4_tops_1(X0,X1) | v4_tops_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.49/1.52      theory(equality) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_1598,plain,
% 7.49/1.52      ( ~ v4_tops_1(X0,X1) | v4_tops_1(X2,sK1) | X2 != X0 | sK1 != X1 ),
% 7.49/1.52      inference(instantiation,[status(thm)],[c_801]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_1937,plain,
% 7.49/1.52      ( ~ v4_tops_1(X0,sK1) | v4_tops_1(X1,sK1) | X1 != X0 | sK1 != sK1 ),
% 7.49/1.52      inference(instantiation,[status(thm)],[c_1598]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_3535,plain,
% 7.49/1.52      ( v4_tops_1(X0,sK1)
% 7.49/1.52      | ~ v4_tops_1(sK3,sK1)
% 7.49/1.52      | X0 != sK3
% 7.49/1.52      | sK1 != sK1 ),
% 7.49/1.52      inference(instantiation,[status(thm)],[c_1937]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_3886,plain,
% 7.49/1.52      ( v4_tops_1(k1_tops_1(sK1,sK3),sK1)
% 7.49/1.52      | ~ v4_tops_1(sK3,sK1)
% 7.49/1.52      | k1_tops_1(sK1,sK3) != sK3
% 7.49/1.52      | sK1 != sK1 ),
% 7.49/1.52      inference(instantiation,[status(thm)],[c_3535]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_7,plain,
% 7.49/1.52      ( v6_tops_1(X0,X1)
% 7.49/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.49/1.52      | ~ l1_pre_topc(X1)
% 7.49/1.52      | k1_tops_1(X1,k2_pre_topc(X1,X0)) != X0 ),
% 7.49/1.52      inference(cnf_transformation,[],[f45]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_433,plain,
% 7.49/1.52      ( v6_tops_1(X0,X1)
% 7.49/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.49/1.52      | k1_tops_1(X1,k2_pre_topc(X1,X0)) != X0
% 7.49/1.52      | sK1 != X1 ),
% 7.49/1.52      inference(resolution_lifted,[status(thm)],[c_7,c_23]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_434,plain,
% 7.49/1.52      ( v6_tops_1(X0,sK1)
% 7.49/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.49/1.52      | k1_tops_1(sK1,k2_pre_topc(sK1,X0)) != X0 ),
% 7.49/1.52      inference(unflattening,[status(thm)],[c_433]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_4553,plain,
% 7.49/1.52      ( v6_tops_1(k1_tops_1(sK1,sK3),sK1)
% 7.49/1.52      | ~ m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 7.49/1.52      | k1_tops_1(sK1,k2_pre_topc(sK1,k1_tops_1(sK1,sK3))) != k1_tops_1(sK1,sK3) ),
% 7.49/1.52      inference(instantiation,[status(thm)],[c_434]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_795,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_2171,plain,
% 7.49/1.52      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 7.49/1.52      inference(instantiation,[status(thm)],[c_795]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_3447,plain,
% 7.49/1.52      ( X0 != sK3 | sK3 = X0 | sK3 != sK3 ),
% 7.49/1.52      inference(instantiation,[status(thm)],[c_2171]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_5859,plain,
% 7.49/1.52      ( k1_tops_1(sK1,sK3) != sK3
% 7.49/1.52      | sK3 = k1_tops_1(sK1,sK3)
% 7.49/1.52      | sK3 != sK3 ),
% 7.49/1.52      inference(instantiation,[status(thm)],[c_3447]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_406,plain,
% 7.49/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.49/1.52      | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0)
% 7.49/1.52      | sK1 != X1 ),
% 7.49/1.52      inference(resolution_lifted,[status(thm)],[c_10,c_23]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_407,plain,
% 7.49/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.49/1.52      | k1_tops_1(sK1,k1_tops_1(sK1,X0)) = k1_tops_1(sK1,X0) ),
% 7.49/1.52      inference(unflattening,[status(thm)],[c_406]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_1453,plain,
% 7.49/1.52      ( k1_tops_1(sK1,k1_tops_1(sK1,X0)) = k1_tops_1(sK1,X0)
% 7.49/1.52      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 7.49/1.52      inference(predicate_to_equality,[status(thm)],[c_407]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_2312,plain,
% 7.49/1.52      ( k1_tops_1(sK1,k1_tops_1(sK1,sK3)) = k1_tops_1(sK1,sK3) ),
% 7.49/1.52      inference(superposition,[status(thm)],[c_1461,c_1453]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_496,plain,
% 7.49/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.49/1.52      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.49/1.52      | sK1 != X1 ),
% 7.49/1.52      inference(resolution_lifted,[status(thm)],[c_3,c_23]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_497,plain,
% 7.49/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.49/1.52      | m1_subset_1(k2_pre_topc(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 7.49/1.52      inference(unflattening,[status(thm)],[c_496]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_1447,plain,
% 7.49/1.52      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 7.49/1.52      | m1_subset_1(k2_pre_topc(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 7.49/1.52      inference(predicate_to_equality,[status(thm)],[c_497]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_12,plain,
% 7.49/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.49/1.52      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 7.49/1.52      | ~ r1_tarski(X0,X2)
% 7.49/1.52      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 7.49/1.52      | ~ l1_pre_topc(X1) ),
% 7.49/1.52      inference(cnf_transformation,[],[f49]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_376,plain,
% 7.49/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.49/1.52      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 7.49/1.52      | ~ r1_tarski(X0,X2)
% 7.49/1.52      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 7.49/1.52      | sK1 != X1 ),
% 7.49/1.52      inference(resolution_lifted,[status(thm)],[c_12,c_23]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_377,plain,
% 7.49/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.49/1.52      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.49/1.52      | ~ r1_tarski(X0,X1)
% 7.49/1.52      | r1_tarski(k1_tops_1(sK1,X0),k1_tops_1(sK1,X1)) ),
% 7.49/1.52      inference(unflattening,[status(thm)],[c_376]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_1455,plain,
% 7.49/1.52      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 7.49/1.52      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 7.49/1.52      | r1_tarski(X0,X1) != iProver_top
% 7.49/1.52      | r1_tarski(k1_tops_1(sK1,X0),k1_tops_1(sK1,X1)) = iProver_top ),
% 7.49/1.52      inference(predicate_to_equality,[status(thm)],[c_377]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_6,plain,
% 7.49/1.52      ( ~ v4_tops_1(X0,X1)
% 7.49/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.49/1.52      | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
% 7.49/1.52      | ~ l1_pre_topc(X1) ),
% 7.49/1.52      inference(cnf_transformation,[],[f41]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_448,plain,
% 7.49/1.52      ( ~ v4_tops_1(X0,X1)
% 7.49/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.49/1.52      | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
% 7.49/1.52      | sK1 != X1 ),
% 7.49/1.52      inference(resolution_lifted,[status(thm)],[c_6,c_23]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_449,plain,
% 7.49/1.52      ( ~ v4_tops_1(X0,sK1)
% 7.49/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.49/1.52      | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,X0)),X0) ),
% 7.49/1.52      inference(unflattening,[status(thm)],[c_448]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_1450,plain,
% 7.49/1.52      ( v4_tops_1(X0,sK1) != iProver_top
% 7.49/1.52      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 7.49/1.52      | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,X0)),X0) = iProver_top ),
% 7.49/1.52      inference(predicate_to_equality,[status(thm)],[c_449]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_1469,plain,
% 7.49/1.52      ( X0 = X1
% 7.49/1.52      | r1_tarski(X0,X1) != iProver_top
% 7.49/1.52      | r1_tarski(X1,X0) != iProver_top ),
% 7.49/1.52      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_2795,plain,
% 7.49/1.52      ( k1_tops_1(sK1,k2_pre_topc(sK1,X0)) = X0
% 7.49/1.52      | v4_tops_1(X0,sK1) != iProver_top
% 7.49/1.52      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 7.49/1.52      | r1_tarski(X0,k1_tops_1(sK1,k2_pre_topc(sK1,X0))) != iProver_top ),
% 7.49/1.52      inference(superposition,[status(thm)],[c_1450,c_1469]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_3127,plain,
% 7.49/1.52      ( k1_tops_1(sK1,k2_pre_topc(sK1,k1_tops_1(sK1,X0))) = k1_tops_1(sK1,X0)
% 7.49/1.52      | v4_tops_1(k1_tops_1(sK1,X0),sK1) != iProver_top
% 7.49/1.52      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 7.49/1.52      | m1_subset_1(k1_tops_1(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 7.49/1.52      | m1_subset_1(k2_pre_topc(sK1,k1_tops_1(sK1,X0)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 7.49/1.52      | r1_tarski(X0,k2_pre_topc(sK1,k1_tops_1(sK1,X0))) != iProver_top ),
% 7.49/1.52      inference(superposition,[status(thm)],[c_1455,c_2795]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_7066,plain,
% 7.49/1.52      ( k1_tops_1(sK1,k2_pre_topc(sK1,k1_tops_1(sK1,X0))) = k1_tops_1(sK1,X0)
% 7.49/1.52      | v4_tops_1(k1_tops_1(sK1,X0),sK1) != iProver_top
% 7.49/1.52      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 7.49/1.52      | m1_subset_1(k1_tops_1(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 7.49/1.52      | r1_tarski(X0,k2_pre_topc(sK1,k1_tops_1(sK1,X0))) != iProver_top ),
% 7.49/1.52      inference(superposition,[status(thm)],[c_1447,c_3127]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_8871,plain,
% 7.49/1.52      ( k1_tops_1(sK1,k2_pre_topc(sK1,k1_tops_1(sK1,k1_tops_1(sK1,sK3)))) = k1_tops_1(sK1,k1_tops_1(sK1,sK3))
% 7.49/1.52      | v4_tops_1(k1_tops_1(sK1,k1_tops_1(sK1,sK3)),sK1) != iProver_top
% 7.49/1.52      | m1_subset_1(k1_tops_1(sK1,k1_tops_1(sK1,sK3)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 7.49/1.52      | m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 7.49/1.52      | r1_tarski(k1_tops_1(sK1,sK3),k2_pre_topc(sK1,k1_tops_1(sK1,sK3))) != iProver_top ),
% 7.49/1.52      inference(superposition,[status(thm)],[c_2312,c_7066]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_8888,plain,
% 7.49/1.52      ( k1_tops_1(sK1,k2_pre_topc(sK1,k1_tops_1(sK1,sK3))) = k1_tops_1(sK1,sK3)
% 7.49/1.52      | v4_tops_1(k1_tops_1(sK1,sK3),sK1) != iProver_top
% 7.49/1.52      | m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 7.49/1.52      | r1_tarski(k1_tops_1(sK1,sK3),k2_pre_topc(sK1,k1_tops_1(sK1,sK3))) != iProver_top ),
% 7.49/1.52      inference(light_normalisation,[status(thm)],[c_8871,c_2312]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_5,plain,
% 7.49/1.52      ( ~ v4_tops_1(X0,X1)
% 7.49/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.49/1.52      | r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
% 7.49/1.52      | ~ l1_pre_topc(X1) ),
% 7.49/1.52      inference(cnf_transformation,[],[f42]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_463,plain,
% 7.49/1.52      ( ~ v4_tops_1(X0,X1)
% 7.49/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.49/1.52      | r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
% 7.49/1.52      | sK1 != X1 ),
% 7.49/1.52      inference(resolution_lifted,[status(thm)],[c_5,c_23]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_464,plain,
% 7.49/1.52      ( ~ v4_tops_1(X0,sK1)
% 7.49/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.49/1.52      | r1_tarski(X0,k2_pre_topc(sK1,k1_tops_1(sK1,X0))) ),
% 7.49/1.52      inference(unflattening,[status(thm)],[c_463]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_1449,plain,
% 7.49/1.52      ( v4_tops_1(X0,sK1) != iProver_top
% 7.49/1.52      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 7.49/1.52      | r1_tarski(X0,k2_pre_topc(sK1,k1_tops_1(sK1,X0))) = iProver_top ),
% 7.49/1.52      inference(predicate_to_equality,[status(thm)],[c_464]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_2767,plain,
% 7.49/1.52      ( v4_tops_1(k1_tops_1(sK1,sK3),sK1) != iProver_top
% 7.49/1.52      | m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 7.49/1.52      | r1_tarski(k1_tops_1(sK1,sK3),k2_pre_topc(sK1,k1_tops_1(sK1,sK3))) = iProver_top ),
% 7.49/1.52      inference(superposition,[status(thm)],[c_2312,c_1449]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_8902,plain,
% 7.49/1.52      ( m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 7.49/1.52      | v4_tops_1(k1_tops_1(sK1,sK3),sK1) != iProver_top
% 7.49/1.52      | k1_tops_1(sK1,k2_pre_topc(sK1,k1_tops_1(sK1,sK3))) = k1_tops_1(sK1,sK3) ),
% 7.49/1.52      inference(global_propositional_subsumption,
% 7.49/1.52                [status(thm)],
% 7.49/1.52                [c_8888,c_2767]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_8903,plain,
% 7.49/1.52      ( k1_tops_1(sK1,k2_pre_topc(sK1,k1_tops_1(sK1,sK3))) = k1_tops_1(sK1,sK3)
% 7.49/1.52      | v4_tops_1(k1_tops_1(sK1,sK3),sK1) != iProver_top
% 7.49/1.52      | m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 7.49/1.52      inference(renaming,[status(thm)],[c_8902]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_8904,plain,
% 7.49/1.52      ( ~ v4_tops_1(k1_tops_1(sK1,sK3),sK1)
% 7.49/1.52      | ~ m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 7.49/1.52      | k1_tops_1(sK1,k2_pre_topc(sK1,k1_tops_1(sK1,sK3))) = k1_tops_1(sK1,sK3) ),
% 7.49/1.52      inference(predicate_to_equality_rev,[status(thm)],[c_8903]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_803,plain,
% 7.49/1.52      ( ~ v6_tops_1(X0,X1) | v6_tops_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.49/1.52      theory(equality) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_1589,plain,
% 7.49/1.52      ( ~ v6_tops_1(X0,X1) | v6_tops_1(X2,sK1) | X2 != X0 | sK1 != X1 ),
% 7.49/1.52      inference(instantiation,[status(thm)],[c_803]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_1785,plain,
% 7.49/1.52      ( ~ v6_tops_1(X0,sK1) | v6_tops_1(X1,sK1) | X1 != X0 | sK1 != sK1 ),
% 7.49/1.52      inference(instantiation,[status(thm)],[c_1589]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_6928,plain,
% 7.49/1.52      ( v6_tops_1(X0,sK1)
% 7.49/1.52      | ~ v6_tops_1(k1_tops_1(sK1,sK3),sK1)
% 7.49/1.52      | X0 != k1_tops_1(sK1,sK3)
% 7.49/1.52      | sK1 != sK1 ),
% 7.49/1.52      inference(instantiation,[status(thm)],[c_1785]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_9297,plain,
% 7.49/1.52      ( ~ v6_tops_1(k1_tops_1(sK1,sK3),sK1)
% 7.49/1.52      | v6_tops_1(sK3,sK1)
% 7.49/1.52      | sK1 != sK1
% 7.49/1.52      | sK3 != k1_tops_1(sK1,sK3) ),
% 7.49/1.52      inference(instantiation,[status(thm)],[c_6928]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_1779,plain,
% 7.49/1.52      ( X0 != X1 | sK2 != X1 | sK2 = X0 ),
% 7.49/1.52      inference(instantiation,[status(thm)],[c_795]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_2243,plain,
% 7.49/1.52      ( X0 != sK2 | sK2 = X0 | sK2 != sK2 ),
% 7.49/1.52      inference(instantiation,[status(thm)],[c_1779]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_13824,plain,
% 7.49/1.52      ( k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) != sK2
% 7.49/1.52      | sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2))
% 7.49/1.52      | sK2 != sK2 ),
% 7.49/1.52      inference(instantiation,[status(thm)],[c_2243]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_804,plain,
% 7.49/1.52      ( ~ v3_pre_topc(X0,X1) | v3_pre_topc(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.49/1.52      theory(equality) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_1540,plain,
% 7.49/1.52      ( ~ v3_pre_topc(X0,X1)
% 7.49/1.52      | v3_pre_topc(sK2,sK0)
% 7.49/1.52      | sK0 != X1
% 7.49/1.52      | sK2 != X0 ),
% 7.49/1.52      inference(instantiation,[status(thm)],[c_804]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_16840,plain,
% 7.49/1.52      ( ~ v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),X0)
% 7.49/1.52      | v3_pre_topc(sK2,sK0)
% 7.49/1.52      | sK0 != X0
% 7.49/1.52      | sK2 != k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) ),
% 7.49/1.52      inference(instantiation,[status(thm)],[c_1540]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_16842,plain,
% 7.49/1.52      ( ~ v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK0)
% 7.49/1.52      | v3_pre_topc(sK2,sK0)
% 7.49/1.52      | sK0 != sK0
% 7.49/1.52      | sK2 != k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) ),
% 7.49/1.52      inference(instantiation,[status(thm)],[c_16840]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_19395,plain,
% 7.49/1.52      ( k1_tops_1(sK0,sK2) = sK2 ),
% 7.49/1.52      inference(global_propositional_subsumption,
% 7.49/1.52                [status(thm)],
% 7.49/1.52                [c_4186,c_22,c_21,c_18,c_74,c_78,c_1569,c_1679,c_2102,
% 7.49/1.52                 c_2295,c_2377,c_2428,c_2449,c_2806,c_2847,c_3021,c_3880,
% 7.49/1.52                 c_3886,c_4553,c_5859,c_8904,c_9297,c_13824,c_16842]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_4,plain,
% 7.49/1.52      ( v4_tops_1(X0,X1)
% 7.49/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.49/1.52      | ~ r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
% 7.49/1.52      | ~ r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
% 7.49/1.52      | ~ l1_pre_topc(X1) ),
% 7.49/1.52      inference(cnf_transformation,[],[f43]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_628,plain,
% 7.49/1.52      ( v4_tops_1(X0,X1)
% 7.49/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.49/1.52      | ~ r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
% 7.49/1.52      | ~ r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
% 7.49/1.52      | sK0 != X1 ),
% 7.49/1.52      inference(resolution_lifted,[status(thm)],[c_4,c_24]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_629,plain,
% 7.49/1.52      ( v4_tops_1(X0,sK0)
% 7.49/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.49/1.52      | ~ r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,X0)))
% 7.49/1.52      | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X0) ),
% 7.49/1.52      inference(unflattening,[status(thm)],[c_628]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_1436,plain,
% 7.49/1.52      ( v4_tops_1(X0,sK0) = iProver_top
% 7.49/1.52      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.49/1.52      | r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,X0))) != iProver_top
% 7.49/1.52      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X0) != iProver_top ),
% 7.49/1.52      inference(predicate_to_equality,[status(thm)],[c_629]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_4127,plain,
% 7.49/1.52      ( k1_tops_1(sK1,sK3) = sK3
% 7.49/1.52      | v4_tops_1(sK2,sK0) = iProver_top
% 7.49/1.52      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.49/1.52      | r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) != iProver_top
% 7.49/1.52      | r1_tarski(sK2,sK2) != iProver_top ),
% 7.49/1.52      inference(superposition,[status(thm)],[c_3021,c_1436]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_1645,plain,
% 7.49/1.52      ( v4_tops_1(sK2,sK0)
% 7.49/1.52      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.49/1.52      | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK2)
% 7.49/1.52      | ~ r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) ),
% 7.49/1.52      inference(instantiation,[status(thm)],[c_629]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_1646,plain,
% 7.49/1.52      ( v4_tops_1(sK2,sK0) = iProver_top
% 7.49/1.52      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.49/1.52      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK2) != iProver_top
% 7.49/1.52      | r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) != iProver_top ),
% 7.49/1.52      inference(predicate_to_equality,[status(thm)],[c_1645]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_2013,plain,
% 7.49/1.52      ( r1_tarski(sK2,sK2) ),
% 7.49/1.52      inference(instantiation,[status(thm)],[c_2]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_2014,plain,
% 7.49/1.52      ( r1_tarski(sK2,sK2) = iProver_top ),
% 7.49/1.52      inference(predicate_to_equality,[status(thm)],[c_2013]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_796,plain,
% 7.49/1.52      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.49/1.52      theory(equality) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_1744,plain,
% 7.49/1.52      ( ~ r1_tarski(X0,X1)
% 7.49/1.52      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK2)
% 7.49/1.52      | k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) != X0
% 7.49/1.52      | sK2 != X1 ),
% 7.49/1.52      inference(instantiation,[status(thm)],[c_796]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_2236,plain,
% 7.49/1.52      ( ~ r1_tarski(X0,sK2)
% 7.49/1.52      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK2)
% 7.49/1.52      | k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) != X0
% 7.49/1.52      | sK2 != sK2 ),
% 7.49/1.52      inference(instantiation,[status(thm)],[c_1744]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_3244,plain,
% 7.49/1.52      ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK2)
% 7.49/1.52      | ~ r1_tarski(sK2,sK2)
% 7.49/1.52      | k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) != sK2
% 7.49/1.52      | sK2 != sK2 ),
% 7.49/1.52      inference(instantiation,[status(thm)],[c_2236]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_3245,plain,
% 7.49/1.52      ( k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) != sK2
% 7.49/1.52      | sK2 != sK2
% 7.49/1.52      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK2) = iProver_top
% 7.49/1.52      | r1_tarski(sK2,sK2) != iProver_top ),
% 7.49/1.52      inference(predicate_to_equality,[status(thm)],[c_3244]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_14018,plain,
% 7.49/1.52      ( r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) != iProver_top
% 7.49/1.52      | v4_tops_1(sK2,sK0) = iProver_top ),
% 7.49/1.52      inference(global_propositional_subsumption,
% 7.49/1.52                [status(thm)],
% 7.49/1.52                [c_4127,c_29,c_21,c_18,c_1646,c_2014,c_2102,c_2295,
% 7.49/1.52                 c_2377,c_2428,c_2449,c_2847,c_3021,c_3245,c_3880,c_3886,
% 7.49/1.52                 c_4553,c_5859,c_8904,c_9297]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_14019,plain,
% 7.49/1.52      ( v4_tops_1(sK2,sK0) = iProver_top
% 7.49/1.52      | r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) != iProver_top ),
% 7.49/1.52      inference(renaming,[status(thm)],[c_14018]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_19426,plain,
% 7.49/1.52      ( v4_tops_1(sK2,sK0) = iProver_top
% 7.49/1.52      | r1_tarski(sK2,k2_pre_topc(sK0,sK2)) != iProver_top ),
% 7.49/1.52      inference(demodulation,[status(thm)],[c_19395,c_14019]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_3650,plain,
% 7.49/1.52      ( ~ r1_tarski(X0,X1)
% 7.49/1.52      | r1_tarski(X2,k2_pre_topc(sK0,sK2))
% 7.49/1.52      | X2 != X0
% 7.49/1.52      | k2_pre_topc(sK0,sK2) != X1 ),
% 7.49/1.52      inference(instantiation,[status(thm)],[c_796]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_6849,plain,
% 7.49/1.52      ( ~ r1_tarski(X0,k2_pre_topc(sK0,sK2))
% 7.49/1.52      | r1_tarski(X1,k2_pre_topc(sK0,sK2))
% 7.49/1.52      | X1 != X0
% 7.49/1.52      | k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,sK2) ),
% 7.49/1.52      inference(instantiation,[status(thm)],[c_3650]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_13002,plain,
% 7.49/1.52      ( r1_tarski(X0,k2_pre_topc(sK0,sK2))
% 7.49/1.52      | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,sK2))
% 7.49/1.52      | X0 != k1_tops_1(sK0,k2_pre_topc(sK0,sK2))
% 7.49/1.52      | k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,sK2) ),
% 7.49/1.52      inference(instantiation,[status(thm)],[c_6849]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_19169,plain,
% 7.49/1.52      ( ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,sK2))
% 7.49/1.52      | r1_tarski(sK2,k2_pre_topc(sK0,sK2))
% 7.49/1.52      | k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,sK2)
% 7.49/1.52      | sK2 != k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) ),
% 7.49/1.52      inference(instantiation,[status(thm)],[c_13002]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_19170,plain,
% 7.49/1.52      ( k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,sK2)
% 7.49/1.52      | sK2 != k1_tops_1(sK0,k2_pre_topc(sK0,sK2))
% 7.49/1.52      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,sK2)) != iProver_top
% 7.49/1.52      | r1_tarski(sK2,k2_pre_topc(sK0,sK2)) = iProver_top ),
% 7.49/1.52      inference(predicate_to_equality,[status(thm)],[c_19169]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_785,plain,
% 7.49/1.52      ( v3_pre_topc(X0,sK0)
% 7.49/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.49/1.52      | k1_tops_1(sK0,X0) != X0
% 7.49/1.52      | ~ sP1_iProver_split ),
% 7.49/1.52      inference(splitting,
% 7.49/1.52                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 7.49/1.52                [c_677]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_1430,plain,
% 7.49/1.52      ( k1_tops_1(sK0,X0) != X0
% 7.49/1.52      | v3_pre_topc(X0,sK0) = iProver_top
% 7.49/1.52      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.49/1.52      | sP1_iProver_split != iProver_top ),
% 7.49/1.52      inference(predicate_to_equality,[status(thm)],[c_785]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_786,plain,
% 7.49/1.52      ( sP1_iProver_split | sP0_iProver_split ),
% 7.49/1.52      inference(splitting,
% 7.49/1.52                [splitting(split),new_symbols(definition,[])],
% 7.49/1.52                [c_677]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_816,plain,
% 7.49/1.52      ( sP1_iProver_split = iProver_top
% 7.49/1.52      | sP0_iProver_split = iProver_top ),
% 7.49/1.52      inference(predicate_to_equality,[status(thm)],[c_786]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_817,plain,
% 7.49/1.52      ( k1_tops_1(sK0,X0) != X0
% 7.49/1.52      | v3_pre_topc(X0,sK0) = iProver_top
% 7.49/1.52      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.49/1.52      | sP1_iProver_split != iProver_top ),
% 7.49/1.52      inference(predicate_to_equality,[status(thm)],[c_785]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_1750,plain,
% 7.49/1.52      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.49/1.52      | v3_pre_topc(X0,sK0) = iProver_top
% 7.49/1.52      | k1_tops_1(sK0,X0) != X0 ),
% 7.49/1.52      inference(global_propositional_subsumption,
% 7.49/1.52                [status(thm)],
% 7.49/1.52                [c_1430,c_29,c_816,c_817,c_1548]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_1751,plain,
% 7.49/1.52      ( k1_tops_1(sK0,X0) != X0
% 7.49/1.52      | v3_pre_topc(X0,sK0) = iProver_top
% 7.49/1.52      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.49/1.52      inference(renaming,[status(thm)],[c_1750]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_3476,plain,
% 7.49/1.52      ( v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK0) = iProver_top
% 7.49/1.52      | m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.49/1.52      inference(superposition,[status(thm)],[c_3467,c_1751]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_1570,plain,
% 7.49/1.52      ( m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 7.49/1.52      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.49/1.52      inference(predicate_to_equality,[status(thm)],[c_1569]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_1683,plain,
% 7.49/1.52      ( v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK0) = iProver_top
% 7.49/1.52      | m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.49/1.52      inference(predicate_to_equality,[status(thm)],[c_1679]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_3678,plain,
% 7.49/1.52      ( v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK0) = iProver_top ),
% 7.49/1.52      inference(global_propositional_subsumption,
% 7.49/1.52                [status(thm)],
% 7.49/1.52                [c_3476,c_29,c_1570,c_1683]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_4129,plain,
% 7.49/1.52      ( k1_tops_1(sK1,sK3) = sK3 | v3_pre_topc(sK2,sK0) = iProver_top ),
% 7.49/1.52      inference(superposition,[status(thm)],[c_3021,c_3678]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_16,negated_conjecture,
% 7.49/1.52      ( ~ v3_pre_topc(sK2,sK0)
% 7.49/1.52      | v4_tops_1(sK3,sK1)
% 7.49/1.52      | ~ v4_tops_1(sK2,sK0) ),
% 7.49/1.52      inference(cnf_transformation,[],[f61]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_1466,plain,
% 7.49/1.52      ( v3_pre_topc(sK2,sK0) != iProver_top
% 7.49/1.52      | v4_tops_1(sK3,sK1) = iProver_top
% 7.49/1.52      | v4_tops_1(sK2,sK0) != iProver_top ),
% 7.49/1.52      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_14695,plain,
% 7.49/1.52      ( k1_tops_1(sK1,sK3) = sK3
% 7.49/1.52      | v4_tops_1(sK3,sK1) = iProver_top
% 7.49/1.52      | v4_tops_1(sK2,sK0) != iProver_top ),
% 7.49/1.52      inference(superposition,[status(thm)],[c_4129,c_1466]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_17,negated_conjecture,
% 7.49/1.52      ( v3_pre_topc(sK3,sK1)
% 7.49/1.52      | ~ v3_pre_topc(sK2,sK0)
% 7.49/1.52      | ~ v4_tops_1(sK2,sK0) ),
% 7.49/1.52      inference(cnf_transformation,[],[f60]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_1465,plain,
% 7.49/1.52      ( v3_pre_topc(sK3,sK1) = iProver_top
% 7.49/1.52      | v3_pre_topc(sK2,sK0) != iProver_top
% 7.49/1.52      | v4_tops_1(sK2,sK0) != iProver_top ),
% 7.49/1.52      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_14696,plain,
% 7.49/1.52      ( k1_tops_1(sK1,sK3) = sK3
% 7.49/1.52      | v3_pre_topc(sK3,sK1) = iProver_top
% 7.49/1.52      | v4_tops_1(sK2,sK0) != iProver_top ),
% 7.49/1.52      inference(superposition,[status(thm)],[c_4129,c_1465]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_14713,plain,
% 7.49/1.52      ( k1_tops_1(sK1,sK3) = sK3 | v4_tops_1(sK2,sK0) != iProver_top ),
% 7.49/1.52      inference(global_propositional_subsumption,
% 7.49/1.52                [status(thm)],
% 7.49/1.52                [c_14695,c_2862,c_14696]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_9298,plain,
% 7.49/1.52      ( sK1 != sK1
% 7.49/1.52      | sK3 != k1_tops_1(sK1,sK3)
% 7.49/1.52      | v6_tops_1(k1_tops_1(sK1,sK3),sK1) != iProver_top
% 7.49/1.52      | v6_tops_1(sK3,sK1) = iProver_top ),
% 7.49/1.52      inference(predicate_to_equality,[status(thm)],[c_9297]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_4563,plain,
% 7.49/1.52      ( k1_tops_1(sK1,k2_pre_topc(sK1,k1_tops_1(sK1,sK3))) != k1_tops_1(sK1,sK3)
% 7.49/1.52      | v6_tops_1(k1_tops_1(sK1,sK3),sK1) = iProver_top
% 7.49/1.52      | m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 7.49/1.52      inference(predicate_to_equality,[status(thm)],[c_4553]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_3887,plain,
% 7.49/1.52      ( k1_tops_1(sK1,sK3) != sK3
% 7.49/1.52      | sK1 != sK1
% 7.49/1.52      | v4_tops_1(k1_tops_1(sK1,sK3),sK1) = iProver_top
% 7.49/1.52      | v4_tops_1(sK3,sK1) != iProver_top ),
% 7.49/1.52      inference(predicate_to_equality,[status(thm)],[c_3886]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_3881,plain,
% 7.49/1.52      ( k1_tops_1(sK1,sK3) != sK3
% 7.49/1.52      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
% 7.49/1.52      | m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 7.49/1.52      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 7.49/1.52      inference(predicate_to_equality,[status(thm)],[c_3880]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_3593,plain,
% 7.49/1.52      ( k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,sK2) ),
% 7.49/1.52      inference(instantiation,[status(thm)],[c_794]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_11,plain,
% 7.49/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.49/1.52      | r1_tarski(k1_tops_1(X1,X0),X0)
% 7.49/1.52      | ~ l1_pre_topc(X1) ),
% 7.49/1.52      inference(cnf_transformation,[],[f48]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_544,plain,
% 7.49/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.49/1.52      | r1_tarski(k1_tops_1(X1,X0),X0)
% 7.49/1.52      | sK0 != X1 ),
% 7.49/1.52      inference(resolution_lifted,[status(thm)],[c_11,c_24]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_545,plain,
% 7.49/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.49/1.52      | r1_tarski(k1_tops_1(sK0,X0),X0) ),
% 7.49/1.52      inference(unflattening,[status(thm)],[c_544]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_1677,plain,
% 7.49/1.52      ( ~ m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 7.49/1.52      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,sK2)) ),
% 7.49/1.52      inference(instantiation,[status(thm)],[c_545]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_1687,plain,
% 7.49/1.52      ( m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.49/1.52      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,sK2)) = iProver_top ),
% 7.49/1.52      inference(predicate_to_equality,[status(thm)],[c_1677]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_916,plain,
% 7.49/1.52      ( k1_tops_1(sK0,X0) != X0
% 7.49/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.49/1.52      | v3_pre_topc(X0,sK0) ),
% 7.49/1.52      inference(global_propositional_subsumption,
% 7.49/1.52                [status(thm)],
% 7.49/1.52                [c_785,c_786,c_784]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_917,plain,
% 7.49/1.52      ( v3_pre_topc(X0,sK0)
% 7.49/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.49/1.52      | k1_tops_1(sK0,X0) != X0 ),
% 7.49/1.52      inference(renaming,[status(thm)],[c_916]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_923,plain,
% 7.49/1.52      ( k1_tops_1(sK0,X0) != X0
% 7.49/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.49/1.52      | v3_pre_topc(X0,sK0) ),
% 7.49/1.52      inference(global_propositional_subsumption,
% 7.49/1.52                [status(thm)],
% 7.49/1.52                [c_785,c_917]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_924,plain,
% 7.49/1.52      ( v3_pre_topc(X0,sK0)
% 7.49/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.49/1.52      | k1_tops_1(sK0,X0) != X0 ),
% 7.49/1.52      inference(renaming,[status(thm)],[c_923]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_1632,plain,
% 7.49/1.52      ( v3_pre_topc(sK2,sK0)
% 7.49/1.52      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.49/1.52      | k1_tops_1(sK0,sK2) != sK2 ),
% 7.49/1.52      inference(instantiation,[status(thm)],[c_924]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_1633,plain,
% 7.49/1.52      ( k1_tops_1(sK0,sK2) != sK2
% 7.49/1.52      | v3_pre_topc(sK2,sK0) = iProver_top
% 7.49/1.52      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.49/1.52      inference(predicate_to_equality,[status(thm)],[c_1632]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_15,negated_conjecture,
% 7.49/1.52      ( ~ v3_pre_topc(sK2,sK0)
% 7.49/1.52      | ~ v6_tops_1(sK3,sK1)
% 7.49/1.52      | ~ v4_tops_1(sK2,sK0) ),
% 7.49/1.52      inference(cnf_transformation,[],[f62]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_36,plain,
% 7.49/1.52      ( v3_pre_topc(sK2,sK0) != iProver_top
% 7.49/1.52      | v6_tops_1(sK3,sK1) != iProver_top
% 7.49/1.52      | v4_tops_1(sK2,sK0) != iProver_top ),
% 7.49/1.52      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_35,plain,
% 7.49/1.52      ( v3_pre_topc(sK2,sK0) != iProver_top
% 7.49/1.52      | v4_tops_1(sK3,sK1) = iProver_top
% 7.49/1.52      | v4_tops_1(sK2,sK0) != iProver_top ),
% 7.49/1.52      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(c_30,plain,
% 7.49/1.52      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 7.49/1.52      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.49/1.52  
% 7.49/1.52  cnf(contradiction,plain,
% 7.49/1.52      ( $false ),
% 7.49/1.52      inference(minisat,
% 7.49/1.52                [status(thm)],
% 7.49/1.52                [c_19426,c_19170,c_16842,c_14713,c_13824,c_9298,c_9297,
% 7.49/1.52                 c_8904,c_8903,c_5859,c_4563,c_4553,c_3887,c_3886,c_3881,
% 7.49/1.52                 c_3880,c_3593,c_3021,c_2847,c_2806,c_2449,c_2428,c_2377,
% 7.49/1.52                 c_2295,c_2102,c_1687,c_1679,c_1633,c_1570,c_1569,c_78,
% 7.49/1.52                 c_74,c_36,c_35,c_18,c_30,c_21,c_29,c_22]) ).
% 7.49/1.52  
% 7.49/1.52  
% 7.49/1.52  % SZS output end CNFRefutation for theBenchmark.p
% 7.49/1.52  
% 7.49/1.52  ------                               Statistics
% 7.49/1.52  
% 7.49/1.52  ------ General
% 7.49/1.52  
% 7.49/1.52  abstr_ref_over_cycles:                  0
% 7.49/1.52  abstr_ref_under_cycles:                 0
% 7.49/1.52  gc_basic_clause_elim:                   0
% 7.49/1.52  forced_gc_time:                         0
% 7.49/1.52  parsing_time:                           0.028
% 7.49/1.52  unif_index_cands_time:                  0.
% 7.49/1.52  unif_index_add_time:                    0.
% 7.49/1.52  orderings_time:                         0.
% 7.49/1.52  out_proof_time:                         0.017
% 7.49/1.52  total_time:                             0.856
% 7.49/1.52  num_of_symbols:                         51
% 7.49/1.52  num_of_terms:                           17407
% 7.49/1.52  
% 7.49/1.52  ------ Preprocessing
% 7.49/1.52  
% 7.49/1.52  num_of_splits:                          8
% 7.49/1.52  num_of_split_atoms:                     5
% 7.49/1.52  num_of_reused_defs:                     3
% 7.49/1.52  num_eq_ax_congr_red:                    2
% 7.49/1.52  num_of_sem_filtered_clauses:            5
% 7.49/1.52  num_of_subtypes:                        0
% 7.49/1.52  monotx_restored_types:                  0
% 7.49/1.52  sat_num_of_epr_types:                   0
% 7.49/1.52  sat_num_of_non_cyclic_types:            0
% 7.49/1.52  sat_guarded_non_collapsed_types:        0
% 7.49/1.52  num_pure_diseq_elim:                    0
% 7.49/1.52  simp_replaced_by:                       0
% 7.49/1.52  res_preprocessed:                       120
% 7.49/1.52  prep_upred:                             0
% 7.49/1.52  prep_unflattend:                        25
% 7.49/1.52  smt_new_axioms:                         0
% 7.49/1.52  pred_elim_cands:                        7
% 7.49/1.52  pred_elim:                              2
% 7.49/1.52  pred_elim_cl:                           -8
% 7.49/1.52  pred_elim_cycles:                       3
% 7.49/1.52  merged_defs:                            0
% 7.49/1.52  merged_defs_ncl:                        0
% 7.49/1.52  bin_hyper_res:                          0
% 7.49/1.52  prep_cycles:                            3
% 7.49/1.52  pred_elim_time:                         0.011
% 7.49/1.52  splitting_time:                         0.
% 7.49/1.52  sem_filter_time:                        0.
% 7.49/1.52  monotx_time:                            0.001
% 7.49/1.52  subtype_inf_time:                       0.
% 7.49/1.52  
% 7.49/1.52  ------ Problem properties
% 7.49/1.52  
% 7.49/1.52  clauses:                                41
% 7.49/1.52  conjectures:                            8
% 7.49/1.52  epr:                                    12
% 7.49/1.52  horn:                                   35
% 7.49/1.52  ground:                                 12
% 7.49/1.52  unary:                                  3
% 7.49/1.52  binary:                                 18
% 7.49/1.52  lits:                                   107
% 7.49/1.52  lits_eq:                                11
% 7.49/1.52  fd_pure:                                0
% 7.49/1.52  fd_pseudo:                              0
% 7.49/1.52  fd_cond:                                0
% 7.49/1.52  fd_pseudo_cond:                         1
% 7.49/1.52  ac_symbols:                             0
% 7.49/1.52  
% 7.49/1.52  ------ Propositional Solver
% 7.49/1.52  
% 7.49/1.52  prop_solver_calls:                      30
% 7.49/1.52  prop_fast_solver_calls:                 2202
% 7.49/1.52  smt_solver_calls:                       0
% 7.49/1.52  smt_fast_solver_calls:                  0
% 7.49/1.52  prop_num_of_clauses:                    10198
% 7.49/1.52  prop_preprocess_simplified:             16212
% 7.49/1.52  prop_fo_subsumed:                       80
% 7.49/1.52  prop_solver_time:                       0.
% 7.49/1.52  smt_solver_time:                        0.
% 7.49/1.52  smt_fast_solver_time:                   0.
% 7.49/1.52  prop_fast_solver_time:                  0.
% 7.49/1.52  prop_unsat_core_time:                   0.001
% 7.49/1.52  
% 7.49/1.52  ------ QBF
% 7.49/1.52  
% 7.49/1.52  qbf_q_res:                              0
% 7.49/1.52  qbf_num_tautologies:                    0
% 7.49/1.52  qbf_prep_cycles:                        0
% 7.49/1.52  
% 7.49/1.52  ------ BMC1
% 7.49/1.52  
% 7.49/1.52  bmc1_current_bound:                     -1
% 7.49/1.52  bmc1_last_solved_bound:                 -1
% 7.49/1.52  bmc1_unsat_core_size:                   -1
% 7.49/1.52  bmc1_unsat_core_parents_size:           -1
% 7.49/1.52  bmc1_merge_next_fun:                    0
% 7.49/1.52  bmc1_unsat_core_clauses_time:           0.
% 7.49/1.52  
% 7.49/1.52  ------ Instantiation
% 7.49/1.52  
% 7.49/1.52  inst_num_of_clauses:                    3017
% 7.49/1.52  inst_num_in_passive:                    708
% 7.49/1.52  inst_num_in_active:                     1685
% 7.49/1.52  inst_num_in_unprocessed:                624
% 7.49/1.52  inst_num_of_loops:                      1830
% 7.49/1.52  inst_num_of_learning_restarts:          0
% 7.49/1.52  inst_num_moves_active_passive:          139
% 7.49/1.52  inst_lit_activity:                      0
% 7.49/1.52  inst_lit_activity_moves:                1
% 7.49/1.52  inst_num_tautologies:                   0
% 7.49/1.52  inst_num_prop_implied:                  0
% 7.49/1.52  inst_num_existing_simplified:           0
% 7.49/1.52  inst_num_eq_res_simplified:             0
% 7.49/1.52  inst_num_child_elim:                    0
% 7.49/1.52  inst_num_of_dismatching_blockings:      737
% 7.49/1.52  inst_num_of_non_proper_insts:           3537
% 7.49/1.52  inst_num_of_duplicates:                 0
% 7.49/1.52  inst_inst_num_from_inst_to_res:         0
% 7.49/1.52  inst_dismatching_checking_time:         0.
% 7.49/1.52  
% 7.49/1.52  ------ Resolution
% 7.49/1.52  
% 7.49/1.52  res_num_of_clauses:                     0
% 7.49/1.52  res_num_in_passive:                     0
% 7.49/1.52  res_num_in_active:                      0
% 7.49/1.52  res_num_of_loops:                       123
% 7.49/1.52  res_forward_subset_subsumed:            220
% 7.49/1.52  res_backward_subset_subsumed:           0
% 7.49/1.52  res_forward_subsumed:                   0
% 7.49/1.52  res_backward_subsumed:                  0
% 7.49/1.52  res_forward_subsumption_resolution:     0
% 7.49/1.52  res_backward_subsumption_resolution:    0
% 7.49/1.52  res_clause_to_clause_subsumption:       5081
% 7.49/1.52  res_orphan_elimination:                 0
% 7.49/1.52  res_tautology_del:                      371
% 7.49/1.52  res_num_eq_res_simplified:              0
% 7.49/1.52  res_num_sel_changes:                    0
% 7.49/1.52  res_moves_from_active_to_pass:          0
% 7.49/1.52  
% 7.49/1.52  ------ Superposition
% 7.49/1.52  
% 7.49/1.52  sup_time_total:                         0.
% 7.49/1.52  sup_time_generating:                    0.
% 7.49/1.52  sup_time_sim_full:                      0.
% 7.49/1.52  sup_time_sim_immed:                     0.
% 7.49/1.52  
% 7.49/1.52  sup_num_of_clauses:                     711
% 7.49/1.52  sup_num_in_active:                      304
% 7.49/1.52  sup_num_in_passive:                     407
% 7.49/1.52  sup_num_of_loops:                       364
% 7.49/1.52  sup_fw_superposition:                   604
% 7.49/1.52  sup_bw_superposition:                   554
% 7.49/1.52  sup_immediate_simplified:               610
% 7.49/1.52  sup_given_eliminated:                   2
% 7.49/1.52  comparisons_done:                       0
% 7.49/1.52  comparisons_avoided:                    42
% 7.49/1.52  
% 7.49/1.52  ------ Simplifications
% 7.49/1.52  
% 7.49/1.52  
% 7.49/1.52  sim_fw_subset_subsumed:                 45
% 7.49/1.52  sim_bw_subset_subsumed:                 53
% 7.49/1.52  sim_fw_subsumed:                        235
% 7.49/1.52  sim_bw_subsumed:                        5
% 7.49/1.52  sim_fw_subsumption_res:                 0
% 7.49/1.52  sim_bw_subsumption_res:                 0
% 7.49/1.52  sim_tautology_del:                      6
% 7.49/1.52  sim_eq_tautology_del:                   37
% 7.49/1.52  sim_eq_res_simp:                        0
% 7.49/1.52  sim_fw_demodulated:                     332
% 7.49/1.52  sim_bw_demodulated:                     55
% 7.49/1.52  sim_light_normalised:                   215
% 7.49/1.52  sim_joinable_taut:                      0
% 7.49/1.52  sim_joinable_simp:                      0
% 7.49/1.52  sim_ac_normalised:                      0
% 7.49/1.52  sim_smt_subsumption:                    0
% 7.49/1.52  
%------------------------------------------------------------------------------
