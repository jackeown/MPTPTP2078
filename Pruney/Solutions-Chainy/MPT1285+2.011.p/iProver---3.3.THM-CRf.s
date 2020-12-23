%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:15:54 EST 2020

% Result     : Theorem 2.64s
% Output     : CNFRefutation 2.64s
% Verified   : 
% Statistics : Number of formulae       :  179 (2905 expanded)
%              Number of clauses        :  122 ( 787 expanded)
%              Number of leaves         :   15 ( 961 expanded)
%              Depth                    :   21
%              Number of atoms          :  694 (25651 expanded)
%              Number of equality atoms :  172 ( 957 expanded)
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

fof(f50,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f33])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f48,plain,(
    v2_pre_topc(sK0) ),
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

fof(f56,plain,
    ( ~ v4_tops_1(sK2,sK0)
    | ~ v3_pre_topc(sK2,sK0)
    | v3_pre_topc(sK3,sK1) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

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

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1400,plain,
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

cnf(c_527,plain,
    ( ~ v6_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,k2_pre_topc(X1,X0)) = X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_23])).

cnf(c_528,plain,
    ( ~ v6_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,k2_pre_topc(sK0,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_527])).

cnf(c_1383,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,X0)) = X0
    | v6_tops_1(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_528])).

cnf(c_2434,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = sK2
    | v6_tops_1(sK2,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1400,c_1383])).

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

cnf(c_476,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_22])).

cnf(c_477,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k2_pre_topc(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_476])).

cnf(c_1687,plain,
    ( m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_477])).

cnf(c_1688,plain,
    ( m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1687])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_464,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_22])).

cnf(c_465,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(X0,k2_pre_topc(sK1,X0)) ),
    inference(unflattening,[status(thm)],[c_464])).

cnf(c_1693,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(sK3,k2_pre_topc(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_465])).

cnf(c_1694,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(sK3,k2_pre_topc(sK1,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1693])).

cnf(c_8,plain,
    ( v6_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,k2_pre_topc(X1,X0)) != X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_401,plain,
    ( v6_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,k2_pre_topc(X1,X0)) != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_22])).

cnf(c_402,plain,
    ( v6_tops_1(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,k2_pre_topc(sK1,X0)) != X0 ),
    inference(unflattening,[status(thm)],[c_401])).

cnf(c_1699,plain,
    ( v6_tops_1(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) != sK3 ),
    inference(instantiation,[status(thm)],[c_402])).

cnf(c_1700,plain,
    ( k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) != sK3
    | v6_tops_1(sK3,sK1) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1699])).

cnf(c_1702,plain,
    ( ~ v6_tops_1(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_528])).

cnf(c_1703,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = sK2
    | v6_tops_1(sK2,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1702])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1819,plain,
    ( ~ r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3)
    | ~ r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))
    | k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) = sK3 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1820,plain,
    ( k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) = sK3
    | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3) != iProver_top
    | r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1819])).

cnf(c_7,plain,
    ( ~ v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_416,plain,
    ( ~ v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_22])).

cnf(c_417,plain,
    ( ~ v4_tops_1(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,X0)),X0) ),
    inference(unflattening,[status(thm)],[c_416])).

cnf(c_1830,plain,
    ( ~ v4_tops_1(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3) ),
    inference(instantiation,[status(thm)],[c_417])).

cnf(c_1831,plain,
    ( v4_tops_1(sK3,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1830])).

cnf(c_13,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_365,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k1_tops_1(X1,X2))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_22])).

cnf(c_366,plain,
    ( ~ v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k1_tops_1(sK1,X1)) ),
    inference(unflattening,[status(thm)],[c_365])).

cnf(c_1840,plain,
    ( ~ v3_pre_topc(sK3,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(sK3,X0)
    | r1_tarski(sK3,k1_tops_1(sK1,X0)) ),
    inference(instantiation,[status(thm)],[c_366])).

cnf(c_1934,plain,
    ( ~ v3_pre_topc(sK3,sK1)
    | ~ m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))
    | ~ r1_tarski(sK3,k2_pre_topc(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_1840])).

cnf(c_1935,plain,
    ( v3_pre_topc(sK3,sK1) != iProver_top
    | m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) = iProver_top
    | r1_tarski(sK3,k2_pre_topc(sK1,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1934])).

cnf(c_2542,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2434,c_28,c_29,c_30,c_31,c_32,c_1688,c_1694,c_1700,c_1703,c_1820,c_1831,c_1935])).

cnf(c_5,plain,
    ( v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
    | ~ r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_587,plain,
    ( v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
    | ~ r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_23])).

cnf(c_588,plain,
    ( v4_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,X0)))
    | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X0) ),
    inference(unflattening,[status(thm)],[c_587])).

cnf(c_1379,plain,
    ( v4_tops_1(X0,sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,X0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_588])).

cnf(c_2808,plain,
    ( v4_tops_1(sK2,sK0) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) != iProver_top
    | r1_tarski(sK2,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2542,c_1379])).

cnf(c_1721,plain,
    ( v4_tops_1(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK2)
    | ~ r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) ),
    inference(instantiation,[status(thm)],[c_588])).

cnf(c_1722,plain,
    ( v4_tops_1(sK2,sK0) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK2) != iProver_top
    | r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1721])).

cnf(c_761,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1943,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_761])).

cnf(c_763,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1858,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK2)
    | k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) != X0
    | sK2 != X1 ),
    inference(instantiation,[status(thm)],[c_763])).

cnf(c_2224,plain,
    ( ~ r1_tarski(X0,sK2)
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK2)
    | k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) != X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1858])).

cnf(c_2757,plain,
    ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK2)
    | ~ r1_tarski(sK2,sK2)
    | k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) != sK2
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_2224])).

cnf(c_2759,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) != sK2
    | sK2 != sK2
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK2) = iProver_top
    | r1_tarski(sK2,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2757])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2758,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2761,plain,
    ( r1_tarski(sK2,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2758])).

cnf(c_617,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_23])).

cnf(c_618,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_617])).

cnf(c_1377,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_618])).

cnf(c_10,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_24,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_264,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_24])).

cnf(c_265,plain,
    ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_264])).

cnf(c_269,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(k1_tops_1(sK0,X0),sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_265,c_23])).

cnf(c_270,plain,
    ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(renaming,[status(thm)],[c_269])).

cnf(c_1399,plain,
    ( v3_pre_topc(k1_tops_1(sK0,X0),sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_270])).

cnf(c_2245,plain,
    ( v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1377,c_1399])).

cnf(c_3873,plain,
    ( v3_pre_topc(sK2,sK0) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2542,c_2245])).

cnf(c_3876,plain,
    ( v3_pre_topc(sK2,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3873,c_28])).

cnf(c_15,negated_conjecture,
    ( ~ v3_pre_topc(sK2,sK0)
    | v4_tops_1(sK3,sK1)
    | ~ v4_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1406,plain,
    ( v3_pre_topc(sK2,sK0) != iProver_top
    | v4_tops_1(sK3,sK1) = iProver_top
    | v4_tops_1(sK2,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3882,plain,
    ( v4_tops_1(sK3,sK1) = iProver_top
    | v4_tops_1(sK2,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3876,c_1406])).

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

cnf(c_16,negated_conjecture,
    ( v3_pre_topc(sK3,sK1)
    | ~ v3_pre_topc(sK2,sK0)
    | ~ v4_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1405,plain,
    ( v3_pre_topc(sK3,sK1) = iProver_top
    | v3_pre_topc(sK2,sK0) != iProver_top
    | v4_tops_1(sK2,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3883,plain,
    ( v3_pre_topc(sK3,sK1) = iProver_top
    | v4_tops_1(sK2,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3876,c_1405])).

cnf(c_3910,plain,
    ( v4_tops_1(sK2,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3882,c_28,c_29,c_35,c_1688,c_1694,c_1700,c_1820,c_1831,c_1935,c_3873,c_3883])).

cnf(c_4251,plain,
    ( r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2808,c_28,c_29,c_30,c_31,c_32,c_35,c_1688,c_1694,c_1700,c_1703,c_1722,c_1820,c_1831,c_1935,c_1943,c_2759,c_2761,c_3873,c_3882,c_3883])).

cnf(c_12,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_307,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X1,X0) = X0
    | sK0 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_24])).

cnf(c_308,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK0)
    | k1_tops_1(X1,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_307])).

cnf(c_312,plain,
    ( ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X0,X1)
    | k1_tops_1(X1,X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_308,c_23])).

cnf(c_313,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = X0 ),
    inference(renaming,[status(thm)],[c_312])).

cnf(c_488,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(X1,X0) = X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_313,c_23])).

cnf(c_489,plain,
    ( ~ v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_488])).

cnf(c_756,plain,
    ( ~ v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) = X0
    | ~ sP3_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP3_iProver_split])],[c_489])).

cnf(c_1386,plain,
    ( k1_tops_1(sK0,X0) = X0
    | v3_pre_topc(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | sP3_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_756])).

cnf(c_757,plain,
    ( sP3_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_489])).

cnf(c_801,plain,
    ( sP3_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_757])).

cnf(c_802,plain,
    ( k1_tops_1(sK0,X0) = X0
    | v3_pre_topc(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | sP3_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_756])).

cnf(c_11,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_282,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X1,X0) != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_24])).

cnf(c_283,plain,
    ( v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(sK0)
    | k1_tops_1(sK0,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_282])).

cnf(c_287,plain,
    ( ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | v3_pre_topc(X0,sK0)
    | k1_tops_1(sK0,X0) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_283,c_23])).

cnf(c_288,plain,
    ( v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(X2)
    | k1_tops_1(sK0,X0) != X0 ),
    inference(renaming,[status(thm)],[c_287])).

cnf(c_647,plain,
    ( v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) != X0
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_288])).

cnf(c_648,plain,
    ( v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_647])).

cnf(c_751,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_648])).

cnf(c_1677,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ sP0_iProver_split ),
    inference(instantiation,[status(thm)],[c_751])).

cnf(c_1678,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1677])).

cnf(c_3070,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v3_pre_topc(X0,sK0) != iProver_top
    | k1_tops_1(sK0,X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1386,c_28,c_801,c_802,c_1678])).

cnf(c_3071,plain,
    ( k1_tops_1(sK0,X0) = X0
    | v3_pre_topc(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3070])).

cnf(c_3077,plain,
    ( k1_tops_1(sK0,sK2) = sK2
    | v3_pre_topc(sK2,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1400,c_3071])).

cnf(c_3881,plain,
    ( k1_tops_1(sK0,sK2) = sK2 ),
    inference(superposition,[status(thm)],[c_3876,c_3077])).

cnf(c_4255,plain,
    ( r1_tarski(sK2,k2_pre_topc(sK0,sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4251,c_3881])).

cnf(c_605,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_23])).

cnf(c_606,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,k2_pre_topc(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_605])).

cnf(c_1378,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_606])).

cnf(c_1885,plain,
    ( r1_tarski(sK2,k2_pre_topc(sK0,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1400,c_1378])).

cnf(c_4257,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4255,c_1885])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:12:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 2.64/1.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.64/1.03  
% 2.64/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.64/1.03  
% 2.64/1.03  ------  iProver source info
% 2.64/1.03  
% 2.64/1.03  git: date: 2020-06-30 10:37:57 +0100
% 2.64/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.64/1.03  git: non_committed_changes: false
% 2.64/1.03  git: last_make_outside_of_git: false
% 2.64/1.03  
% 2.64/1.03  ------ 
% 2.64/1.03  
% 2.64/1.03  ------ Input Options
% 2.64/1.03  
% 2.64/1.03  --out_options                           all
% 2.64/1.03  --tptp_safe_out                         true
% 2.64/1.03  --problem_path                          ""
% 2.64/1.03  --include_path                          ""
% 2.64/1.03  --clausifier                            res/vclausify_rel
% 2.64/1.03  --clausifier_options                    --mode clausify
% 2.64/1.03  --stdin                                 false
% 2.64/1.03  --stats_out                             all
% 2.64/1.03  
% 2.64/1.03  ------ General Options
% 2.64/1.03  
% 2.64/1.03  --fof                                   false
% 2.64/1.03  --time_out_real                         305.
% 2.64/1.03  --time_out_virtual                      -1.
% 2.64/1.03  --symbol_type_check                     false
% 2.64/1.03  --clausify_out                          false
% 2.64/1.03  --sig_cnt_out                           false
% 2.64/1.03  --trig_cnt_out                          false
% 2.64/1.03  --trig_cnt_out_tolerance                1.
% 2.64/1.03  --trig_cnt_out_sk_spl                   false
% 2.64/1.03  --abstr_cl_out                          false
% 2.64/1.03  
% 2.64/1.03  ------ Global Options
% 2.64/1.03  
% 2.64/1.03  --schedule                              default
% 2.64/1.03  --add_important_lit                     false
% 2.64/1.03  --prop_solver_per_cl                    1000
% 2.64/1.03  --min_unsat_core                        false
% 2.64/1.03  --soft_assumptions                      false
% 2.64/1.03  --soft_lemma_size                       3
% 2.64/1.03  --prop_impl_unit_size                   0
% 2.64/1.03  --prop_impl_unit                        []
% 2.64/1.03  --share_sel_clauses                     true
% 2.64/1.03  --reset_solvers                         false
% 2.64/1.03  --bc_imp_inh                            [conj_cone]
% 2.64/1.03  --conj_cone_tolerance                   3.
% 2.64/1.03  --extra_neg_conj                        none
% 2.64/1.03  --large_theory_mode                     true
% 2.64/1.03  --prolific_symb_bound                   200
% 2.64/1.03  --lt_threshold                          2000
% 2.64/1.03  --clause_weak_htbl                      true
% 2.64/1.03  --gc_record_bc_elim                     false
% 2.64/1.03  
% 2.64/1.03  ------ Preprocessing Options
% 2.64/1.03  
% 2.64/1.03  --preprocessing_flag                    true
% 2.64/1.03  --time_out_prep_mult                    0.1
% 2.64/1.03  --splitting_mode                        input
% 2.64/1.03  --splitting_grd                         true
% 2.64/1.03  --splitting_cvd                         false
% 2.64/1.03  --splitting_cvd_svl                     false
% 2.64/1.03  --splitting_nvd                         32
% 2.64/1.03  --sub_typing                            true
% 2.64/1.03  --prep_gs_sim                           true
% 2.64/1.03  --prep_unflatten                        true
% 2.64/1.03  --prep_res_sim                          true
% 2.64/1.03  --prep_upred                            true
% 2.64/1.03  --prep_sem_filter                       exhaustive
% 2.64/1.03  --prep_sem_filter_out                   false
% 2.64/1.03  --pred_elim                             true
% 2.64/1.03  --res_sim_input                         true
% 2.64/1.03  --eq_ax_congr_red                       true
% 2.64/1.03  --pure_diseq_elim                       true
% 2.64/1.03  --brand_transform                       false
% 2.64/1.03  --non_eq_to_eq                          false
% 2.64/1.03  --prep_def_merge                        true
% 2.64/1.03  --prep_def_merge_prop_impl              false
% 2.64/1.03  --prep_def_merge_mbd                    true
% 2.64/1.03  --prep_def_merge_tr_red                 false
% 2.64/1.03  --prep_def_merge_tr_cl                  false
% 2.64/1.03  --smt_preprocessing                     true
% 2.64/1.03  --smt_ac_axioms                         fast
% 2.64/1.03  --preprocessed_out                      false
% 2.64/1.03  --preprocessed_stats                    false
% 2.64/1.03  
% 2.64/1.03  ------ Abstraction refinement Options
% 2.64/1.03  
% 2.64/1.03  --abstr_ref                             []
% 2.64/1.03  --abstr_ref_prep                        false
% 2.64/1.03  --abstr_ref_until_sat                   false
% 2.64/1.03  --abstr_ref_sig_restrict                funpre
% 2.64/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.64/1.03  --abstr_ref_under                       []
% 2.64/1.03  
% 2.64/1.03  ------ SAT Options
% 2.64/1.03  
% 2.64/1.03  --sat_mode                              false
% 2.64/1.03  --sat_fm_restart_options                ""
% 2.64/1.03  --sat_gr_def                            false
% 2.64/1.03  --sat_epr_types                         true
% 2.64/1.03  --sat_non_cyclic_types                  false
% 2.64/1.03  --sat_finite_models                     false
% 2.64/1.03  --sat_fm_lemmas                         false
% 2.64/1.03  --sat_fm_prep                           false
% 2.64/1.03  --sat_fm_uc_incr                        true
% 2.64/1.03  --sat_out_model                         small
% 2.64/1.03  --sat_out_clauses                       false
% 2.64/1.03  
% 2.64/1.03  ------ QBF Options
% 2.64/1.03  
% 2.64/1.03  --qbf_mode                              false
% 2.64/1.03  --qbf_elim_univ                         false
% 2.64/1.03  --qbf_dom_inst                          none
% 2.64/1.03  --qbf_dom_pre_inst                      false
% 2.64/1.03  --qbf_sk_in                             false
% 2.64/1.03  --qbf_pred_elim                         true
% 2.64/1.03  --qbf_split                             512
% 2.64/1.03  
% 2.64/1.03  ------ BMC1 Options
% 2.64/1.03  
% 2.64/1.03  --bmc1_incremental                      false
% 2.64/1.03  --bmc1_axioms                           reachable_all
% 2.64/1.03  --bmc1_min_bound                        0
% 2.64/1.03  --bmc1_max_bound                        -1
% 2.64/1.03  --bmc1_max_bound_default                -1
% 2.64/1.03  --bmc1_symbol_reachability              true
% 2.64/1.03  --bmc1_property_lemmas                  false
% 2.64/1.03  --bmc1_k_induction                      false
% 2.64/1.03  --bmc1_non_equiv_states                 false
% 2.64/1.03  --bmc1_deadlock                         false
% 2.64/1.03  --bmc1_ucm                              false
% 2.64/1.03  --bmc1_add_unsat_core                   none
% 2.64/1.03  --bmc1_unsat_core_children              false
% 2.64/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.64/1.03  --bmc1_out_stat                         full
% 2.64/1.03  --bmc1_ground_init                      false
% 2.64/1.03  --bmc1_pre_inst_next_state              false
% 2.64/1.03  --bmc1_pre_inst_state                   false
% 2.64/1.03  --bmc1_pre_inst_reach_state             false
% 2.64/1.03  --bmc1_out_unsat_core                   false
% 2.64/1.03  --bmc1_aig_witness_out                  false
% 2.64/1.03  --bmc1_verbose                          false
% 2.64/1.03  --bmc1_dump_clauses_tptp                false
% 2.64/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.64/1.03  --bmc1_dump_file                        -
% 2.64/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.64/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.64/1.03  --bmc1_ucm_extend_mode                  1
% 2.64/1.03  --bmc1_ucm_init_mode                    2
% 2.64/1.03  --bmc1_ucm_cone_mode                    none
% 2.64/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.64/1.03  --bmc1_ucm_relax_model                  4
% 2.64/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.64/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.64/1.03  --bmc1_ucm_layered_model                none
% 2.64/1.03  --bmc1_ucm_max_lemma_size               10
% 2.64/1.03  
% 2.64/1.03  ------ AIG Options
% 2.64/1.03  
% 2.64/1.03  --aig_mode                              false
% 2.64/1.03  
% 2.64/1.03  ------ Instantiation Options
% 2.64/1.03  
% 2.64/1.03  --instantiation_flag                    true
% 2.64/1.03  --inst_sos_flag                         false
% 2.64/1.03  --inst_sos_phase                        true
% 2.64/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.64/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.64/1.03  --inst_lit_sel_side                     num_symb
% 2.64/1.03  --inst_solver_per_active                1400
% 2.64/1.03  --inst_solver_calls_frac                1.
% 2.64/1.03  --inst_passive_queue_type               priority_queues
% 2.64/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.64/1.03  --inst_passive_queues_freq              [25;2]
% 2.64/1.03  --inst_dismatching                      true
% 2.64/1.03  --inst_eager_unprocessed_to_passive     true
% 2.64/1.03  --inst_prop_sim_given                   true
% 2.64/1.03  --inst_prop_sim_new                     false
% 2.64/1.03  --inst_subs_new                         false
% 2.64/1.03  --inst_eq_res_simp                      false
% 2.64/1.03  --inst_subs_given                       false
% 2.64/1.03  --inst_orphan_elimination               true
% 2.64/1.03  --inst_learning_loop_flag               true
% 2.64/1.03  --inst_learning_start                   3000
% 2.64/1.03  --inst_learning_factor                  2
% 2.64/1.03  --inst_start_prop_sim_after_learn       3
% 2.64/1.03  --inst_sel_renew                        solver
% 2.64/1.03  --inst_lit_activity_flag                true
% 2.64/1.03  --inst_restr_to_given                   false
% 2.64/1.03  --inst_activity_threshold               500
% 2.64/1.03  --inst_out_proof                        true
% 2.64/1.03  
% 2.64/1.03  ------ Resolution Options
% 2.64/1.03  
% 2.64/1.03  --resolution_flag                       true
% 2.64/1.03  --res_lit_sel                           adaptive
% 2.64/1.03  --res_lit_sel_side                      none
% 2.64/1.03  --res_ordering                          kbo
% 2.64/1.03  --res_to_prop_solver                    active
% 2.64/1.03  --res_prop_simpl_new                    false
% 2.64/1.03  --res_prop_simpl_given                  true
% 2.64/1.03  --res_passive_queue_type                priority_queues
% 2.64/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.64/1.03  --res_passive_queues_freq               [15;5]
% 2.64/1.03  --res_forward_subs                      full
% 2.64/1.03  --res_backward_subs                     full
% 2.64/1.03  --res_forward_subs_resolution           true
% 2.64/1.03  --res_backward_subs_resolution          true
% 2.64/1.03  --res_orphan_elimination                true
% 2.64/1.03  --res_time_limit                        2.
% 2.64/1.03  --res_out_proof                         true
% 2.64/1.03  
% 2.64/1.03  ------ Superposition Options
% 2.64/1.03  
% 2.64/1.03  --superposition_flag                    true
% 2.64/1.03  --sup_passive_queue_type                priority_queues
% 2.64/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.64/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.64/1.03  --demod_completeness_check              fast
% 2.64/1.03  --demod_use_ground                      true
% 2.64/1.03  --sup_to_prop_solver                    passive
% 2.64/1.03  --sup_prop_simpl_new                    true
% 2.64/1.03  --sup_prop_simpl_given                  true
% 2.64/1.03  --sup_fun_splitting                     false
% 2.64/1.03  --sup_smt_interval                      50000
% 2.64/1.03  
% 2.64/1.03  ------ Superposition Simplification Setup
% 2.64/1.03  
% 2.64/1.03  --sup_indices_passive                   []
% 2.64/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.64/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.64/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.64/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.64/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.64/1.03  --sup_full_bw                           [BwDemod]
% 2.64/1.03  --sup_immed_triv                        [TrivRules]
% 2.64/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.64/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.64/1.03  --sup_immed_bw_main                     []
% 2.64/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.64/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.64/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.64/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.64/1.03  
% 2.64/1.03  ------ Combination Options
% 2.64/1.03  
% 2.64/1.03  --comb_res_mult                         3
% 2.64/1.03  --comb_sup_mult                         2
% 2.64/1.03  --comb_inst_mult                        10
% 2.64/1.03  
% 2.64/1.03  ------ Debug Options
% 2.64/1.03  
% 2.64/1.03  --dbg_backtrace                         false
% 2.64/1.03  --dbg_dump_prop_clauses                 false
% 2.64/1.03  --dbg_dump_prop_clauses_file            -
% 2.64/1.03  --dbg_out_stat                          false
% 2.64/1.03  ------ Parsing...
% 2.64/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.64/1.03  
% 2.64/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 2.64/1.03  
% 2.64/1.03  ------ Preprocessing... gs_s  sp: 8 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.64/1.03  
% 2.64/1.03  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.64/1.03  ------ Proving...
% 2.64/1.03  ------ Problem Properties 
% 2.64/1.03  
% 2.64/1.03  
% 2.64/1.03  clauses                                 39
% 2.64/1.03  conjectures                             8
% 2.64/1.03  EPR                                     12
% 2.64/1.03  Horn                                    33
% 2.64/1.03  unary                                   3
% 2.64/1.03  binary                                  16
% 2.64/1.03  lits                                    105
% 2.64/1.03  lits eq                                 9
% 2.64/1.03  fd_pure                                 0
% 2.64/1.03  fd_pseudo                               0
% 2.64/1.03  fd_cond                                 0
% 2.64/1.03  fd_pseudo_cond                          1
% 2.64/1.03  AC symbols                              0
% 2.64/1.03  
% 2.64/1.03  ------ Schedule dynamic 5 is on 
% 2.64/1.03  
% 2.64/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.64/1.03  
% 2.64/1.03  
% 2.64/1.03  ------ 
% 2.64/1.03  Current options:
% 2.64/1.03  ------ 
% 2.64/1.03  
% 2.64/1.03  ------ Input Options
% 2.64/1.03  
% 2.64/1.03  --out_options                           all
% 2.64/1.03  --tptp_safe_out                         true
% 2.64/1.03  --problem_path                          ""
% 2.64/1.03  --include_path                          ""
% 2.64/1.03  --clausifier                            res/vclausify_rel
% 2.64/1.03  --clausifier_options                    --mode clausify
% 2.64/1.03  --stdin                                 false
% 2.64/1.03  --stats_out                             all
% 2.64/1.03  
% 2.64/1.03  ------ General Options
% 2.64/1.03  
% 2.64/1.03  --fof                                   false
% 2.64/1.03  --time_out_real                         305.
% 2.64/1.03  --time_out_virtual                      -1.
% 2.64/1.03  --symbol_type_check                     false
% 2.64/1.03  --clausify_out                          false
% 2.64/1.03  --sig_cnt_out                           false
% 2.64/1.03  --trig_cnt_out                          false
% 2.64/1.03  --trig_cnt_out_tolerance                1.
% 2.64/1.03  --trig_cnt_out_sk_spl                   false
% 2.64/1.03  --abstr_cl_out                          false
% 2.64/1.03  
% 2.64/1.03  ------ Global Options
% 2.64/1.03  
% 2.64/1.03  --schedule                              default
% 2.64/1.03  --add_important_lit                     false
% 2.64/1.03  --prop_solver_per_cl                    1000
% 2.64/1.03  --min_unsat_core                        false
% 2.64/1.03  --soft_assumptions                      false
% 2.64/1.03  --soft_lemma_size                       3
% 2.64/1.03  --prop_impl_unit_size                   0
% 2.64/1.03  --prop_impl_unit                        []
% 2.64/1.03  --share_sel_clauses                     true
% 2.64/1.03  --reset_solvers                         false
% 2.64/1.03  --bc_imp_inh                            [conj_cone]
% 2.64/1.03  --conj_cone_tolerance                   3.
% 2.64/1.03  --extra_neg_conj                        none
% 2.64/1.03  --large_theory_mode                     true
% 2.64/1.03  --prolific_symb_bound                   200
% 2.64/1.03  --lt_threshold                          2000
% 2.64/1.03  --clause_weak_htbl                      true
% 2.64/1.03  --gc_record_bc_elim                     false
% 2.64/1.03  
% 2.64/1.03  ------ Preprocessing Options
% 2.64/1.03  
% 2.64/1.03  --preprocessing_flag                    true
% 2.64/1.03  --time_out_prep_mult                    0.1
% 2.64/1.03  --splitting_mode                        input
% 2.64/1.03  --splitting_grd                         true
% 2.64/1.03  --splitting_cvd                         false
% 2.64/1.03  --splitting_cvd_svl                     false
% 2.64/1.03  --splitting_nvd                         32
% 2.64/1.03  --sub_typing                            true
% 2.64/1.03  --prep_gs_sim                           true
% 2.64/1.03  --prep_unflatten                        true
% 2.64/1.03  --prep_res_sim                          true
% 2.64/1.03  --prep_upred                            true
% 2.64/1.03  --prep_sem_filter                       exhaustive
% 2.64/1.03  --prep_sem_filter_out                   false
% 2.64/1.03  --pred_elim                             true
% 2.64/1.03  --res_sim_input                         true
% 2.64/1.03  --eq_ax_congr_red                       true
% 2.64/1.03  --pure_diseq_elim                       true
% 2.64/1.03  --brand_transform                       false
% 2.64/1.03  --non_eq_to_eq                          false
% 2.64/1.03  --prep_def_merge                        true
% 2.64/1.03  --prep_def_merge_prop_impl              false
% 2.64/1.03  --prep_def_merge_mbd                    true
% 2.64/1.03  --prep_def_merge_tr_red                 false
% 2.64/1.03  --prep_def_merge_tr_cl                  false
% 2.64/1.03  --smt_preprocessing                     true
% 2.64/1.03  --smt_ac_axioms                         fast
% 2.64/1.03  --preprocessed_out                      false
% 2.64/1.03  --preprocessed_stats                    false
% 2.64/1.03  
% 2.64/1.03  ------ Abstraction refinement Options
% 2.64/1.03  
% 2.64/1.03  --abstr_ref                             []
% 2.64/1.03  --abstr_ref_prep                        false
% 2.64/1.03  --abstr_ref_until_sat                   false
% 2.64/1.03  --abstr_ref_sig_restrict                funpre
% 2.64/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.64/1.03  --abstr_ref_under                       []
% 2.64/1.03  
% 2.64/1.03  ------ SAT Options
% 2.64/1.03  
% 2.64/1.03  --sat_mode                              false
% 2.64/1.03  --sat_fm_restart_options                ""
% 2.64/1.03  --sat_gr_def                            false
% 2.64/1.03  --sat_epr_types                         true
% 2.64/1.03  --sat_non_cyclic_types                  false
% 2.64/1.03  --sat_finite_models                     false
% 2.64/1.03  --sat_fm_lemmas                         false
% 2.64/1.03  --sat_fm_prep                           false
% 2.64/1.03  --sat_fm_uc_incr                        true
% 2.64/1.03  --sat_out_model                         small
% 2.64/1.03  --sat_out_clauses                       false
% 2.64/1.03  
% 2.64/1.03  ------ QBF Options
% 2.64/1.03  
% 2.64/1.03  --qbf_mode                              false
% 2.64/1.03  --qbf_elim_univ                         false
% 2.64/1.03  --qbf_dom_inst                          none
% 2.64/1.03  --qbf_dom_pre_inst                      false
% 2.64/1.03  --qbf_sk_in                             false
% 2.64/1.03  --qbf_pred_elim                         true
% 2.64/1.03  --qbf_split                             512
% 2.64/1.03  
% 2.64/1.03  ------ BMC1 Options
% 2.64/1.03  
% 2.64/1.03  --bmc1_incremental                      false
% 2.64/1.03  --bmc1_axioms                           reachable_all
% 2.64/1.03  --bmc1_min_bound                        0
% 2.64/1.03  --bmc1_max_bound                        -1
% 2.64/1.03  --bmc1_max_bound_default                -1
% 2.64/1.03  --bmc1_symbol_reachability              true
% 2.64/1.03  --bmc1_property_lemmas                  false
% 2.64/1.03  --bmc1_k_induction                      false
% 2.64/1.03  --bmc1_non_equiv_states                 false
% 2.64/1.03  --bmc1_deadlock                         false
% 2.64/1.03  --bmc1_ucm                              false
% 2.64/1.03  --bmc1_add_unsat_core                   none
% 2.64/1.03  --bmc1_unsat_core_children              false
% 2.64/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.64/1.03  --bmc1_out_stat                         full
% 2.64/1.03  --bmc1_ground_init                      false
% 2.64/1.03  --bmc1_pre_inst_next_state              false
% 2.64/1.03  --bmc1_pre_inst_state                   false
% 2.64/1.03  --bmc1_pre_inst_reach_state             false
% 2.64/1.03  --bmc1_out_unsat_core                   false
% 2.64/1.03  --bmc1_aig_witness_out                  false
% 2.64/1.03  --bmc1_verbose                          false
% 2.64/1.03  --bmc1_dump_clauses_tptp                false
% 2.64/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.64/1.03  --bmc1_dump_file                        -
% 2.64/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.64/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.64/1.03  --bmc1_ucm_extend_mode                  1
% 2.64/1.03  --bmc1_ucm_init_mode                    2
% 2.64/1.03  --bmc1_ucm_cone_mode                    none
% 2.64/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.64/1.03  --bmc1_ucm_relax_model                  4
% 2.64/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.64/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.64/1.03  --bmc1_ucm_layered_model                none
% 2.64/1.03  --bmc1_ucm_max_lemma_size               10
% 2.64/1.03  
% 2.64/1.03  ------ AIG Options
% 2.64/1.03  
% 2.64/1.03  --aig_mode                              false
% 2.64/1.03  
% 2.64/1.03  ------ Instantiation Options
% 2.64/1.03  
% 2.64/1.03  --instantiation_flag                    true
% 2.64/1.03  --inst_sos_flag                         false
% 2.64/1.03  --inst_sos_phase                        true
% 2.64/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.64/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.64/1.03  --inst_lit_sel_side                     none
% 2.64/1.03  --inst_solver_per_active                1400
% 2.64/1.03  --inst_solver_calls_frac                1.
% 2.64/1.03  --inst_passive_queue_type               priority_queues
% 2.64/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.64/1.03  --inst_passive_queues_freq              [25;2]
% 2.64/1.03  --inst_dismatching                      true
% 2.64/1.03  --inst_eager_unprocessed_to_passive     true
% 2.64/1.03  --inst_prop_sim_given                   true
% 2.64/1.03  --inst_prop_sim_new                     false
% 2.64/1.03  --inst_subs_new                         false
% 2.64/1.03  --inst_eq_res_simp                      false
% 2.64/1.03  --inst_subs_given                       false
% 2.64/1.03  --inst_orphan_elimination               true
% 2.64/1.03  --inst_learning_loop_flag               true
% 2.64/1.03  --inst_learning_start                   3000
% 2.64/1.03  --inst_learning_factor                  2
% 2.64/1.03  --inst_start_prop_sim_after_learn       3
% 2.64/1.03  --inst_sel_renew                        solver
% 2.64/1.03  --inst_lit_activity_flag                true
% 2.64/1.03  --inst_restr_to_given                   false
% 2.64/1.03  --inst_activity_threshold               500
% 2.64/1.03  --inst_out_proof                        true
% 2.64/1.03  
% 2.64/1.03  ------ Resolution Options
% 2.64/1.03  
% 2.64/1.03  --resolution_flag                       false
% 2.64/1.03  --res_lit_sel                           adaptive
% 2.64/1.03  --res_lit_sel_side                      none
% 2.64/1.03  --res_ordering                          kbo
% 2.64/1.03  --res_to_prop_solver                    active
% 2.64/1.03  --res_prop_simpl_new                    false
% 2.64/1.03  --res_prop_simpl_given                  true
% 2.64/1.03  --res_passive_queue_type                priority_queues
% 2.64/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.64/1.03  --res_passive_queues_freq               [15;5]
% 2.64/1.03  --res_forward_subs                      full
% 2.64/1.03  --res_backward_subs                     full
% 2.64/1.03  --res_forward_subs_resolution           true
% 2.64/1.03  --res_backward_subs_resolution          true
% 2.64/1.03  --res_orphan_elimination                true
% 2.64/1.03  --res_time_limit                        2.
% 2.64/1.03  --res_out_proof                         true
% 2.64/1.03  
% 2.64/1.03  ------ Superposition Options
% 2.64/1.03  
% 2.64/1.03  --superposition_flag                    true
% 2.64/1.03  --sup_passive_queue_type                priority_queues
% 2.64/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.64/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.64/1.03  --demod_completeness_check              fast
% 2.64/1.03  --demod_use_ground                      true
% 2.64/1.03  --sup_to_prop_solver                    passive
% 2.64/1.03  --sup_prop_simpl_new                    true
% 2.64/1.03  --sup_prop_simpl_given                  true
% 2.64/1.03  --sup_fun_splitting                     false
% 2.64/1.03  --sup_smt_interval                      50000
% 2.64/1.03  
% 2.64/1.03  ------ Superposition Simplification Setup
% 2.64/1.03  
% 2.64/1.03  --sup_indices_passive                   []
% 2.64/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.64/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.64/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.64/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.64/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.64/1.03  --sup_full_bw                           [BwDemod]
% 2.64/1.03  --sup_immed_triv                        [TrivRules]
% 2.64/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.64/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.64/1.03  --sup_immed_bw_main                     []
% 2.64/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.64/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.64/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.64/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.64/1.03  
% 2.64/1.03  ------ Combination Options
% 2.64/1.03  
% 2.64/1.03  --comb_res_mult                         3
% 2.64/1.03  --comb_sup_mult                         2
% 2.64/1.03  --comb_inst_mult                        10
% 2.64/1.03  
% 2.64/1.03  ------ Debug Options
% 2.64/1.03  
% 2.64/1.03  --dbg_backtrace                         false
% 2.64/1.03  --dbg_dump_prop_clauses                 false
% 2.64/1.03  --dbg_dump_prop_clauses_file            -
% 2.64/1.03  --dbg_out_stat                          false
% 2.64/1.03  
% 2.64/1.03  
% 2.64/1.03  
% 2.64/1.03  
% 2.64/1.03  ------ Proving...
% 2.64/1.03  
% 2.64/1.03  
% 2.64/1.03  % SZS status Theorem for theBenchmark.p
% 2.64/1.03  
% 2.64/1.03   Resolution empty clause
% 2.64/1.03  
% 2.64/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 2.64/1.03  
% 2.64/1.03  fof(f9,conjecture,(
% 2.64/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v6_tops_1(X2,X0) => (v4_tops_1(X2,X0) & v3_pre_topc(X2,X0))) & ((v4_tops_1(X3,X1) & v3_pre_topc(X3,X1)) => v6_tops_1(X3,X1)))))))),
% 2.64/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.64/1.03  
% 2.64/1.03  fof(f10,negated_conjecture,(
% 2.64/1.03    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v6_tops_1(X2,X0) => (v4_tops_1(X2,X0) & v3_pre_topc(X2,X0))) & ((v4_tops_1(X3,X1) & v3_pre_topc(X3,X1)) => v6_tops_1(X3,X1)))))))),
% 2.64/1.03    inference(negated_conjecture,[],[f9])).
% 2.64/1.03  
% 2.64/1.03  fof(f22,plain,(
% 2.64/1.03    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(X3,X1) & (v4_tops_1(X3,X1) & v3_pre_topc(X3,X1)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.64/1.03    inference(ennf_transformation,[],[f10])).
% 2.64/1.03  
% 2.64/1.03  fof(f23,plain,(
% 2.64/1.03    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.64/1.03    inference(flattening,[],[f22])).
% 2.64/1.03  
% 2.64/1.03  fof(f32,plain,(
% 2.64/1.03    ( ! [X2,X0,X1] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(sK3,X1) & v4_tops_1(sK3,X1) & v3_pre_topc(sK3,X1))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X1))))) )),
% 2.64/1.03    introduced(choice_axiom,[])).
% 2.64/1.03  
% 2.64/1.03  fof(f31,plain,(
% 2.64/1.03    ( ! [X0,X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X3] : ((((~v4_tops_1(sK2,X0) | ~v3_pre_topc(sK2,X0)) & v6_tops_1(sK2,X0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.64/1.03    introduced(choice_axiom,[])).
% 2.64/1.03  
% 2.64/1.03  fof(f30,plain,(
% 2.64/1.03    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) => (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(X3,sK1) & v4_tops_1(X3,sK1) & v3_pre_topc(X3,sK1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(sK1))) )),
% 2.64/1.03    introduced(choice_axiom,[])).
% 2.64/1.03  
% 2.64/1.03  fof(f29,plain,(
% 2.64/1.03    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,sK0) | ~v3_pre_topc(X2,sK0)) & v6_tops_1(X2,sK0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 2.64/1.03    introduced(choice_axiom,[])).
% 2.64/1.03  
% 2.64/1.03  fof(f33,plain,(
% 2.64/1.03    ((((((~v4_tops_1(sK2,sK0) | ~v3_pre_topc(sK2,sK0)) & v6_tops_1(sK2,sK0)) | (~v6_tops_1(sK3,sK1) & v4_tops_1(sK3,sK1) & v3_pre_topc(sK3,sK1))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 2.64/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f32,f31,f30,f29])).
% 2.64/1.03  
% 2.64/1.03  fof(f51,plain,(
% 2.64/1.03    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.64/1.03    inference(cnf_transformation,[],[f33])).
% 2.64/1.03  
% 2.64/1.03  fof(f5,axiom,(
% 2.64/1.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v6_tops_1(X1,X0) <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1)))),
% 2.64/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.64/1.03  
% 2.64/1.03  fof(f15,plain,(
% 2.64/1.03    ! [X0] : (! [X1] : ((v6_tops_1(X1,X0) <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.64/1.03    inference(ennf_transformation,[],[f5])).
% 2.64/1.03  
% 2.64/1.03  fof(f28,plain,(
% 2.64/1.03    ! [X0] : (! [X1] : (((v6_tops_1(X1,X0) | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1) & (k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 | ~v6_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.64/1.03    inference(nnf_transformation,[],[f15])).
% 2.64/1.03  
% 2.64/1.03  fof(f42,plain,(
% 2.64/1.03    ( ! [X0,X1] : (k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 | ~v6_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.64/1.03    inference(cnf_transformation,[],[f28])).
% 2.64/1.03  
% 2.64/1.03  fof(f49,plain,(
% 2.64/1.03    l1_pre_topc(sK0)),
% 2.64/1.03    inference(cnf_transformation,[],[f33])).
% 2.64/1.03  
% 2.64/1.03  fof(f52,plain,(
% 2.64/1.03    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 2.64/1.03    inference(cnf_transformation,[],[f33])).
% 2.64/1.03  
% 2.64/1.03  fof(f53,plain,(
% 2.64/1.03    v6_tops_1(sK2,sK0) | v3_pre_topc(sK3,sK1)),
% 2.64/1.03    inference(cnf_transformation,[],[f33])).
% 2.64/1.03  
% 2.64/1.03  fof(f54,plain,(
% 2.64/1.03    v6_tops_1(sK2,sK0) | v4_tops_1(sK3,sK1)),
% 2.64/1.03    inference(cnf_transformation,[],[f33])).
% 2.64/1.03  
% 2.64/1.03  fof(f55,plain,(
% 2.64/1.03    v6_tops_1(sK2,sK0) | ~v6_tops_1(sK3,sK1)),
% 2.64/1.03    inference(cnf_transformation,[],[f33])).
% 2.64/1.03  
% 2.64/1.03  fof(f2,axiom,(
% 2.64/1.03    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.64/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.64/1.03  
% 2.64/1.03  fof(f11,plain,(
% 2.64/1.03    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.64/1.03    inference(ennf_transformation,[],[f2])).
% 2.64/1.03  
% 2.64/1.03  fof(f12,plain,(
% 2.64/1.03    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.64/1.03    inference(flattening,[],[f11])).
% 2.64/1.03  
% 2.64/1.03  fof(f37,plain,(
% 2.64/1.03    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.64/1.03    inference(cnf_transformation,[],[f12])).
% 2.64/1.03  
% 2.64/1.03  fof(f50,plain,(
% 2.64/1.03    l1_pre_topc(sK1)),
% 2.64/1.03    inference(cnf_transformation,[],[f33])).
% 2.64/1.03  
% 2.64/1.03  fof(f3,axiom,(
% 2.64/1.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 2.64/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.64/1.03  
% 2.64/1.03  fof(f13,plain,(
% 2.64/1.03    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.64/1.03    inference(ennf_transformation,[],[f3])).
% 2.64/1.03  
% 2.64/1.03  fof(f38,plain,(
% 2.64/1.03    ( ! [X0,X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.64/1.03    inference(cnf_transformation,[],[f13])).
% 2.64/1.03  
% 2.64/1.03  fof(f43,plain,(
% 2.64/1.03    ( ! [X0,X1] : (v6_tops_1(X1,X0) | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.64/1.03    inference(cnf_transformation,[],[f28])).
% 2.64/1.03  
% 2.64/1.03  fof(f1,axiom,(
% 2.64/1.03    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.64/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.64/1.03  
% 2.64/1.03  fof(f24,plain,(
% 2.64/1.03    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.64/1.03    inference(nnf_transformation,[],[f1])).
% 2.64/1.03  
% 2.64/1.03  fof(f25,plain,(
% 2.64/1.03    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.64/1.03    inference(flattening,[],[f24])).
% 2.64/1.03  
% 2.64/1.03  fof(f36,plain,(
% 2.64/1.03    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.64/1.03    inference(cnf_transformation,[],[f25])).
% 2.64/1.03  
% 2.64/1.03  fof(f4,axiom,(
% 2.64/1.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)))))),
% 2.64/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.64/1.03  
% 2.64/1.03  fof(f14,plain,(
% 2.64/1.03    ! [X0] : (! [X1] : ((v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.64/1.03    inference(ennf_transformation,[],[f4])).
% 2.64/1.03  
% 2.64/1.03  fof(f26,plain,(
% 2.64/1.03    ! [X0] : (! [X1] : (((v4_tops_1(X1,X0) | (~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1))) & ((r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) | ~v4_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.64/1.03    inference(nnf_transformation,[],[f14])).
% 2.64/1.03  
% 2.64/1.03  fof(f27,plain,(
% 2.64/1.03    ! [X0] : (! [X1] : (((v4_tops_1(X1,X0) | ~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) & ((r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) | ~v4_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.64/1.03    inference(flattening,[],[f26])).
% 2.64/1.03  
% 2.64/1.03  fof(f39,plain,(
% 2.64/1.03    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) | ~v4_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.64/1.03    inference(cnf_transformation,[],[f27])).
% 2.64/1.03  
% 2.64/1.03  fof(f8,axiom,(
% 2.64/1.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 2.64/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.64/1.03  
% 2.64/1.03  fof(f20,plain,(
% 2.64/1.03    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.64/1.03    inference(ennf_transformation,[],[f8])).
% 2.64/1.03  
% 2.64/1.03  fof(f21,plain,(
% 2.64/1.03    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.64/1.03    inference(flattening,[],[f20])).
% 2.64/1.03  
% 2.64/1.03  fof(f47,plain,(
% 2.64/1.03    ( ! [X2,X0,X1] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.64/1.03    inference(cnf_transformation,[],[f21])).
% 2.64/1.03  
% 2.64/1.03  fof(f41,plain,(
% 2.64/1.03    ( ! [X0,X1] : (v4_tops_1(X1,X0) | ~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.64/1.03    inference(cnf_transformation,[],[f27])).
% 2.64/1.03  
% 2.64/1.03  fof(f34,plain,(
% 2.64/1.03    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.64/1.03    inference(cnf_transformation,[],[f25])).
% 2.64/1.03  
% 2.64/1.03  fof(f60,plain,(
% 2.64/1.03    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.64/1.03    inference(equality_resolution,[],[f34])).
% 2.64/1.03  
% 2.64/1.03  fof(f6,axiom,(
% 2.64/1.03    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 2.64/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.64/1.03  
% 2.64/1.03  fof(f16,plain,(
% 2.64/1.03    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.64/1.03    inference(ennf_transformation,[],[f6])).
% 2.64/1.03  
% 2.64/1.03  fof(f17,plain,(
% 2.64/1.03    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.64/1.03    inference(flattening,[],[f16])).
% 2.64/1.03  
% 2.64/1.03  fof(f44,plain,(
% 2.64/1.03    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.64/1.03    inference(cnf_transformation,[],[f17])).
% 2.64/1.03  
% 2.64/1.03  fof(f48,plain,(
% 2.64/1.03    v2_pre_topc(sK0)),
% 2.64/1.03    inference(cnf_transformation,[],[f33])).
% 2.64/1.03  
% 2.64/1.03  fof(f57,plain,(
% 2.64/1.03    ~v4_tops_1(sK2,sK0) | ~v3_pre_topc(sK2,sK0) | v4_tops_1(sK3,sK1)),
% 2.64/1.03    inference(cnf_transformation,[],[f33])).
% 2.64/1.03  
% 2.64/1.03  fof(f58,plain,(
% 2.64/1.03    ~v4_tops_1(sK2,sK0) | ~v3_pre_topc(sK2,sK0) | ~v6_tops_1(sK3,sK1)),
% 2.64/1.03    inference(cnf_transformation,[],[f33])).
% 2.64/1.03  
% 2.64/1.03  fof(f56,plain,(
% 2.64/1.03    ~v4_tops_1(sK2,sK0) | ~v3_pre_topc(sK2,sK0) | v3_pre_topc(sK3,sK1)),
% 2.64/1.03    inference(cnf_transformation,[],[f33])).
% 2.64/1.03  
% 2.64/1.03  fof(f7,axiom,(
% 2.64/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 2.64/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.64/1.03  
% 2.64/1.03  fof(f18,plain,(
% 2.64/1.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.64/1.03    inference(ennf_transformation,[],[f7])).
% 2.64/1.03  
% 2.64/1.03  fof(f19,plain,(
% 2.64/1.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.64/1.03    inference(flattening,[],[f18])).
% 2.64/1.03  
% 2.64/1.03  fof(f45,plain,(
% 2.64/1.03    ( ! [X2,X0,X3,X1] : (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.64/1.03    inference(cnf_transformation,[],[f19])).
% 2.64/1.03  
% 2.64/1.03  fof(f46,plain,(
% 2.64/1.03    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.64/1.03    inference(cnf_transformation,[],[f19])).
% 2.64/1.03  
% 2.64/1.03  cnf(c_21,negated_conjecture,
% 2.64/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.64/1.03      inference(cnf_transformation,[],[f51]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_1400,plain,
% 2.64/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.64/1.03      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_9,plain,
% 2.64/1.03      ( ~ v6_tops_1(X0,X1)
% 2.64/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.64/1.03      | ~ l1_pre_topc(X1)
% 2.64/1.03      | k1_tops_1(X1,k2_pre_topc(X1,X0)) = X0 ),
% 2.64/1.03      inference(cnf_transformation,[],[f42]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_23,negated_conjecture,
% 2.64/1.03      ( l1_pre_topc(sK0) ),
% 2.64/1.03      inference(cnf_transformation,[],[f49]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_527,plain,
% 2.64/1.03      ( ~ v6_tops_1(X0,X1)
% 2.64/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.64/1.03      | k1_tops_1(X1,k2_pre_topc(X1,X0)) = X0
% 2.64/1.03      | sK0 != X1 ),
% 2.64/1.03      inference(resolution_lifted,[status(thm)],[c_9,c_23]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_528,plain,
% 2.64/1.03      ( ~ v6_tops_1(X0,sK0)
% 2.64/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.64/1.03      | k1_tops_1(sK0,k2_pre_topc(sK0,X0)) = X0 ),
% 2.64/1.03      inference(unflattening,[status(thm)],[c_527]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_1383,plain,
% 2.64/1.03      ( k1_tops_1(sK0,k2_pre_topc(sK0,X0)) = X0
% 2.64/1.03      | v6_tops_1(X0,sK0) != iProver_top
% 2.64/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.64/1.03      inference(predicate_to_equality,[status(thm)],[c_528]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_2434,plain,
% 2.64/1.03      ( k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = sK2
% 2.64/1.03      | v6_tops_1(sK2,sK0) != iProver_top ),
% 2.64/1.03      inference(superposition,[status(thm)],[c_1400,c_1383]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_28,plain,
% 2.64/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.64/1.03      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_20,negated_conjecture,
% 2.64/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.64/1.03      inference(cnf_transformation,[],[f52]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_29,plain,
% 2.64/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.64/1.03      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_19,negated_conjecture,
% 2.64/1.03      ( v3_pre_topc(sK3,sK1) | v6_tops_1(sK2,sK0) ),
% 2.64/1.03      inference(cnf_transformation,[],[f53]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_30,plain,
% 2.64/1.03      ( v3_pre_topc(sK3,sK1) = iProver_top | v6_tops_1(sK2,sK0) = iProver_top ),
% 2.64/1.03      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_18,negated_conjecture,
% 2.64/1.03      ( v6_tops_1(sK2,sK0) | v4_tops_1(sK3,sK1) ),
% 2.64/1.03      inference(cnf_transformation,[],[f54]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_31,plain,
% 2.64/1.03      ( v6_tops_1(sK2,sK0) = iProver_top | v4_tops_1(sK3,sK1) = iProver_top ),
% 2.64/1.03      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_17,negated_conjecture,
% 2.64/1.03      ( ~ v6_tops_1(sK3,sK1) | v6_tops_1(sK2,sK0) ),
% 2.64/1.03      inference(cnf_transformation,[],[f55]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_32,plain,
% 2.64/1.03      ( v6_tops_1(sK3,sK1) != iProver_top | v6_tops_1(sK2,sK0) = iProver_top ),
% 2.64/1.03      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_3,plain,
% 2.64/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.64/1.03      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.64/1.03      | ~ l1_pre_topc(X1) ),
% 2.64/1.03      inference(cnf_transformation,[],[f37]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_22,negated_conjecture,
% 2.64/1.03      ( l1_pre_topc(sK1) ),
% 2.64/1.03      inference(cnf_transformation,[],[f50]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_476,plain,
% 2.64/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.64/1.03      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.64/1.03      | sK1 != X1 ),
% 2.64/1.03      inference(resolution_lifted,[status(thm)],[c_3,c_22]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_477,plain,
% 2.64/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.64/1.03      | m1_subset_1(k2_pre_topc(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.64/1.03      inference(unflattening,[status(thm)],[c_476]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_1687,plain,
% 2.64/1.03      ( m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.64/1.03      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.64/1.03      inference(instantiation,[status(thm)],[c_477]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_1688,plain,
% 2.64/1.03      ( m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 2.64/1.03      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.64/1.03      inference(predicate_to_equality,[status(thm)],[c_1687]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_4,plain,
% 2.64/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.64/1.03      | r1_tarski(X0,k2_pre_topc(X1,X0))
% 2.64/1.03      | ~ l1_pre_topc(X1) ),
% 2.64/1.03      inference(cnf_transformation,[],[f38]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_464,plain,
% 2.64/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.64/1.03      | r1_tarski(X0,k2_pre_topc(X1,X0))
% 2.64/1.03      | sK1 != X1 ),
% 2.64/1.03      inference(resolution_lifted,[status(thm)],[c_4,c_22]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_465,plain,
% 2.64/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.64/1.03      | r1_tarski(X0,k2_pre_topc(sK1,X0)) ),
% 2.64/1.03      inference(unflattening,[status(thm)],[c_464]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_1693,plain,
% 2.64/1.03      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.64/1.03      | r1_tarski(sK3,k2_pre_topc(sK1,sK3)) ),
% 2.64/1.03      inference(instantiation,[status(thm)],[c_465]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_1694,plain,
% 2.64/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.64/1.03      | r1_tarski(sK3,k2_pre_topc(sK1,sK3)) = iProver_top ),
% 2.64/1.03      inference(predicate_to_equality,[status(thm)],[c_1693]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_8,plain,
% 2.64/1.03      ( v6_tops_1(X0,X1)
% 2.64/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.64/1.03      | ~ l1_pre_topc(X1)
% 2.64/1.03      | k1_tops_1(X1,k2_pre_topc(X1,X0)) != X0 ),
% 2.64/1.03      inference(cnf_transformation,[],[f43]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_401,plain,
% 2.64/1.03      ( v6_tops_1(X0,X1)
% 2.64/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.64/1.03      | k1_tops_1(X1,k2_pre_topc(X1,X0)) != X0
% 2.64/1.03      | sK1 != X1 ),
% 2.64/1.03      inference(resolution_lifted,[status(thm)],[c_8,c_22]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_402,plain,
% 2.64/1.03      ( v6_tops_1(X0,sK1)
% 2.64/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.64/1.03      | k1_tops_1(sK1,k2_pre_topc(sK1,X0)) != X0 ),
% 2.64/1.03      inference(unflattening,[status(thm)],[c_401]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_1699,plain,
% 2.64/1.03      ( v6_tops_1(sK3,sK1)
% 2.64/1.03      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.64/1.03      | k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) != sK3 ),
% 2.64/1.03      inference(instantiation,[status(thm)],[c_402]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_1700,plain,
% 2.64/1.03      ( k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) != sK3
% 2.64/1.03      | v6_tops_1(sK3,sK1) = iProver_top
% 2.64/1.03      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.64/1.03      inference(predicate_to_equality,[status(thm)],[c_1699]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_1702,plain,
% 2.64/1.03      ( ~ v6_tops_1(sK2,sK0)
% 2.64/1.03      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.64/1.03      | k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = sK2 ),
% 2.64/1.03      inference(instantiation,[status(thm)],[c_528]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_1703,plain,
% 2.64/1.03      ( k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = sK2
% 2.64/1.03      | v6_tops_1(sK2,sK0) != iProver_top
% 2.64/1.03      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.64/1.03      inference(predicate_to_equality,[status(thm)],[c_1702]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_0,plain,
% 2.64/1.03      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.64/1.03      inference(cnf_transformation,[],[f36]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_1819,plain,
% 2.64/1.03      ( ~ r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3)
% 2.64/1.03      | ~ r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))
% 2.64/1.03      | k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) = sK3 ),
% 2.64/1.03      inference(instantiation,[status(thm)],[c_0]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_1820,plain,
% 2.64/1.03      ( k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) = sK3
% 2.64/1.03      | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3) != iProver_top
% 2.64/1.03      | r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) != iProver_top ),
% 2.64/1.03      inference(predicate_to_equality,[status(thm)],[c_1819]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_7,plain,
% 2.64/1.03      ( ~ v4_tops_1(X0,X1)
% 2.64/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.64/1.03      | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
% 2.64/1.03      | ~ l1_pre_topc(X1) ),
% 2.64/1.03      inference(cnf_transformation,[],[f39]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_416,plain,
% 2.64/1.03      ( ~ v4_tops_1(X0,X1)
% 2.64/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.64/1.03      | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
% 2.64/1.03      | sK1 != X1 ),
% 2.64/1.03      inference(resolution_lifted,[status(thm)],[c_7,c_22]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_417,plain,
% 2.64/1.03      ( ~ v4_tops_1(X0,sK1)
% 2.64/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.64/1.03      | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,X0)),X0) ),
% 2.64/1.03      inference(unflattening,[status(thm)],[c_416]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_1830,plain,
% 2.64/1.03      ( ~ v4_tops_1(sK3,sK1)
% 2.64/1.03      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.64/1.03      | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3) ),
% 2.64/1.03      inference(instantiation,[status(thm)],[c_417]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_1831,plain,
% 2.64/1.03      ( v4_tops_1(sK3,sK1) != iProver_top
% 2.64/1.03      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.64/1.03      | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3) = iProver_top ),
% 2.64/1.03      inference(predicate_to_equality,[status(thm)],[c_1830]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_13,plain,
% 2.64/1.03      ( ~ v3_pre_topc(X0,X1)
% 2.64/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.64/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.64/1.03      | ~ r1_tarski(X0,X2)
% 2.64/1.03      | r1_tarski(X0,k1_tops_1(X1,X2))
% 2.64/1.03      | ~ l1_pre_topc(X1) ),
% 2.64/1.03      inference(cnf_transformation,[],[f47]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_365,plain,
% 2.64/1.03      ( ~ v3_pre_topc(X0,X1)
% 2.64/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.64/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.64/1.03      | ~ r1_tarski(X0,X2)
% 2.64/1.03      | r1_tarski(X0,k1_tops_1(X1,X2))
% 2.64/1.03      | sK1 != X1 ),
% 2.64/1.03      inference(resolution_lifted,[status(thm)],[c_13,c_22]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_366,plain,
% 2.64/1.03      ( ~ v3_pre_topc(X0,sK1)
% 2.64/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.64/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.64/1.03      | ~ r1_tarski(X0,X1)
% 2.64/1.03      | r1_tarski(X0,k1_tops_1(sK1,X1)) ),
% 2.64/1.03      inference(unflattening,[status(thm)],[c_365]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_1840,plain,
% 2.64/1.03      ( ~ v3_pre_topc(sK3,sK1)
% 2.64/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.64/1.03      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.64/1.03      | ~ r1_tarski(sK3,X0)
% 2.64/1.03      | r1_tarski(sK3,k1_tops_1(sK1,X0)) ),
% 2.64/1.03      inference(instantiation,[status(thm)],[c_366]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_1934,plain,
% 2.64/1.03      ( ~ v3_pre_topc(sK3,sK1)
% 2.64/1.03      | ~ m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.64/1.03      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.64/1.03      | r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))
% 2.64/1.03      | ~ r1_tarski(sK3,k2_pre_topc(sK1,sK3)) ),
% 2.64/1.03      inference(instantiation,[status(thm)],[c_1840]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_1935,plain,
% 2.64/1.03      ( v3_pre_topc(sK3,sK1) != iProver_top
% 2.64/1.03      | m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.64/1.03      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.64/1.03      | r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) = iProver_top
% 2.64/1.03      | r1_tarski(sK3,k2_pre_topc(sK1,sK3)) != iProver_top ),
% 2.64/1.03      inference(predicate_to_equality,[status(thm)],[c_1934]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_2542,plain,
% 2.64/1.03      ( k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = sK2 ),
% 2.64/1.03      inference(global_propositional_subsumption,
% 2.64/1.03                [status(thm)],
% 2.64/1.03                [c_2434,c_28,c_29,c_30,c_31,c_32,c_1688,c_1694,c_1700,c_1703,
% 2.64/1.03                 c_1820,c_1831,c_1935]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_5,plain,
% 2.64/1.03      ( v4_tops_1(X0,X1)
% 2.64/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.64/1.03      | ~ r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
% 2.64/1.03      | ~ r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
% 2.64/1.03      | ~ l1_pre_topc(X1) ),
% 2.64/1.03      inference(cnf_transformation,[],[f41]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_587,plain,
% 2.64/1.03      ( v4_tops_1(X0,X1)
% 2.64/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.64/1.03      | ~ r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
% 2.64/1.03      | ~ r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
% 2.64/1.03      | sK0 != X1 ),
% 2.64/1.03      inference(resolution_lifted,[status(thm)],[c_5,c_23]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_588,plain,
% 2.64/1.03      ( v4_tops_1(X0,sK0)
% 2.64/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.64/1.03      | ~ r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,X0)))
% 2.64/1.03      | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X0) ),
% 2.64/1.03      inference(unflattening,[status(thm)],[c_587]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_1379,plain,
% 2.64/1.03      ( v4_tops_1(X0,sK0) = iProver_top
% 2.64/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.64/1.03      | r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,X0))) != iProver_top
% 2.64/1.03      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X0) != iProver_top ),
% 2.64/1.03      inference(predicate_to_equality,[status(thm)],[c_588]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_2808,plain,
% 2.64/1.03      ( v4_tops_1(sK2,sK0) = iProver_top
% 2.64/1.03      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.64/1.03      | r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) != iProver_top
% 2.64/1.03      | r1_tarski(sK2,sK2) != iProver_top ),
% 2.64/1.03      inference(superposition,[status(thm)],[c_2542,c_1379]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_1721,plain,
% 2.64/1.03      ( v4_tops_1(sK2,sK0)
% 2.64/1.03      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.64/1.03      | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK2)
% 2.64/1.03      | ~ r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) ),
% 2.64/1.03      inference(instantiation,[status(thm)],[c_588]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_1722,plain,
% 2.64/1.03      ( v4_tops_1(sK2,sK0) = iProver_top
% 2.64/1.03      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.64/1.03      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK2) != iProver_top
% 2.64/1.03      | r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) != iProver_top ),
% 2.64/1.03      inference(predicate_to_equality,[status(thm)],[c_1721]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_761,plain,( X0 = X0 ),theory(equality) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_1943,plain,
% 2.64/1.03      ( sK2 = sK2 ),
% 2.64/1.03      inference(instantiation,[status(thm)],[c_761]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_763,plain,
% 2.64/1.03      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.64/1.03      theory(equality) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_1858,plain,
% 2.64/1.03      ( ~ r1_tarski(X0,X1)
% 2.64/1.03      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK2)
% 2.64/1.03      | k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) != X0
% 2.64/1.03      | sK2 != X1 ),
% 2.64/1.03      inference(instantiation,[status(thm)],[c_763]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_2224,plain,
% 2.64/1.03      ( ~ r1_tarski(X0,sK2)
% 2.64/1.03      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK2)
% 2.64/1.03      | k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) != X0
% 2.64/1.03      | sK2 != sK2 ),
% 2.64/1.03      inference(instantiation,[status(thm)],[c_1858]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_2757,plain,
% 2.64/1.03      ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK2)
% 2.64/1.03      | ~ r1_tarski(sK2,sK2)
% 2.64/1.03      | k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) != sK2
% 2.64/1.03      | sK2 != sK2 ),
% 2.64/1.03      inference(instantiation,[status(thm)],[c_2224]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_2759,plain,
% 2.64/1.03      ( k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) != sK2
% 2.64/1.03      | sK2 != sK2
% 2.64/1.03      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK2) = iProver_top
% 2.64/1.03      | r1_tarski(sK2,sK2) != iProver_top ),
% 2.64/1.03      inference(predicate_to_equality,[status(thm)],[c_2757]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_2,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f60]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_2758,plain,
% 2.64/1.03      ( r1_tarski(sK2,sK2) ),
% 2.64/1.03      inference(instantiation,[status(thm)],[c_2]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_2761,plain,
% 2.64/1.03      ( r1_tarski(sK2,sK2) = iProver_top ),
% 2.64/1.03      inference(predicate_to_equality,[status(thm)],[c_2758]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_617,plain,
% 2.64/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.64/1.03      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.64/1.03      | sK0 != X1 ),
% 2.64/1.03      inference(resolution_lifted,[status(thm)],[c_3,c_23]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_618,plain,
% 2.64/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.64/1.03      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.64/1.03      inference(unflattening,[status(thm)],[c_617]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_1377,plain,
% 2.64/1.03      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.64/1.03      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.64/1.03      inference(predicate_to_equality,[status(thm)],[c_618]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_10,plain,
% 2.64/1.03      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 2.64/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.64/1.03      | ~ v2_pre_topc(X0)
% 2.64/1.03      | ~ l1_pre_topc(X0) ),
% 2.64/1.03      inference(cnf_transformation,[],[f44]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_24,negated_conjecture,
% 2.64/1.03      ( v2_pre_topc(sK0) ),
% 2.64/1.03      inference(cnf_transformation,[],[f48]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_264,plain,
% 2.64/1.03      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 2.64/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.64/1.03      | ~ l1_pre_topc(X0)
% 2.64/1.03      | sK0 != X0 ),
% 2.64/1.03      inference(resolution_lifted,[status(thm)],[c_10,c_24]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_265,plain,
% 2.64/1.03      ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
% 2.64/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.64/1.03      | ~ l1_pre_topc(sK0) ),
% 2.64/1.03      inference(unflattening,[status(thm)],[c_264]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_269,plain,
% 2.64/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.64/1.03      | v3_pre_topc(k1_tops_1(sK0,X0),sK0) ),
% 2.64/1.03      inference(global_propositional_subsumption,[status(thm)],[c_265,c_23]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_270,plain,
% 2.64/1.03      ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
% 2.64/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.64/1.03      inference(renaming,[status(thm)],[c_269]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_1399,plain,
% 2.64/1.03      ( v3_pre_topc(k1_tops_1(sK0,X0),sK0) = iProver_top
% 2.64/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.64/1.03      inference(predicate_to_equality,[status(thm)],[c_270]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_2245,plain,
% 2.64/1.03      ( v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),sK0) = iProver_top
% 2.64/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.64/1.03      inference(superposition,[status(thm)],[c_1377,c_1399]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_3873,plain,
% 2.64/1.03      ( v3_pre_topc(sK2,sK0) = iProver_top
% 2.64/1.03      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.64/1.03      inference(superposition,[status(thm)],[c_2542,c_2245]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_3876,plain,
% 2.64/1.03      ( v3_pre_topc(sK2,sK0) = iProver_top ),
% 2.64/1.03      inference(global_propositional_subsumption,[status(thm)],[c_3873,c_28]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_15,negated_conjecture,
% 2.64/1.03      ( ~ v3_pre_topc(sK2,sK0) | v4_tops_1(sK3,sK1) | ~ v4_tops_1(sK2,sK0) ),
% 2.64/1.03      inference(cnf_transformation,[],[f57]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_1406,plain,
% 2.64/1.03      ( v3_pre_topc(sK2,sK0) != iProver_top
% 2.64/1.03      | v4_tops_1(sK3,sK1) = iProver_top
% 2.64/1.03      | v4_tops_1(sK2,sK0) != iProver_top ),
% 2.64/1.03      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_3882,plain,
% 2.64/1.03      ( v4_tops_1(sK3,sK1) = iProver_top | v4_tops_1(sK2,sK0) != iProver_top ),
% 2.64/1.03      inference(superposition,[status(thm)],[c_3876,c_1406]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_14,negated_conjecture,
% 2.64/1.03      ( ~ v3_pre_topc(sK2,sK0) | ~ v6_tops_1(sK3,sK1) | ~ v4_tops_1(sK2,sK0) ),
% 2.64/1.03      inference(cnf_transformation,[],[f58]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_35,plain,
% 2.64/1.03      ( v3_pre_topc(sK2,sK0) != iProver_top
% 2.64/1.03      | v6_tops_1(sK3,sK1) != iProver_top
% 2.64/1.03      | v4_tops_1(sK2,sK0) != iProver_top ),
% 2.64/1.03      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_16,negated_conjecture,
% 2.64/1.03      ( v3_pre_topc(sK3,sK1) | ~ v3_pre_topc(sK2,sK0) | ~ v4_tops_1(sK2,sK0) ),
% 2.64/1.03      inference(cnf_transformation,[],[f56]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_1405,plain,
% 2.64/1.03      ( v3_pre_topc(sK3,sK1) = iProver_top
% 2.64/1.03      | v3_pre_topc(sK2,sK0) != iProver_top
% 2.64/1.03      | v4_tops_1(sK2,sK0) != iProver_top ),
% 2.64/1.03      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_3883,plain,
% 2.64/1.03      ( v3_pre_topc(sK3,sK1) = iProver_top
% 2.64/1.03      | v4_tops_1(sK2,sK0) != iProver_top ),
% 2.64/1.03      inference(superposition,[status(thm)],[c_3876,c_1405]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_3910,plain,
% 2.64/1.03      ( v4_tops_1(sK2,sK0) != iProver_top ),
% 2.64/1.03      inference(global_propositional_subsumption,
% 2.64/1.03                [status(thm)],
% 2.64/1.03                [c_3882,c_28,c_29,c_35,c_1688,c_1694,c_1700,c_1820,c_1831,
% 2.64/1.03                 c_1935,c_3873,c_3883]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_4251,plain,
% 2.64/1.03      ( r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) != iProver_top ),
% 2.64/1.03      inference(global_propositional_subsumption,
% 2.64/1.03                [status(thm)],
% 2.64/1.03                [c_2808,c_28,c_29,c_30,c_31,c_32,c_35,c_1688,c_1694,c_1700,
% 2.64/1.03                 c_1703,c_1722,c_1820,c_1831,c_1935,c_1943,c_2759,c_2761,
% 2.64/1.03                 c_3873,c_3882,c_3883]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_12,plain,
% 2.64/1.03      ( ~ v3_pre_topc(X0,X1)
% 2.64/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.64/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 2.64/1.03      | ~ v2_pre_topc(X3)
% 2.64/1.03      | ~ l1_pre_topc(X3)
% 2.64/1.03      | ~ l1_pre_topc(X1)
% 2.64/1.03      | k1_tops_1(X1,X0) = X0 ),
% 2.64/1.03      inference(cnf_transformation,[],[f45]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_307,plain,
% 2.64/1.03      ( ~ v3_pre_topc(X0,X1)
% 2.64/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.64/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 2.64/1.03      | ~ l1_pre_topc(X1)
% 2.64/1.03      | ~ l1_pre_topc(X3)
% 2.64/1.03      | k1_tops_1(X1,X0) = X0
% 2.64/1.03      | sK0 != X3 ),
% 2.64/1.03      inference(resolution_lifted,[status(thm)],[c_12,c_24]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_308,plain,
% 2.64/1.03      ( ~ v3_pre_topc(X0,X1)
% 2.64/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.64/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.64/1.03      | ~ l1_pre_topc(X1)
% 2.64/1.03      | ~ l1_pre_topc(sK0)
% 2.64/1.03      | k1_tops_1(X1,X0) = X0 ),
% 2.64/1.03      inference(unflattening,[status(thm)],[c_307]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_312,plain,
% 2.64/1.03      ( ~ l1_pre_topc(X1)
% 2.64/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.64/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.64/1.03      | ~ v3_pre_topc(X0,X1)
% 2.64/1.03      | k1_tops_1(X1,X0) = X0 ),
% 2.64/1.03      inference(global_propositional_subsumption,[status(thm)],[c_308,c_23]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_313,plain,
% 2.64/1.03      ( ~ v3_pre_topc(X0,X1)
% 2.64/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.64/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.64/1.03      | ~ l1_pre_topc(X1)
% 2.64/1.03      | k1_tops_1(X1,X0) = X0 ),
% 2.64/1.03      inference(renaming,[status(thm)],[c_312]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_488,plain,
% 2.64/1.03      ( ~ v3_pre_topc(X0,X1)
% 2.64/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.64/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.64/1.03      | k1_tops_1(X1,X0) = X0
% 2.64/1.03      | sK0 != X1 ),
% 2.64/1.03      inference(resolution_lifted,[status(thm)],[c_313,c_23]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_489,plain,
% 2.64/1.03      ( ~ v3_pre_topc(X0,sK0)
% 2.64/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.64/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.64/1.03      | k1_tops_1(sK0,X0) = X0 ),
% 2.64/1.03      inference(unflattening,[status(thm)],[c_488]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_756,plain,
% 2.64/1.03      ( ~ v3_pre_topc(X0,sK0)
% 2.64/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.64/1.03      | k1_tops_1(sK0,X0) = X0
% 2.64/1.03      | ~ sP3_iProver_split ),
% 2.64/1.03      inference(splitting,
% 2.64/1.03                [splitting(split),new_symbols(definition,[sP3_iProver_split])],
% 2.64/1.03                [c_489]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_1386,plain,
% 2.64/1.03      ( k1_tops_1(sK0,X0) = X0
% 2.64/1.03      | v3_pre_topc(X0,sK0) != iProver_top
% 2.64/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.64/1.03      | sP3_iProver_split != iProver_top ),
% 2.64/1.03      inference(predicate_to_equality,[status(thm)],[c_756]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_757,plain,
% 2.64/1.03      ( sP3_iProver_split | sP0_iProver_split ),
% 2.64/1.03      inference(splitting,
% 2.64/1.03                [splitting(split),new_symbols(definition,[])],
% 2.64/1.03                [c_489]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_801,plain,
% 2.64/1.03      ( sP3_iProver_split = iProver_top | sP0_iProver_split = iProver_top ),
% 2.64/1.03      inference(predicate_to_equality,[status(thm)],[c_757]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_802,plain,
% 2.64/1.03      ( k1_tops_1(sK0,X0) = X0
% 2.64/1.03      | v3_pre_topc(X0,sK0) != iProver_top
% 2.64/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.64/1.03      | sP3_iProver_split != iProver_top ),
% 2.64/1.03      inference(predicate_to_equality,[status(thm)],[c_756]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_11,plain,
% 2.64/1.03      ( v3_pre_topc(X0,X1)
% 2.64/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 2.64/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.64/1.03      | ~ v2_pre_topc(X1)
% 2.64/1.03      | ~ l1_pre_topc(X1)
% 2.64/1.03      | ~ l1_pre_topc(X3)
% 2.64/1.03      | k1_tops_1(X1,X0) != X0 ),
% 2.64/1.03      inference(cnf_transformation,[],[f46]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_282,plain,
% 2.64/1.03      ( v3_pre_topc(X0,X1)
% 2.64/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.64/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 2.64/1.03      | ~ l1_pre_topc(X1)
% 2.64/1.03      | ~ l1_pre_topc(X3)
% 2.64/1.03      | k1_tops_1(X1,X0) != X0
% 2.64/1.03      | sK0 != X1 ),
% 2.64/1.03      inference(resolution_lifted,[status(thm)],[c_11,c_24]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_283,plain,
% 2.64/1.03      ( v3_pre_topc(X0,sK0)
% 2.64/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.64/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.64/1.03      | ~ l1_pre_topc(X2)
% 2.64/1.03      | ~ l1_pre_topc(sK0)
% 2.64/1.03      | k1_tops_1(sK0,X0) != X0 ),
% 2.64/1.03      inference(unflattening,[status(thm)],[c_282]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_287,plain,
% 2.64/1.03      ( ~ l1_pre_topc(X2)
% 2.64/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.64/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.64/1.03      | v3_pre_topc(X0,sK0)
% 2.64/1.03      | k1_tops_1(sK0,X0) != X0 ),
% 2.64/1.03      inference(global_propositional_subsumption,[status(thm)],[c_283,c_23]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_288,plain,
% 2.64/1.03      ( v3_pre_topc(X0,sK0)
% 2.64/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.64/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.64/1.03      | ~ l1_pre_topc(X2)
% 2.64/1.03      | k1_tops_1(sK0,X0) != X0 ),
% 2.64/1.03      inference(renaming,[status(thm)],[c_287]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_647,plain,
% 2.64/1.03      ( v3_pre_topc(X0,sK0)
% 2.64/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.64/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.64/1.03      | k1_tops_1(sK0,X0) != X0
% 2.64/1.03      | sK0 != X2 ),
% 2.64/1.03      inference(resolution_lifted,[status(thm)],[c_23,c_288]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_648,plain,
% 2.64/1.03      ( v3_pre_topc(X0,sK0)
% 2.64/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.64/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.64/1.03      | k1_tops_1(sK0,X0) != X0 ),
% 2.64/1.03      inference(unflattening,[status(thm)],[c_647]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_751,plain,
% 2.64/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~ sP0_iProver_split ),
% 2.64/1.03      inference(splitting,
% 2.64/1.03                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.64/1.03                [c_648]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_1677,plain,
% 2.64/1.03      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.64/1.03      | ~ sP0_iProver_split ),
% 2.64/1.03      inference(instantiation,[status(thm)],[c_751]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_1678,plain,
% 2.64/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.64/1.03      | sP0_iProver_split != iProver_top ),
% 2.64/1.03      inference(predicate_to_equality,[status(thm)],[c_1677]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_3070,plain,
% 2.64/1.03      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.64/1.03      | v3_pre_topc(X0,sK0) != iProver_top
% 2.64/1.03      | k1_tops_1(sK0,X0) = X0 ),
% 2.64/1.03      inference(global_propositional_subsumption,
% 2.64/1.03                [status(thm)],
% 2.64/1.03                [c_1386,c_28,c_801,c_802,c_1678]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_3071,plain,
% 2.64/1.03      ( k1_tops_1(sK0,X0) = X0
% 2.64/1.03      | v3_pre_topc(X0,sK0) != iProver_top
% 2.64/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.64/1.03      inference(renaming,[status(thm)],[c_3070]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_3077,plain,
% 2.64/1.03      ( k1_tops_1(sK0,sK2) = sK2 | v3_pre_topc(sK2,sK0) != iProver_top ),
% 2.64/1.03      inference(superposition,[status(thm)],[c_1400,c_3071]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_3881,plain,
% 2.64/1.03      ( k1_tops_1(sK0,sK2) = sK2 ),
% 2.64/1.03      inference(superposition,[status(thm)],[c_3876,c_3077]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_4255,plain,
% 2.64/1.03      ( r1_tarski(sK2,k2_pre_topc(sK0,sK2)) != iProver_top ),
% 2.64/1.03      inference(light_normalisation,[status(thm)],[c_4251,c_3881]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_605,plain,
% 2.64/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.64/1.03      | r1_tarski(X0,k2_pre_topc(X1,X0))
% 2.64/1.03      | sK0 != X1 ),
% 2.64/1.03      inference(resolution_lifted,[status(thm)],[c_4,c_23]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_606,plain,
% 2.64/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.64/1.03      | r1_tarski(X0,k2_pre_topc(sK0,X0)) ),
% 2.64/1.03      inference(unflattening,[status(thm)],[c_605]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_1378,plain,
% 2.64/1.03      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.64/1.03      | r1_tarski(X0,k2_pre_topc(sK0,X0)) = iProver_top ),
% 2.64/1.03      inference(predicate_to_equality,[status(thm)],[c_606]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_1885,plain,
% 2.64/1.03      ( r1_tarski(sK2,k2_pre_topc(sK0,sK2)) = iProver_top ),
% 2.64/1.03      inference(superposition,[status(thm)],[c_1400,c_1378]) ).
% 2.64/1.03  
% 2.64/1.03  cnf(c_4257,plain,
% 2.64/1.03      ( $false ),
% 2.64/1.03      inference(forward_subsumption_resolution,[status(thm)],[c_4255,c_1885]) ).
% 2.64/1.03  
% 2.64/1.03  
% 2.64/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 2.64/1.03  
% 2.64/1.03  ------                               Statistics
% 2.64/1.03  
% 2.64/1.03  ------ General
% 2.64/1.03  
% 2.64/1.03  abstr_ref_over_cycles:                  0
% 2.64/1.03  abstr_ref_under_cycles:                 0
% 2.64/1.03  gc_basic_clause_elim:                   0
% 2.64/1.03  forced_gc_time:                         0
% 2.64/1.03  parsing_time:                           0.01
% 2.64/1.03  unif_index_cands_time:                  0.
% 2.64/1.03  unif_index_add_time:                    0.
% 2.64/1.03  orderings_time:                         0.
% 2.64/1.03  out_proof_time:                         0.019
% 2.64/1.03  total_time:                             0.177
% 2.64/1.03  num_of_symbols:                         51
% 2.64/1.03  num_of_terms:                           2970
% 2.64/1.03  
% 2.64/1.03  ------ Preprocessing
% 2.64/1.03  
% 2.64/1.03  num_of_splits:                          8
% 2.64/1.03  num_of_split_atoms:                     5
% 2.64/1.03  num_of_reused_defs:                     3
% 2.64/1.03  num_eq_ax_congr_red:                    2
% 2.64/1.03  num_of_sem_filtered_clauses:            5
% 2.64/1.03  num_of_subtypes:                        0
% 2.64/1.03  monotx_restored_types:                  0
% 2.64/1.03  sat_num_of_epr_types:                   0
% 2.64/1.03  sat_num_of_non_cyclic_types:            0
% 2.64/1.03  sat_guarded_non_collapsed_types:        0
% 2.64/1.03  num_pure_diseq_elim:                    0
% 2.64/1.03  simp_replaced_by:                       0
% 2.64/1.03  res_preprocessed:                       115
% 2.64/1.03  prep_upred:                             0
% 2.64/1.03  prep_unflattend:                        23
% 2.64/1.03  smt_new_axioms:                         0
% 2.64/1.03  pred_elim_cands:                        7
% 2.64/1.03  pred_elim:                              2
% 2.64/1.03  pred_elim_cl:                           -7
% 2.64/1.03  pred_elim_cycles:                       3
% 2.64/1.03  merged_defs:                            0
% 2.64/1.03  merged_defs_ncl:                        0
% 2.64/1.03  bin_hyper_res:                          0
% 2.64/1.03  prep_cycles:                            3
% 2.64/1.03  pred_elim_time:                         0.012
% 2.64/1.03  splitting_time:                         0.
% 2.64/1.03  sem_filter_time:                        0.
% 2.64/1.03  monotx_time:                            0.001
% 2.64/1.03  subtype_inf_time:                       0.
% 2.64/1.03  
% 2.64/1.03  ------ Problem properties
% 2.64/1.03  
% 2.64/1.03  clauses:                                39
% 2.64/1.03  conjectures:                            8
% 2.64/1.03  epr:                                    12
% 2.64/1.03  horn:                                   33
% 2.64/1.03  ground:                                 12
% 2.64/1.03  unary:                                  3
% 2.64/1.03  binary:                                 16
% 2.64/1.03  lits:                                   105
% 2.64/1.03  lits_eq:                                9
% 2.64/1.03  fd_pure:                                0
% 2.64/1.03  fd_pseudo:                              0
% 2.64/1.03  fd_cond:                                0
% 2.64/1.03  fd_pseudo_cond:                         1
% 2.64/1.03  ac_symbols:                             0
% 2.64/1.03  
% 2.64/1.03  ------ Propositional Solver
% 2.64/1.03  
% 2.64/1.03  prop_solver_calls:                      24
% 2.64/1.03  prop_fast_solver_calls:                 978
% 2.64/1.03  smt_solver_calls:                       0
% 2.64/1.03  smt_fast_solver_calls:                  0
% 2.64/1.03  prop_num_of_clauses:                    1489
% 2.64/1.03  prop_preprocess_simplified:             5018
% 2.64/1.03  prop_fo_subsumed:                       26
% 2.64/1.03  prop_solver_time:                       0.
% 2.64/1.03  smt_solver_time:                        0.
% 2.64/1.03  smt_fast_solver_time:                   0.
% 2.64/1.03  prop_fast_solver_time:                  0.
% 2.64/1.03  prop_unsat_core_time:                   0.
% 2.64/1.03  
% 2.64/1.03  ------ QBF
% 2.64/1.03  
% 2.64/1.03  qbf_q_res:                              0
% 2.64/1.03  qbf_num_tautologies:                    0
% 2.64/1.03  qbf_prep_cycles:                        0
% 2.64/1.03  
% 2.64/1.03  ------ BMC1
% 2.64/1.03  
% 2.64/1.03  bmc1_current_bound:                     -1
% 2.64/1.03  bmc1_last_solved_bound:                 -1
% 2.64/1.03  bmc1_unsat_core_size:                   -1
% 2.64/1.03  bmc1_unsat_core_parents_size:           -1
% 2.64/1.03  bmc1_merge_next_fun:                    0
% 2.64/1.03  bmc1_unsat_core_clauses_time:           0.
% 2.64/1.03  
% 2.64/1.03  ------ Instantiation
% 2.64/1.03  
% 2.64/1.03  inst_num_of_clauses:                    477
% 2.64/1.03  inst_num_in_passive:                    69
% 2.64/1.03  inst_num_in_active:                     306
% 2.64/1.03  inst_num_in_unprocessed:                103
% 2.64/1.03  inst_num_of_loops:                      340
% 2.64/1.03  inst_num_of_learning_restarts:          0
% 2.64/1.03  inst_num_moves_active_passive:          31
% 2.64/1.03  inst_lit_activity:                      0
% 2.64/1.03  inst_lit_activity_moves:                0
% 2.64/1.03  inst_num_tautologies:                   0
% 2.64/1.03  inst_num_prop_implied:                  0
% 2.64/1.03  inst_num_existing_simplified:           0
% 2.64/1.03  inst_num_eq_res_simplified:             0
% 2.64/1.03  inst_num_child_elim:                    0
% 2.64/1.03  inst_num_of_dismatching_blockings:      58
% 2.64/1.03  inst_num_of_non_proper_insts:           454
% 2.64/1.03  inst_num_of_duplicates:                 0
% 2.64/1.03  inst_inst_num_from_inst_to_res:         0
% 2.64/1.03  inst_dismatching_checking_time:         0.
% 2.64/1.03  
% 2.64/1.03  ------ Resolution
% 2.64/1.03  
% 2.64/1.03  res_num_of_clauses:                     0
% 2.64/1.03  res_num_in_passive:                     0
% 2.64/1.03  res_num_in_active:                      0
% 2.64/1.03  res_num_of_loops:                       118
% 2.64/1.03  res_forward_subset_subsumed:            31
% 2.64/1.03  res_backward_subset_subsumed:           2
% 2.64/1.03  res_forward_subsumed:                   0
% 2.64/1.03  res_backward_subsumed:                  0
% 2.64/1.03  res_forward_subsumption_resolution:     0
% 2.64/1.03  res_backward_subsumption_resolution:    0
% 2.64/1.03  res_clause_to_clause_subsumption:       284
% 2.64/1.03  res_orphan_elimination:                 0
% 2.64/1.03  res_tautology_del:                      37
% 2.64/1.03  res_num_eq_res_simplified:              0
% 2.64/1.03  res_num_sel_changes:                    0
% 2.64/1.03  res_moves_from_active_to_pass:          0
% 2.64/1.03  
% 2.64/1.03  ------ Superposition
% 2.64/1.03  
% 2.64/1.03  sup_time_total:                         0.
% 2.64/1.03  sup_time_generating:                    0.
% 2.64/1.03  sup_time_sim_full:                      0.
% 2.64/1.03  sup_time_sim_immed:                     0.
% 2.64/1.03  
% 2.64/1.03  sup_num_of_clauses:                     70
% 2.64/1.03  sup_num_in_active:                      63
% 2.64/1.03  sup_num_in_passive:                     7
% 2.64/1.03  sup_num_of_loops:                       67
% 2.64/1.03  sup_fw_superposition:                   31
% 2.64/1.03  sup_bw_superposition:                   24
% 2.64/1.03  sup_immediate_simplified:               11
% 2.64/1.03  sup_given_eliminated:                   0
% 2.64/1.03  comparisons_done:                       0
% 2.64/1.03  comparisons_avoided:                    0
% 2.64/1.03  
% 2.64/1.03  ------ Simplifications
% 2.64/1.03  
% 2.64/1.03  
% 2.64/1.03  sim_fw_subset_subsumed:                 6
% 2.64/1.03  sim_bw_subset_subsumed:                 3
% 2.64/1.03  sim_fw_subsumed:                        4
% 2.64/1.03  sim_bw_subsumed:                        0
% 2.64/1.03  sim_fw_subsumption_res:                 1
% 2.64/1.03  sim_bw_subsumption_res:                 0
% 2.64/1.03  sim_tautology_del:                      1
% 2.64/1.03  sim_eq_tautology_del:                   2
% 2.64/1.03  sim_eq_res_simp:                        0
% 2.64/1.03  sim_fw_demodulated:                     0
% 2.64/1.03  sim_bw_demodulated:                     2
% 2.64/1.03  sim_light_normalised:                   2
% 2.64/1.03  sim_joinable_taut:                      0
% 2.64/1.03  sim_joinable_simp:                      0
% 2.64/1.03  sim_ac_normalised:                      0
% 2.64/1.03  sim_smt_subsumption:                    0
% 2.64/1.03  
%------------------------------------------------------------------------------
