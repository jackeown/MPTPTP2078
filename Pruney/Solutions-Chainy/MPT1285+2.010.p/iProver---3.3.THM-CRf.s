%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:15:54 EST 2020

% Result     : Theorem 3.31s
% Output     : CNFRefutation 3.31s
% Verified   : 
% Statistics : Number of formulae       :  245 (9910 expanded)
%              Number of clauses        :  187 (2697 expanded)
%              Number of leaves         :   18 (3375 expanded)
%              Depth                    :   41
%              Number of atoms          :  922 (93561 expanded)
%              Number of equality atoms :  349 (4161 expanded)
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

fof(f41,plain,(
    ! [X0,X1] :
      ( v4_tops_1(X1,X0)
      | ~ r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
      | ~ r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

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

fof(f55,plain,
    ( v6_tops_1(sK2,sK0)
    | ~ v6_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f60,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f34])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v6_tops_1(X1,X0)
      | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f54,plain,
    ( v6_tops_1(sK2,sK0)
    | v4_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)
      | ~ v4_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f56,plain,
    ( ~ v4_tops_1(sK2,sK0)
    | ~ v3_pre_topc(sK2,sK0)
    | v3_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
      | ~ v4_tops_1(X1,X0)
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

cnf(c_755,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1926,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK2,X2)
    | X2 != X1
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_755])).

cnf(c_2662,plain,
    ( ~ r1_tarski(sK2,X0)
    | r1_tarski(sK2,X1)
    | X1 != X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1926])).

cnf(c_4515,plain,
    ( r1_tarski(sK2,X0)
    | ~ r1_tarski(sK2,k2_pre_topc(sK0,sK2))
    | X0 != k2_pre_topc(sK0,sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_2662])).

cnf(c_8673,plain,
    ( r1_tarski(sK2,k2_pre_topc(X0,k1_tops_1(sK0,sK2)))
    | ~ r1_tarski(sK2,k2_pre_topc(sK0,sK2))
    | k2_pre_topc(X0,k1_tops_1(sK0,sK2)) != k2_pre_topc(sK0,sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_4515])).

cnf(c_8678,plain,
    ( r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2)))
    | ~ r1_tarski(sK2,k2_pre_topc(sK0,sK2))
    | k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) != k2_pre_topc(sK0,sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_8673])).

cnf(c_19,negated_conjecture,
    ( v3_pre_topc(sK3,sK1)
    | v6_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1394,plain,
    ( v3_pre_topc(sK3,sK1) = iProver_top
    | v6_tops_1(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1393,plain,
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

cnf(c_307,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X1,X0) = X0
    | sK0 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_24])).

cnf(c_308,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK0)
    | k1_tops_1(X1,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_307])).

cnf(c_23,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f49])).

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

cnf(c_22,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_347,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(X1,X0) = X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_313,c_22])).

cnf(c_348,plain,
    ( ~ v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK1,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_347])).

cnf(c_750,plain,
    ( ~ v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,X0) = X0
    | ~ sP4_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP4_iProver_split])],[c_348])).

cnf(c_1389,plain,
    ( k1_tops_1(sK1,X0) = X0
    | v3_pre_topc(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | sP4_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_750])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_28,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_751,plain,
    ( sP4_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_348])).

cnf(c_804,plain,
    ( sP4_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_751])).

cnf(c_805,plain,
    ( k1_tops_1(sK1,X0) = X0
    | v3_pre_topc(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | sP4_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_750])).

cnf(c_12,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_282,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X1,X0) != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_24])).

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

cnf(c_641,plain,
    ( v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) != X0
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_288])).

cnf(c_642,plain,
    ( v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_641])).

cnf(c_743,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_642])).

cnf(c_1665,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ sP0_iProver_split ),
    inference(instantiation,[status(thm)],[c_743])).

cnf(c_1666,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1665])).

cnf(c_3083,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v3_pre_topc(X0,sK1) != iProver_top
    | k1_tops_1(sK1,X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1389,c_28,c_804,c_805,c_1666])).

cnf(c_3084,plain,
    ( k1_tops_1(sK1,X0) = X0
    | v3_pre_topc(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3083])).

cnf(c_3092,plain,
    ( k1_tops_1(sK1,sK3) = sK3
    | v3_pre_topc(sK3,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1393,c_3084])).

cnf(c_3181,plain,
    ( k1_tops_1(sK1,sK3) = sK3
    | v6_tops_1(sK2,sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1394,c_3092])).

cnf(c_1392,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_9,plain,
    ( ~ v6_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,k2_pre_topc(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_521,plain,
    ( ~ v6_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,k2_pre_topc(X1,X0)) = X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_23])).

cnf(c_522,plain,
    ( ~ v6_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,k2_pre_topc(sK0,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_521])).

cnf(c_1375,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,X0)) = X0
    | v6_tops_1(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_522])).

cnf(c_2412,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = sK2
    | v6_tops_1(sK2,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1392,c_1375])).

cnf(c_3365,plain,
    ( k1_tops_1(sK1,sK3) = sK3
    | k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_3181,c_2412])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_503,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_23])).

cnf(c_504,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,X1)
    | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1)) ),
    inference(unflattening,[status(thm)],[c_503])).

cnf(c_1376,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_504])).

cnf(c_5,plain,
    ( v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
    | ~ r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_581,plain,
    ( v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
    | ~ r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_23])).

cnf(c_582,plain,
    ( v4_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,X0)))
    | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X0) ),
    inference(unflattening,[status(thm)],[c_581])).

cnf(c_1371,plain,
    ( v4_tops_1(X0,sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,X0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_582])).

cnf(c_3189,plain,
    ( v4_tops_1(k1_tops_1(sK0,X0),sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,X0)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),k2_pre_topc(sK0,k1_tops_1(sK0,k1_tops_1(sK0,X0)))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,X0)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1376,c_1371])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_611,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_23])).

cnf(c_612,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_611])).

cnf(c_1369,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_612])).

cnf(c_4390,plain,
    ( v4_tops_1(k1_tops_1(sK0,X0),sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),k2_pre_topc(sK0,k1_tops_1(sK0,k1_tops_1(sK0,X0)))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,X0)),X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3189,c_1369])).

cnf(c_4395,plain,
    ( k1_tops_1(sK1,sK3) = sK3
    | v4_tops_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK0) = iProver_top
    | m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK2))),k2_pre_topc(sK0,sK2)) != iProver_top
    | r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3365,c_4390])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_599,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_23])).

cnf(c_600,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,k2_pre_topc(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_599])).

cnf(c_1684,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK2,k2_pre_topc(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_600])).

cnf(c_1685,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK2,k2_pre_topc(sK0,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1684])).

cnf(c_3888,plain,
    ( k1_tops_1(sK1,sK3) = sK3
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,sK2)) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3365,c_1376])).

cnf(c_1678,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_612])).

cnf(c_1679,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1678])).

cnf(c_6062,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | k1_tops_1(sK1,sK3) = sK3
    | r1_tarski(X0,k2_pre_topc(sK0,sK2)) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3888,c_28,c_1679])).

cnf(c_6063,plain,
    ( k1_tops_1(sK1,sK3) = sK3
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,sK2)) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),sK2) = iProver_top ),
    inference(renaming,[status(thm)],[c_6062])).

cnf(c_6072,plain,
    ( k1_tops_1(sK1,sK3) = sK3
    | r1_tarski(k1_tops_1(sK0,sK2),sK2) = iProver_top
    | r1_tarski(sK2,k2_pre_topc(sK0,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1392,c_6063])).

cnf(c_6093,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2) = iProver_top
    | k1_tops_1(sK1,sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6072,c_28,c_1685])).

cnf(c_6094,plain,
    ( k1_tops_1(sK1,sK3) = sK3
    | r1_tarski(k1_tops_1(sK0,sK2),sK2) = iProver_top ),
    inference(renaming,[status(thm)],[c_6093])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1401,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_6099,plain,
    ( k1_tops_1(sK1,sK3) = sK3
    | k1_tops_1(sK0,sK2) = sK2
    | r1_tarski(sK2,k1_tops_1(sK0,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6094,c_1401])).

cnf(c_485,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(X1,X0) = X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_313,c_23])).

cnf(c_486,plain,
    ( ~ v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_485])).

cnf(c_748,plain,
    ( ~ v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) = X0
    | ~ sP3_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP3_iProver_split])],[c_486])).

cnf(c_1378,plain,
    ( k1_tops_1(sK0,X0) = X0
    | v3_pre_topc(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | sP3_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_748])).

cnf(c_749,plain,
    ( sP3_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_486])).

cnf(c_793,plain,
    ( sP3_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_749])).

cnf(c_794,plain,
    ( k1_tops_1(sK0,X0) = X0
    | v3_pre_topc(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | sP3_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_748])).

cnf(c_2973,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v3_pre_topc(X0,sK0) != iProver_top
    | k1_tops_1(sK0,X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1378,c_28,c_793,c_794,c_1666])).

cnf(c_2974,plain,
    ( k1_tops_1(sK0,X0) = X0
    | v3_pre_topc(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2973])).

cnf(c_2980,plain,
    ( k1_tops_1(sK0,sK2) = sK2
    | v3_pre_topc(sK2,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1392,c_2974])).

cnf(c_10,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f44])).

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

cnf(c_1391,plain,
    ( v3_pre_topc(k1_tops_1(sK0,X0),sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_270])).

cnf(c_2235,plain,
    ( v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1369,c_1391])).

cnf(c_3894,plain,
    ( k1_tops_1(sK1,sK3) = sK3
    | v3_pre_topc(sK2,sK0) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3365,c_2235])).

cnf(c_6140,plain,
    ( k1_tops_1(sK0,sK2) = sK2
    | k1_tops_1(sK1,sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6099,c_28,c_2980,c_3894])).

cnf(c_6141,plain,
    ( k1_tops_1(sK1,sK3) = sK3
    | k1_tops_1(sK0,sK2) = sK2 ),
    inference(renaming,[status(thm)],[c_6140])).

cnf(c_365,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_22])).

cnf(c_366,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X0,X1)
    | r1_tarski(k1_tops_1(sK1,X0),k1_tops_1(sK1,X1)) ),
    inference(unflattening,[status(thm)],[c_365])).

cnf(c_1387,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_tops_1(sK1,X0),k1_tops_1(sK1,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_366])).

cnf(c_6153,plain,
    ( k1_tops_1(sK0,sK2) = sK2
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(k1_tops_1(sK1,X0),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_6141,c_1387])).

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

cnf(c_74,plain,
    ( ~ r1_tarski(sK0,sK0)
    | sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_461,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_22])).

cnf(c_462,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(X0,k2_pre_topc(sK1,X0)) ),
    inference(unflattening,[status(thm)],[c_461])).

cnf(c_1681,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(sK3,k2_pre_topc(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_462])).

cnf(c_1682,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(sK3,k2_pre_topc(sK1,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1681])).

cnf(c_8,plain,
    ( v6_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,k2_pre_topc(X1,X0)) != X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_398,plain,
    ( v6_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,k2_pre_topc(X1,X0)) != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_22])).

cnf(c_399,plain,
    ( v6_tops_1(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,k2_pre_topc(sK1,X0)) != X0 ),
    inference(unflattening,[status(thm)],[c_398])).

cnf(c_1687,plain,
    ( v6_tops_1(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) != sK3 ),
    inference(instantiation,[status(thm)],[c_399])).

cnf(c_1688,plain,
    ( k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) != sK3
    | v6_tops_1(sK3,sK1) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1687])).

cnf(c_1792,plain,
    ( v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK0)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_270])).

cnf(c_1796,plain,
    ( v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK0) = iProver_top
    | m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1792])).

cnf(c_753,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1953,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_753])).

cnf(c_18,negated_conjecture,
    ( v6_tops_1(sK2,sK0)
    | v4_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1395,plain,
    ( v6_tops_1(sK2,sK0) = iProver_top
    | v4_tops_1(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2535,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = sK2
    | v4_tops_1(sK3,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1395,c_2412])).

cnf(c_754,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2125,plain,
    ( X0 != X1
    | sK2 != X1
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_754])).

cnf(c_2882,plain,
    ( X0 != sK2
    | sK2 = X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_2125])).

cnf(c_4233,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) != sK2
    | sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2))
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_2882])).

cnf(c_763,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v3_pre_topc(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2085,plain,
    ( v3_pre_topc(X0,X1)
    | ~ v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK0)
    | X0 != k1_tops_1(sK0,k2_pre_topc(sK0,sK2))
    | X1 != sK0 ),
    inference(instantiation,[status(thm)],[c_763])).

cnf(c_5853,plain,
    ( ~ v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK0)
    | v3_pre_topc(sK2,X0)
    | X0 != sK0
    | sK2 != k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_2085])).

cnf(c_5854,plain,
    ( X0 != sK0
    | sK2 != k1_tops_1(sK0,k2_pre_topc(sK0,sK2))
    | v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK0) != iProver_top
    | v3_pre_topc(sK2,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5853])).

cnf(c_5856,plain,
    ( sK0 != sK0
    | sK2 != k1_tops_1(sK0,k2_pre_topc(sK0,sK2))
    | v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK0) != iProver_top
    | v3_pre_topc(sK2,sK0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_5854])).

cnf(c_473,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_22])).

cnf(c_474,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k2_pre_topc(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_473])).

cnf(c_1380,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_474])).

cnf(c_6149,plain,
    ( k1_tops_1(sK0,sK2) = sK2
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top
    | r1_tarski(sK3,k1_tops_1(sK1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6141,c_1387])).

cnf(c_7530,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | k1_tops_1(sK0,sK2) = sK2
    | r1_tarski(sK3,X0) != iProver_top
    | r1_tarski(sK3,k1_tops_1(sK1,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6149,c_29])).

cnf(c_7531,plain,
    ( k1_tops_1(sK0,sK2) = sK2
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top
    | r1_tarski(sK3,k1_tops_1(sK1,X0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_7530])).

cnf(c_7541,plain,
    ( k1_tops_1(sK0,sK2) = sK2
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,X0))) = iProver_top
    | r1_tarski(sK3,k2_pre_topc(sK1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1380,c_7531])).

cnf(c_7,plain,
    ( ~ v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_413,plain,
    ( ~ v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_22])).

cnf(c_414,plain,
    ( ~ v4_tops_1(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,X0)),X0) ),
    inference(unflattening,[status(thm)],[c_413])).

cnf(c_1384,plain,
    ( v4_tops_1(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,X0)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_414])).

cnf(c_2968,plain,
    ( k1_tops_1(sK1,k2_pre_topc(sK1,X0)) = X0
    | v4_tops_1(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X0,k1_tops_1(sK1,k2_pre_topc(sK1,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1384,c_1401])).

cnf(c_7819,plain,
    ( k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) = sK3
    | k1_tops_1(sK0,sK2) = sK2
    | v4_tops_1(sK3,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(sK3,k2_pre_topc(sK1,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7541,c_2968])).

cnf(c_7845,plain,
    ( k1_tops_1(sK0,sK2) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6153,c_28,c_29,c_32,c_70,c_74,c_1679,c_1682,c_1688,c_1796,c_1953,c_2412,c_2535,c_2980,c_4233,c_5856,c_7819])).

cnf(c_3896,plain,
    ( k1_tops_1(sK1,sK3) = sK3
    | v4_tops_1(sK2,sK0) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) != iProver_top
    | r1_tarski(sK2,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3365,c_1371])).

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

cnf(c_1921,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1924,plain,
    ( r1_tarski(sK2,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1921])).

cnf(c_7482,plain,
    ( r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) != iProver_top
    | k1_tops_1(sK1,sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3896,c_28,c_33,c_1924,c_3092,c_3894])).

cnf(c_7483,plain,
    ( k1_tops_1(sK1,sK3) = sK3
    | r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_7482])).

cnf(c_7848,plain,
    ( k1_tops_1(sK1,sK3) = sK3
    | r1_tarski(sK2,k2_pre_topc(sK0,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7845,c_7483])).

cnf(c_8506,plain,
    ( k1_tops_1(sK1,sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4395,c_28,c_1685,c_7848])).

cnf(c_6,plain,
    ( ~ v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_428,plain,
    ( ~ v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_22])).

cnf(c_429,plain,
    ( ~ v4_tops_1(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(X0,k2_pre_topc(sK1,k1_tops_1(sK1,X0))) ),
    inference(unflattening,[status(thm)],[c_428])).

cnf(c_1383,plain,
    ( v4_tops_1(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK1,k1_tops_1(sK1,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_429])).

cnf(c_3396,plain,
    ( k1_tops_1(sK1,k2_pre_topc(sK1,k1_tops_1(sK1,X0))) = k1_tops_1(sK1,X0)
    | v4_tops_1(k1_tops_1(sK1,X0),sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k1_tops_1(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK1,k1_tops_1(sK1,X0)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK1,k1_tops_1(sK1,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1387,c_2968])).

cnf(c_5877,plain,
    ( k1_tops_1(sK1,k2_pre_topc(sK1,k1_tops_1(sK1,X0))) = k1_tops_1(sK1,X0)
    | v4_tops_1(k1_tops_1(sK1,X0),sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k1_tops_1(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK1,k1_tops_1(sK1,X0))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3396,c_1380])).

cnf(c_5881,plain,
    ( k1_tops_1(sK1,k2_pre_topc(sK1,k1_tops_1(sK1,X0))) = k1_tops_1(sK1,X0)
    | v4_tops_1(X0,sK1) != iProver_top
    | v4_tops_1(k1_tops_1(sK1,X0),sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k1_tops_1(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1383,c_5877])).

cnf(c_8553,plain,
    ( k1_tops_1(sK1,k2_pre_topc(sK1,k1_tops_1(sK1,sK3))) = k1_tops_1(sK1,sK3)
    | v4_tops_1(k1_tops_1(sK1,sK3),sK1) != iProver_top
    | v4_tops_1(sK3,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8506,c_5881])).

cnf(c_8618,plain,
    ( k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) = sK3
    | v4_tops_1(sK3,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8553,c_8506])).

cnf(c_8644,plain,
    ( ~ v4_tops_1(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) = sK3 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_8618])).

cnf(c_756,plain,
    ( X0 != X1
    | X2 != X3
    | k2_pre_topc(X0,X2) = k2_pre_topc(X1,X3) ),
    theory(equality)).

cnf(c_2196,plain,
    ( X0 != sK0
    | X1 != sK2
    | k2_pre_topc(X0,X1) = k2_pre_topc(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_756])).

cnf(c_6400,plain,
    ( X0 != sK0
    | k1_tops_1(sK0,sK2) != sK2
    | k2_pre_topc(X0,k1_tops_1(sK0,sK2)) = k2_pre_topc(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_2196])).

cnf(c_6403,plain,
    ( k1_tops_1(sK0,sK2) != sK2
    | k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = k2_pre_topc(sK0,sK2)
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_6400])).

cnf(c_1856,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK2)
    | k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) != X0
    | sK2 != X1 ),
    inference(instantiation,[status(thm)],[c_755])).

cnf(c_2227,plain,
    ( ~ r1_tarski(X0,sK2)
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK2)
    | k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) != X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1856])).

cnf(c_2767,plain,
    ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK2)
    | ~ r1_tarski(sK2,sK2)
    | k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) != sK2
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_2227])).

cnf(c_2536,plain,
    ( v4_tops_1(sK3,sK1)
    | k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = sK2 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2535])).

cnf(c_1727,plain,
    ( v4_tops_1(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK2)
    | ~ r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) ),
    inference(instantiation,[status(thm)],[c_582])).

cnf(c_744,plain,
    ( v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) != X0
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_642])).

cnf(c_745,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_642])).

cnf(c_871,plain,
    ( k1_tops_1(sK0,X0) != X0
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(X0,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_744,c_745,c_743])).

cnf(c_872,plain,
    ( v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) != X0 ),
    inference(renaming,[status(thm)],[c_871])).

cnf(c_878,plain,
    ( k1_tops_1(sK0,X0) != X0
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(X0,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_744,c_872])).

cnf(c_879,plain,
    ( v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) != X0 ),
    inference(renaming,[status(thm)],[c_878])).

cnf(c_1703,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,sK2) != sK2 ),
    inference(instantiation,[status(thm)],[c_879])).

cnf(c_1690,plain,
    ( ~ v6_tops_1(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_522])).

cnf(c_14,negated_conjecture,
    ( ~ v3_pre_topc(sK2,sK0)
    | ~ v6_tops_1(sK3,sK1)
    | ~ v4_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_15,negated_conjecture,
    ( ~ v3_pre_topc(sK2,sK0)
    | v4_tops_1(sK3,sK1)
    | ~ v4_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f57])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8678,c_8644,c_7845,c_6403,c_2767,c_2536,c_1953,c_1921,c_1727,c_1703,c_1690,c_1687,c_1684,c_74,c_70,c_14,c_15,c_17,c_20,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:02:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.31/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.31/1.00  
% 3.31/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.31/1.00  
% 3.31/1.00  ------  iProver source info
% 3.31/1.00  
% 3.31/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.31/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.31/1.00  git: non_committed_changes: false
% 3.31/1.00  git: last_make_outside_of_git: false
% 3.31/1.00  
% 3.31/1.00  ------ 
% 3.31/1.00  
% 3.31/1.00  ------ Input Options
% 3.31/1.00  
% 3.31/1.00  --out_options                           all
% 3.31/1.00  --tptp_safe_out                         true
% 3.31/1.00  --problem_path                          ""
% 3.31/1.00  --include_path                          ""
% 3.31/1.00  --clausifier                            res/vclausify_rel
% 3.31/1.00  --clausifier_options                    --mode clausify
% 3.31/1.00  --stdin                                 false
% 3.31/1.00  --stats_out                             all
% 3.31/1.00  
% 3.31/1.00  ------ General Options
% 3.31/1.00  
% 3.31/1.00  --fof                                   false
% 3.31/1.00  --time_out_real                         305.
% 3.31/1.00  --time_out_virtual                      -1.
% 3.31/1.00  --symbol_type_check                     false
% 3.31/1.00  --clausify_out                          false
% 3.31/1.00  --sig_cnt_out                           false
% 3.31/1.00  --trig_cnt_out                          false
% 3.31/1.00  --trig_cnt_out_tolerance                1.
% 3.31/1.00  --trig_cnt_out_sk_spl                   false
% 3.31/1.00  --abstr_cl_out                          false
% 3.31/1.00  
% 3.31/1.00  ------ Global Options
% 3.31/1.00  
% 3.31/1.00  --schedule                              default
% 3.31/1.00  --add_important_lit                     false
% 3.31/1.00  --prop_solver_per_cl                    1000
% 3.31/1.00  --min_unsat_core                        false
% 3.31/1.00  --soft_assumptions                      false
% 3.31/1.00  --soft_lemma_size                       3
% 3.31/1.00  --prop_impl_unit_size                   0
% 3.31/1.00  --prop_impl_unit                        []
% 3.31/1.00  --share_sel_clauses                     true
% 3.31/1.00  --reset_solvers                         false
% 3.31/1.00  --bc_imp_inh                            [conj_cone]
% 3.31/1.00  --conj_cone_tolerance                   3.
% 3.31/1.00  --extra_neg_conj                        none
% 3.31/1.00  --large_theory_mode                     true
% 3.31/1.00  --prolific_symb_bound                   200
% 3.31/1.00  --lt_threshold                          2000
% 3.31/1.00  --clause_weak_htbl                      true
% 3.31/1.00  --gc_record_bc_elim                     false
% 3.31/1.00  
% 3.31/1.00  ------ Preprocessing Options
% 3.31/1.00  
% 3.31/1.00  --preprocessing_flag                    true
% 3.31/1.00  --time_out_prep_mult                    0.1
% 3.31/1.00  --splitting_mode                        input
% 3.31/1.00  --splitting_grd                         true
% 3.31/1.00  --splitting_cvd                         false
% 3.31/1.00  --splitting_cvd_svl                     false
% 3.31/1.00  --splitting_nvd                         32
% 3.31/1.00  --sub_typing                            true
% 3.31/1.00  --prep_gs_sim                           true
% 3.31/1.00  --prep_unflatten                        true
% 3.31/1.00  --prep_res_sim                          true
% 3.31/1.00  --prep_upred                            true
% 3.31/1.00  --prep_sem_filter                       exhaustive
% 3.31/1.00  --prep_sem_filter_out                   false
% 3.31/1.00  --pred_elim                             true
% 3.31/1.00  --res_sim_input                         true
% 3.31/1.00  --eq_ax_congr_red                       true
% 3.31/1.00  --pure_diseq_elim                       true
% 3.31/1.00  --brand_transform                       false
% 3.31/1.00  --non_eq_to_eq                          false
% 3.31/1.00  --prep_def_merge                        true
% 3.31/1.00  --prep_def_merge_prop_impl              false
% 3.31/1.00  --prep_def_merge_mbd                    true
% 3.31/1.00  --prep_def_merge_tr_red                 false
% 3.31/1.00  --prep_def_merge_tr_cl                  false
% 3.31/1.00  --smt_preprocessing                     true
% 3.31/1.00  --smt_ac_axioms                         fast
% 3.31/1.00  --preprocessed_out                      false
% 3.31/1.00  --preprocessed_stats                    false
% 3.31/1.00  
% 3.31/1.00  ------ Abstraction refinement Options
% 3.31/1.00  
% 3.31/1.00  --abstr_ref                             []
% 3.31/1.00  --abstr_ref_prep                        false
% 3.31/1.00  --abstr_ref_until_sat                   false
% 3.31/1.00  --abstr_ref_sig_restrict                funpre
% 3.31/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.31/1.00  --abstr_ref_under                       []
% 3.31/1.00  
% 3.31/1.00  ------ SAT Options
% 3.31/1.00  
% 3.31/1.00  --sat_mode                              false
% 3.31/1.00  --sat_fm_restart_options                ""
% 3.31/1.00  --sat_gr_def                            false
% 3.31/1.00  --sat_epr_types                         true
% 3.31/1.00  --sat_non_cyclic_types                  false
% 3.31/1.00  --sat_finite_models                     false
% 3.31/1.00  --sat_fm_lemmas                         false
% 3.31/1.00  --sat_fm_prep                           false
% 3.31/1.00  --sat_fm_uc_incr                        true
% 3.31/1.00  --sat_out_model                         small
% 3.31/1.00  --sat_out_clauses                       false
% 3.31/1.00  
% 3.31/1.00  ------ QBF Options
% 3.31/1.00  
% 3.31/1.00  --qbf_mode                              false
% 3.31/1.00  --qbf_elim_univ                         false
% 3.31/1.00  --qbf_dom_inst                          none
% 3.31/1.00  --qbf_dom_pre_inst                      false
% 3.31/1.00  --qbf_sk_in                             false
% 3.31/1.00  --qbf_pred_elim                         true
% 3.31/1.00  --qbf_split                             512
% 3.31/1.00  
% 3.31/1.00  ------ BMC1 Options
% 3.31/1.00  
% 3.31/1.00  --bmc1_incremental                      false
% 3.31/1.00  --bmc1_axioms                           reachable_all
% 3.31/1.00  --bmc1_min_bound                        0
% 3.31/1.00  --bmc1_max_bound                        -1
% 3.31/1.00  --bmc1_max_bound_default                -1
% 3.31/1.00  --bmc1_symbol_reachability              true
% 3.31/1.00  --bmc1_property_lemmas                  false
% 3.31/1.00  --bmc1_k_induction                      false
% 3.31/1.00  --bmc1_non_equiv_states                 false
% 3.31/1.00  --bmc1_deadlock                         false
% 3.31/1.00  --bmc1_ucm                              false
% 3.31/1.00  --bmc1_add_unsat_core                   none
% 3.31/1.00  --bmc1_unsat_core_children              false
% 3.31/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.31/1.00  --bmc1_out_stat                         full
% 3.31/1.00  --bmc1_ground_init                      false
% 3.31/1.00  --bmc1_pre_inst_next_state              false
% 3.31/1.00  --bmc1_pre_inst_state                   false
% 3.31/1.00  --bmc1_pre_inst_reach_state             false
% 3.31/1.00  --bmc1_out_unsat_core                   false
% 3.31/1.00  --bmc1_aig_witness_out                  false
% 3.31/1.00  --bmc1_verbose                          false
% 3.31/1.00  --bmc1_dump_clauses_tptp                false
% 3.31/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.31/1.00  --bmc1_dump_file                        -
% 3.31/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.31/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.31/1.00  --bmc1_ucm_extend_mode                  1
% 3.31/1.00  --bmc1_ucm_init_mode                    2
% 3.31/1.00  --bmc1_ucm_cone_mode                    none
% 3.31/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.31/1.00  --bmc1_ucm_relax_model                  4
% 3.31/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.31/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.31/1.00  --bmc1_ucm_layered_model                none
% 3.31/1.00  --bmc1_ucm_max_lemma_size               10
% 3.31/1.00  
% 3.31/1.00  ------ AIG Options
% 3.31/1.00  
% 3.31/1.00  --aig_mode                              false
% 3.31/1.00  
% 3.31/1.00  ------ Instantiation Options
% 3.31/1.00  
% 3.31/1.00  --instantiation_flag                    true
% 3.31/1.00  --inst_sos_flag                         false
% 3.31/1.00  --inst_sos_phase                        true
% 3.31/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.31/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.31/1.00  --inst_lit_sel_side                     num_symb
% 3.31/1.00  --inst_solver_per_active                1400
% 3.31/1.00  --inst_solver_calls_frac                1.
% 3.31/1.00  --inst_passive_queue_type               priority_queues
% 3.31/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.31/1.00  --inst_passive_queues_freq              [25;2]
% 3.31/1.00  --inst_dismatching                      true
% 3.31/1.00  --inst_eager_unprocessed_to_passive     true
% 3.31/1.00  --inst_prop_sim_given                   true
% 3.31/1.00  --inst_prop_sim_new                     false
% 3.31/1.00  --inst_subs_new                         false
% 3.31/1.00  --inst_eq_res_simp                      false
% 3.31/1.00  --inst_subs_given                       false
% 3.31/1.00  --inst_orphan_elimination               true
% 3.31/1.00  --inst_learning_loop_flag               true
% 3.31/1.00  --inst_learning_start                   3000
% 3.31/1.00  --inst_learning_factor                  2
% 3.31/1.00  --inst_start_prop_sim_after_learn       3
% 3.31/1.00  --inst_sel_renew                        solver
% 3.31/1.00  --inst_lit_activity_flag                true
% 3.31/1.00  --inst_restr_to_given                   false
% 3.31/1.00  --inst_activity_threshold               500
% 3.31/1.00  --inst_out_proof                        true
% 3.31/1.00  
% 3.31/1.00  ------ Resolution Options
% 3.31/1.00  
% 3.31/1.00  --resolution_flag                       true
% 3.31/1.00  --res_lit_sel                           adaptive
% 3.31/1.00  --res_lit_sel_side                      none
% 3.31/1.00  --res_ordering                          kbo
% 3.31/1.00  --res_to_prop_solver                    active
% 3.31/1.00  --res_prop_simpl_new                    false
% 3.31/1.00  --res_prop_simpl_given                  true
% 3.31/1.00  --res_passive_queue_type                priority_queues
% 3.31/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.31/1.00  --res_passive_queues_freq               [15;5]
% 3.31/1.00  --res_forward_subs                      full
% 3.31/1.00  --res_backward_subs                     full
% 3.31/1.00  --res_forward_subs_resolution           true
% 3.31/1.00  --res_backward_subs_resolution          true
% 3.31/1.00  --res_orphan_elimination                true
% 3.31/1.00  --res_time_limit                        2.
% 3.31/1.00  --res_out_proof                         true
% 3.31/1.00  
% 3.31/1.00  ------ Superposition Options
% 3.31/1.00  
% 3.31/1.00  --superposition_flag                    true
% 3.31/1.00  --sup_passive_queue_type                priority_queues
% 3.31/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.31/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.31/1.00  --demod_completeness_check              fast
% 3.31/1.00  --demod_use_ground                      true
% 3.31/1.00  --sup_to_prop_solver                    passive
% 3.31/1.00  --sup_prop_simpl_new                    true
% 3.31/1.00  --sup_prop_simpl_given                  true
% 3.31/1.00  --sup_fun_splitting                     false
% 3.31/1.00  --sup_smt_interval                      50000
% 3.31/1.00  
% 3.31/1.00  ------ Superposition Simplification Setup
% 3.31/1.00  
% 3.31/1.00  --sup_indices_passive                   []
% 3.31/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.31/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.31/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.31/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.31/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.31/1.00  --sup_full_bw                           [BwDemod]
% 3.31/1.00  --sup_immed_triv                        [TrivRules]
% 3.31/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.31/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.31/1.00  --sup_immed_bw_main                     []
% 3.31/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.31/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.31/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.31/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.31/1.00  
% 3.31/1.00  ------ Combination Options
% 3.31/1.00  
% 3.31/1.00  --comb_res_mult                         3
% 3.31/1.00  --comb_sup_mult                         2
% 3.31/1.00  --comb_inst_mult                        10
% 3.31/1.00  
% 3.31/1.00  ------ Debug Options
% 3.31/1.00  
% 3.31/1.00  --dbg_backtrace                         false
% 3.31/1.00  --dbg_dump_prop_clauses                 false
% 3.31/1.00  --dbg_dump_prop_clauses_file            -
% 3.31/1.00  --dbg_out_stat                          false
% 3.31/1.00  ------ Parsing...
% 3.31/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.31/1.00  
% 3.31/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 3.31/1.00  
% 3.31/1.00  ------ Preprocessing... gs_s  sp: 8 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.31/1.00  
% 3.31/1.00  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.31/1.00  ------ Proving...
% 3.31/1.00  ------ Problem Properties 
% 3.31/1.00  
% 3.31/1.00  
% 3.31/1.00  clauses                                 39
% 3.31/1.00  conjectures                             8
% 3.31/1.00  EPR                                     12
% 3.31/1.00  Horn                                    33
% 3.31/1.00  unary                                   3
% 3.31/1.00  binary                                  16
% 3.31/1.00  lits                                    103
% 3.31/1.00  lits eq                                 9
% 3.31/1.00  fd_pure                                 0
% 3.31/1.00  fd_pseudo                               0
% 3.31/1.00  fd_cond                                 0
% 3.31/1.00  fd_pseudo_cond                          1
% 3.31/1.00  AC symbols                              0
% 3.31/1.00  
% 3.31/1.00  ------ Schedule dynamic 5 is on 
% 3.31/1.00  
% 3.31/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.31/1.00  
% 3.31/1.00  
% 3.31/1.00  ------ 
% 3.31/1.00  Current options:
% 3.31/1.00  ------ 
% 3.31/1.00  
% 3.31/1.00  ------ Input Options
% 3.31/1.00  
% 3.31/1.00  --out_options                           all
% 3.31/1.00  --tptp_safe_out                         true
% 3.31/1.00  --problem_path                          ""
% 3.31/1.00  --include_path                          ""
% 3.31/1.00  --clausifier                            res/vclausify_rel
% 3.31/1.00  --clausifier_options                    --mode clausify
% 3.31/1.00  --stdin                                 false
% 3.31/1.00  --stats_out                             all
% 3.31/1.00  
% 3.31/1.00  ------ General Options
% 3.31/1.00  
% 3.31/1.00  --fof                                   false
% 3.31/1.00  --time_out_real                         305.
% 3.31/1.00  --time_out_virtual                      -1.
% 3.31/1.00  --symbol_type_check                     false
% 3.31/1.00  --clausify_out                          false
% 3.31/1.00  --sig_cnt_out                           false
% 3.31/1.00  --trig_cnt_out                          false
% 3.31/1.00  --trig_cnt_out_tolerance                1.
% 3.31/1.00  --trig_cnt_out_sk_spl                   false
% 3.31/1.00  --abstr_cl_out                          false
% 3.31/1.00  
% 3.31/1.00  ------ Global Options
% 3.31/1.00  
% 3.31/1.00  --schedule                              default
% 3.31/1.00  --add_important_lit                     false
% 3.31/1.00  --prop_solver_per_cl                    1000
% 3.31/1.00  --min_unsat_core                        false
% 3.31/1.00  --soft_assumptions                      false
% 3.31/1.00  --soft_lemma_size                       3
% 3.31/1.00  --prop_impl_unit_size                   0
% 3.31/1.00  --prop_impl_unit                        []
% 3.31/1.00  --share_sel_clauses                     true
% 3.31/1.00  --reset_solvers                         false
% 3.31/1.00  --bc_imp_inh                            [conj_cone]
% 3.31/1.00  --conj_cone_tolerance                   3.
% 3.31/1.00  --extra_neg_conj                        none
% 3.31/1.00  --large_theory_mode                     true
% 3.31/1.00  --prolific_symb_bound                   200
% 3.31/1.00  --lt_threshold                          2000
% 3.31/1.00  --clause_weak_htbl                      true
% 3.31/1.00  --gc_record_bc_elim                     false
% 3.31/1.00  
% 3.31/1.00  ------ Preprocessing Options
% 3.31/1.00  
% 3.31/1.00  --preprocessing_flag                    true
% 3.31/1.00  --time_out_prep_mult                    0.1
% 3.31/1.00  --splitting_mode                        input
% 3.31/1.00  --splitting_grd                         true
% 3.31/1.00  --splitting_cvd                         false
% 3.31/1.00  --splitting_cvd_svl                     false
% 3.31/1.00  --splitting_nvd                         32
% 3.31/1.00  --sub_typing                            true
% 3.31/1.00  --prep_gs_sim                           true
% 3.31/1.00  --prep_unflatten                        true
% 3.31/1.00  --prep_res_sim                          true
% 3.31/1.00  --prep_upred                            true
% 3.31/1.00  --prep_sem_filter                       exhaustive
% 3.31/1.00  --prep_sem_filter_out                   false
% 3.31/1.00  --pred_elim                             true
% 3.31/1.00  --res_sim_input                         true
% 3.31/1.00  --eq_ax_congr_red                       true
% 3.31/1.00  --pure_diseq_elim                       true
% 3.31/1.00  --brand_transform                       false
% 3.31/1.00  --non_eq_to_eq                          false
% 3.31/1.00  --prep_def_merge                        true
% 3.31/1.00  --prep_def_merge_prop_impl              false
% 3.31/1.00  --prep_def_merge_mbd                    true
% 3.31/1.00  --prep_def_merge_tr_red                 false
% 3.31/1.00  --prep_def_merge_tr_cl                  false
% 3.31/1.00  --smt_preprocessing                     true
% 3.31/1.00  --smt_ac_axioms                         fast
% 3.31/1.00  --preprocessed_out                      false
% 3.31/1.00  --preprocessed_stats                    false
% 3.31/1.00  
% 3.31/1.00  ------ Abstraction refinement Options
% 3.31/1.00  
% 3.31/1.00  --abstr_ref                             []
% 3.31/1.00  --abstr_ref_prep                        false
% 3.31/1.00  --abstr_ref_until_sat                   false
% 3.31/1.00  --abstr_ref_sig_restrict                funpre
% 3.31/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.31/1.00  --abstr_ref_under                       []
% 3.31/1.00  
% 3.31/1.00  ------ SAT Options
% 3.31/1.00  
% 3.31/1.00  --sat_mode                              false
% 3.31/1.00  --sat_fm_restart_options                ""
% 3.31/1.00  --sat_gr_def                            false
% 3.31/1.00  --sat_epr_types                         true
% 3.31/1.00  --sat_non_cyclic_types                  false
% 3.31/1.00  --sat_finite_models                     false
% 3.31/1.00  --sat_fm_lemmas                         false
% 3.31/1.00  --sat_fm_prep                           false
% 3.31/1.00  --sat_fm_uc_incr                        true
% 3.31/1.00  --sat_out_model                         small
% 3.31/1.00  --sat_out_clauses                       false
% 3.31/1.00  
% 3.31/1.00  ------ QBF Options
% 3.31/1.00  
% 3.31/1.00  --qbf_mode                              false
% 3.31/1.00  --qbf_elim_univ                         false
% 3.31/1.00  --qbf_dom_inst                          none
% 3.31/1.00  --qbf_dom_pre_inst                      false
% 3.31/1.00  --qbf_sk_in                             false
% 3.31/1.00  --qbf_pred_elim                         true
% 3.31/1.00  --qbf_split                             512
% 3.31/1.00  
% 3.31/1.00  ------ BMC1 Options
% 3.31/1.00  
% 3.31/1.00  --bmc1_incremental                      false
% 3.31/1.00  --bmc1_axioms                           reachable_all
% 3.31/1.00  --bmc1_min_bound                        0
% 3.31/1.00  --bmc1_max_bound                        -1
% 3.31/1.00  --bmc1_max_bound_default                -1
% 3.31/1.00  --bmc1_symbol_reachability              true
% 3.31/1.00  --bmc1_property_lemmas                  false
% 3.31/1.00  --bmc1_k_induction                      false
% 3.31/1.00  --bmc1_non_equiv_states                 false
% 3.31/1.00  --bmc1_deadlock                         false
% 3.31/1.00  --bmc1_ucm                              false
% 3.31/1.00  --bmc1_add_unsat_core                   none
% 3.31/1.00  --bmc1_unsat_core_children              false
% 3.31/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.31/1.00  --bmc1_out_stat                         full
% 3.31/1.00  --bmc1_ground_init                      false
% 3.31/1.00  --bmc1_pre_inst_next_state              false
% 3.31/1.00  --bmc1_pre_inst_state                   false
% 3.31/1.00  --bmc1_pre_inst_reach_state             false
% 3.31/1.00  --bmc1_out_unsat_core                   false
% 3.31/1.00  --bmc1_aig_witness_out                  false
% 3.31/1.00  --bmc1_verbose                          false
% 3.31/1.00  --bmc1_dump_clauses_tptp                false
% 3.31/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.31/1.00  --bmc1_dump_file                        -
% 3.31/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.31/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.31/1.00  --bmc1_ucm_extend_mode                  1
% 3.31/1.00  --bmc1_ucm_init_mode                    2
% 3.31/1.00  --bmc1_ucm_cone_mode                    none
% 3.31/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.31/1.00  --bmc1_ucm_relax_model                  4
% 3.31/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.31/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.31/1.00  --bmc1_ucm_layered_model                none
% 3.31/1.00  --bmc1_ucm_max_lemma_size               10
% 3.31/1.00  
% 3.31/1.00  ------ AIG Options
% 3.31/1.00  
% 3.31/1.00  --aig_mode                              false
% 3.31/1.00  
% 3.31/1.00  ------ Instantiation Options
% 3.31/1.00  
% 3.31/1.00  --instantiation_flag                    true
% 3.31/1.00  --inst_sos_flag                         false
% 3.31/1.00  --inst_sos_phase                        true
% 3.31/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.31/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.31/1.00  --inst_lit_sel_side                     none
% 3.31/1.00  --inst_solver_per_active                1400
% 3.31/1.00  --inst_solver_calls_frac                1.
% 3.31/1.00  --inst_passive_queue_type               priority_queues
% 3.31/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.31/1.00  --inst_passive_queues_freq              [25;2]
% 3.31/1.00  --inst_dismatching                      true
% 3.31/1.00  --inst_eager_unprocessed_to_passive     true
% 3.31/1.00  --inst_prop_sim_given                   true
% 3.31/1.00  --inst_prop_sim_new                     false
% 3.31/1.00  --inst_subs_new                         false
% 3.31/1.00  --inst_eq_res_simp                      false
% 3.31/1.00  --inst_subs_given                       false
% 3.31/1.00  --inst_orphan_elimination               true
% 3.31/1.00  --inst_learning_loop_flag               true
% 3.31/1.00  --inst_learning_start                   3000
% 3.31/1.00  --inst_learning_factor                  2
% 3.31/1.00  --inst_start_prop_sim_after_learn       3
% 3.31/1.00  --inst_sel_renew                        solver
% 3.31/1.00  --inst_lit_activity_flag                true
% 3.31/1.00  --inst_restr_to_given                   false
% 3.31/1.00  --inst_activity_threshold               500
% 3.31/1.00  --inst_out_proof                        true
% 3.31/1.00  
% 3.31/1.00  ------ Resolution Options
% 3.31/1.00  
% 3.31/1.00  --resolution_flag                       false
% 3.31/1.00  --res_lit_sel                           adaptive
% 3.31/1.00  --res_lit_sel_side                      none
% 3.31/1.00  --res_ordering                          kbo
% 3.31/1.00  --res_to_prop_solver                    active
% 3.31/1.00  --res_prop_simpl_new                    false
% 3.31/1.00  --res_prop_simpl_given                  true
% 3.31/1.00  --res_passive_queue_type                priority_queues
% 3.31/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.31/1.00  --res_passive_queues_freq               [15;5]
% 3.31/1.00  --res_forward_subs                      full
% 3.31/1.00  --res_backward_subs                     full
% 3.31/1.00  --res_forward_subs_resolution           true
% 3.31/1.00  --res_backward_subs_resolution          true
% 3.31/1.00  --res_orphan_elimination                true
% 3.31/1.00  --res_time_limit                        2.
% 3.31/1.00  --res_out_proof                         true
% 3.31/1.00  
% 3.31/1.00  ------ Superposition Options
% 3.31/1.00  
% 3.31/1.00  --superposition_flag                    true
% 3.31/1.00  --sup_passive_queue_type                priority_queues
% 3.31/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.31/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.31/1.00  --demod_completeness_check              fast
% 3.31/1.00  --demod_use_ground                      true
% 3.31/1.00  --sup_to_prop_solver                    passive
% 3.31/1.00  --sup_prop_simpl_new                    true
% 3.31/1.00  --sup_prop_simpl_given                  true
% 3.31/1.00  --sup_fun_splitting                     false
% 3.31/1.00  --sup_smt_interval                      50000
% 3.31/1.00  
% 3.31/1.00  ------ Superposition Simplification Setup
% 3.31/1.00  
% 3.31/1.00  --sup_indices_passive                   []
% 3.31/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.31/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.31/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.31/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.31/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.31/1.00  --sup_full_bw                           [BwDemod]
% 3.31/1.00  --sup_immed_triv                        [TrivRules]
% 3.31/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.31/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.31/1.00  --sup_immed_bw_main                     []
% 3.31/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.31/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.31/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.31/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.31/1.00  
% 3.31/1.00  ------ Combination Options
% 3.31/1.00  
% 3.31/1.00  --comb_res_mult                         3
% 3.31/1.00  --comb_sup_mult                         2
% 3.31/1.00  --comb_inst_mult                        10
% 3.31/1.00  
% 3.31/1.00  ------ Debug Options
% 3.31/1.00  
% 3.31/1.00  --dbg_backtrace                         false
% 3.31/1.00  --dbg_dump_prop_clauses                 false
% 3.31/1.00  --dbg_dump_prop_clauses_file            -
% 3.31/1.00  --dbg_out_stat                          false
% 3.31/1.00  
% 3.31/1.00  
% 3.31/1.00  
% 3.31/1.00  
% 3.31/1.00  ------ Proving...
% 3.31/1.00  
% 3.31/1.00  
% 3.31/1.00  % SZS status Theorem for theBenchmark.p
% 3.31/1.00  
% 3.31/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.31/1.00  
% 3.31/1.00  fof(f9,conjecture,(
% 3.31/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v6_tops_1(X2,X0) => (v4_tops_1(X2,X0) & v3_pre_topc(X2,X0))) & ((v4_tops_1(X3,X1) & v3_pre_topc(X3,X1)) => v6_tops_1(X3,X1)))))))),
% 3.31/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.31/1.00  
% 3.31/1.00  fof(f10,negated_conjecture,(
% 3.31/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v6_tops_1(X2,X0) => (v4_tops_1(X2,X0) & v3_pre_topc(X2,X0))) & ((v4_tops_1(X3,X1) & v3_pre_topc(X3,X1)) => v6_tops_1(X3,X1)))))))),
% 3.31/1.00    inference(negated_conjecture,[],[f9])).
% 3.31/1.00  
% 3.31/1.00  fof(f22,plain,(
% 3.31/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(X3,X1) & (v4_tops_1(X3,X1) & v3_pre_topc(X3,X1)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.31/1.00    inference(ennf_transformation,[],[f10])).
% 3.31/1.00  
% 3.31/1.00  fof(f23,plain,(
% 3.31/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.31/1.00    inference(flattening,[],[f22])).
% 3.31/1.00  
% 3.31/1.00  fof(f32,plain,(
% 3.31/1.00    ( ! [X2,X0,X1] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(sK3,X1) & v4_tops_1(sK3,X1) & v3_pre_topc(sK3,X1))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X1))))) )),
% 3.31/1.00    introduced(choice_axiom,[])).
% 3.31/1.00  
% 3.31/1.00  fof(f31,plain,(
% 3.31/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X3] : ((((~v4_tops_1(sK2,X0) | ~v3_pre_topc(sK2,X0)) & v6_tops_1(sK2,X0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.31/1.00    introduced(choice_axiom,[])).
% 3.31/1.00  
% 3.31/1.00  fof(f30,plain,(
% 3.31/1.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) => (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(X3,sK1) & v4_tops_1(X3,sK1) & v3_pre_topc(X3,sK1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(sK1))) )),
% 3.31/1.00    introduced(choice_axiom,[])).
% 3.31/1.00  
% 3.31/1.00  fof(f29,plain,(
% 3.31/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,sK0) | ~v3_pre_topc(X2,sK0)) & v6_tops_1(X2,sK0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 3.31/1.00    introduced(choice_axiom,[])).
% 3.31/1.00  
% 3.31/1.00  fof(f33,plain,(
% 3.31/1.00    ((((((~v4_tops_1(sK2,sK0) | ~v3_pre_topc(sK2,sK0)) & v6_tops_1(sK2,sK0)) | (~v6_tops_1(sK3,sK1) & v4_tops_1(sK3,sK1) & v3_pre_topc(sK3,sK1))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 3.31/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f32,f31,f30,f29])).
% 3.31/1.00  
% 3.31/1.00  fof(f53,plain,(
% 3.31/1.00    v6_tops_1(sK2,sK0) | v3_pre_topc(sK3,sK1)),
% 3.31/1.00    inference(cnf_transformation,[],[f33])).
% 3.31/1.00  
% 3.31/1.00  fof(f52,plain,(
% 3.31/1.00    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 3.31/1.00    inference(cnf_transformation,[],[f33])).
% 3.31/1.00  
% 3.31/1.00  fof(f8,axiom,(
% 3.31/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 3.31/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.31/1.00  
% 3.31/1.00  fof(f20,plain,(
% 3.31/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.31/1.00    inference(ennf_transformation,[],[f8])).
% 3.31/1.00  
% 3.31/1.00  fof(f21,plain,(
% 3.31/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.31/1.00    inference(flattening,[],[f20])).
% 3.31/1.00  
% 3.31/1.00  fof(f46,plain,(
% 3.31/1.00    ( ! [X2,X0,X3,X1] : (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.31/1.00    inference(cnf_transformation,[],[f21])).
% 3.31/1.00  
% 3.31/1.00  fof(f48,plain,(
% 3.31/1.00    v2_pre_topc(sK0)),
% 3.31/1.00    inference(cnf_transformation,[],[f33])).
% 3.31/1.00  
% 3.31/1.00  fof(f49,plain,(
% 3.31/1.00    l1_pre_topc(sK0)),
% 3.31/1.00    inference(cnf_transformation,[],[f33])).
% 3.31/1.00  
% 3.31/1.00  fof(f50,plain,(
% 3.31/1.00    l1_pre_topc(sK1)),
% 3.31/1.00    inference(cnf_transformation,[],[f33])).
% 3.31/1.00  
% 3.31/1.00  fof(f51,plain,(
% 3.31/1.00    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.31/1.00    inference(cnf_transformation,[],[f33])).
% 3.31/1.00  
% 3.31/1.00  fof(f47,plain,(
% 3.31/1.00    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.31/1.00    inference(cnf_transformation,[],[f21])).
% 3.31/1.00  
% 3.31/1.00  fof(f5,axiom,(
% 3.31/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v6_tops_1(X1,X0) <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1)))),
% 3.31/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.31/1.00  
% 3.31/1.00  fof(f15,plain,(
% 3.31/1.00    ! [X0] : (! [X1] : ((v6_tops_1(X1,X0) <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.31/1.00    inference(ennf_transformation,[],[f5])).
% 3.31/1.00  
% 3.31/1.00  fof(f28,plain,(
% 3.31/1.00    ! [X0] : (! [X1] : (((v6_tops_1(X1,X0) | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1) & (k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 | ~v6_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.31/1.00    inference(nnf_transformation,[],[f15])).
% 3.31/1.00  
% 3.31/1.00  fof(f42,plain,(
% 3.31/1.00    ( ! [X0,X1] : (k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 | ~v6_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.31/1.00    inference(cnf_transformation,[],[f28])).
% 3.31/1.00  
% 3.31/1.00  fof(f7,axiom,(
% 3.31/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 3.31/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.31/1.00  
% 3.31/1.00  fof(f18,plain,(
% 3.31/1.00    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.31/1.00    inference(ennf_transformation,[],[f7])).
% 3.31/1.00  
% 3.31/1.00  fof(f19,plain,(
% 3.31/1.00    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.31/1.00    inference(flattening,[],[f18])).
% 3.31/1.00  
% 3.31/1.00  fof(f45,plain,(
% 3.31/1.00    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.31/1.00    inference(cnf_transformation,[],[f19])).
% 3.31/1.00  
% 3.31/1.00  fof(f4,axiom,(
% 3.31/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)))))),
% 3.31/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.31/1.00  
% 3.31/1.00  fof(f14,plain,(
% 3.31/1.00    ! [X0] : (! [X1] : ((v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.31/1.00    inference(ennf_transformation,[],[f4])).
% 3.31/1.00  
% 3.31/1.00  fof(f26,plain,(
% 3.31/1.00    ! [X0] : (! [X1] : (((v4_tops_1(X1,X0) | (~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1))) & ((r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) | ~v4_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.31/1.00    inference(nnf_transformation,[],[f14])).
% 3.31/1.00  
% 3.31/1.00  fof(f27,plain,(
% 3.31/1.00    ! [X0] : (! [X1] : (((v4_tops_1(X1,X0) | ~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) & ((r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) | ~v4_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.31/1.00    inference(flattening,[],[f26])).
% 3.31/1.00  
% 3.31/1.00  fof(f41,plain,(
% 3.31/1.00    ( ! [X0,X1] : (v4_tops_1(X1,X0) | ~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.31/1.00    inference(cnf_transformation,[],[f27])).
% 3.31/1.00  
% 3.31/1.00  fof(f2,axiom,(
% 3.31/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.31/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.31/1.00  
% 3.31/1.00  fof(f11,plain,(
% 3.31/1.00    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.31/1.00    inference(ennf_transformation,[],[f2])).
% 3.31/1.00  
% 3.31/1.00  fof(f12,plain,(
% 3.31/1.00    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.31/1.00    inference(flattening,[],[f11])).
% 3.31/1.00  
% 3.31/1.00  fof(f37,plain,(
% 3.31/1.00    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.31/1.00    inference(cnf_transformation,[],[f12])).
% 3.31/1.00  
% 3.31/1.00  fof(f3,axiom,(
% 3.31/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 3.31/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.31/1.00  
% 3.31/1.00  fof(f13,plain,(
% 3.31/1.00    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.31/1.00    inference(ennf_transformation,[],[f3])).
% 3.31/1.00  
% 3.31/1.00  fof(f38,plain,(
% 3.31/1.00    ( ! [X0,X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.31/1.00    inference(cnf_transformation,[],[f13])).
% 3.31/1.00  
% 3.31/1.00  fof(f1,axiom,(
% 3.31/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.31/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.31/1.00  
% 3.31/1.00  fof(f24,plain,(
% 3.31/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.31/1.00    inference(nnf_transformation,[],[f1])).
% 3.31/1.00  
% 3.31/1.00  fof(f25,plain,(
% 3.31/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.31/1.00    inference(flattening,[],[f24])).
% 3.31/1.00  
% 3.31/1.00  fof(f36,plain,(
% 3.31/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.31/1.00    inference(cnf_transformation,[],[f25])).
% 3.31/1.00  
% 3.31/1.00  fof(f6,axiom,(
% 3.31/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 3.31/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.31/1.00  
% 3.31/1.00  fof(f16,plain,(
% 3.31/1.00    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.31/1.00    inference(ennf_transformation,[],[f6])).
% 3.31/1.00  
% 3.31/1.00  fof(f17,plain,(
% 3.31/1.00    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.31/1.00    inference(flattening,[],[f16])).
% 3.31/1.00  
% 3.31/1.00  fof(f44,plain,(
% 3.31/1.00    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.31/1.00    inference(cnf_transformation,[],[f17])).
% 3.31/1.00  
% 3.31/1.00  fof(f55,plain,(
% 3.31/1.00    v6_tops_1(sK2,sK0) | ~v6_tops_1(sK3,sK1)),
% 3.31/1.00    inference(cnf_transformation,[],[f33])).
% 3.31/1.00  
% 3.31/1.00  fof(f34,plain,(
% 3.31/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.31/1.00    inference(cnf_transformation,[],[f25])).
% 3.31/1.00  
% 3.31/1.00  fof(f60,plain,(
% 3.31/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.31/1.00    inference(equality_resolution,[],[f34])).
% 3.31/1.00  
% 3.31/1.00  fof(f43,plain,(
% 3.31/1.00    ( ! [X0,X1] : (v6_tops_1(X1,X0) | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.31/1.00    inference(cnf_transformation,[],[f28])).
% 3.31/1.00  
% 3.31/1.00  fof(f54,plain,(
% 3.31/1.00    v6_tops_1(sK2,sK0) | v4_tops_1(sK3,sK1)),
% 3.31/1.00    inference(cnf_transformation,[],[f33])).
% 3.31/1.00  
% 3.31/1.00  fof(f39,plain,(
% 3.31/1.00    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) | ~v4_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.31/1.00    inference(cnf_transformation,[],[f27])).
% 3.31/1.00  
% 3.31/1.00  fof(f56,plain,(
% 3.31/1.00    ~v4_tops_1(sK2,sK0) | ~v3_pre_topc(sK2,sK0) | v3_pre_topc(sK3,sK1)),
% 3.31/1.00    inference(cnf_transformation,[],[f33])).
% 3.31/1.00  
% 3.31/1.00  fof(f40,plain,(
% 3.31/1.00    ( ! [X0,X1] : (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~v4_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.31/1.00    inference(cnf_transformation,[],[f27])).
% 3.31/1.00  
% 3.31/1.00  fof(f58,plain,(
% 3.31/1.00    ~v4_tops_1(sK2,sK0) | ~v3_pre_topc(sK2,sK0) | ~v6_tops_1(sK3,sK1)),
% 3.31/1.00    inference(cnf_transformation,[],[f33])).
% 3.31/1.00  
% 3.31/1.00  fof(f57,plain,(
% 3.31/1.00    ~v4_tops_1(sK2,sK0) | ~v3_pre_topc(sK2,sK0) | v4_tops_1(sK3,sK1)),
% 3.31/1.00    inference(cnf_transformation,[],[f33])).
% 3.31/1.00  
% 3.31/1.00  cnf(c_755,plain,
% 3.31/1.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.31/1.00      theory(equality) ).
% 3.31/1.00  
% 3.31/1.00  cnf(c_1926,plain,
% 3.31/1.00      ( ~ r1_tarski(X0,X1) | r1_tarski(sK2,X2) | X2 != X1 | sK2 != X0 ),
% 3.31/1.00      inference(instantiation,[status(thm)],[c_755]) ).
% 3.31/1.00  
% 3.31/1.00  cnf(c_2662,plain,
% 3.31/1.00      ( ~ r1_tarski(sK2,X0) | r1_tarski(sK2,X1) | X1 != X0 | sK2 != sK2 ),
% 3.31/1.00      inference(instantiation,[status(thm)],[c_1926]) ).
% 3.31/1.00  
% 3.31/1.00  cnf(c_4515,plain,
% 3.31/1.00      ( r1_tarski(sK2,X0)
% 3.31/1.00      | ~ r1_tarski(sK2,k2_pre_topc(sK0,sK2))
% 3.31/1.00      | X0 != k2_pre_topc(sK0,sK2)
% 3.31/1.00      | sK2 != sK2 ),
% 3.31/1.00      inference(instantiation,[status(thm)],[c_2662]) ).
% 3.31/1.00  
% 3.31/1.00  cnf(c_8673,plain,
% 3.31/1.00      ( r1_tarski(sK2,k2_pre_topc(X0,k1_tops_1(sK0,sK2)))
% 3.31/1.00      | ~ r1_tarski(sK2,k2_pre_topc(sK0,sK2))
% 3.31/1.00      | k2_pre_topc(X0,k1_tops_1(sK0,sK2)) != k2_pre_topc(sK0,sK2)
% 3.31/1.00      | sK2 != sK2 ),
% 3.31/1.00      inference(instantiation,[status(thm)],[c_4515]) ).
% 3.31/1.00  
% 3.31/1.00  cnf(c_8678,plain,
% 3.31/1.00      ( r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2)))
% 3.31/1.00      | ~ r1_tarski(sK2,k2_pre_topc(sK0,sK2))
% 3.31/1.00      | k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) != k2_pre_topc(sK0,sK2)
% 3.31/1.00      | sK2 != sK2 ),
% 3.31/1.00      inference(instantiation,[status(thm)],[c_8673]) ).
% 3.31/1.00  
% 3.31/1.00  cnf(c_19,negated_conjecture,
% 3.31/1.00      ( v3_pre_topc(sK3,sK1) | v6_tops_1(sK2,sK0) ),
% 3.31/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.31/1.00  
% 3.31/1.00  cnf(c_1394,plain,
% 3.31/1.00      ( v3_pre_topc(sK3,sK1) = iProver_top
% 3.31/1.00      | v6_tops_1(sK2,sK0) = iProver_top ),
% 3.31/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.31/1.00  
% 3.31/1.00  cnf(c_20,negated_conjecture,
% 3.31/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 3.31/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.31/1.00  
% 3.31/1.00  cnf(c_1393,plain,
% 3.31/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 3.31/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.31/1.00  
% 3.31/1.00  cnf(c_13,plain,
% 3.31/1.00      ( ~ v3_pre_topc(X0,X1)
% 3.31/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 3.31/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.31/1.00      | ~ v2_pre_topc(X3)
% 3.31/1.00      | ~ l1_pre_topc(X3)
% 3.31/1.00      | ~ l1_pre_topc(X1)
% 3.31/1.00      | k1_tops_1(X1,X0) = X0 ),
% 3.31/1.00      inference(cnf_transformation,[],[f46]) ).
% 3.31/1.00  
% 3.31/1.00  cnf(c_24,negated_conjecture,
% 3.31/1.00      ( v2_pre_topc(sK0) ),
% 3.31/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.31/1.00  
% 3.31/1.00  cnf(c_307,plain,
% 3.31/1.00      ( ~ v3_pre_topc(X0,X1)
% 3.31/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.31/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 3.31/1.00      | ~ l1_pre_topc(X1)
% 3.31/1.00      | ~ l1_pre_topc(X3)
% 3.31/1.00      | k1_tops_1(X1,X0) = X0
% 3.31/1.00      | sK0 != X3 ),
% 3.31/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_24]) ).
% 3.31/1.00  
% 3.31/1.00  cnf(c_308,plain,
% 3.31/1.00      ( ~ v3_pre_topc(X0,X1)
% 3.31/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.31/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.31/1.00      | ~ l1_pre_topc(X1)
% 3.31/1.00      | ~ l1_pre_topc(sK0)
% 3.31/1.00      | k1_tops_1(X1,X0) = X0 ),
% 3.31/1.00      inference(unflattening,[status(thm)],[c_307]) ).
% 3.31/1.00  
% 3.31/1.00  cnf(c_23,negated_conjecture,
% 3.31/1.00      ( l1_pre_topc(sK0) ),
% 3.31/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.31/1.00  
% 3.31/1.00  cnf(c_312,plain,
% 3.31/1.00      ( ~ l1_pre_topc(X1)
% 3.31/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.31/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.31/1.00      | ~ v3_pre_topc(X0,X1)
% 3.31/1.00      | k1_tops_1(X1,X0) = X0 ),
% 3.31/1.00      inference(global_propositional_subsumption,
% 3.31/1.00                [status(thm)],
% 3.31/1.00                [c_308,c_23]) ).
% 3.31/1.00  
% 3.31/1.00  cnf(c_313,plain,
% 3.31/1.00      ( ~ v3_pre_topc(X0,X1)
% 3.31/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.31/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.31/1.00      | ~ l1_pre_topc(X1)
% 3.31/1.00      | k1_tops_1(X1,X0) = X0 ),
% 3.31/1.00      inference(renaming,[status(thm)],[c_312]) ).
% 3.31/1.00  
% 3.31/1.00  cnf(c_22,negated_conjecture,
% 3.31/1.00      ( l1_pre_topc(sK1) ),
% 3.31/1.00      inference(cnf_transformation,[],[f50]) ).
% 3.31/1.00  
% 3.31/1.00  cnf(c_347,plain,
% 3.31/1.00      ( ~ v3_pre_topc(X0,X1)
% 3.31/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.31/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.31/1.00      | k1_tops_1(X1,X0) = X0
% 3.31/1.00      | sK1 != X1 ),
% 3.31/1.00      inference(resolution_lifted,[status(thm)],[c_313,c_22]) ).
% 3.31/1.00  
% 3.31/1.00  cnf(c_348,plain,
% 3.31/1.00      ( ~ v3_pre_topc(X0,sK1)
% 3.31/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.31/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.31/1.00      | k1_tops_1(sK1,X0) = X0 ),
% 3.31/1.00      inference(unflattening,[status(thm)],[c_347]) ).
% 3.31/1.00  
% 3.31/1.00  cnf(c_750,plain,
% 3.31/1.00      ( ~ v3_pre_topc(X0,sK1)
% 3.31/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.31/1.00      | k1_tops_1(sK1,X0) = X0
% 3.31/1.00      | ~ sP4_iProver_split ),
% 3.31/1.00      inference(splitting,
% 3.31/1.00                [splitting(split),new_symbols(definition,[sP4_iProver_split])],
% 3.31/1.00                [c_348]) ).
% 3.31/1.00  
% 3.31/1.00  cnf(c_1389,plain,
% 3.31/1.00      ( k1_tops_1(sK1,X0) = X0
% 3.31/1.00      | v3_pre_topc(X0,sK1) != iProver_top
% 3.31/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.31/1.00      | sP4_iProver_split != iProver_top ),
% 3.31/1.00      inference(predicate_to_equality,[status(thm)],[c_750]) ).
% 3.31/1.00  
% 3.31/1.00  cnf(c_21,negated_conjecture,
% 3.31/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.31/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.31/1.00  
% 3.31/1.00  cnf(c_28,plain,
% 3.31/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.31/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.31/1.00  
% 3.31/1.00  cnf(c_751,plain,
% 3.31/1.00      ( sP4_iProver_split | sP0_iProver_split ),
% 3.31/1.00      inference(splitting,
% 3.31/1.00                [splitting(split),new_symbols(definition,[])],
% 3.31/1.00                [c_348]) ).
% 3.31/1.00  
% 3.31/1.00  cnf(c_804,plain,
% 3.31/1.00      ( sP4_iProver_split = iProver_top
% 3.31/1.00      | sP0_iProver_split = iProver_top ),
% 3.31/1.00      inference(predicate_to_equality,[status(thm)],[c_751]) ).
% 3.31/1.00  
% 3.31/1.00  cnf(c_805,plain,
% 3.31/1.00      ( k1_tops_1(sK1,X0) = X0
% 3.31/1.00      | v3_pre_topc(X0,sK1) != iProver_top
% 3.31/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.31/1.00      | sP4_iProver_split != iProver_top ),
% 3.31/1.00      inference(predicate_to_equality,[status(thm)],[c_750]) ).
% 3.31/1.00  
% 3.31/1.00  cnf(c_12,plain,
% 3.31/1.00      ( v3_pre_topc(X0,X1)
% 3.31/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.31/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 3.31/1.00      | ~ v2_pre_topc(X1)
% 3.31/1.00      | ~ l1_pre_topc(X1)
% 3.31/1.00      | ~ l1_pre_topc(X3)
% 3.31/1.00      | k1_tops_1(X1,X0) != X0 ),
% 3.31/1.00      inference(cnf_transformation,[],[f47]) ).
% 3.31/1.00  
% 3.31/1.00  cnf(c_282,plain,
% 3.31/1.00      ( v3_pre_topc(X0,X1)
% 3.31/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.31/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 3.31/1.00      | ~ l1_pre_topc(X1)
% 3.31/1.00      | ~ l1_pre_topc(X3)
% 3.31/1.00      | k1_tops_1(X1,X0) != X0
% 3.31/1.00      | sK0 != X1 ),
% 3.31/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_24]) ).
% 3.31/1.00  
% 3.31/1.00  cnf(c_283,plain,
% 3.31/1.00      ( v3_pre_topc(X0,sK0)
% 3.31/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 3.31/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.31/1.00      | ~ l1_pre_topc(X2)
% 3.31/1.00      | ~ l1_pre_topc(sK0)
% 3.31/1.00      | k1_tops_1(sK0,X0) != X0 ),
% 3.31/1.00      inference(unflattening,[status(thm)],[c_282]) ).
% 3.31/1.00  
% 3.31/1.00  cnf(c_287,plain,
% 3.31/1.00      ( ~ l1_pre_topc(X2)
% 3.31/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.31/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 3.31/1.00      | v3_pre_topc(X0,sK0)
% 3.31/1.00      | k1_tops_1(sK0,X0) != X0 ),
% 3.31/1.00      inference(global_propositional_subsumption,
% 3.31/1.00                [status(thm)],
% 3.31/1.00                [c_283,c_23]) ).
% 3.31/1.00  
% 3.31/1.00  cnf(c_288,plain,
% 3.31/1.00      ( v3_pre_topc(X0,sK0)
% 3.31/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 3.31/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.31/1.00      | ~ l1_pre_topc(X2)
% 3.31/1.00      | k1_tops_1(sK0,X0) != X0 ),
% 3.31/1.00      inference(renaming,[status(thm)],[c_287]) ).
% 3.31/1.00  
% 3.31/1.00  cnf(c_641,plain,
% 3.31/1.00      ( v3_pre_topc(X0,sK0)
% 3.31/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 3.31/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.31/1.00      | k1_tops_1(sK0,X0) != X0
% 3.31/1.00      | sK0 != X2 ),
% 3.31/1.00      inference(resolution_lifted,[status(thm)],[c_23,c_288]) ).
% 3.31/1.00  
% 3.31/1.00  cnf(c_642,plain,
% 3.31/1.00      ( v3_pre_topc(X0,sK0)
% 3.31/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.31/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.31/1.00      | k1_tops_1(sK0,X0) != X0 ),
% 3.31/1.00      inference(unflattening,[status(thm)],[c_641]) ).
% 3.31/1.00  
% 3.31/1.00  cnf(c_743,plain,
% 3.31/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.31/1.00      | ~ sP0_iProver_split ),
% 3.31/1.00      inference(splitting,
% 3.31/1.00                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 3.31/1.00                [c_642]) ).
% 3.31/1.00  
% 3.31/1.00  cnf(c_1665,plain,
% 3.31/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.31/1.00      | ~ sP0_iProver_split ),
% 3.31/1.00      inference(instantiation,[status(thm)],[c_743]) ).
% 3.31/1.00  
% 3.31/1.00  cnf(c_1666,plain,
% 3.31/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.31/1.00      | sP0_iProver_split != iProver_top ),
% 3.31/1.00      inference(predicate_to_equality,[status(thm)],[c_1665]) ).
% 3.31/1.00  
% 3.31/1.00  cnf(c_3083,plain,
% 3.31/1.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.31/1.00      | v3_pre_topc(X0,sK1) != iProver_top
% 3.31/1.00      | k1_tops_1(sK1,X0) = X0 ),
% 3.31/1.01      inference(global_propositional_subsumption,
% 3.31/1.01                [status(thm)],
% 3.31/1.01                [c_1389,c_28,c_804,c_805,c_1666]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_3084,plain,
% 3.31/1.01      ( k1_tops_1(sK1,X0) = X0
% 3.31/1.01      | v3_pre_topc(X0,sK1) != iProver_top
% 3.31/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 3.31/1.01      inference(renaming,[status(thm)],[c_3083]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_3092,plain,
% 3.31/1.01      ( k1_tops_1(sK1,sK3) = sK3 | v3_pre_topc(sK3,sK1) != iProver_top ),
% 3.31/1.01      inference(superposition,[status(thm)],[c_1393,c_3084]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_3181,plain,
% 3.31/1.01      ( k1_tops_1(sK1,sK3) = sK3 | v6_tops_1(sK2,sK0) = iProver_top ),
% 3.31/1.01      inference(superposition,[status(thm)],[c_1394,c_3092]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_1392,plain,
% 3.31/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.31/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_9,plain,
% 3.31/1.01      ( ~ v6_tops_1(X0,X1)
% 3.31/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.31/1.01      | ~ l1_pre_topc(X1)
% 3.31/1.01      | k1_tops_1(X1,k2_pre_topc(X1,X0)) = X0 ),
% 3.31/1.01      inference(cnf_transformation,[],[f42]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_521,plain,
% 3.31/1.01      ( ~ v6_tops_1(X0,X1)
% 3.31/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.31/1.01      | k1_tops_1(X1,k2_pre_topc(X1,X0)) = X0
% 3.31/1.01      | sK0 != X1 ),
% 3.31/1.01      inference(resolution_lifted,[status(thm)],[c_9,c_23]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_522,plain,
% 3.31/1.01      ( ~ v6_tops_1(X0,sK0)
% 3.31/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.31/1.01      | k1_tops_1(sK0,k2_pre_topc(sK0,X0)) = X0 ),
% 3.31/1.01      inference(unflattening,[status(thm)],[c_521]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_1375,plain,
% 3.31/1.01      ( k1_tops_1(sK0,k2_pre_topc(sK0,X0)) = X0
% 3.31/1.01      | v6_tops_1(X0,sK0) != iProver_top
% 3.31/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.31/1.01      inference(predicate_to_equality,[status(thm)],[c_522]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_2412,plain,
% 3.31/1.01      ( k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = sK2
% 3.31/1.01      | v6_tops_1(sK2,sK0) != iProver_top ),
% 3.31/1.01      inference(superposition,[status(thm)],[c_1392,c_1375]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_3365,plain,
% 3.31/1.01      ( k1_tops_1(sK1,sK3) = sK3
% 3.31/1.01      | k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = sK2 ),
% 3.31/1.01      inference(superposition,[status(thm)],[c_3181,c_2412]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_11,plain,
% 3.31/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.31/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.31/1.01      | ~ r1_tarski(X0,X2)
% 3.31/1.01      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 3.31/1.01      | ~ l1_pre_topc(X1) ),
% 3.31/1.01      inference(cnf_transformation,[],[f45]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_503,plain,
% 3.31/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.31/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.31/1.01      | ~ r1_tarski(X0,X2)
% 3.31/1.01      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 3.31/1.01      | sK0 != X1 ),
% 3.31/1.01      inference(resolution_lifted,[status(thm)],[c_11,c_23]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_504,plain,
% 3.31/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.31/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.31/1.01      | ~ r1_tarski(X0,X1)
% 3.31/1.01      | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1)) ),
% 3.31/1.01      inference(unflattening,[status(thm)],[c_503]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_1376,plain,
% 3.31/1.01      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.31/1.01      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.31/1.01      | r1_tarski(X0,X1) != iProver_top
% 3.31/1.01      | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1)) = iProver_top ),
% 3.31/1.01      inference(predicate_to_equality,[status(thm)],[c_504]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_5,plain,
% 3.31/1.01      ( v4_tops_1(X0,X1)
% 3.31/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.31/1.01      | ~ r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
% 3.31/1.01      | ~ r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
% 3.31/1.01      | ~ l1_pre_topc(X1) ),
% 3.31/1.01      inference(cnf_transformation,[],[f41]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_581,plain,
% 3.31/1.01      ( v4_tops_1(X0,X1)
% 3.31/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.31/1.01      | ~ r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
% 3.31/1.01      | ~ r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
% 3.31/1.01      | sK0 != X1 ),
% 3.31/1.01      inference(resolution_lifted,[status(thm)],[c_5,c_23]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_582,plain,
% 3.31/1.01      ( v4_tops_1(X0,sK0)
% 3.31/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.31/1.01      | ~ r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,X0)))
% 3.31/1.01      | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X0) ),
% 3.31/1.01      inference(unflattening,[status(thm)],[c_581]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_1371,plain,
% 3.31/1.01      ( v4_tops_1(X0,sK0) = iProver_top
% 3.31/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.31/1.01      | r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,X0))) != iProver_top
% 3.31/1.01      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X0) != iProver_top ),
% 3.31/1.01      inference(predicate_to_equality,[status(thm)],[c_582]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_3189,plain,
% 3.31/1.01      ( v4_tops_1(k1_tops_1(sK0,X0),sK0) = iProver_top
% 3.31/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.31/1.01      | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.31/1.01      | m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,X0)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.31/1.01      | r1_tarski(k1_tops_1(sK0,X0),k2_pre_topc(sK0,k1_tops_1(sK0,k1_tops_1(sK0,X0)))) != iProver_top
% 3.31/1.01      | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,X0)),X0) != iProver_top ),
% 3.31/1.01      inference(superposition,[status(thm)],[c_1376,c_1371]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_3,plain,
% 3.31/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.31/1.01      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.31/1.01      | ~ l1_pre_topc(X1) ),
% 3.31/1.01      inference(cnf_transformation,[],[f37]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_611,plain,
% 3.31/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.31/1.01      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.31/1.01      | sK0 != X1 ),
% 3.31/1.01      inference(resolution_lifted,[status(thm)],[c_3,c_23]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_612,plain,
% 3.31/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.31/1.01      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.31/1.01      inference(unflattening,[status(thm)],[c_611]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_1369,plain,
% 3.31/1.01      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.31/1.01      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.31/1.01      inference(predicate_to_equality,[status(thm)],[c_612]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_4390,plain,
% 3.31/1.01      ( v4_tops_1(k1_tops_1(sK0,X0),sK0) = iProver_top
% 3.31/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.31/1.01      | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.31/1.01      | r1_tarski(k1_tops_1(sK0,X0),k2_pre_topc(sK0,k1_tops_1(sK0,k1_tops_1(sK0,X0)))) != iProver_top
% 3.31/1.01      | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,X0)),X0) != iProver_top ),
% 3.31/1.01      inference(forward_subsumption_resolution,
% 3.31/1.01                [status(thm)],
% 3.31/1.01                [c_3189,c_1369]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_4395,plain,
% 3.31/1.01      ( k1_tops_1(sK1,sK3) = sK3
% 3.31/1.01      | v4_tops_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK0) = iProver_top
% 3.31/1.01      | m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.31/1.01      | m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.31/1.01      | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK2))),k2_pre_topc(sK0,sK2)) != iProver_top
% 3.31/1.01      | r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) != iProver_top ),
% 3.31/1.01      inference(superposition,[status(thm)],[c_3365,c_4390]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_4,plain,
% 3.31/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.31/1.01      | r1_tarski(X0,k2_pre_topc(X1,X0))
% 3.31/1.01      | ~ l1_pre_topc(X1) ),
% 3.31/1.01      inference(cnf_transformation,[],[f38]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_599,plain,
% 3.31/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.31/1.01      | r1_tarski(X0,k2_pre_topc(X1,X0))
% 3.31/1.01      | sK0 != X1 ),
% 3.31/1.01      inference(resolution_lifted,[status(thm)],[c_4,c_23]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_600,plain,
% 3.31/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.31/1.01      | r1_tarski(X0,k2_pre_topc(sK0,X0)) ),
% 3.31/1.01      inference(unflattening,[status(thm)],[c_599]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_1684,plain,
% 3.31/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.31/1.01      | r1_tarski(sK2,k2_pre_topc(sK0,sK2)) ),
% 3.31/1.01      inference(instantiation,[status(thm)],[c_600]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_1685,plain,
% 3.31/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.31/1.01      | r1_tarski(sK2,k2_pre_topc(sK0,sK2)) = iProver_top ),
% 3.31/1.01      inference(predicate_to_equality,[status(thm)],[c_1684]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_3888,plain,
% 3.31/1.01      ( k1_tops_1(sK1,sK3) = sK3
% 3.31/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.31/1.01      | m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.31/1.01      | r1_tarski(X0,k2_pre_topc(sK0,sK2)) != iProver_top
% 3.31/1.01      | r1_tarski(k1_tops_1(sK0,X0),sK2) = iProver_top ),
% 3.31/1.01      inference(superposition,[status(thm)],[c_3365,c_1376]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_1678,plain,
% 3.31/1.01      ( m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.31/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.31/1.01      inference(instantiation,[status(thm)],[c_612]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_1679,plain,
% 3.31/1.01      ( m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 3.31/1.01      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.31/1.01      inference(predicate_to_equality,[status(thm)],[c_1678]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_6062,plain,
% 3.31/1.01      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.31/1.01      | k1_tops_1(sK1,sK3) = sK3
% 3.31/1.01      | r1_tarski(X0,k2_pre_topc(sK0,sK2)) != iProver_top
% 3.31/1.01      | r1_tarski(k1_tops_1(sK0,X0),sK2) = iProver_top ),
% 3.31/1.01      inference(global_propositional_subsumption,
% 3.31/1.01                [status(thm)],
% 3.31/1.01                [c_3888,c_28,c_1679]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_6063,plain,
% 3.31/1.01      ( k1_tops_1(sK1,sK3) = sK3
% 3.31/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.31/1.01      | r1_tarski(X0,k2_pre_topc(sK0,sK2)) != iProver_top
% 3.31/1.01      | r1_tarski(k1_tops_1(sK0,X0),sK2) = iProver_top ),
% 3.31/1.01      inference(renaming,[status(thm)],[c_6062]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_6072,plain,
% 3.31/1.01      ( k1_tops_1(sK1,sK3) = sK3
% 3.31/1.01      | r1_tarski(k1_tops_1(sK0,sK2),sK2) = iProver_top
% 3.31/1.01      | r1_tarski(sK2,k2_pre_topc(sK0,sK2)) != iProver_top ),
% 3.31/1.01      inference(superposition,[status(thm)],[c_1392,c_6063]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_6093,plain,
% 3.31/1.01      ( r1_tarski(k1_tops_1(sK0,sK2),sK2) = iProver_top
% 3.31/1.01      | k1_tops_1(sK1,sK3) = sK3 ),
% 3.31/1.01      inference(global_propositional_subsumption,
% 3.31/1.01                [status(thm)],
% 3.31/1.01                [c_6072,c_28,c_1685]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_6094,plain,
% 3.31/1.01      ( k1_tops_1(sK1,sK3) = sK3
% 3.31/1.01      | r1_tarski(k1_tops_1(sK0,sK2),sK2) = iProver_top ),
% 3.31/1.01      inference(renaming,[status(thm)],[c_6093]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_0,plain,
% 3.31/1.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.31/1.01      inference(cnf_transformation,[],[f36]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_1401,plain,
% 3.31/1.01      ( X0 = X1
% 3.31/1.01      | r1_tarski(X0,X1) != iProver_top
% 3.31/1.01      | r1_tarski(X1,X0) != iProver_top ),
% 3.31/1.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_6099,plain,
% 3.31/1.01      ( k1_tops_1(sK1,sK3) = sK3
% 3.31/1.01      | k1_tops_1(sK0,sK2) = sK2
% 3.31/1.01      | r1_tarski(sK2,k1_tops_1(sK0,sK2)) != iProver_top ),
% 3.31/1.01      inference(superposition,[status(thm)],[c_6094,c_1401]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_485,plain,
% 3.31/1.01      ( ~ v3_pre_topc(X0,X1)
% 3.31/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.31/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.31/1.01      | k1_tops_1(X1,X0) = X0
% 3.31/1.01      | sK0 != X1 ),
% 3.31/1.01      inference(resolution_lifted,[status(thm)],[c_313,c_23]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_486,plain,
% 3.31/1.01      ( ~ v3_pre_topc(X0,sK0)
% 3.31/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.31/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.31/1.01      | k1_tops_1(sK0,X0) = X0 ),
% 3.31/1.01      inference(unflattening,[status(thm)],[c_485]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_748,plain,
% 3.31/1.01      ( ~ v3_pre_topc(X0,sK0)
% 3.31/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.31/1.01      | k1_tops_1(sK0,X0) = X0
% 3.31/1.01      | ~ sP3_iProver_split ),
% 3.31/1.01      inference(splitting,
% 3.31/1.01                [splitting(split),new_symbols(definition,[sP3_iProver_split])],
% 3.31/1.01                [c_486]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_1378,plain,
% 3.31/1.01      ( k1_tops_1(sK0,X0) = X0
% 3.31/1.01      | v3_pre_topc(X0,sK0) != iProver_top
% 3.31/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.31/1.01      | sP3_iProver_split != iProver_top ),
% 3.31/1.01      inference(predicate_to_equality,[status(thm)],[c_748]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_749,plain,
% 3.31/1.01      ( sP3_iProver_split | sP0_iProver_split ),
% 3.31/1.01      inference(splitting,
% 3.31/1.01                [splitting(split),new_symbols(definition,[])],
% 3.31/1.01                [c_486]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_793,plain,
% 3.31/1.01      ( sP3_iProver_split = iProver_top
% 3.31/1.01      | sP0_iProver_split = iProver_top ),
% 3.31/1.01      inference(predicate_to_equality,[status(thm)],[c_749]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_794,plain,
% 3.31/1.01      ( k1_tops_1(sK0,X0) = X0
% 3.31/1.01      | v3_pre_topc(X0,sK0) != iProver_top
% 3.31/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.31/1.01      | sP3_iProver_split != iProver_top ),
% 3.31/1.01      inference(predicate_to_equality,[status(thm)],[c_748]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_2973,plain,
% 3.31/1.01      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.31/1.01      | v3_pre_topc(X0,sK0) != iProver_top
% 3.31/1.01      | k1_tops_1(sK0,X0) = X0 ),
% 3.31/1.01      inference(global_propositional_subsumption,
% 3.31/1.01                [status(thm)],
% 3.31/1.01                [c_1378,c_28,c_793,c_794,c_1666]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_2974,plain,
% 3.31/1.01      ( k1_tops_1(sK0,X0) = X0
% 3.31/1.01      | v3_pre_topc(X0,sK0) != iProver_top
% 3.31/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.31/1.01      inference(renaming,[status(thm)],[c_2973]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_2980,plain,
% 3.31/1.01      ( k1_tops_1(sK0,sK2) = sK2 | v3_pre_topc(sK2,sK0) != iProver_top ),
% 3.31/1.01      inference(superposition,[status(thm)],[c_1392,c_2974]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_10,plain,
% 3.31/1.01      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 3.31/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.31/1.01      | ~ v2_pre_topc(X0)
% 3.31/1.01      | ~ l1_pre_topc(X0) ),
% 3.31/1.01      inference(cnf_transformation,[],[f44]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_264,plain,
% 3.31/1.01      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 3.31/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.31/1.01      | ~ l1_pre_topc(X0)
% 3.31/1.01      | sK0 != X0 ),
% 3.31/1.01      inference(resolution_lifted,[status(thm)],[c_10,c_24]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_265,plain,
% 3.31/1.01      ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
% 3.31/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.31/1.01      | ~ l1_pre_topc(sK0) ),
% 3.31/1.01      inference(unflattening,[status(thm)],[c_264]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_269,plain,
% 3.31/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.31/1.01      | v3_pre_topc(k1_tops_1(sK0,X0),sK0) ),
% 3.31/1.01      inference(global_propositional_subsumption,
% 3.31/1.01                [status(thm)],
% 3.31/1.01                [c_265,c_23]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_270,plain,
% 3.31/1.01      ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
% 3.31/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.31/1.01      inference(renaming,[status(thm)],[c_269]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_1391,plain,
% 3.31/1.01      ( v3_pre_topc(k1_tops_1(sK0,X0),sK0) = iProver_top
% 3.31/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.31/1.01      inference(predicate_to_equality,[status(thm)],[c_270]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_2235,plain,
% 3.31/1.01      ( v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),sK0) = iProver_top
% 3.31/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.31/1.01      inference(superposition,[status(thm)],[c_1369,c_1391]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_3894,plain,
% 3.31/1.01      ( k1_tops_1(sK1,sK3) = sK3
% 3.31/1.01      | v3_pre_topc(sK2,sK0) = iProver_top
% 3.31/1.01      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.31/1.01      inference(superposition,[status(thm)],[c_3365,c_2235]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_6140,plain,
% 3.31/1.01      ( k1_tops_1(sK0,sK2) = sK2 | k1_tops_1(sK1,sK3) = sK3 ),
% 3.31/1.01      inference(global_propositional_subsumption,
% 3.31/1.01                [status(thm)],
% 3.31/1.01                [c_6099,c_28,c_2980,c_3894]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_6141,plain,
% 3.31/1.01      ( k1_tops_1(sK1,sK3) = sK3 | k1_tops_1(sK0,sK2) = sK2 ),
% 3.31/1.01      inference(renaming,[status(thm)],[c_6140]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_365,plain,
% 3.31/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.31/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.31/1.01      | ~ r1_tarski(X0,X2)
% 3.31/1.01      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 3.31/1.01      | sK1 != X1 ),
% 3.31/1.01      inference(resolution_lifted,[status(thm)],[c_11,c_22]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_366,plain,
% 3.31/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.31/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.31/1.01      | ~ r1_tarski(X0,X1)
% 3.31/1.01      | r1_tarski(k1_tops_1(sK1,X0),k1_tops_1(sK1,X1)) ),
% 3.31/1.01      inference(unflattening,[status(thm)],[c_365]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_1387,plain,
% 3.31/1.01      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.31/1.01      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.31/1.01      | r1_tarski(X0,X1) != iProver_top
% 3.31/1.01      | r1_tarski(k1_tops_1(sK1,X0),k1_tops_1(sK1,X1)) = iProver_top ),
% 3.31/1.01      inference(predicate_to_equality,[status(thm)],[c_366]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_6153,plain,
% 3.31/1.01      ( k1_tops_1(sK0,sK2) = sK2
% 3.31/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.31/1.01      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.31/1.01      | r1_tarski(X0,sK3) != iProver_top
% 3.31/1.01      | r1_tarski(k1_tops_1(sK1,X0),sK3) = iProver_top ),
% 3.31/1.01      inference(superposition,[status(thm)],[c_6141,c_1387]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_29,plain,
% 3.31/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 3.31/1.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_17,negated_conjecture,
% 3.31/1.01      ( ~ v6_tops_1(sK3,sK1) | v6_tops_1(sK2,sK0) ),
% 3.31/1.01      inference(cnf_transformation,[],[f55]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_32,plain,
% 3.31/1.01      ( v6_tops_1(sK3,sK1) != iProver_top
% 3.31/1.01      | v6_tops_1(sK2,sK0) = iProver_top ),
% 3.31/1.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_2,plain,
% 3.31/1.01      ( r1_tarski(X0,X0) ),
% 3.31/1.01      inference(cnf_transformation,[],[f60]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_70,plain,
% 3.31/1.01      ( r1_tarski(sK0,sK0) ),
% 3.31/1.01      inference(instantiation,[status(thm)],[c_2]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_74,plain,
% 3.31/1.01      ( ~ r1_tarski(sK0,sK0) | sK0 = sK0 ),
% 3.31/1.01      inference(instantiation,[status(thm)],[c_0]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_461,plain,
% 3.31/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.31/1.01      | r1_tarski(X0,k2_pre_topc(X1,X0))
% 3.31/1.01      | sK1 != X1 ),
% 3.31/1.01      inference(resolution_lifted,[status(thm)],[c_4,c_22]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_462,plain,
% 3.31/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.31/1.01      | r1_tarski(X0,k2_pre_topc(sK1,X0)) ),
% 3.31/1.01      inference(unflattening,[status(thm)],[c_461]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_1681,plain,
% 3.31/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.31/1.01      | r1_tarski(sK3,k2_pre_topc(sK1,sK3)) ),
% 3.31/1.01      inference(instantiation,[status(thm)],[c_462]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_1682,plain,
% 3.31/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.31/1.01      | r1_tarski(sK3,k2_pre_topc(sK1,sK3)) = iProver_top ),
% 3.31/1.01      inference(predicate_to_equality,[status(thm)],[c_1681]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_8,plain,
% 3.31/1.01      ( v6_tops_1(X0,X1)
% 3.31/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.31/1.01      | ~ l1_pre_topc(X1)
% 3.31/1.01      | k1_tops_1(X1,k2_pre_topc(X1,X0)) != X0 ),
% 3.31/1.01      inference(cnf_transformation,[],[f43]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_398,plain,
% 3.31/1.01      ( v6_tops_1(X0,X1)
% 3.31/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.31/1.01      | k1_tops_1(X1,k2_pre_topc(X1,X0)) != X0
% 3.31/1.01      | sK1 != X1 ),
% 3.31/1.01      inference(resolution_lifted,[status(thm)],[c_8,c_22]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_399,plain,
% 3.31/1.01      ( v6_tops_1(X0,sK1)
% 3.31/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.31/1.01      | k1_tops_1(sK1,k2_pre_topc(sK1,X0)) != X0 ),
% 3.31/1.01      inference(unflattening,[status(thm)],[c_398]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_1687,plain,
% 3.31/1.01      ( v6_tops_1(sK3,sK1)
% 3.31/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.31/1.01      | k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) != sK3 ),
% 3.31/1.01      inference(instantiation,[status(thm)],[c_399]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_1688,plain,
% 3.31/1.01      ( k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) != sK3
% 3.31/1.01      | v6_tops_1(sK3,sK1) = iProver_top
% 3.31/1.01      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 3.31/1.01      inference(predicate_to_equality,[status(thm)],[c_1687]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_1792,plain,
% 3.31/1.01      ( v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK0)
% 3.31/1.01      | ~ m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.31/1.01      inference(instantiation,[status(thm)],[c_270]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_1796,plain,
% 3.31/1.01      ( v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK0) = iProver_top
% 3.31/1.01      | m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.31/1.01      inference(predicate_to_equality,[status(thm)],[c_1792]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_753,plain,( X0 = X0 ),theory(equality) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_1953,plain,
% 3.31/1.01      ( sK2 = sK2 ),
% 3.31/1.01      inference(instantiation,[status(thm)],[c_753]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_18,negated_conjecture,
% 3.31/1.01      ( v6_tops_1(sK2,sK0) | v4_tops_1(sK3,sK1) ),
% 3.31/1.01      inference(cnf_transformation,[],[f54]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_1395,plain,
% 3.31/1.01      ( v6_tops_1(sK2,sK0) = iProver_top
% 3.31/1.01      | v4_tops_1(sK3,sK1) = iProver_top ),
% 3.31/1.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_2535,plain,
% 3.31/1.01      ( k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = sK2
% 3.31/1.01      | v4_tops_1(sK3,sK1) = iProver_top ),
% 3.31/1.01      inference(superposition,[status(thm)],[c_1395,c_2412]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_754,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_2125,plain,
% 3.31/1.01      ( X0 != X1 | sK2 != X1 | sK2 = X0 ),
% 3.31/1.01      inference(instantiation,[status(thm)],[c_754]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_2882,plain,
% 3.31/1.01      ( X0 != sK2 | sK2 = X0 | sK2 != sK2 ),
% 3.31/1.01      inference(instantiation,[status(thm)],[c_2125]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_4233,plain,
% 3.31/1.01      ( k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) != sK2
% 3.31/1.01      | sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2))
% 3.31/1.01      | sK2 != sK2 ),
% 3.31/1.01      inference(instantiation,[status(thm)],[c_2882]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_763,plain,
% 3.31/1.01      ( ~ v3_pre_topc(X0,X1) | v3_pre_topc(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.31/1.01      theory(equality) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_2085,plain,
% 3.31/1.01      ( v3_pre_topc(X0,X1)
% 3.31/1.01      | ~ v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK0)
% 3.31/1.01      | X0 != k1_tops_1(sK0,k2_pre_topc(sK0,sK2))
% 3.31/1.01      | X1 != sK0 ),
% 3.31/1.01      inference(instantiation,[status(thm)],[c_763]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_5853,plain,
% 3.31/1.01      ( ~ v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK0)
% 3.31/1.01      | v3_pre_topc(sK2,X0)
% 3.31/1.01      | X0 != sK0
% 3.31/1.01      | sK2 != k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) ),
% 3.31/1.01      inference(instantiation,[status(thm)],[c_2085]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_5854,plain,
% 3.31/1.01      ( X0 != sK0
% 3.31/1.01      | sK2 != k1_tops_1(sK0,k2_pre_topc(sK0,sK2))
% 3.31/1.01      | v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK0) != iProver_top
% 3.31/1.01      | v3_pre_topc(sK2,X0) = iProver_top ),
% 3.31/1.01      inference(predicate_to_equality,[status(thm)],[c_5853]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_5856,plain,
% 3.31/1.01      ( sK0 != sK0
% 3.31/1.01      | sK2 != k1_tops_1(sK0,k2_pre_topc(sK0,sK2))
% 3.31/1.01      | v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK0) != iProver_top
% 3.31/1.01      | v3_pre_topc(sK2,sK0) = iProver_top ),
% 3.31/1.01      inference(instantiation,[status(thm)],[c_5854]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_473,plain,
% 3.31/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.31/1.01      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.31/1.01      | sK1 != X1 ),
% 3.31/1.01      inference(resolution_lifted,[status(thm)],[c_3,c_22]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_474,plain,
% 3.31/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.31/1.01      | m1_subset_1(k2_pre_topc(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 3.31/1.01      inference(unflattening,[status(thm)],[c_473]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_1380,plain,
% 3.31/1.01      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.31/1.01      | m1_subset_1(k2_pre_topc(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 3.31/1.01      inference(predicate_to_equality,[status(thm)],[c_474]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_6149,plain,
% 3.31/1.01      ( k1_tops_1(sK0,sK2) = sK2
% 3.31/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.31/1.01      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.31/1.01      | r1_tarski(sK3,X0) != iProver_top
% 3.31/1.01      | r1_tarski(sK3,k1_tops_1(sK1,X0)) = iProver_top ),
% 3.31/1.01      inference(superposition,[status(thm)],[c_6141,c_1387]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_7530,plain,
% 3.31/1.01      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.31/1.01      | k1_tops_1(sK0,sK2) = sK2
% 3.31/1.01      | r1_tarski(sK3,X0) != iProver_top
% 3.31/1.01      | r1_tarski(sK3,k1_tops_1(sK1,X0)) = iProver_top ),
% 3.31/1.01      inference(global_propositional_subsumption,
% 3.31/1.01                [status(thm)],
% 3.31/1.01                [c_6149,c_29]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_7531,plain,
% 3.31/1.01      ( k1_tops_1(sK0,sK2) = sK2
% 3.31/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.31/1.01      | r1_tarski(sK3,X0) != iProver_top
% 3.31/1.01      | r1_tarski(sK3,k1_tops_1(sK1,X0)) = iProver_top ),
% 3.31/1.01      inference(renaming,[status(thm)],[c_7530]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_7541,plain,
% 3.31/1.01      ( k1_tops_1(sK0,sK2) = sK2
% 3.31/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.31/1.01      | r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,X0))) = iProver_top
% 3.31/1.01      | r1_tarski(sK3,k2_pre_topc(sK1,X0)) != iProver_top ),
% 3.31/1.01      inference(superposition,[status(thm)],[c_1380,c_7531]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_7,plain,
% 3.31/1.01      ( ~ v4_tops_1(X0,X1)
% 3.31/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.31/1.01      | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
% 3.31/1.01      | ~ l1_pre_topc(X1) ),
% 3.31/1.01      inference(cnf_transformation,[],[f39]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_413,plain,
% 3.31/1.01      ( ~ v4_tops_1(X0,X1)
% 3.31/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.31/1.01      | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
% 3.31/1.01      | sK1 != X1 ),
% 3.31/1.01      inference(resolution_lifted,[status(thm)],[c_7,c_22]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_414,plain,
% 3.31/1.01      ( ~ v4_tops_1(X0,sK1)
% 3.31/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.31/1.01      | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,X0)),X0) ),
% 3.31/1.01      inference(unflattening,[status(thm)],[c_413]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_1384,plain,
% 3.31/1.01      ( v4_tops_1(X0,sK1) != iProver_top
% 3.31/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.31/1.01      | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,X0)),X0) = iProver_top ),
% 3.31/1.01      inference(predicate_to_equality,[status(thm)],[c_414]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_2968,plain,
% 3.31/1.01      ( k1_tops_1(sK1,k2_pre_topc(sK1,X0)) = X0
% 3.31/1.01      | v4_tops_1(X0,sK1) != iProver_top
% 3.31/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.31/1.01      | r1_tarski(X0,k1_tops_1(sK1,k2_pre_topc(sK1,X0))) != iProver_top ),
% 3.31/1.01      inference(superposition,[status(thm)],[c_1384,c_1401]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_7819,plain,
% 3.31/1.01      ( k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) = sK3
% 3.31/1.01      | k1_tops_1(sK0,sK2) = sK2
% 3.31/1.01      | v4_tops_1(sK3,sK1) != iProver_top
% 3.31/1.01      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.31/1.01      | r1_tarski(sK3,k2_pre_topc(sK1,sK3)) != iProver_top ),
% 3.31/1.01      inference(superposition,[status(thm)],[c_7541,c_2968]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_7845,plain,
% 3.31/1.01      ( k1_tops_1(sK0,sK2) = sK2 ),
% 3.31/1.01      inference(global_propositional_subsumption,
% 3.31/1.01                [status(thm)],
% 3.31/1.01                [c_6153,c_28,c_29,c_32,c_70,c_74,c_1679,c_1682,c_1688,
% 3.31/1.01                 c_1796,c_1953,c_2412,c_2535,c_2980,c_4233,c_5856,c_7819]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_3896,plain,
% 3.31/1.01      ( k1_tops_1(sK1,sK3) = sK3
% 3.31/1.01      | v4_tops_1(sK2,sK0) = iProver_top
% 3.31/1.01      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.31/1.01      | r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) != iProver_top
% 3.31/1.01      | r1_tarski(sK2,sK2) != iProver_top ),
% 3.31/1.01      inference(superposition,[status(thm)],[c_3365,c_1371]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_16,negated_conjecture,
% 3.31/1.01      ( v3_pre_topc(sK3,sK1)
% 3.31/1.01      | ~ v3_pre_topc(sK2,sK0)
% 3.31/1.01      | ~ v4_tops_1(sK2,sK0) ),
% 3.31/1.01      inference(cnf_transformation,[],[f56]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_33,plain,
% 3.31/1.01      ( v3_pre_topc(sK3,sK1) = iProver_top
% 3.31/1.01      | v3_pre_topc(sK2,sK0) != iProver_top
% 3.31/1.01      | v4_tops_1(sK2,sK0) != iProver_top ),
% 3.31/1.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_1921,plain,
% 3.31/1.01      ( r1_tarski(sK2,sK2) ),
% 3.31/1.01      inference(instantiation,[status(thm)],[c_2]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_1924,plain,
% 3.31/1.01      ( r1_tarski(sK2,sK2) = iProver_top ),
% 3.31/1.01      inference(predicate_to_equality,[status(thm)],[c_1921]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_7482,plain,
% 3.31/1.01      ( r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) != iProver_top
% 3.31/1.01      | k1_tops_1(sK1,sK3) = sK3 ),
% 3.31/1.01      inference(global_propositional_subsumption,
% 3.31/1.01                [status(thm)],
% 3.31/1.01                [c_3896,c_28,c_33,c_1924,c_3092,c_3894]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_7483,plain,
% 3.31/1.01      ( k1_tops_1(sK1,sK3) = sK3
% 3.31/1.01      | r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) != iProver_top ),
% 3.31/1.01      inference(renaming,[status(thm)],[c_7482]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_7848,plain,
% 3.31/1.01      ( k1_tops_1(sK1,sK3) = sK3
% 3.31/1.01      | r1_tarski(sK2,k2_pre_topc(sK0,sK2)) != iProver_top ),
% 3.31/1.01      inference(demodulation,[status(thm)],[c_7845,c_7483]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_8506,plain,
% 3.31/1.01      ( k1_tops_1(sK1,sK3) = sK3 ),
% 3.31/1.01      inference(global_propositional_subsumption,
% 3.31/1.01                [status(thm)],
% 3.31/1.01                [c_4395,c_28,c_1685,c_7848]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_6,plain,
% 3.31/1.01      ( ~ v4_tops_1(X0,X1)
% 3.31/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.31/1.01      | r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
% 3.31/1.01      | ~ l1_pre_topc(X1) ),
% 3.31/1.01      inference(cnf_transformation,[],[f40]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_428,plain,
% 3.31/1.01      ( ~ v4_tops_1(X0,X1)
% 3.31/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.31/1.01      | r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
% 3.31/1.01      | sK1 != X1 ),
% 3.31/1.01      inference(resolution_lifted,[status(thm)],[c_6,c_22]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_429,plain,
% 3.31/1.01      ( ~ v4_tops_1(X0,sK1)
% 3.31/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.31/1.01      | r1_tarski(X0,k2_pre_topc(sK1,k1_tops_1(sK1,X0))) ),
% 3.31/1.01      inference(unflattening,[status(thm)],[c_428]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_1383,plain,
% 3.31/1.01      ( v4_tops_1(X0,sK1) != iProver_top
% 3.31/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.31/1.01      | r1_tarski(X0,k2_pre_topc(sK1,k1_tops_1(sK1,X0))) = iProver_top ),
% 3.31/1.01      inference(predicate_to_equality,[status(thm)],[c_429]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_3396,plain,
% 3.31/1.01      ( k1_tops_1(sK1,k2_pre_topc(sK1,k1_tops_1(sK1,X0))) = k1_tops_1(sK1,X0)
% 3.31/1.01      | v4_tops_1(k1_tops_1(sK1,X0),sK1) != iProver_top
% 3.31/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.31/1.01      | m1_subset_1(k1_tops_1(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.31/1.01      | m1_subset_1(k2_pre_topc(sK1,k1_tops_1(sK1,X0)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.31/1.01      | r1_tarski(X0,k2_pre_topc(sK1,k1_tops_1(sK1,X0))) != iProver_top ),
% 3.31/1.01      inference(superposition,[status(thm)],[c_1387,c_2968]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_5877,plain,
% 3.31/1.01      ( k1_tops_1(sK1,k2_pre_topc(sK1,k1_tops_1(sK1,X0))) = k1_tops_1(sK1,X0)
% 3.31/1.01      | v4_tops_1(k1_tops_1(sK1,X0),sK1) != iProver_top
% 3.31/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.31/1.01      | m1_subset_1(k1_tops_1(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.31/1.01      | r1_tarski(X0,k2_pre_topc(sK1,k1_tops_1(sK1,X0))) != iProver_top ),
% 3.31/1.01      inference(forward_subsumption_resolution,
% 3.31/1.01                [status(thm)],
% 3.31/1.01                [c_3396,c_1380]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_5881,plain,
% 3.31/1.01      ( k1_tops_1(sK1,k2_pre_topc(sK1,k1_tops_1(sK1,X0))) = k1_tops_1(sK1,X0)
% 3.31/1.01      | v4_tops_1(X0,sK1) != iProver_top
% 3.31/1.01      | v4_tops_1(k1_tops_1(sK1,X0),sK1) != iProver_top
% 3.31/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.31/1.01      | m1_subset_1(k1_tops_1(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 3.31/1.01      inference(superposition,[status(thm)],[c_1383,c_5877]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_8553,plain,
% 3.31/1.01      ( k1_tops_1(sK1,k2_pre_topc(sK1,k1_tops_1(sK1,sK3))) = k1_tops_1(sK1,sK3)
% 3.31/1.01      | v4_tops_1(k1_tops_1(sK1,sK3),sK1) != iProver_top
% 3.31/1.01      | v4_tops_1(sK3,sK1) != iProver_top
% 3.31/1.01      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 3.31/1.01      inference(superposition,[status(thm)],[c_8506,c_5881]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_8618,plain,
% 3.31/1.01      ( k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) = sK3
% 3.31/1.01      | v4_tops_1(sK3,sK1) != iProver_top
% 3.31/1.01      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 3.31/1.01      inference(light_normalisation,[status(thm)],[c_8553,c_8506]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_8644,plain,
% 3.31/1.01      ( ~ v4_tops_1(sK3,sK1)
% 3.31/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.31/1.01      | k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) = sK3 ),
% 3.31/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_8618]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_756,plain,
% 3.31/1.01      ( X0 != X1 | X2 != X3 | k2_pre_topc(X0,X2) = k2_pre_topc(X1,X3) ),
% 3.31/1.01      theory(equality) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_2196,plain,
% 3.31/1.01      ( X0 != sK0
% 3.31/1.01      | X1 != sK2
% 3.31/1.01      | k2_pre_topc(X0,X1) = k2_pre_topc(sK0,sK2) ),
% 3.31/1.01      inference(instantiation,[status(thm)],[c_756]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_6400,plain,
% 3.31/1.01      ( X0 != sK0
% 3.31/1.01      | k1_tops_1(sK0,sK2) != sK2
% 3.31/1.01      | k2_pre_topc(X0,k1_tops_1(sK0,sK2)) = k2_pre_topc(sK0,sK2) ),
% 3.31/1.01      inference(instantiation,[status(thm)],[c_2196]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_6403,plain,
% 3.31/1.01      ( k1_tops_1(sK0,sK2) != sK2
% 3.31/1.01      | k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = k2_pre_topc(sK0,sK2)
% 3.31/1.01      | sK0 != sK0 ),
% 3.31/1.01      inference(instantiation,[status(thm)],[c_6400]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_1856,plain,
% 3.31/1.01      ( ~ r1_tarski(X0,X1)
% 3.31/1.01      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK2)
% 3.31/1.01      | k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) != X0
% 3.31/1.01      | sK2 != X1 ),
% 3.31/1.01      inference(instantiation,[status(thm)],[c_755]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_2227,plain,
% 3.31/1.01      ( ~ r1_tarski(X0,sK2)
% 3.31/1.01      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK2)
% 3.31/1.01      | k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) != X0
% 3.31/1.01      | sK2 != sK2 ),
% 3.31/1.01      inference(instantiation,[status(thm)],[c_1856]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_2767,plain,
% 3.31/1.01      ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK2)
% 3.31/1.01      | ~ r1_tarski(sK2,sK2)
% 3.31/1.01      | k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) != sK2
% 3.31/1.01      | sK2 != sK2 ),
% 3.31/1.01      inference(instantiation,[status(thm)],[c_2227]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_2536,plain,
% 3.31/1.01      ( v4_tops_1(sK3,sK1) | k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = sK2 ),
% 3.31/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_2535]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_1727,plain,
% 3.31/1.01      ( v4_tops_1(sK2,sK0)
% 3.31/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.31/1.01      | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK2)
% 3.31/1.01      | ~ r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) ),
% 3.31/1.01      inference(instantiation,[status(thm)],[c_582]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_744,plain,
% 3.31/1.01      ( v3_pre_topc(X0,sK0)
% 3.31/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.31/1.01      | k1_tops_1(sK0,X0) != X0
% 3.31/1.01      | ~ sP1_iProver_split ),
% 3.31/1.01      inference(splitting,
% 3.31/1.01                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 3.31/1.01                [c_642]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_745,plain,
% 3.31/1.01      ( sP1_iProver_split | sP0_iProver_split ),
% 3.31/1.01      inference(splitting,
% 3.31/1.01                [splitting(split),new_symbols(definition,[])],
% 3.31/1.01                [c_642]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_871,plain,
% 3.31/1.01      ( k1_tops_1(sK0,X0) != X0
% 3.31/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.31/1.01      | v3_pre_topc(X0,sK0) ),
% 3.31/1.01      inference(global_propositional_subsumption,
% 3.31/1.01                [status(thm)],
% 3.31/1.01                [c_744,c_745,c_743]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_872,plain,
% 3.31/1.01      ( v3_pre_topc(X0,sK0)
% 3.31/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.31/1.01      | k1_tops_1(sK0,X0) != X0 ),
% 3.31/1.01      inference(renaming,[status(thm)],[c_871]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_878,plain,
% 3.31/1.01      ( k1_tops_1(sK0,X0) != X0
% 3.31/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.31/1.01      | v3_pre_topc(X0,sK0) ),
% 3.31/1.01      inference(global_propositional_subsumption,
% 3.31/1.01                [status(thm)],
% 3.31/1.01                [c_744,c_872]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_879,plain,
% 3.31/1.01      ( v3_pre_topc(X0,sK0)
% 3.31/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.31/1.01      | k1_tops_1(sK0,X0) != X0 ),
% 3.31/1.01      inference(renaming,[status(thm)],[c_878]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_1703,plain,
% 3.31/1.01      ( v3_pre_topc(sK2,sK0)
% 3.31/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.31/1.01      | k1_tops_1(sK0,sK2) != sK2 ),
% 3.31/1.01      inference(instantiation,[status(thm)],[c_879]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_1690,plain,
% 3.31/1.01      ( ~ v6_tops_1(sK2,sK0)
% 3.31/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.31/1.01      | k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = sK2 ),
% 3.31/1.01      inference(instantiation,[status(thm)],[c_522]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_14,negated_conjecture,
% 3.31/1.01      ( ~ v3_pre_topc(sK2,sK0)
% 3.31/1.01      | ~ v6_tops_1(sK3,sK1)
% 3.31/1.01      | ~ v4_tops_1(sK2,sK0) ),
% 3.31/1.01      inference(cnf_transformation,[],[f58]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(c_15,negated_conjecture,
% 3.31/1.01      ( ~ v3_pre_topc(sK2,sK0)
% 3.31/1.01      | v4_tops_1(sK3,sK1)
% 3.31/1.01      | ~ v4_tops_1(sK2,sK0) ),
% 3.31/1.01      inference(cnf_transformation,[],[f57]) ).
% 3.31/1.01  
% 3.31/1.01  cnf(contradiction,plain,
% 3.31/1.01      ( $false ),
% 3.31/1.01      inference(minisat,
% 3.31/1.01                [status(thm)],
% 3.31/1.01                [c_8678,c_8644,c_7845,c_6403,c_2767,c_2536,c_1953,c_1921,
% 3.31/1.01                 c_1727,c_1703,c_1690,c_1687,c_1684,c_74,c_70,c_14,c_15,
% 3.31/1.01                 c_17,c_20,c_21]) ).
% 3.31/1.01  
% 3.31/1.01  
% 3.31/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.31/1.01  
% 3.31/1.01  ------                               Statistics
% 3.31/1.01  
% 3.31/1.01  ------ General
% 3.31/1.01  
% 3.31/1.01  abstr_ref_over_cycles:                  0
% 3.31/1.01  abstr_ref_under_cycles:                 0
% 3.31/1.01  gc_basic_clause_elim:                   0
% 3.31/1.01  forced_gc_time:                         0
% 3.31/1.01  parsing_time:                           0.01
% 3.31/1.01  unif_index_cands_time:                  0.
% 3.31/1.01  unif_index_add_time:                    0.
% 3.31/1.01  orderings_time:                         0.
% 3.31/1.01  out_proof_time:                         0.016
% 3.31/1.01  total_time:                             0.455
% 3.31/1.01  num_of_symbols:                         51
% 3.31/1.01  num_of_terms:                           6184
% 3.31/1.01  
% 3.31/1.01  ------ Preprocessing
% 3.31/1.01  
% 3.31/1.01  num_of_splits:                          8
% 3.31/1.01  num_of_split_atoms:                     5
% 3.31/1.01  num_of_reused_defs:                     3
% 3.31/1.01  num_eq_ax_congr_red:                    2
% 3.31/1.01  num_of_sem_filtered_clauses:            5
% 3.31/1.01  num_of_subtypes:                        0
% 3.31/1.01  monotx_restored_types:                  0
% 3.31/1.01  sat_num_of_epr_types:                   0
% 3.31/1.01  sat_num_of_non_cyclic_types:            0
% 3.31/1.01  sat_guarded_non_collapsed_types:        0
% 3.31/1.01  num_pure_diseq_elim:                    0
% 3.31/1.01  simp_replaced_by:                       0
% 3.31/1.01  res_preprocessed:                       115
% 3.31/1.01  prep_upred:                             0
% 3.31/1.01  prep_unflattend:                        23
% 3.31/1.01  smt_new_axioms:                         0
% 3.31/1.01  pred_elim_cands:                        7
% 3.31/1.01  pred_elim:                              2
% 3.31/1.01  pred_elim_cl:                           -7
% 3.31/1.01  pred_elim_cycles:                       3
% 3.31/1.01  merged_defs:                            0
% 3.31/1.01  merged_defs_ncl:                        0
% 3.31/1.01  bin_hyper_res:                          0
% 3.31/1.01  prep_cycles:                            3
% 3.31/1.01  pred_elim_time:                         0.008
% 3.31/1.01  splitting_time:                         0.
% 3.31/1.01  sem_filter_time:                        0.
% 3.31/1.01  monotx_time:                            0.
% 3.31/1.01  subtype_inf_time:                       0.
% 3.31/1.01  
% 3.31/1.01  ------ Problem properties
% 3.31/1.01  
% 3.31/1.01  clauses:                                39
% 3.31/1.01  conjectures:                            8
% 3.31/1.01  epr:                                    12
% 3.31/1.01  horn:                                   33
% 3.31/1.01  ground:                                 12
% 3.31/1.01  unary:                                  3
% 3.31/1.01  binary:                                 16
% 3.31/1.01  lits:                                   103
% 3.31/1.01  lits_eq:                                9
% 3.31/1.01  fd_pure:                                0
% 3.31/1.01  fd_pseudo:                              0
% 3.31/1.01  fd_cond:                                0
% 3.31/1.01  fd_pseudo_cond:                         1
% 3.31/1.01  ac_symbols:                             0
% 3.31/1.01  
% 3.31/1.01  ------ Propositional Solver
% 3.31/1.01  
% 3.31/1.01  prop_solver_calls:                      25
% 3.31/1.01  prop_fast_solver_calls:                 1354
% 3.31/1.01  smt_solver_calls:                       0
% 3.31/1.01  smt_fast_solver_calls:                  0
% 3.31/1.01  prop_num_of_clauses:                    3348
% 3.31/1.01  prop_preprocess_simplified:             7374
% 3.31/1.01  prop_fo_subsumed:                       68
% 3.31/1.01  prop_solver_time:                       0.
% 3.31/1.01  smt_solver_time:                        0.
% 3.31/1.01  smt_fast_solver_time:                   0.
% 3.31/1.01  prop_fast_solver_time:                  0.
% 3.31/1.01  prop_unsat_core_time:                   0.
% 3.31/1.01  
% 3.31/1.01  ------ QBF
% 3.31/1.01  
% 3.31/1.01  qbf_q_res:                              0
% 3.31/1.01  qbf_num_tautologies:                    0
% 3.31/1.01  qbf_prep_cycles:                        0
% 3.31/1.01  
% 3.31/1.01  ------ BMC1
% 3.31/1.01  
% 3.31/1.01  bmc1_current_bound:                     -1
% 3.31/1.01  bmc1_last_solved_bound:                 -1
% 3.31/1.01  bmc1_unsat_core_size:                   -1
% 3.31/1.01  bmc1_unsat_core_parents_size:           -1
% 3.31/1.01  bmc1_merge_next_fun:                    0
% 3.31/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.31/1.01  
% 3.31/1.01  ------ Instantiation
% 3.31/1.01  
% 3.31/1.01  inst_num_of_clauses:                    1057
% 3.31/1.01  inst_num_in_passive:                    145
% 3.31/1.01  inst_num_in_active:                     588
% 3.31/1.01  inst_num_in_unprocessed:                324
% 3.31/1.01  inst_num_of_loops:                      680
% 3.31/1.01  inst_num_of_learning_restarts:          0
% 3.31/1.01  inst_num_moves_active_passive:          88
% 3.31/1.01  inst_lit_activity:                      0
% 3.31/1.01  inst_lit_activity_moves:                0
% 3.31/1.01  inst_num_tautologies:                   0
% 3.31/1.01  inst_num_prop_implied:                  0
% 3.31/1.01  inst_num_existing_simplified:           0
% 3.31/1.01  inst_num_eq_res_simplified:             0
% 3.31/1.01  inst_num_child_elim:                    0
% 3.31/1.01  inst_num_of_dismatching_blockings:      134
% 3.31/1.01  inst_num_of_non_proper_insts:           1077
% 3.31/1.01  inst_num_of_duplicates:                 0
% 3.31/1.01  inst_inst_num_from_inst_to_res:         0
% 3.31/1.01  inst_dismatching_checking_time:         0.
% 3.31/1.01  
% 3.31/1.01  ------ Resolution
% 3.31/1.01  
% 3.31/1.01  res_num_of_clauses:                     0
% 3.31/1.01  res_num_in_passive:                     0
% 3.31/1.01  res_num_in_active:                      0
% 3.31/1.01  res_num_of_loops:                       118
% 3.31/1.01  res_forward_subset_subsumed:            85
% 3.31/1.01  res_backward_subset_subsumed:           0
% 3.31/1.01  res_forward_subsumed:                   0
% 3.31/1.01  res_backward_subsumed:                  0
% 3.31/1.01  res_forward_subsumption_resolution:     0
% 3.31/1.01  res_backward_subsumption_resolution:    0
% 3.31/1.01  res_clause_to_clause_subsumption:       1004
% 3.31/1.01  res_orphan_elimination:                 0
% 3.31/1.01  res_tautology_del:                      86
% 3.31/1.01  res_num_eq_res_simplified:              0
% 3.31/1.01  res_num_sel_changes:                    0
% 3.31/1.01  res_moves_from_active_to_pass:          0
% 3.31/1.01  
% 3.31/1.01  ------ Superposition
% 3.31/1.01  
% 3.31/1.01  sup_time_total:                         0.
% 3.31/1.01  sup_time_generating:                    0.
% 3.31/1.01  sup_time_sim_full:                      0.
% 3.31/1.01  sup_time_sim_immed:                     0.
% 3.31/1.01  
% 3.31/1.01  sup_num_of_clauses:                     125
% 3.31/1.01  sup_num_in_active:                      93
% 3.31/1.01  sup_num_in_passive:                     32
% 3.31/1.01  sup_num_of_loops:                       134
% 3.31/1.01  sup_fw_superposition:                   121
% 3.31/1.01  sup_bw_superposition:                   115
% 3.31/1.01  sup_immediate_simplified:               46
% 3.31/1.01  sup_given_eliminated:                   0
% 3.31/1.01  comparisons_done:                       0
% 3.31/1.01  comparisons_avoided:                    39
% 3.31/1.01  
% 3.31/1.01  ------ Simplifications
% 3.31/1.01  
% 3.31/1.01  
% 3.31/1.01  sim_fw_subset_subsumed:                 19
% 3.31/1.01  sim_bw_subset_subsumed:                 64
% 3.31/1.01  sim_fw_subsumed:                        11
% 3.31/1.01  sim_bw_subsumed:                        1
% 3.31/1.01  sim_fw_subsumption_res:                 5
% 3.31/1.01  sim_bw_subsumption_res:                 0
% 3.31/1.01  sim_tautology_del:                      5
% 3.31/1.01  sim_eq_tautology_del:                   19
% 3.31/1.01  sim_eq_res_simp:                        0
% 3.31/1.01  sim_fw_demodulated:                     0
% 3.31/1.01  sim_bw_demodulated:                     15
% 3.31/1.01  sim_light_normalised:                   15
% 3.31/1.01  sim_joinable_taut:                      0
% 3.31/1.01  sim_joinable_simp:                      0
% 3.31/1.01  sim_ac_normalised:                      0
% 3.31/1.01  sim_smt_subsumption:                    0
% 3.31/1.01  
%------------------------------------------------------------------------------
