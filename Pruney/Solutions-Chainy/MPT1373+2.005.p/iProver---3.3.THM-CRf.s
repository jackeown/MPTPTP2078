%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:18:07 EST 2020

% Result     : Theorem 3.94s
% Output     : CNFRefutation 3.94s
% Verified   : 
% Statistics : Number of formulae       :  170 (2658 expanded)
%              Number of clauses        :  107 ( 741 expanded)
%              Number of leaves         :   22 ( 783 expanded)
%              Depth                    :   27
%              Number of atoms          :  628 (17414 expanded)
%              Number of equality atoms :  152 (2562 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( X2 = X3
                   => ( v2_compts_1(X2,X0)
                    <=> v2_compts_1(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( X2 = X3
                     => ( v2_compts_1(X2,X0)
                      <=> v2_compts_1(X3,X1) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v2_compts_1(X2,X0)
                  <~> v2_compts_1(X3,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v2_compts_1(X2,X0)
                  <~> v2_compts_1(X3,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v2_compts_1(X3,X1)
                    | ~ v2_compts_1(X2,X0) )
                  & ( v2_compts_1(X3,X1)
                    | v2_compts_1(X2,X0) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v2_compts_1(X3,X1)
                    | ~ v2_compts_1(X2,X0) )
                  & ( v2_compts_1(X3,X1)
                    | v2_compts_1(X2,X0) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ~ v2_compts_1(X3,X1)
            | ~ v2_compts_1(X2,X0) )
          & ( v2_compts_1(X3,X1)
            | v2_compts_1(X2,X0) )
          & X2 = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ( ~ v2_compts_1(sK5,X1)
          | ~ v2_compts_1(X2,X0) )
        & ( v2_compts_1(sK5,X1)
          | v2_compts_1(X2,X0) )
        & sK5 = X2
        & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ( ~ v2_compts_1(X3,X1)
                | ~ v2_compts_1(X2,X0) )
              & ( v2_compts_1(X3,X1)
                | v2_compts_1(X2,X0) )
              & X2 = X3
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X3] :
            ( ( ~ v2_compts_1(X3,X1)
              | ~ v2_compts_1(sK4,X0) )
            & ( v2_compts_1(X3,X1)
              | v2_compts_1(sK4,X0) )
            & sK4 = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v2_compts_1(X3,X1)
                    | ~ v2_compts_1(X2,X0) )
                  & ( v2_compts_1(X3,X1)
                    | v2_compts_1(X2,X0) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_pre_topc(X1,X0) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ( ~ v2_compts_1(X3,sK3)
                  | ~ v2_compts_1(X2,X0) )
                & ( v2_compts_1(X3,sK3)
                  | v2_compts_1(X2,X0) )
                & X2 = X3
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_pre_topc(sK3,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ v2_compts_1(X3,X1)
                      | ~ v2_compts_1(X2,X0) )
                    & ( v2_compts_1(X3,X1)
                      | v2_compts_1(X2,X0) )
                    & X2 = X3
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_pre_topc(X1,X0) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v2_compts_1(X3,X1)
                    | ~ v2_compts_1(X2,sK2) )
                  & ( v2_compts_1(X3,X1)
                    | v2_compts_1(X2,sK2) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
          & m1_pre_topc(X1,sK2) )
      & l1_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ( ~ v2_compts_1(sK5,sK3)
      | ~ v2_compts_1(sK4,sK2) )
    & ( v2_compts_1(sK5,sK3)
      | v2_compts_1(sK4,sK2) )
    & sK4 = sK5
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    & m1_pre_topc(sK3,sK2)
    & l1_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f36,f40,f39,f38,f37])).

fof(f63,plain,(
    sK4 = sK5 ),
    inference(cnf_transformation,[],[f41])).

fof(f61,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f41])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X2,k2_struct_0(X1))
               => ( v2_compts_1(X2,X0)
                <=> ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                     => ( X2 = X3
                       => v2_compts_1(X3,X1) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_compts_1(X2,X0)
              <=> ! [X3] :
                    ( v2_compts_1(X3,X1)
                    | X2 != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ r1_tarski(X2,k2_struct_0(X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_compts_1(X2,X0)
              <=> ! [X3] :
                    ( v2_compts_1(X3,X1)
                    | X2 != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ r1_tarski(X2,k2_struct_0(X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v2_compts_1(X2,X0)
                  | ? [X3] :
                      ( ~ v2_compts_1(X3,X1)
                      & X2 = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X3] :
                      ( v2_compts_1(X3,X1)
                      | X2 != X3
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v2_compts_1(X2,X0) ) )
              | ~ r1_tarski(X2,k2_struct_0(X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v2_compts_1(X2,X0)
                  | ? [X3] :
                      ( ~ v2_compts_1(X3,X1)
                      & X2 = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v2_compts_1(X4,X1)
                      | X2 != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v2_compts_1(X2,X0) ) )
              | ~ r1_tarski(X2,k2_struct_0(X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f31])).

fof(f33,plain,(
    ! [X2,X1] :
      ( ? [X3] :
          ( ~ v2_compts_1(X3,X1)
          & X2 = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v2_compts_1(sK1(X1,X2),X1)
        & sK1(X1,X2) = X2
        & m1_subset_1(sK1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v2_compts_1(X2,X0)
                  | ( ~ v2_compts_1(sK1(X1,X2),X1)
                    & sK1(X1,X2) = X2
                    & m1_subset_1(sK1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v2_compts_1(X4,X1)
                      | X2 != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v2_compts_1(X2,X0) ) )
              | ~ r1_tarski(X2,k2_struct_0(X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f32,f33])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v2_compts_1(X2,X0)
      | ~ v2_compts_1(sK1(X1,X2),X1)
      | ~ r1_tarski(X2,k2_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f60,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f59,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f65,plain,
    ( ~ v2_compts_1(sK5,sK3)
    | ~ v2_compts_1(sK4,sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f55,plain,(
    ! [X4,X2,X0,X1] :
      ( v2_compts_1(X4,X1)
      | X2 != X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_compts_1(X2,X0)
      | ~ r1_tarski(X2,k2_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f66,plain,(
    ! [X4,X0,X1] :
      ( v2_compts_1(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_compts_1(X4,X0)
      | ~ r1_tarski(X4,k2_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f55])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f62,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f41])).

fof(f64,plain,
    ( v2_compts_1(sK5,sK3)
    | v2_compts_1(sK4,sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f2,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_pre_topc(X0,X1) = k2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_pre_topc(X0,X1) = k2_struct_0(X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_pre_topc(X0,X1) != k2_struct_0(X0) )
            & ( k2_pre_topc(X0,X1) = k2_struct_0(X0)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_struct_0(X0)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f47,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ? [X1] :
          ( v1_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( v1_tops_1(sK0(X0),X0)
        & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_tops_1(sK0(X0),X0)
        & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f29])).

fof(f52,plain,(
    ! [X0] :
      ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f53,plain,(
    ! [X0] :
      ( v1_tops_1(sK0(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v1_tops_1(X1,X0) )
               => v1_tops_1(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v1_tops_1(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ v1_tops_1(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v1_tops_1(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ v1_tops_1(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v1_tops_1(X2,X0)
      | ~ r1_tarski(X1,X2)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v2_compts_1(X2,X0)
      | sK1(X1,X2) = X2
      | ~ r1_tarski(X2,k2_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_19,negated_conjecture,
    ( sK4 = sK5 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1273,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_13,plain,
    ( v2_compts_1(X0,X1)
    | ~ v2_compts_1(sK1(X2,X0),X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,k2_struct_0(X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_22,negated_conjecture,
    ( m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_396,plain,
    ( v2_compts_1(X0,X1)
    | ~ v2_compts_1(sK1(X2,X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,k2_struct_0(X2))
    | ~ l1_pre_topc(X1)
    | sK2 != X1
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_22])).

cnf(c_397,plain,
    ( v2_compts_1(X0,sK2)
    | ~ v2_compts_1(sK1(sK3,X0),sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X0,k2_struct_0(sK3))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_396])).

cnf(c_23,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_401,plain,
    ( ~ r1_tarski(X0,k2_struct_0(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_compts_1(sK1(sK3,X0),sK3)
    | v2_compts_1(X0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_397,c_23])).

cnf(c_402,plain,
    ( v2_compts_1(X0,sK2)
    | ~ v2_compts_1(sK1(sK3,X0),sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X0,k2_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_401])).

cnf(c_1268,plain,
    ( v2_compts_1(X0,sK2) = iProver_top
    | v2_compts_1(sK1(sK3,X0),sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(X0,k2_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_402])).

cnf(c_4797,plain,
    ( v2_compts_1(sK1(sK3,sK4),sK3) != iProver_top
    | v2_compts_1(sK4,sK2) = iProver_top
    | r1_tarski(sK4,k2_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1273,c_1268])).

cnf(c_17,negated_conjecture,
    ( ~ v2_compts_1(sK4,sK2)
    | ~ v2_compts_1(sK5,sK3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_29,plain,
    ( v2_compts_1(sK4,sK2) != iProver_top
    | v2_compts_1(sK5,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_16,plain,
    ( ~ v2_compts_1(X0,X1)
    | v2_compts_1(X0,X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,k2_struct_0(X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_324,plain,
    ( ~ v2_compts_1(X0,X1)
    | v2_compts_1(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(X0,k2_struct_0(X2))
    | ~ l1_pre_topc(X1)
    | sK2 != X1
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_22])).

cnf(c_325,plain,
    ( ~ v2_compts_1(X0,sK2)
    | v2_compts_1(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(X0,k2_struct_0(sK3))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_324])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_295,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | sK2 != X2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_22])).

cnf(c_296,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_295])).

cnf(c_300,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_296,c_23])).

cnf(c_301,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(renaming,[status(thm)],[c_300])).

cnf(c_329,plain,
    ( ~ r1_tarski(X0,k2_struct_0(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_compts_1(X0,sK2)
    | v2_compts_1(X0,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_325,c_23,c_296])).

cnf(c_330,plain,
    ( ~ v2_compts_1(X0,sK2)
    | v2_compts_1(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(X0,k2_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_329])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_4438,plain,
    ( ~ v2_compts_1(sK5,sK2)
    | v2_compts_1(sK5,sK3)
    | ~ r1_tarski(sK5,k2_struct_0(sK3)) ),
    inference(resolution,[status(thm)],[c_330,c_20])).

cnf(c_18,negated_conjecture,
    ( v2_compts_1(sK4,sK2)
    | v2_compts_1(sK5,sK3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1275,plain,
    ( v2_compts_1(sK4,sK2) = iProver_top
    | v2_compts_1(sK5,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1662,plain,
    ( v2_compts_1(sK5,sK2) = iProver_top
    | v2_compts_1(sK5,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_19,c_1275])).

cnf(c_1663,plain,
    ( v2_compts_1(sK5,sK2)
    | v2_compts_1(sK5,sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1662])).

cnf(c_4550,plain,
    ( v2_compts_1(sK5,sK3)
    | ~ r1_tarski(sK5,k2_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4438,c_1663])).

cnf(c_4552,plain,
    ( v2_compts_1(sK5,sK3) = iProver_top
    | r1_tarski(sK5,k2_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4550])).

cnf(c_1274,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1277,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1793,plain,
    ( r1_tarski(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1274,c_1277])).

cnf(c_1,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_2,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1279,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_9,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_313,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK2 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_22])).

cnf(c_314,plain,
    ( ~ l1_pre_topc(sK2)
    | l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_313])).

cnf(c_316,plain,
    ( l1_pre_topc(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_314,c_23])).

cnf(c_553,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,X0) = k2_struct_0(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_316])).

cnf(c_554,plain,
    ( ~ v1_tops_1(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | k2_pre_topc(sK3,X0) = k2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_553])).

cnf(c_1258,plain,
    ( k2_pre_topc(sK3,X0) = k2_struct_0(sK3)
    | v1_tops_1(X0,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_554])).

cnf(c_1712,plain,
    ( k2_pre_topc(sK3,k2_subset_1(u1_struct_0(sK3))) = k2_struct_0(sK3)
    | v1_tops_1(k2_subset_1(u1_struct_0(sK3)),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1279,c_1258])).

cnf(c_11,plain,
    ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_459,plain,
    ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_316])).

cnf(c_460,plain,
    ( m1_subset_1(sK0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(unflattening,[status(thm)],[c_459])).

cnf(c_10,plain,
    ( v1_tops_1(sK0(X0),X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_466,plain,
    ( v1_tops_1(sK0(X0),X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_316])).

cnf(c_467,plain,
    ( v1_tops_1(sK0(sK3),sK3) ),
    inference(unflattening,[status(thm)],[c_466])).

cnf(c_1413,plain,
    ( m1_subset_1(k2_subset_1(u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1715,plain,
    ( ~ v1_tops_1(k2_subset_1(u1_struct_0(sK3)),sK3)
    | k2_pre_topc(sK3,k2_subset_1(u1_struct_0(sK3))) = k2_struct_0(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1712])).

cnf(c_638,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1969,plain,
    ( sK0(sK3) = sK0(sK3) ),
    inference(instantiation,[status(thm)],[c_638])).

cnf(c_641,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_2039,plain,
    ( X0 != u1_struct_0(sK3)
    | k1_zfmisc_1(X0) = k1_zfmisc_1(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_641])).

cnf(c_2342,plain,
    ( k1_zfmisc_1(k2_subset_1(u1_struct_0(sK3))) = k1_zfmisc_1(u1_struct_0(sK3))
    | k2_subset_1(u1_struct_0(sK3)) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2039])).

cnf(c_2343,plain,
    ( k2_subset_1(u1_struct_0(sK3)) = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_12,plain,
    ( ~ v1_tops_1(X0,X1)
    | v1_tops_1(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_534,plain,
    ( ~ v1_tops_1(X0,X1)
    | v1_tops_1(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_316])).

cnf(c_535,plain,
    ( ~ v1_tops_1(X0,sK3)
    | v1_tops_1(X1,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(X0,X1) ),
    inference(unflattening,[status(thm)],[c_534])).

cnf(c_1887,plain,
    ( v1_tops_1(X0,sK3)
    | ~ v1_tops_1(sK0(sK3),sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(sK0(sK3),X0) ),
    inference(instantiation,[status(thm)],[c_535])).

cnf(c_2572,plain,
    ( ~ v1_tops_1(sK0(sK3),sK3)
    | v1_tops_1(k2_subset_1(u1_struct_0(sK3)),sK3)
    | ~ m1_subset_1(sK0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k2_subset_1(u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(sK0(sK3),k2_subset_1(u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_1887])).

cnf(c_642,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1494,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | X0 != sK0(sK3)
    | X1 != k1_zfmisc_1(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_642])).

cnf(c_1968,plain,
    ( m1_subset_1(sK0(sK3),X0)
    | ~ m1_subset_1(sK0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | X0 != k1_zfmisc_1(u1_struct_0(sK3))
    | sK0(sK3) != sK0(sK3) ),
    inference(instantiation,[status(thm)],[c_1494])).

cnf(c_3209,plain,
    ( ~ m1_subset_1(sK0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(sK0(sK3),k1_zfmisc_1(k2_subset_1(u1_struct_0(sK3))))
    | sK0(sK3) != sK0(sK3)
    | k1_zfmisc_1(k2_subset_1(u1_struct_0(sK3))) != k1_zfmisc_1(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1968])).

cnf(c_3311,plain,
    ( ~ m1_subset_1(sK0(sK3),k1_zfmisc_1(k2_subset_1(u1_struct_0(sK3))))
    | r1_tarski(sK0(sK3),k2_subset_1(u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_4930,plain,
    ( k2_pre_topc(sK3,k2_subset_1(u1_struct_0(sK3))) = k2_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1712,c_460,c_467,c_1413,c_1715,c_1969,c_2342,c_2343,c_2572,c_3209,c_3311])).

cnf(c_4932,plain,
    ( k2_pre_topc(sK3,u1_struct_0(sK3)) = k2_struct_0(sK3) ),
    inference(superposition,[status(thm)],[c_1,c_4930])).

cnf(c_1515,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_1279])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_583,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_316])).

cnf(c_584,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | r1_tarski(X0,k2_pre_topc(sK3,X0)) ),
    inference(unflattening,[status(thm)],[c_583])).

cnf(c_1256,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK3,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_584])).

cnf(c_1522,plain,
    ( r1_tarski(u1_struct_0(sK3),k2_pre_topc(sK3,u1_struct_0(sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1515,c_1256])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1280,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2604,plain,
    ( r1_tarski(X0,k2_pre_topc(sK3,u1_struct_0(sK3))) = iProver_top
    | r1_tarski(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1522,c_1280])).

cnf(c_5063,plain,
    ( r1_tarski(X0,k2_struct_0(sK3)) = iProver_top
    | r1_tarski(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4932,c_2604])).

cnf(c_5305,plain,
    ( r1_tarski(sK5,k2_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1793,c_5063])).

cnf(c_11346,plain,
    ( v2_compts_1(sK1(sK3,sK4),sK3) != iProver_top
    | r1_tarski(sK4,k2_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4797,c_29,c_4552,c_5305])).

cnf(c_11351,plain,
    ( v2_compts_1(sK1(sK3,sK5),sK3) != iProver_top
    | r1_tarski(sK4,k2_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_19,c_11346])).

cnf(c_1990,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_638])).

cnf(c_648,plain,
    ( ~ v2_compts_1(X0,X1)
    | v2_compts_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2976,plain,
    ( v2_compts_1(X0,X1)
    | ~ v2_compts_1(sK5,sK3)
    | X1 != sK3
    | X0 != sK5 ),
    inference(instantiation,[status(thm)],[c_648])).

cnf(c_3378,plain,
    ( v2_compts_1(X0,sK3)
    | ~ v2_compts_1(sK5,sK3)
    | X0 != sK5
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2976])).

cnf(c_5839,plain,
    ( v2_compts_1(sK4,sK3)
    | ~ v2_compts_1(sK5,sK3)
    | sK4 != sK5
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_3378])).

cnf(c_5840,plain,
    ( sK4 != sK5
    | sK3 != sK3
    | v2_compts_1(sK4,sK3) = iProver_top
    | v2_compts_1(sK5,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5839])).

cnf(c_14,plain,
    ( v2_compts_1(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,k2_struct_0(X2))
    | ~ l1_pre_topc(X1)
    | sK1(X2,X0) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_372,plain,
    ( v2_compts_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,k2_struct_0(X2))
    | ~ l1_pre_topc(X1)
    | sK1(X2,X0) = X0
    | sK2 != X1
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_22])).

cnf(c_373,plain,
    ( v2_compts_1(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X0,k2_struct_0(sK3))
    | ~ l1_pre_topc(sK2)
    | sK1(sK3,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_372])).

cnf(c_377,plain,
    ( ~ r1_tarski(X0,k2_struct_0(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_compts_1(X0,sK2)
    | sK1(sK3,X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_373,c_23])).

cnf(c_378,plain,
    ( v2_compts_1(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X0,k2_struct_0(sK3))
    | sK1(sK3,X0) = X0 ),
    inference(renaming,[status(thm)],[c_377])).

cnf(c_1269,plain,
    ( sK1(sK3,X0) = X0
    | v2_compts_1(X0,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(X0,k2_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_378])).

cnf(c_5291,plain,
    ( sK1(sK3,sK4) = sK4
    | v2_compts_1(sK4,sK2) = iProver_top
    | r1_tarski(sK4,k2_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1273,c_1269])).

cnf(c_7810,plain,
    ( sK1(sK3,sK4) = sK4
    | r1_tarski(sK4,k2_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5291,c_29,c_4552,c_5305])).

cnf(c_7814,plain,
    ( sK1(sK3,sK4) = sK4
    | r1_tarski(sK5,k2_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_19,c_7810])).

cnf(c_7950,plain,
    ( sK1(sK3,sK4) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7814,c_5305])).

cnf(c_11350,plain,
    ( v2_compts_1(sK4,sK3) != iProver_top
    | r1_tarski(sK4,k2_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7950,c_11346])).

cnf(c_11355,plain,
    ( r1_tarski(sK4,k2_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11351,c_19,c_1990,c_4552,c_5305,c_5840,c_11350])).

cnf(c_11359,plain,
    ( r1_tarski(sK5,k2_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_19,c_11355])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11359,c_5305])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:52:33 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.94/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.94/0.99  
% 3.94/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.94/0.99  
% 3.94/0.99  ------  iProver source info
% 3.94/0.99  
% 3.94/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.94/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.94/0.99  git: non_committed_changes: false
% 3.94/0.99  git: last_make_outside_of_git: false
% 3.94/0.99  
% 3.94/0.99  ------ 
% 3.94/0.99  ------ Parsing...
% 3.94/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.94/0.99  
% 3.94/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 3.94/0.99  
% 3.94/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.94/0.99  
% 3.94/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.94/0.99  ------ Proving...
% 3.94/0.99  ------ Problem Properties 
% 3.94/0.99  
% 3.94/0.99  
% 3.94/0.99  clauses                                 27
% 3.94/0.99  conjectures                             5
% 3.94/0.99  EPR                                     4
% 3.94/0.99  Horn                                    24
% 3.94/0.99  unary                                   9
% 3.94/0.99  binary                                  7
% 3.94/0.99  lits                                    64
% 3.94/0.99  lits eq                                 7
% 3.94/0.99  fd_pure                                 0
% 3.94/0.99  fd_pseudo                               0
% 3.94/0.99  fd_cond                                 0
% 3.94/0.99  fd_pseudo_cond                          0
% 3.94/0.99  AC symbols                              0
% 3.94/0.99  
% 3.94/0.99  ------ Input Options Time Limit: Unbounded
% 3.94/0.99  
% 3.94/0.99  
% 3.94/0.99  ------ 
% 3.94/0.99  Current options:
% 3.94/0.99  ------ 
% 3.94/0.99  
% 3.94/0.99  
% 3.94/0.99  
% 3.94/0.99  
% 3.94/0.99  ------ Proving...
% 3.94/0.99  
% 3.94/0.99  
% 3.94/0.99  % SZS status Theorem for theBenchmark.p
% 3.94/0.99  
% 3.94/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.94/0.99  
% 3.94/0.99  fof(f12,conjecture,(
% 3.94/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (X2 = X3 => (v2_compts_1(X2,X0) <=> v2_compts_1(X3,X1)))))))),
% 3.94/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.94/0.99  
% 3.94/0.99  fof(f13,negated_conjecture,(
% 3.94/0.99    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (X2 = X3 => (v2_compts_1(X2,X0) <=> v2_compts_1(X3,X1)))))))),
% 3.94/0.99    inference(negated_conjecture,[],[f12])).
% 3.94/0.99  
% 3.94/0.99  fof(f25,plain,(
% 3.94/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((v2_compts_1(X2,X0) <~> v2_compts_1(X3,X1)) & X2 = X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 3.94/0.99    inference(ennf_transformation,[],[f13])).
% 3.94/0.99  
% 3.94/0.99  fof(f26,plain,(
% 3.94/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((v2_compts_1(X2,X0) <~> v2_compts_1(X3,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 3.94/0.99    inference(flattening,[],[f25])).
% 3.94/0.99  
% 3.94/0.99  fof(f35,plain,(
% 3.94/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~v2_compts_1(X3,X1) | ~v2_compts_1(X2,X0)) & (v2_compts_1(X3,X1) | v2_compts_1(X2,X0))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 3.94/0.99    inference(nnf_transformation,[],[f26])).
% 3.94/0.99  
% 3.94/0.99  fof(f36,plain,(
% 3.94/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v2_compts_1(X3,X1) | ~v2_compts_1(X2,X0)) & (v2_compts_1(X3,X1) | v2_compts_1(X2,X0)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 3.94/0.99    inference(flattening,[],[f35])).
% 3.94/0.99  
% 3.94/0.99  fof(f40,plain,(
% 3.94/0.99    ( ! [X2,X0,X1] : (? [X3] : ((~v2_compts_1(X3,X1) | ~v2_compts_1(X2,X0)) & (v2_compts_1(X3,X1) | v2_compts_1(X2,X0)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => ((~v2_compts_1(sK5,X1) | ~v2_compts_1(X2,X0)) & (v2_compts_1(sK5,X1) | v2_compts_1(X2,X0)) & sK5 = X2 & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X1))))) )),
% 3.94/0.99    introduced(choice_axiom,[])).
% 3.94/0.99  
% 3.94/0.99  fof(f39,plain,(
% 3.94/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : ((~v2_compts_1(X3,X1) | ~v2_compts_1(X2,X0)) & (v2_compts_1(X3,X1) | v2_compts_1(X2,X0)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X3] : ((~v2_compts_1(X3,X1) | ~v2_compts_1(sK4,X0)) & (v2_compts_1(X3,X1) | v2_compts_1(sK4,X0)) & sK4 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.94/0.99    introduced(choice_axiom,[])).
% 3.94/0.99  
% 3.94/0.99  fof(f38,plain,(
% 3.94/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v2_compts_1(X3,X1) | ~v2_compts_1(X2,X0)) & (v2_compts_1(X3,X1) | v2_compts_1(X2,X0)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_pre_topc(X1,X0)) => (? [X2] : (? [X3] : ((~v2_compts_1(X3,sK3) | ~v2_compts_1(X2,X0)) & (v2_compts_1(X3,sK3) | v2_compts_1(X2,X0)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_pre_topc(sK3,X0))) )),
% 3.94/0.99    introduced(choice_axiom,[])).
% 3.94/0.99  
% 3.94/0.99  fof(f37,plain,(
% 3.94/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v2_compts_1(X3,X1) | ~v2_compts_1(X2,X0)) & (v2_compts_1(X3,X1) | v2_compts_1(X2,X0)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~v2_compts_1(X3,X1) | ~v2_compts_1(X2,sK2)) & (v2_compts_1(X3,X1) | v2_compts_1(X2,sK2)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_pre_topc(X1,sK2)) & l1_pre_topc(sK2))),
% 3.94/0.99    introduced(choice_axiom,[])).
% 3.94/0.99  
% 3.94/0.99  fof(f41,plain,(
% 3.94/0.99    ((((~v2_compts_1(sK5,sK3) | ~v2_compts_1(sK4,sK2)) & (v2_compts_1(sK5,sK3) | v2_compts_1(sK4,sK2)) & sK4 = sK5 & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_pre_topc(sK3,sK2)) & l1_pre_topc(sK2)),
% 3.94/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f36,f40,f39,f38,f37])).
% 3.94/0.99  
% 3.94/0.99  fof(f63,plain,(
% 3.94/0.99    sK4 = sK5),
% 3.94/0.99    inference(cnf_transformation,[],[f41])).
% 3.94/0.99  
% 3.94/0.99  fof(f61,plain,(
% 3.94/0.99    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))),
% 3.94/0.99    inference(cnf_transformation,[],[f41])).
% 3.94/0.99  
% 3.94/0.99  fof(f11,axiom,(
% 3.94/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X2,k2_struct_0(X1)) => (v2_compts_1(X2,X0) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (X2 = X3 => v2_compts_1(X3,X1))))))))),
% 3.94/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.94/0.99  
% 3.94/0.99  fof(f23,plain,(
% 3.94/0.99    ! [X0] : (! [X1] : (! [X2] : (((v2_compts_1(X2,X0) <=> ! [X3] : ((v2_compts_1(X3,X1) | X2 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~r1_tarski(X2,k2_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.94/0.99    inference(ennf_transformation,[],[f11])).
% 3.94/0.99  
% 3.94/0.99  fof(f24,plain,(
% 3.94/0.99    ! [X0] : (! [X1] : (! [X2] : ((v2_compts_1(X2,X0) <=> ! [X3] : (v2_compts_1(X3,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.94/0.99    inference(flattening,[],[f23])).
% 3.94/0.99  
% 3.94/0.99  fof(f31,plain,(
% 3.94/0.99    ! [X0] : (! [X1] : (! [X2] : (((v2_compts_1(X2,X0) | ? [X3] : (~v2_compts_1(X3,X1) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (v2_compts_1(X3,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_compts_1(X2,X0))) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.94/0.99    inference(nnf_transformation,[],[f24])).
% 3.94/0.99  
% 3.94/0.99  fof(f32,plain,(
% 3.94/0.99    ! [X0] : (! [X1] : (! [X2] : (((v2_compts_1(X2,X0) | ? [X3] : (~v2_compts_1(X3,X1) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v2_compts_1(X4,X1) | X2 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_compts_1(X2,X0))) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.94/0.99    inference(rectify,[],[f31])).
% 3.94/0.99  
% 3.94/0.99  fof(f33,plain,(
% 3.94/0.99    ! [X2,X1] : (? [X3] : (~v2_compts_1(X3,X1) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => (~v2_compts_1(sK1(X1,X2),X1) & sK1(X1,X2) = X2 & m1_subset_1(sK1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))))),
% 3.94/0.99    introduced(choice_axiom,[])).
% 3.94/0.99  
% 3.94/0.99  fof(f34,plain,(
% 3.94/0.99    ! [X0] : (! [X1] : (! [X2] : (((v2_compts_1(X2,X0) | (~v2_compts_1(sK1(X1,X2),X1) & sK1(X1,X2) = X2 & m1_subset_1(sK1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v2_compts_1(X4,X1) | X2 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_compts_1(X2,X0))) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.94/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f32,f33])).
% 3.94/0.99  
% 3.94/0.99  fof(f58,plain,(
% 3.94/0.99    ( ! [X2,X0,X1] : (v2_compts_1(X2,X0) | ~v2_compts_1(sK1(X1,X2),X1) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.94/0.99    inference(cnf_transformation,[],[f34])).
% 3.94/0.99  
% 3.94/0.99  fof(f60,plain,(
% 3.94/0.99    m1_pre_topc(sK3,sK2)),
% 3.94/0.99    inference(cnf_transformation,[],[f41])).
% 3.94/0.99  
% 3.94/0.99  fof(f59,plain,(
% 3.94/0.99    l1_pre_topc(sK2)),
% 3.94/0.99    inference(cnf_transformation,[],[f41])).
% 3.94/0.99  
% 3.94/0.99  fof(f65,plain,(
% 3.94/0.99    ~v2_compts_1(sK5,sK3) | ~v2_compts_1(sK4,sK2)),
% 3.94/0.99    inference(cnf_transformation,[],[f41])).
% 3.94/0.99  
% 3.94/0.99  fof(f55,plain,(
% 3.94/0.99    ( ! [X4,X2,X0,X1] : (v2_compts_1(X4,X1) | X2 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v2_compts_1(X2,X0) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.94/0.99    inference(cnf_transformation,[],[f34])).
% 3.94/0.99  
% 3.94/0.99  fof(f66,plain,(
% 3.94/0.99    ( ! [X4,X0,X1] : (v2_compts_1(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v2_compts_1(X4,X0) | ~r1_tarski(X4,k2_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.94/0.99    inference(equality_resolution,[],[f55])).
% 3.94/0.99  
% 3.94/0.99  fof(f6,axiom,(
% 3.94/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 3.94/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.94/0.99  
% 3.94/0.99  fof(f17,plain,(
% 3.94/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.94/0.99    inference(ennf_transformation,[],[f6])).
% 3.94/0.99  
% 3.94/0.99  fof(f48,plain,(
% 3.94/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.94/0.99    inference(cnf_transformation,[],[f17])).
% 3.94/0.99  
% 3.94/0.99  fof(f62,plain,(
% 3.94/0.99    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))),
% 3.94/0.99    inference(cnf_transformation,[],[f41])).
% 3.94/0.99  
% 3.94/0.99  fof(f64,plain,(
% 3.94/0.99    v2_compts_1(sK5,sK3) | v2_compts_1(sK4,sK2)),
% 3.94/0.99    inference(cnf_transformation,[],[f41])).
% 3.94/0.99  
% 3.94/0.99  fof(f4,axiom,(
% 3.94/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.94/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.94/0.99  
% 3.94/0.99  fof(f27,plain,(
% 3.94/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.94/0.99    inference(nnf_transformation,[],[f4])).
% 3.94/0.99  
% 3.94/0.99  fof(f45,plain,(
% 3.94/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.94/0.99    inference(cnf_transformation,[],[f27])).
% 3.94/0.99  
% 3.94/0.99  fof(f2,axiom,(
% 3.94/0.99    ! [X0] : k2_subset_1(X0) = X0),
% 3.94/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.94/0.99  
% 3.94/0.99  fof(f43,plain,(
% 3.94/0.99    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 3.94/0.99    inference(cnf_transformation,[],[f2])).
% 3.94/0.99  
% 3.94/0.99  fof(f3,axiom,(
% 3.94/0.99    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 3.94/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.94/0.99  
% 3.94/0.99  fof(f44,plain,(
% 3.94/0.99    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 3.94/0.99    inference(cnf_transformation,[],[f3])).
% 3.94/0.99  
% 3.94/0.99  fof(f8,axiom,(
% 3.94/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_pre_topc(X0,X1) = k2_struct_0(X0))))),
% 3.94/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.94/0.99  
% 3.94/0.99  fof(f19,plain,(
% 3.94/0.99    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_pre_topc(X0,X1) = k2_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.94/0.99    inference(ennf_transformation,[],[f8])).
% 3.94/0.99  
% 3.94/0.99  fof(f28,plain,(
% 3.94/0.99    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_pre_topc(X0,X1) != k2_struct_0(X0)) & (k2_pre_topc(X0,X1) = k2_struct_0(X0) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.94/0.99    inference(nnf_transformation,[],[f19])).
% 3.94/0.99  
% 3.94/0.99  fof(f50,plain,(
% 3.94/0.99    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_struct_0(X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.94/0.99    inference(cnf_transformation,[],[f28])).
% 3.94/0.99  
% 3.94/0.99  fof(f5,axiom,(
% 3.94/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.94/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.94/0.99  
% 3.94/0.99  fof(f16,plain,(
% 3.94/0.99    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.94/0.99    inference(ennf_transformation,[],[f5])).
% 3.94/0.99  
% 3.94/0.99  fof(f47,plain,(
% 3.94/0.99    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.94/0.99    inference(cnf_transformation,[],[f16])).
% 3.94/0.99  
% 3.94/0.99  fof(f9,axiom,(
% 3.94/0.99    ! [X0] : (l1_pre_topc(X0) => ? [X1] : (v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.94/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.94/0.99  
% 3.94/0.99  fof(f20,plain,(
% 3.94/0.99    ! [X0] : (? [X1] : (v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.94/0.99    inference(ennf_transformation,[],[f9])).
% 3.94/0.99  
% 3.94/0.99  fof(f29,plain,(
% 3.94/0.99    ! [X0] : (? [X1] : (v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_1(sK0(X0),X0) & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.94/0.99    introduced(choice_axiom,[])).
% 3.94/0.99  
% 3.94/0.99  fof(f30,plain,(
% 3.94/0.99    ! [X0] : ((v1_tops_1(sK0(X0),X0) & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.94/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f29])).
% 3.94/0.99  
% 3.94/0.99  fof(f52,plain,(
% 3.94/0.99    ( ! [X0] : (m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.94/0.99    inference(cnf_transformation,[],[f30])).
% 3.94/0.99  
% 3.94/0.99  fof(f53,plain,(
% 3.94/0.99    ( ! [X0] : (v1_tops_1(sK0(X0),X0) | ~l1_pre_topc(X0)) )),
% 3.94/0.99    inference(cnf_transformation,[],[f30])).
% 3.94/0.99  
% 3.94/0.99  fof(f10,axiom,(
% 3.94/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v1_tops_1(X1,X0)) => v1_tops_1(X2,X0)))))),
% 3.94/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.94/0.99  
% 3.94/0.99  fof(f21,plain,(
% 3.94/0.99    ! [X0] : (! [X1] : (! [X2] : ((v1_tops_1(X2,X0) | (~r1_tarski(X1,X2) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.94/0.99    inference(ennf_transformation,[],[f10])).
% 3.94/0.99  
% 3.94/0.99  fof(f22,plain,(
% 3.94/0.99    ! [X0] : (! [X1] : (! [X2] : (v1_tops_1(X2,X0) | ~r1_tarski(X1,X2) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.94/0.99    inference(flattening,[],[f21])).
% 3.94/0.99  
% 3.94/0.99  fof(f54,plain,(
% 3.94/0.99    ( ! [X2,X0,X1] : (v1_tops_1(X2,X0) | ~r1_tarski(X1,X2) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.94/0.99    inference(cnf_transformation,[],[f22])).
% 3.94/0.99  
% 3.94/0.99  fof(f7,axiom,(
% 3.94/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 3.94/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.94/0.99  
% 3.94/0.99  fof(f18,plain,(
% 3.94/0.99    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.94/0.99    inference(ennf_transformation,[],[f7])).
% 3.94/0.99  
% 3.94/0.99  fof(f49,plain,(
% 3.94/0.99    ( ! [X0,X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.94/0.99    inference(cnf_transformation,[],[f18])).
% 3.94/0.99  
% 3.94/0.99  fof(f1,axiom,(
% 3.94/0.99    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.94/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.94/0.99  
% 3.94/0.99  fof(f14,plain,(
% 3.94/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.94/0.99    inference(ennf_transformation,[],[f1])).
% 3.94/0.99  
% 3.94/0.99  fof(f15,plain,(
% 3.94/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.94/0.99    inference(flattening,[],[f14])).
% 3.94/0.99  
% 3.94/0.99  fof(f42,plain,(
% 3.94/0.99    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 3.94/0.99    inference(cnf_transformation,[],[f15])).
% 3.94/0.99  
% 3.94/0.99  fof(f57,plain,(
% 3.94/0.99    ( ! [X2,X0,X1] : (v2_compts_1(X2,X0) | sK1(X1,X2) = X2 | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.94/0.99    inference(cnf_transformation,[],[f34])).
% 3.94/0.99  
% 3.94/0.99  cnf(c_19,negated_conjecture,
% 3.94/0.99      ( sK4 = sK5 ),
% 3.94/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_21,negated_conjecture,
% 3.94/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.94/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_1273,plain,
% 3.94/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_13,plain,
% 3.94/0.99      ( v2_compts_1(X0,X1)
% 3.94/0.99      | ~ v2_compts_1(sK1(X2,X0),X2)
% 3.94/0.99      | ~ m1_pre_topc(X2,X1)
% 3.94/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.94/0.99      | ~ r1_tarski(X0,k2_struct_0(X2))
% 3.94/0.99      | ~ l1_pre_topc(X1) ),
% 3.94/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_22,negated_conjecture,
% 3.94/0.99      ( m1_pre_topc(sK3,sK2) ),
% 3.94/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_396,plain,
% 3.94/0.99      ( v2_compts_1(X0,X1)
% 3.94/0.99      | ~ v2_compts_1(sK1(X2,X0),X2)
% 3.94/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.94/0.99      | ~ r1_tarski(X0,k2_struct_0(X2))
% 3.94/0.99      | ~ l1_pre_topc(X1)
% 3.94/0.99      | sK2 != X1
% 3.94/0.99      | sK3 != X2 ),
% 3.94/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_22]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_397,plain,
% 3.94/0.99      ( v2_compts_1(X0,sK2)
% 3.94/0.99      | ~ v2_compts_1(sK1(sK3,X0),sK3)
% 3.94/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.94/0.99      | ~ r1_tarski(X0,k2_struct_0(sK3))
% 3.94/0.99      | ~ l1_pre_topc(sK2) ),
% 3.94/0.99      inference(unflattening,[status(thm)],[c_396]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_23,negated_conjecture,
% 3.94/0.99      ( l1_pre_topc(sK2) ),
% 3.94/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_401,plain,
% 3.94/0.99      ( ~ r1_tarski(X0,k2_struct_0(sK3))
% 3.94/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.94/0.99      | ~ v2_compts_1(sK1(sK3,X0),sK3)
% 3.94/0.99      | v2_compts_1(X0,sK2) ),
% 3.94/0.99      inference(global_propositional_subsumption,
% 3.94/0.99                [status(thm)],
% 3.94/0.99                [c_397,c_23]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_402,plain,
% 3.94/0.99      ( v2_compts_1(X0,sK2)
% 3.94/0.99      | ~ v2_compts_1(sK1(sK3,X0),sK3)
% 3.94/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.94/0.99      | ~ r1_tarski(X0,k2_struct_0(sK3)) ),
% 3.94/0.99      inference(renaming,[status(thm)],[c_401]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_1268,plain,
% 3.94/0.99      ( v2_compts_1(X0,sK2) = iProver_top
% 3.94/0.99      | v2_compts_1(sK1(sK3,X0),sK3) != iProver_top
% 3.94/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.94/0.99      | r1_tarski(X0,k2_struct_0(sK3)) != iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_402]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_4797,plain,
% 3.94/0.99      ( v2_compts_1(sK1(sK3,sK4),sK3) != iProver_top
% 3.94/0.99      | v2_compts_1(sK4,sK2) = iProver_top
% 3.94/0.99      | r1_tarski(sK4,k2_struct_0(sK3)) != iProver_top ),
% 3.94/0.99      inference(superposition,[status(thm)],[c_1273,c_1268]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_17,negated_conjecture,
% 3.94/0.99      ( ~ v2_compts_1(sK4,sK2) | ~ v2_compts_1(sK5,sK3) ),
% 3.94/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_29,plain,
% 3.94/0.99      ( v2_compts_1(sK4,sK2) != iProver_top
% 3.94/0.99      | v2_compts_1(sK5,sK3) != iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_16,plain,
% 3.94/0.99      ( ~ v2_compts_1(X0,X1)
% 3.94/0.99      | v2_compts_1(X0,X2)
% 3.94/0.99      | ~ m1_pre_topc(X2,X1)
% 3.94/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 3.94/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.94/0.99      | ~ r1_tarski(X0,k2_struct_0(X2))
% 3.94/0.99      | ~ l1_pre_topc(X1) ),
% 3.94/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_324,plain,
% 3.94/0.99      ( ~ v2_compts_1(X0,X1)
% 3.94/0.99      | v2_compts_1(X0,X2)
% 3.94/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.94/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 3.94/0.99      | ~ r1_tarski(X0,k2_struct_0(X2))
% 3.94/0.99      | ~ l1_pre_topc(X1)
% 3.94/0.99      | sK2 != X1
% 3.94/0.99      | sK3 != X2 ),
% 3.94/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_22]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_325,plain,
% 3.94/0.99      ( ~ v2_compts_1(X0,sK2)
% 3.94/0.99      | v2_compts_1(X0,sK3)
% 3.94/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.94/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.94/0.99      | ~ r1_tarski(X0,k2_struct_0(sK3))
% 3.94/0.99      | ~ l1_pre_topc(sK2) ),
% 3.94/0.99      inference(unflattening,[status(thm)],[c_324]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_6,plain,
% 3.94/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.94/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 3.94/0.99      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.94/0.99      | ~ l1_pre_topc(X1) ),
% 3.94/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_295,plain,
% 3.94/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.94/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 3.94/0.99      | ~ l1_pre_topc(X2)
% 3.94/0.99      | sK2 != X2
% 3.94/0.99      | sK3 != X1 ),
% 3.94/0.99      inference(resolution_lifted,[status(thm)],[c_6,c_22]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_296,plain,
% 3.94/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.94/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.94/0.99      | ~ l1_pre_topc(sK2) ),
% 3.94/0.99      inference(unflattening,[status(thm)],[c_295]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_300,plain,
% 3.94/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.94/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.94/0.99      inference(global_propositional_subsumption,
% 3.94/0.99                [status(thm)],
% 3.94/0.99                [c_296,c_23]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_301,plain,
% 3.94/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.94/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.94/0.99      inference(renaming,[status(thm)],[c_300]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_329,plain,
% 3.94/0.99      ( ~ r1_tarski(X0,k2_struct_0(sK3))
% 3.94/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.94/0.99      | ~ v2_compts_1(X0,sK2)
% 3.94/0.99      | v2_compts_1(X0,sK3) ),
% 3.94/0.99      inference(global_propositional_subsumption,
% 3.94/0.99                [status(thm)],
% 3.94/0.99                [c_325,c_23,c_296]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_330,plain,
% 3.94/0.99      ( ~ v2_compts_1(X0,sK2)
% 3.94/0.99      | v2_compts_1(X0,sK3)
% 3.94/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.94/0.99      | ~ r1_tarski(X0,k2_struct_0(sK3)) ),
% 3.94/0.99      inference(renaming,[status(thm)],[c_329]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_20,negated_conjecture,
% 3.94/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.94/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_4438,plain,
% 3.94/0.99      ( ~ v2_compts_1(sK5,sK2)
% 3.94/0.99      | v2_compts_1(sK5,sK3)
% 3.94/0.99      | ~ r1_tarski(sK5,k2_struct_0(sK3)) ),
% 3.94/0.99      inference(resolution,[status(thm)],[c_330,c_20]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_18,negated_conjecture,
% 3.94/0.99      ( v2_compts_1(sK4,sK2) | v2_compts_1(sK5,sK3) ),
% 3.94/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_1275,plain,
% 3.94/0.99      ( v2_compts_1(sK4,sK2) = iProver_top
% 3.94/0.99      | v2_compts_1(sK5,sK3) = iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_1662,plain,
% 3.94/0.99      ( v2_compts_1(sK5,sK2) = iProver_top
% 3.94/0.99      | v2_compts_1(sK5,sK3) = iProver_top ),
% 3.94/0.99      inference(superposition,[status(thm)],[c_19,c_1275]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_1663,plain,
% 3.94/0.99      ( v2_compts_1(sK5,sK2) | v2_compts_1(sK5,sK3) ),
% 3.94/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_1662]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_4550,plain,
% 3.94/0.99      ( v2_compts_1(sK5,sK3) | ~ r1_tarski(sK5,k2_struct_0(sK3)) ),
% 3.94/0.99      inference(global_propositional_subsumption,
% 3.94/0.99                [status(thm)],
% 3.94/0.99                [c_4438,c_1663]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_4552,plain,
% 3.94/0.99      ( v2_compts_1(sK5,sK3) = iProver_top
% 3.94/0.99      | r1_tarski(sK5,k2_struct_0(sK3)) != iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_4550]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_1274,plain,
% 3.94/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_4,plain,
% 3.94/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.94/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_1277,plain,
% 3.94/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.94/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_1793,plain,
% 3.94/1.00      ( r1_tarski(sK5,u1_struct_0(sK3)) = iProver_top ),
% 3.94/1.00      inference(superposition,[status(thm)],[c_1274,c_1277]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_1,plain,
% 3.94/1.00      ( k2_subset_1(X0) = X0 ),
% 3.94/1.00      inference(cnf_transformation,[],[f43]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_2,plain,
% 3.94/1.00      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 3.94/1.00      inference(cnf_transformation,[],[f44]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_1279,plain,
% 3.94/1.00      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 3.94/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_9,plain,
% 3.94/1.00      ( ~ v1_tops_1(X0,X1)
% 3.94/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.94/1.00      | ~ l1_pre_topc(X1)
% 3.94/1.00      | k2_pre_topc(X1,X0) = k2_struct_0(X1) ),
% 3.94/1.00      inference(cnf_transformation,[],[f50]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_5,plain,
% 3.94/1.00      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.94/1.00      inference(cnf_transformation,[],[f47]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_313,plain,
% 3.94/1.00      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | sK2 != X0 | sK3 != X1 ),
% 3.94/1.00      inference(resolution_lifted,[status(thm)],[c_5,c_22]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_314,plain,
% 3.94/1.00      ( ~ l1_pre_topc(sK2) | l1_pre_topc(sK3) ),
% 3.94/1.00      inference(unflattening,[status(thm)],[c_313]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_316,plain,
% 3.94/1.00      ( l1_pre_topc(sK3) ),
% 3.94/1.00      inference(global_propositional_subsumption,
% 3.94/1.00                [status(thm)],
% 3.94/1.00                [c_314,c_23]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_553,plain,
% 3.94/1.00      ( ~ v1_tops_1(X0,X1)
% 3.94/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.94/1.00      | k2_pre_topc(X1,X0) = k2_struct_0(X1)
% 3.94/1.00      | sK3 != X1 ),
% 3.94/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_316]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_554,plain,
% 3.94/1.00      ( ~ v1_tops_1(X0,sK3)
% 3.94/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.94/1.00      | k2_pre_topc(sK3,X0) = k2_struct_0(sK3) ),
% 3.94/1.00      inference(unflattening,[status(thm)],[c_553]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_1258,plain,
% 3.94/1.00      ( k2_pre_topc(sK3,X0) = k2_struct_0(sK3)
% 3.94/1.00      | v1_tops_1(X0,sK3) != iProver_top
% 3.94/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 3.94/1.00      inference(predicate_to_equality,[status(thm)],[c_554]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_1712,plain,
% 3.94/1.00      ( k2_pre_topc(sK3,k2_subset_1(u1_struct_0(sK3))) = k2_struct_0(sK3)
% 3.94/1.00      | v1_tops_1(k2_subset_1(u1_struct_0(sK3)),sK3) != iProver_top ),
% 3.94/1.00      inference(superposition,[status(thm)],[c_1279,c_1258]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_11,plain,
% 3.94/1.00      ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 3.94/1.00      | ~ l1_pre_topc(X0) ),
% 3.94/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_459,plain,
% 3.94/1.00      ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) | sK3 != X0 ),
% 3.94/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_316]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_460,plain,
% 3.94/1.00      ( m1_subset_1(sK0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.94/1.00      inference(unflattening,[status(thm)],[c_459]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_10,plain,
% 3.94/1.00      ( v1_tops_1(sK0(X0),X0) | ~ l1_pre_topc(X0) ),
% 3.94/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_466,plain,
% 3.94/1.00      ( v1_tops_1(sK0(X0),X0) | sK3 != X0 ),
% 3.94/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_316]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_467,plain,
% 3.94/1.00      ( v1_tops_1(sK0(sK3),sK3) ),
% 3.94/1.00      inference(unflattening,[status(thm)],[c_466]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_1413,plain,
% 3.94/1.00      ( m1_subset_1(k2_subset_1(u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.94/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_1715,plain,
% 3.94/1.00      ( ~ v1_tops_1(k2_subset_1(u1_struct_0(sK3)),sK3)
% 3.94/1.00      | k2_pre_topc(sK3,k2_subset_1(u1_struct_0(sK3))) = k2_struct_0(sK3) ),
% 3.94/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_1712]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_638,plain,( X0 = X0 ),theory(equality) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_1969,plain,
% 3.94/1.00      ( sK0(sK3) = sK0(sK3) ),
% 3.94/1.00      inference(instantiation,[status(thm)],[c_638]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_641,plain,
% 3.94/1.00      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 3.94/1.00      theory(equality) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_2039,plain,
% 3.94/1.00      ( X0 != u1_struct_0(sK3)
% 3.94/1.00      | k1_zfmisc_1(X0) = k1_zfmisc_1(u1_struct_0(sK3)) ),
% 3.94/1.00      inference(instantiation,[status(thm)],[c_641]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_2342,plain,
% 3.94/1.00      ( k1_zfmisc_1(k2_subset_1(u1_struct_0(sK3))) = k1_zfmisc_1(u1_struct_0(sK3))
% 3.94/1.00      | k2_subset_1(u1_struct_0(sK3)) != u1_struct_0(sK3) ),
% 3.94/1.00      inference(instantiation,[status(thm)],[c_2039]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_2343,plain,
% 3.94/1.00      ( k2_subset_1(u1_struct_0(sK3)) = u1_struct_0(sK3) ),
% 3.94/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_12,plain,
% 3.94/1.00      ( ~ v1_tops_1(X0,X1)
% 3.94/1.00      | v1_tops_1(X2,X1)
% 3.94/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.94/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.94/1.00      | ~ r1_tarski(X0,X2)
% 3.94/1.00      | ~ l1_pre_topc(X1) ),
% 3.94/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_534,plain,
% 3.94/1.00      ( ~ v1_tops_1(X0,X1)
% 3.94/1.00      | v1_tops_1(X2,X1)
% 3.94/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.94/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.94/1.00      | ~ r1_tarski(X0,X2)
% 3.94/1.00      | sK3 != X1 ),
% 3.94/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_316]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_535,plain,
% 3.94/1.00      ( ~ v1_tops_1(X0,sK3)
% 3.94/1.00      | v1_tops_1(X1,sK3)
% 3.94/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.94/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.94/1.00      | ~ r1_tarski(X0,X1) ),
% 3.94/1.00      inference(unflattening,[status(thm)],[c_534]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_1887,plain,
% 3.94/1.00      ( v1_tops_1(X0,sK3)
% 3.94/1.00      | ~ v1_tops_1(sK0(sK3),sK3)
% 3.94/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.94/1.00      | ~ m1_subset_1(sK0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.94/1.00      | ~ r1_tarski(sK0(sK3),X0) ),
% 3.94/1.00      inference(instantiation,[status(thm)],[c_535]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_2572,plain,
% 3.94/1.00      ( ~ v1_tops_1(sK0(sK3),sK3)
% 3.94/1.00      | v1_tops_1(k2_subset_1(u1_struct_0(sK3)),sK3)
% 3.94/1.00      | ~ m1_subset_1(sK0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.94/1.00      | ~ m1_subset_1(k2_subset_1(u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.94/1.00      | ~ r1_tarski(sK0(sK3),k2_subset_1(u1_struct_0(sK3))) ),
% 3.94/1.00      inference(instantiation,[status(thm)],[c_1887]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_642,plain,
% 3.94/1.00      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.94/1.00      theory(equality) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_1494,plain,
% 3.94/1.00      ( m1_subset_1(X0,X1)
% 3.94/1.00      | ~ m1_subset_1(sK0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.94/1.00      | X0 != sK0(sK3)
% 3.94/1.00      | X1 != k1_zfmisc_1(u1_struct_0(sK3)) ),
% 3.94/1.00      inference(instantiation,[status(thm)],[c_642]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_1968,plain,
% 3.94/1.00      ( m1_subset_1(sK0(sK3),X0)
% 3.94/1.00      | ~ m1_subset_1(sK0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.94/1.00      | X0 != k1_zfmisc_1(u1_struct_0(sK3))
% 3.94/1.00      | sK0(sK3) != sK0(sK3) ),
% 3.94/1.00      inference(instantiation,[status(thm)],[c_1494]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_3209,plain,
% 3.94/1.00      ( ~ m1_subset_1(sK0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.94/1.00      | m1_subset_1(sK0(sK3),k1_zfmisc_1(k2_subset_1(u1_struct_0(sK3))))
% 3.94/1.00      | sK0(sK3) != sK0(sK3)
% 3.94/1.00      | k1_zfmisc_1(k2_subset_1(u1_struct_0(sK3))) != k1_zfmisc_1(u1_struct_0(sK3)) ),
% 3.94/1.00      inference(instantiation,[status(thm)],[c_1968]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_3311,plain,
% 3.94/1.00      ( ~ m1_subset_1(sK0(sK3),k1_zfmisc_1(k2_subset_1(u1_struct_0(sK3))))
% 3.94/1.00      | r1_tarski(sK0(sK3),k2_subset_1(u1_struct_0(sK3))) ),
% 3.94/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_4930,plain,
% 3.94/1.00      ( k2_pre_topc(sK3,k2_subset_1(u1_struct_0(sK3))) = k2_struct_0(sK3) ),
% 3.94/1.00      inference(global_propositional_subsumption,
% 3.94/1.00                [status(thm)],
% 3.94/1.00                [c_1712,c_460,c_467,c_1413,c_1715,c_1969,c_2342,c_2343,
% 3.94/1.00                 c_2572,c_3209,c_3311]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_4932,plain,
% 3.94/1.00      ( k2_pre_topc(sK3,u1_struct_0(sK3)) = k2_struct_0(sK3) ),
% 3.94/1.00      inference(superposition,[status(thm)],[c_1,c_4930]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_1515,plain,
% 3.94/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.94/1.00      inference(superposition,[status(thm)],[c_1,c_1279]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_7,plain,
% 3.94/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.94/1.00      | r1_tarski(X0,k2_pre_topc(X1,X0))
% 3.94/1.00      | ~ l1_pre_topc(X1) ),
% 3.94/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_583,plain,
% 3.94/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.94/1.00      | r1_tarski(X0,k2_pre_topc(X1,X0))
% 3.94/1.00      | sK3 != X1 ),
% 3.94/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_316]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_584,plain,
% 3.94/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.94/1.00      | r1_tarski(X0,k2_pre_topc(sK3,X0)) ),
% 3.94/1.00      inference(unflattening,[status(thm)],[c_583]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_1256,plain,
% 3.94/1.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.94/1.00      | r1_tarski(X0,k2_pre_topc(sK3,X0)) = iProver_top ),
% 3.94/1.00      inference(predicate_to_equality,[status(thm)],[c_584]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_1522,plain,
% 3.94/1.00      ( r1_tarski(u1_struct_0(sK3),k2_pre_topc(sK3,u1_struct_0(sK3))) = iProver_top ),
% 3.94/1.00      inference(superposition,[status(thm)],[c_1515,c_1256]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_0,plain,
% 3.94/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 3.94/1.00      inference(cnf_transformation,[],[f42]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_1280,plain,
% 3.94/1.00      ( r1_tarski(X0,X1) != iProver_top
% 3.94/1.00      | r1_tarski(X2,X0) != iProver_top
% 3.94/1.00      | r1_tarski(X2,X1) = iProver_top ),
% 3.94/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_2604,plain,
% 3.94/1.00      ( r1_tarski(X0,k2_pre_topc(sK3,u1_struct_0(sK3))) = iProver_top
% 3.94/1.00      | r1_tarski(X0,u1_struct_0(sK3)) != iProver_top ),
% 3.94/1.00      inference(superposition,[status(thm)],[c_1522,c_1280]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_5063,plain,
% 3.94/1.00      ( r1_tarski(X0,k2_struct_0(sK3)) = iProver_top
% 3.94/1.00      | r1_tarski(X0,u1_struct_0(sK3)) != iProver_top ),
% 3.94/1.00      inference(superposition,[status(thm)],[c_4932,c_2604]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_5305,plain,
% 3.94/1.00      ( r1_tarski(sK5,k2_struct_0(sK3)) = iProver_top ),
% 3.94/1.00      inference(superposition,[status(thm)],[c_1793,c_5063]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_11346,plain,
% 3.94/1.00      ( v2_compts_1(sK1(sK3,sK4),sK3) != iProver_top
% 3.94/1.00      | r1_tarski(sK4,k2_struct_0(sK3)) != iProver_top ),
% 3.94/1.00      inference(global_propositional_subsumption,
% 3.94/1.00                [status(thm)],
% 3.94/1.00                [c_4797,c_29,c_4552,c_5305]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_11351,plain,
% 3.94/1.00      ( v2_compts_1(sK1(sK3,sK5),sK3) != iProver_top
% 3.94/1.00      | r1_tarski(sK4,k2_struct_0(sK3)) != iProver_top ),
% 3.94/1.00      inference(superposition,[status(thm)],[c_19,c_11346]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_1990,plain,
% 3.94/1.00      ( sK3 = sK3 ),
% 3.94/1.00      inference(instantiation,[status(thm)],[c_638]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_648,plain,
% 3.94/1.00      ( ~ v2_compts_1(X0,X1) | v2_compts_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.94/1.00      theory(equality) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_2976,plain,
% 3.94/1.00      ( v2_compts_1(X0,X1)
% 3.94/1.00      | ~ v2_compts_1(sK5,sK3)
% 3.94/1.00      | X1 != sK3
% 3.94/1.00      | X0 != sK5 ),
% 3.94/1.00      inference(instantiation,[status(thm)],[c_648]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_3378,plain,
% 3.94/1.00      ( v2_compts_1(X0,sK3)
% 3.94/1.00      | ~ v2_compts_1(sK5,sK3)
% 3.94/1.00      | X0 != sK5
% 3.94/1.00      | sK3 != sK3 ),
% 3.94/1.00      inference(instantiation,[status(thm)],[c_2976]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_5839,plain,
% 3.94/1.00      ( v2_compts_1(sK4,sK3)
% 3.94/1.00      | ~ v2_compts_1(sK5,sK3)
% 3.94/1.00      | sK4 != sK5
% 3.94/1.00      | sK3 != sK3 ),
% 3.94/1.00      inference(instantiation,[status(thm)],[c_3378]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_5840,plain,
% 3.94/1.00      ( sK4 != sK5
% 3.94/1.00      | sK3 != sK3
% 3.94/1.00      | v2_compts_1(sK4,sK3) = iProver_top
% 3.94/1.00      | v2_compts_1(sK5,sK3) != iProver_top ),
% 3.94/1.00      inference(predicate_to_equality,[status(thm)],[c_5839]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_14,plain,
% 3.94/1.00      ( v2_compts_1(X0,X1)
% 3.94/1.00      | ~ m1_pre_topc(X2,X1)
% 3.94/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.94/1.00      | ~ r1_tarski(X0,k2_struct_0(X2))
% 3.94/1.00      | ~ l1_pre_topc(X1)
% 3.94/1.00      | sK1(X2,X0) = X0 ),
% 3.94/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_372,plain,
% 3.94/1.00      ( v2_compts_1(X0,X1)
% 3.94/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.94/1.00      | ~ r1_tarski(X0,k2_struct_0(X2))
% 3.94/1.00      | ~ l1_pre_topc(X1)
% 3.94/1.00      | sK1(X2,X0) = X0
% 3.94/1.00      | sK2 != X1
% 3.94/1.00      | sK3 != X2 ),
% 3.94/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_22]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_373,plain,
% 3.94/1.00      ( v2_compts_1(X0,sK2)
% 3.94/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.94/1.00      | ~ r1_tarski(X0,k2_struct_0(sK3))
% 3.94/1.00      | ~ l1_pre_topc(sK2)
% 3.94/1.00      | sK1(sK3,X0) = X0 ),
% 3.94/1.00      inference(unflattening,[status(thm)],[c_372]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_377,plain,
% 3.94/1.00      ( ~ r1_tarski(X0,k2_struct_0(sK3))
% 3.94/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.94/1.00      | v2_compts_1(X0,sK2)
% 3.94/1.00      | sK1(sK3,X0) = X0 ),
% 3.94/1.00      inference(global_propositional_subsumption,
% 3.94/1.00                [status(thm)],
% 3.94/1.00                [c_373,c_23]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_378,plain,
% 3.94/1.00      ( v2_compts_1(X0,sK2)
% 3.94/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.94/1.00      | ~ r1_tarski(X0,k2_struct_0(sK3))
% 3.94/1.00      | sK1(sK3,X0) = X0 ),
% 3.94/1.00      inference(renaming,[status(thm)],[c_377]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_1269,plain,
% 3.94/1.00      ( sK1(sK3,X0) = X0
% 3.94/1.00      | v2_compts_1(X0,sK2) = iProver_top
% 3.94/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.94/1.00      | r1_tarski(X0,k2_struct_0(sK3)) != iProver_top ),
% 3.94/1.00      inference(predicate_to_equality,[status(thm)],[c_378]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_5291,plain,
% 3.94/1.00      ( sK1(sK3,sK4) = sK4
% 3.94/1.00      | v2_compts_1(sK4,sK2) = iProver_top
% 3.94/1.00      | r1_tarski(sK4,k2_struct_0(sK3)) != iProver_top ),
% 3.94/1.00      inference(superposition,[status(thm)],[c_1273,c_1269]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_7810,plain,
% 3.94/1.00      ( sK1(sK3,sK4) = sK4
% 3.94/1.00      | r1_tarski(sK4,k2_struct_0(sK3)) != iProver_top ),
% 3.94/1.00      inference(global_propositional_subsumption,
% 3.94/1.00                [status(thm)],
% 3.94/1.00                [c_5291,c_29,c_4552,c_5305]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_7814,plain,
% 3.94/1.00      ( sK1(sK3,sK4) = sK4
% 3.94/1.00      | r1_tarski(sK5,k2_struct_0(sK3)) != iProver_top ),
% 3.94/1.00      inference(superposition,[status(thm)],[c_19,c_7810]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_7950,plain,
% 3.94/1.00      ( sK1(sK3,sK4) = sK4 ),
% 3.94/1.00      inference(global_propositional_subsumption,
% 3.94/1.00                [status(thm)],
% 3.94/1.00                [c_7814,c_5305]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_11350,plain,
% 3.94/1.00      ( v2_compts_1(sK4,sK3) != iProver_top
% 3.94/1.00      | r1_tarski(sK4,k2_struct_0(sK3)) != iProver_top ),
% 3.94/1.00      inference(superposition,[status(thm)],[c_7950,c_11346]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_11355,plain,
% 3.94/1.00      ( r1_tarski(sK4,k2_struct_0(sK3)) != iProver_top ),
% 3.94/1.00      inference(global_propositional_subsumption,
% 3.94/1.00                [status(thm)],
% 3.94/1.00                [c_11351,c_19,c_1990,c_4552,c_5305,c_5840,c_11350]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_11359,plain,
% 3.94/1.00      ( r1_tarski(sK5,k2_struct_0(sK3)) != iProver_top ),
% 3.94/1.00      inference(superposition,[status(thm)],[c_19,c_11355]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(contradiction,plain,
% 3.94/1.00      ( $false ),
% 3.94/1.00      inference(minisat,[status(thm)],[c_11359,c_5305]) ).
% 3.94/1.00  
% 3.94/1.00  
% 3.94/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.94/1.00  
% 3.94/1.00  ------                               Statistics
% 3.94/1.00  
% 3.94/1.00  ------ Selected
% 3.94/1.00  
% 3.94/1.00  total_time:                             0.288
% 3.94/1.00  
%------------------------------------------------------------------------------
