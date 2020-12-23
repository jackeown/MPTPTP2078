%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1373+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:34 EST 2020

% Result     : Theorem 0.95s
% Output     : CNFRefutation 0.95s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 813 expanded)
%              Number of clauses        :   97 ( 226 expanded)
%              Number of leaves         :   18 ( 241 expanded)
%              Depth                    :   21
%              Number of atoms          :  539 (5576 expanded)
%              Number of equality atoms :  159 ( 891 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
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
    inference(negated_conjecture,[],[f6])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ~ v2_compts_1(X3,X1)
            | ~ v2_compts_1(X2,X0) )
          & ( v2_compts_1(X3,X1)
            | v2_compts_1(X2,X0) )
          & X2 = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ( ~ v2_compts_1(sK4,X1)
          | ~ v2_compts_1(X2,X0) )
        & ( v2_compts_1(sK4,X1)
          | v2_compts_1(X2,X0) )
        & sK4 = X2
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
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
              | ~ v2_compts_1(sK3,X0) )
            & ( v2_compts_1(X3,X1)
              | v2_compts_1(sK3,X0) )
            & sK3 = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
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
                ( ( ~ v2_compts_1(X3,sK2)
                  | ~ v2_compts_1(X2,X0) )
                & ( v2_compts_1(X3,sK2)
                  | v2_compts_1(X2,X0) )
                & X2 = X3
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_pre_topc(sK2,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
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
                    | ~ v2_compts_1(X2,sK1) )
                  & ( v2_compts_1(X3,X1)
                    | v2_compts_1(X2,sK1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) )
          & m1_pre_topc(X1,sK1) )
      & l1_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ( ~ v2_compts_1(sK4,sK2)
      | ~ v2_compts_1(sK3,sK1) )
    & ( v2_compts_1(sK4,sK2)
      | v2_compts_1(sK3,sK1) )
    & sK3 = sK4
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_pre_topc(sK2,sK1)
    & l1_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f22,f26,f25,f24,f23])).

fof(f39,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f27])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f29,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f28,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f30,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f37,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f36,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f5])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f17,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f18,plain,(
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
    inference(rectify,[],[f17])).

fof(f19,plain,(
    ! [X2,X1] :
      ( ? [X3] :
          ( ~ v2_compts_1(X3,X1)
          & X2 = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v2_compts_1(sK0(X1,X2),X1)
        & sK0(X1,X2) = X2
        & m1_subset_1(sK0(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v2_compts_1(X2,X0)
                  | ( ~ v2_compts_1(sK0(X1,X2),X1)
                    & sK0(X1,X2) = X2
                    & m1_subset_1(sK0(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v2_compts_1(X4,X1)
                      | X2 != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v2_compts_1(X2,X0) ) )
              | ~ r1_tarski(X2,k2_struct_0(X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).

fof(f31,plain,(
    ! [X4,X2,X0,X1] :
      ( v2_compts_1(X4,X1)
      | X2 != X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_compts_1(X2,X0)
      | ~ r1_tarski(X2,k2_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f43,plain,(
    ! [X4,X0,X1] :
      ( v2_compts_1(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_compts_1(X4,X0)
      | ~ r1_tarski(X4,k2_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f31])).

fof(f41,plain,
    ( v2_compts_1(sK4,sK2)
    | v2_compts_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f40,plain,(
    sK3 = sK4 ),
    inference(cnf_transformation,[],[f27])).

fof(f38,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f27])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( v2_compts_1(X2,X0)
      | sK0(X1,X2) = X2
      | ~ r1_tarski(X2,k2_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( v2_compts_1(X2,X0)
      | ~ v2_compts_1(sK0(X1,X2),X1)
      | ~ r1_tarski(X2,k2_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f42,plain,
    ( ~ v2_compts_1(sK4,sK2)
    | ~ v2_compts_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_545,plain,
    ( ~ v2_compts_1(X0_42,X0_45)
    | v2_compts_1(X1_42,X0_45)
    | X1_42 != X0_42 ),
    theory(equality)).

cnf(c_900,plain,
    ( ~ v2_compts_1(X0_42,sK2)
    | v2_compts_1(X1_42,sK2)
    | X1_42 != X0_42 ),
    inference(instantiation,[status(thm)],[c_545])).

cnf(c_1126,plain,
    ( ~ v2_compts_1(X0_42,sK2)
    | v2_compts_1(sK0(sK2,X1_42),sK2)
    | sK0(sK2,X1_42) != X0_42 ),
    inference(instantiation,[status(thm)],[c_900])).

cnf(c_1128,plain,
    ( v2_compts_1(sK0(sK2,sK3),sK2)
    | ~ v2_compts_1(sK3,sK2)
    | sK0(sK2,sK3) != sK3 ),
    inference(instantiation,[status(thm)],[c_1126])).

cnf(c_11,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_535,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_788,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_535])).

cnf(c_1,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_0,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_190,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_1,c_0])).

cnf(c_2,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_13,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_204,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK1 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_13])).

cnf(c_205,plain,
    ( ~ l1_pre_topc(sK1)
    | l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_204])).

cnf(c_14,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_207,plain,
    ( l1_pre_topc(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_205,c_14])).

cnf(c_342,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_190,c_207])).

cnf(c_343,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_342])).

cnf(c_532,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(subtyping,[status(esa)],[c_343])).

cnf(c_800,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_struct_0(sK2))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_788,c_532])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(X0,k2_struct_0(X1))
    | ~ v2_compts_1(X0,X2)
    | v2_compts_1(X0,X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_287,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(X0,k2_struct_0(X1))
    | ~ v2_compts_1(X0,X2)
    | v2_compts_1(X0,X1)
    | ~ l1_pre_topc(X2)
    | sK1 != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_13])).

cnf(c_288,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X0,k2_struct_0(sK2))
    | ~ v2_compts_1(X0,sK1)
    | v2_compts_1(X0,sK2)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_287])).

cnf(c_292,plain,
    ( v2_compts_1(X0,sK2)
    | ~ v2_compts_1(X0,sK1)
    | ~ r1_tarski(X0,k2_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_288,c_14])).

cnf(c_293,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X0,k2_struct_0(sK2))
    | ~ v2_compts_1(X0,sK1)
    | v2_compts_1(X0,sK2) ),
    inference(renaming,[status(thm)],[c_292])).

cnf(c_349,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_compts_1(X2,sK1)
    | v2_compts_1(X2,sK2)
    | X2 != X0
    | k2_struct_0(sK2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_293])).

cnf(c_350,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2)))
    | ~ v2_compts_1(X0,sK1)
    | v2_compts_1(X0,sK2) ),
    inference(unflattening,[status(thm)],[c_349])).

cnf(c_531,plain,
    ( ~ m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0_42,k1_zfmisc_1(k2_struct_0(sK2)))
    | ~ v2_compts_1(X0_42,sK1)
    | v2_compts_1(X0_42,sK2) ),
    inference(subtyping,[status(esa)],[c_350])).

cnf(c_790,plain,
    ( m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X0_42,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | v2_compts_1(X0_42,sK1) != iProver_top
    | v2_compts_1(X0_42,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_531])).

cnf(c_337,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_190,c_14])).

cnf(c_338,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_337])).

cnf(c_533,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_338])).

cnf(c_843,plain,
    ( m1_subset_1(X0_42,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | m1_subset_1(X0_42,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | v2_compts_1(X0_42,sK1) != iProver_top
    | v2_compts_1(X0_42,sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_790,c_532,c_533])).

cnf(c_988,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | v2_compts_1(sK4,sK1) != iProver_top
    | v2_compts_1(sK4,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_800,c_843])).

cnf(c_9,negated_conjecture,
    ( v2_compts_1(sK3,sK1)
    | v2_compts_1(sK4,sK2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_537,negated_conjecture,
    ( v2_compts_1(sK3,sK1)
    | v2_compts_1(sK4,sK2) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_787,plain,
    ( v2_compts_1(sK3,sK1) = iProver_top
    | v2_compts_1(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_537])).

cnf(c_10,negated_conjecture,
    ( sK3 = sK4 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_536,negated_conjecture,
    ( sK3 = sK4 ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_806,plain,
    ( v2_compts_1(sK4,sK1) = iProver_top
    | v2_compts_1(sK4,sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_787,c_536])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_534,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_789,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_534])).

cnf(c_803,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_789,c_533,c_536])).

cnf(c_1078,plain,
    ( v2_compts_1(sK4,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_988,c_806,c_803])).

cnf(c_1080,plain,
    ( v2_compts_1(sK4,sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1078])).

cnf(c_547,plain,
    ( ~ m1_subset_1(X0_42,X0_43)
    | m1_subset_1(X1_42,X1_43)
    | X1_43 != X0_43
    | X1_42 != X0_42 ),
    theory(equality)).

cnf(c_929,plain,
    ( m1_subset_1(X0_42,X0_43)
    | ~ m1_subset_1(X1_42,k1_zfmisc_1(u1_struct_0(sK2)))
    | X0_43 != k1_zfmisc_1(u1_struct_0(sK2))
    | X0_42 != X1_42 ),
    inference(instantiation,[status(thm)],[c_547])).

cnf(c_1066,plain,
    ( ~ m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(X1_42,k1_zfmisc_1(k2_struct_0(sK2)))
    | k1_zfmisc_1(k2_struct_0(sK2)) != k1_zfmisc_1(u1_struct_0(sK2))
    | X1_42 != X0_42 ),
    inference(instantiation,[status(thm)],[c_929])).

cnf(c_1068,plain,
    ( k1_zfmisc_1(k2_struct_0(sK2)) != k1_zfmisc_1(u1_struct_0(sK2))
    | X0_42 != X1_42
    | m1_subset_1(X1_42,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X0_42,k1_zfmisc_1(k2_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1066])).

cnf(c_1070,plain,
    ( k1_zfmisc_1(k2_struct_0(sK2)) != k1_zfmisc_1(u1_struct_0(sK2))
    | sK3 != sK3
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK2))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1068])).

cnf(c_1069,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK2)))
    | k1_zfmisc_1(k2_struct_0(sK2)) != k1_zfmisc_1(u1_struct_0(sK2))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1066])).

cnf(c_546,plain,
    ( X0_44 != X1_44
    | k1_zfmisc_1(X0_44) = k1_zfmisc_1(X1_44) ),
    theory(equality)).

cnf(c_910,plain,
    ( X0_44 != u1_struct_0(sK2)
    | k1_zfmisc_1(X0_44) = k1_zfmisc_1(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_546])).

cnf(c_1035,plain,
    ( k2_struct_0(sK2) != u1_struct_0(sK2)
    | k1_zfmisc_1(k2_struct_0(sK2)) = k1_zfmisc_1(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_910])).

cnf(c_542,plain,
    ( X0_44 = X0_44 ),
    theory(equality)).

cnf(c_977,plain,
    ( k2_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_542])).

cnf(c_544,plain,
    ( X0_44 != X1_44
    | X2_44 != X1_44
    | X2_44 = X0_44 ),
    theory(equality)).

cnf(c_936,plain,
    ( X0_44 != X1_44
    | X0_44 = u1_struct_0(sK2)
    | u1_struct_0(sK2) != X1_44 ),
    inference(instantiation,[status(thm)],[c_544])).

cnf(c_954,plain,
    ( X0_44 = u1_struct_0(sK2)
    | X0_44 != k2_struct_0(sK2)
    | u1_struct_0(sK2) != k2_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_936])).

cnf(c_976,plain,
    ( u1_struct_0(sK2) != k2_struct_0(sK2)
    | k2_struct_0(sK2) = u1_struct_0(sK2)
    | k2_struct_0(sK2) != k2_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_954])).

cnf(c_541,plain,
    ( X0_43 = X0_43 ),
    theory(equality)).

cnf(c_904,plain,
    ( k1_zfmisc_1(u1_struct_0(sK2)) = k1_zfmisc_1(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_541])).

cnf(c_885,plain,
    ( m1_subset_1(X0_42,X0_43)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | X0_43 != k1_zfmisc_1(u1_struct_0(sK2))
    | X0_42 != sK4 ),
    inference(instantiation,[status(thm)],[c_547])).

cnf(c_903,plain,
    ( m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(u1_struct_0(sK2))
    | X0_42 != sK4 ),
    inference(instantiation,[status(thm)],[c_885])).

cnf(c_905,plain,
    ( k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(u1_struct_0(sK2))
    | X0_42 != sK4
    | m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_903])).

cnf(c_907,plain,
    ( k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(u1_struct_0(sK2))
    | sK3 != sK4
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_905])).

cnf(c_906,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(u1_struct_0(sK2))
    | sK3 != sK4 ),
    inference(instantiation,[status(thm)],[c_903])).

cnf(c_880,plain,
    ( v2_compts_1(X0_42,sK2)
    | ~ v2_compts_1(sK4,sK2)
    | X0_42 != sK4 ),
    inference(instantiation,[status(thm)],[c_545])).

cnf(c_882,plain,
    ( v2_compts_1(sK3,sK2)
    | ~ v2_compts_1(sK4,sK2)
    | sK3 != sK4 ),
    inference(instantiation,[status(thm)],[c_880])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,k2_struct_0(X2))
    | v2_compts_1(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | sK0(X2,X0) = X0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_239,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,k2_struct_0(X2))
    | v2_compts_1(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK0(X2,X0) = X0
    | sK1 != X1
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_13])).

cnf(c_240,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X0,k2_struct_0(sK2))
    | v2_compts_1(X0,sK1)
    | ~ l1_pre_topc(sK1)
    | sK0(sK2,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_239])).

cnf(c_244,plain,
    ( v2_compts_1(X0,sK1)
    | ~ r1_tarski(X0,k2_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | sK0(sK2,X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_240,c_14])).

cnf(c_245,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X0,k2_struct_0(sK2))
    | v2_compts_1(X0,sK1)
    | sK0(sK2,X0) = X0 ),
    inference(renaming,[status(thm)],[c_244])).

cnf(c_388,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_compts_1(X2,sK1)
    | X2 != X0
    | sK0(sK2,X2) = X2
    | k2_struct_0(sK2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_245])).

cnf(c_389,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2)))
    | v2_compts_1(X0,sK1)
    | sK0(sK2,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_388])).

cnf(c_529,plain,
    ( ~ m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0_42,k1_zfmisc_1(k2_struct_0(sK2)))
    | v2_compts_1(X0_42,sK1)
    | sK0(sK2,X0_42) = X0_42 ),
    inference(subtyping,[status(esa)],[c_389])).

cnf(c_565,plain,
    ( sK0(sK2,X0_42) = X0_42
    | m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X0_42,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | v2_compts_1(X0_42,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_529])).

cnf(c_567,plain,
    ( sK0(sK2,sK3) = sK3
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | v2_compts_1(sK3,sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_565])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,k2_struct_0(X2))
    | v2_compts_1(X0,X1)
    | ~ v2_compts_1(sK0(X2,X0),X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_263,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,k2_struct_0(X2))
    | v2_compts_1(X0,X1)
    | ~ v2_compts_1(sK0(X2,X0),X2)
    | ~ l1_pre_topc(X1)
    | sK1 != X1
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_13])).

cnf(c_264,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X0,k2_struct_0(sK2))
    | v2_compts_1(X0,sK1)
    | ~ v2_compts_1(sK0(sK2,X0),sK2)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_263])).

cnf(c_268,plain,
    ( ~ v2_compts_1(sK0(sK2,X0),sK2)
    | v2_compts_1(X0,sK1)
    | ~ r1_tarski(X0,k2_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_264,c_14])).

cnf(c_269,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X0,k2_struct_0(sK2))
    | v2_compts_1(X0,sK1)
    | ~ v2_compts_1(sK0(sK2,X0),sK2) ),
    inference(renaming,[status(thm)],[c_268])).

cnf(c_370,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_compts_1(X2,sK1)
    | ~ v2_compts_1(sK0(sK2,X2),sK2)
    | X2 != X0
    | k2_struct_0(sK2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_269])).

cnf(c_371,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2)))
    | v2_compts_1(X0,sK1)
    | ~ v2_compts_1(sK0(sK2,X0),sK2) ),
    inference(unflattening,[status(thm)],[c_370])).

cnf(c_530,plain,
    ( ~ m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0_42,k1_zfmisc_1(k2_struct_0(sK2)))
    | v2_compts_1(X0_42,sK1)
    | ~ v2_compts_1(sK0(sK2,X0_42),sK2) ),
    inference(subtyping,[status(esa)],[c_371])).

cnf(c_563,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK2)))
    | ~ v2_compts_1(sK0(sK2,sK3),sK2)
    | v2_compts_1(sK3,sK1) ),
    inference(instantiation,[status(thm)],[c_530])).

cnf(c_540,plain,
    ( X0_42 = X0_42 ),
    theory(equality)).

cnf(c_552,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_540])).

cnf(c_8,negated_conjecture,
    ( ~ v2_compts_1(sK3,sK1)
    | ~ v2_compts_1(sK4,sK2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_20,plain,
    ( v2_compts_1(sK3,sK1) != iProver_top
    | v2_compts_1(sK4,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_18,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_17,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1128,c_1080,c_1078,c_1070,c_1069,c_1035,c_977,c_976,c_904,c_907,c_906,c_882,c_567,c_563,c_532,c_536,c_552,c_20,c_8,c_18,c_11,c_17,c_12])).


%------------------------------------------------------------------------------
