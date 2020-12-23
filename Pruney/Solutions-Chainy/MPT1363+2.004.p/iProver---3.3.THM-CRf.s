%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:17:56 EST 2020

% Result     : Theorem 7.92s
% Output     : CNFRefutation 7.92s
% Verified   : 
% Statistics : Number of formulae       :  185 (1239 expanded)
%              Number of clauses        :  119 ( 399 expanded)
%              Number of leaves         :   19 ( 312 expanded)
%              Depth                    :   25
%              Number of atoms          :  694 (6385 expanded)
%              Number of equality atoms :  247 ( 629 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v4_pre_topc(X2,X0)
                  & r1_tarski(X2,X1)
                  & v2_compts_1(X1,X0) )
               => v2_compts_1(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v4_pre_topc(X2,X0)
                    & r1_tarski(X2,X1)
                    & v2_compts_1(X1,X0) )
                 => v2_compts_1(X2,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f15,plain,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v4_pre_topc(X2,X0)
                    & r1_tarski(X2,X1)
                    & v2_compts_1(X1,X0) )
                 => v2_compts_1(X2,X0) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_compts_1(X2,X0)
              & v4_pre_topc(X2,X0)
              & r1_tarski(X2,X1)
              & v2_compts_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_compts_1(X2,X0)
              & v4_pre_topc(X2,X0)
              & r1_tarski(X2,X1)
              & v2_compts_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v2_compts_1(X2,X0)
          & v4_pre_topc(X2,X0)
          & r1_tarski(X2,X1)
          & v2_compts_1(X1,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v2_compts_1(sK3,X0)
        & v4_pre_topc(sK3,X0)
        & r1_tarski(sK3,X1)
        & v2_compts_1(X1,X0)
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_compts_1(X2,X0)
              & v4_pre_topc(X2,X0)
              & r1_tarski(X2,X1)
              & v2_compts_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ v2_compts_1(X2,X0)
            & v4_pre_topc(X2,X0)
            & r1_tarski(X2,sK2)
            & v2_compts_1(sK2,X0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v2_compts_1(X2,X0)
                & v4_pre_topc(X2,X0)
                & r1_tarski(X2,X1)
                & v2_compts_1(X1,X0)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_compts_1(X2,sK1)
              & v4_pre_topc(X2,sK1)
              & r1_tarski(X2,X1)
              & v2_compts_1(X1,sK1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
      & l1_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ~ v2_compts_1(sK3,sK1)
    & v4_pre_topc(sK3,sK1)
    & r1_tarski(sK3,sK2)
    & v2_compts_1(sK2,sK1)
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & l1_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f32,f43,f42,f41])).

fof(f64,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f52,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f50,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f65,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f44])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_pre_topc(k1_pre_topc(X0,X1),X0) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f53,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f54,plain,(
    ! [X0,X1] :
      ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f66,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f44])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
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

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f38,plain,(
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
    inference(rectify,[],[f37])).

fof(f39,plain,(
    ! [X2,X1] :
      ( ? [X3] :
          ( ~ v2_compts_1(X3,X1)
          & X2 = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v2_compts_1(sK0(X1,X2),X1)
        & sK0(X1,X2) = X2
        & m1_subset_1(sK0(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f38,f39])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v2_compts_1(X2,X0)
      | sK0(X1,X2) = X2
      | ~ r1_tarski(X2,k2_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f70,plain,(
    ~ v2_compts_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f68,plain,(
    r1_tarski(sK3,sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v2_compts_1(X2,X0)
      | m1_subset_1(sK0(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r1_tarski(X2,k2_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v4_pre_topc(X1,X0)
              & v1_compts_1(X0) )
           => v2_compts_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_compts_1(X1,X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ v1_compts_1(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_compts_1(X1,X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ v1_compts_1(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v2_compts_1(X1,X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ v1_compts_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v2_compts_1(X2,X0)
      | ~ v2_compts_1(sK0(X1,X2),X1)
      | ~ r1_tarski(X2,k2_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_compts_1(X0)
      <=> v2_compts_1(k2_struct_0(X0),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_compts_1(X0)
      <=> v2_compts_1(k2_struct_0(X0),X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f36,plain,(
    ! [X0] :
      ( ( ( v1_compts_1(X0)
          | ~ v2_compts_1(k2_struct_0(X0),X0) )
        & ( v2_compts_1(k2_struct_0(X0),X0)
          | ~ v1_compts_1(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f58,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | ~ v2_compts_1(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f59,plain,(
    ! [X4,X2,X0,X1] :
      ( v2_compts_1(X4,X1)
      | X2 != X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_compts_1(X2,X0)
      | ~ r1_tarski(X2,k2_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f74,plain,(
    ! [X4,X0,X1] :
      ( v2_compts_1(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_compts_1(X4,X0)
      | ~ r1_tarski(X4,k2_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f59])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v4_pre_topc(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( X1 = X3
                     => v4_pre_topc(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v4_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v4_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( v4_pre_topc(X3,X2)
      | X1 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f73,plain,(
    ! [X2,X0,X3] :
      ( v4_pre_topc(X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v4_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f33])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f72,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f45])).

fof(f69,plain,(
    v4_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f67,plain,(
    v2_compts_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_438,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1594,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK2,X2)
    | X2 != X1
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_438])).

cnf(c_2679,plain,
    ( ~ r1_tarski(sK2,X0)
    | r1_tarski(sK2,X1)
    | X1 != X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1594])).

cnf(c_3668,plain,
    ( r1_tarski(sK2,X0)
    | ~ r1_tarski(sK2,u1_struct_0(k1_pre_topc(sK1,sK2)))
    | X0 != u1_struct_0(k1_pre_topc(sK1,sK2))
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_2679])).

cnf(c_33024,plain,
    ( ~ r1_tarski(sK2,u1_struct_0(k1_pre_topc(sK1,sK2)))
    | r1_tarski(sK2,k2_struct_0(k1_pre_topc(sK1,sK2)))
    | k2_struct_0(k1_pre_topc(sK1,sK2)) != u1_struct_0(k1_pre_topc(sK1,sK2))
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_3668])).

cnf(c_25,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_992,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_7,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1010,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1539,plain,
    ( l1_struct_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_992,c_1010])).

cnf(c_5,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1012,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1760,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(superposition,[status(thm)],[c_1539,c_1012])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_993,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2058,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1760,c_993])).

cnf(c_6,plain,
    ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1011,plain,
    ( m1_pre_topc(k1_pre_topc(X0,X1),X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3373,plain,
    ( m1_pre_topc(k1_pre_topc(sK1,X0),sK1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1760,c_1011])).

cnf(c_26,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_4243,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | m1_pre_topc(k1_pre_topc(sK1,X0),sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3373,c_26])).

cnf(c_4244,plain,
    ( m1_pre_topc(k1_pre_topc(sK1,X0),sK1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4243])).

cnf(c_4253,plain,
    ( m1_pre_topc(k1_pre_topc(sK1,sK2),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2058,c_4244])).

cnf(c_8,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1009,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4445,plain,
    ( l1_pre_topc(k1_pre_topc(sK1,sK2)) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4253,c_1009])).

cnf(c_27,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1257,plain,
    ( m1_pre_topc(k1_pre_topc(sK1,sK2),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1258,plain,
    ( m1_pre_topc(k1_pre_topc(sK1,sK2),sK1) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1257])).

cnf(c_2106,plain,
    ( ~ m1_pre_topc(k1_pre_topc(sK1,sK2),X0)
    | ~ l1_pre_topc(X0)
    | l1_pre_topc(k1_pre_topc(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2107,plain,
    ( m1_pre_topc(k1_pre_topc(sK1,sK2),X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(k1_pre_topc(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2106])).

cnf(c_2109,plain,
    ( m1_pre_topc(k1_pre_topc(sK1,sK2),sK1) != iProver_top
    | l1_pre_topc(k1_pre_topc(sK1,sK2)) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2107])).

cnf(c_4520,plain,
    ( l1_pre_topc(k1_pre_topc(sK1,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4445,c_26,c_27,c_1258,c_2109])).

cnf(c_4525,plain,
    ( l1_struct_0(k1_pre_topc(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4520,c_1010])).

cnf(c_4881,plain,
    ( u1_struct_0(k1_pre_topc(sK1,sK2)) = k2_struct_0(k1_pre_topc(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_4525,c_1012])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1008,plain,
    ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3333,plain,
    ( u1_struct_0(k1_pre_topc(sK1,X0)) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1760,c_1008])).

cnf(c_3748,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | u1_struct_0(k1_pre_topc(sK1,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3333,c_26])).

cnf(c_3749,plain,
    ( u1_struct_0(k1_pre_topc(sK1,X0)) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3748])).

cnf(c_3758,plain,
    ( u1_struct_0(k1_pre_topc(sK1,sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_2058,c_3749])).

cnf(c_4882,plain,
    ( k2_struct_0(k1_pre_topc(sK1,sK2)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_4881,c_3758])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_994,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2057,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1760,c_994])).

cnf(c_15,plain,
    ( v2_compts_1(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,k2_struct_0(X2))
    | ~ l1_pre_topc(X1)
    | sK0(X2,X0) = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1002,plain,
    ( sK0(X0,X1) = X1
    | v2_compts_1(X1,X2) = iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
    | r1_tarski(X1,k2_struct_0(X0)) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3173,plain,
    ( sK0(X0,X1) = X1
    | v2_compts_1(X1,sK1) = iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | r1_tarski(X1,k2_struct_0(X0)) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1760,c_1002])).

cnf(c_25487,plain,
    ( r1_tarski(X1,k2_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | v2_compts_1(X1,sK1) = iProver_top
    | sK0(X0,X1) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3173,c_26])).

cnf(c_25488,plain,
    ( sK0(X0,X1) = X1
    | v2_compts_1(X1,sK1) = iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | r1_tarski(X1,k2_struct_0(X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_25487])).

cnf(c_25499,plain,
    ( sK0(X0,sK3) = sK3
    | v2_compts_1(sK3,sK1) = iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | r1_tarski(sK3,k2_struct_0(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2057,c_25488])).

cnf(c_4907,plain,
    ( v2_compts_1(sK3,sK1)
    | ~ m1_pre_topc(X0,sK1)
    | ~ r1_tarski(sK3,k2_struct_0(X0))
    | ~ l1_pre_topc(sK1)
    | sK0(X0,sK3) = sK3 ),
    inference(resolution,[status(thm)],[c_15,c_23])).

cnf(c_19,negated_conjecture,
    ( ~ v2_compts_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_5234,plain,
    ( ~ r1_tarski(sK3,k2_struct_0(X0))
    | ~ m1_pre_topc(X0,sK1)
    | sK0(X0,sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4907,c_25,c_19])).

cnf(c_5235,plain,
    ( ~ m1_pre_topc(X0,sK1)
    | ~ r1_tarski(sK3,k2_struct_0(X0))
    | sK0(X0,sK3) = sK3 ),
    inference(renaming,[status(thm)],[c_5234])).

cnf(c_5236,plain,
    ( sK0(X0,sK3) = sK3
    | m1_pre_topc(X0,sK1) != iProver_top
    | r1_tarski(sK3,k2_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5235])).

cnf(c_26534,plain,
    ( sK0(X0,sK3) = sK3
    | m1_pre_topc(X0,sK1) != iProver_top
    | r1_tarski(sK3,k2_struct_0(X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_25499,c_5236])).

cnf(c_26545,plain,
    ( sK0(k1_pre_topc(sK1,sK2),sK3) = sK3
    | m1_pre_topc(k1_pre_topc(sK1,sK2),sK1) != iProver_top
    | r1_tarski(sK3,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4882,c_26534])).

cnf(c_21,negated_conjecture,
    ( r1_tarski(sK3,sK2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_30,plain,
    ( r1_tarski(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_26943,plain,
    ( sK0(k1_pre_topc(sK1,sK2),sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_26545,c_26,c_27,c_30,c_1258])).

cnf(c_16,plain,
    ( v2_compts_1(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(X0,k2_struct_0(X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1001,plain,
    ( v2_compts_1(X0,X1) = iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(sK0(X2,X0),k1_zfmisc_1(u1_struct_0(X2))) = iProver_top
    | r1_tarski(X0,k2_struct_0(X2)) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2216,plain,
    ( v2_compts_1(X0,sK1) = iProver_top
    | m1_pre_topc(X1,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | r1_tarski(X0,k2_struct_0(X1)) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1760,c_1001])).

cnf(c_2891,plain,
    ( r1_tarski(X0,k2_struct_0(X1)) != iProver_top
    | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | m1_pre_topc(X1,sK1) != iProver_top
    | v2_compts_1(X0,sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2216,c_26])).

cnf(c_2892,plain,
    ( v2_compts_1(X0,sK1) = iProver_top
    | m1_pre_topc(X1,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | r1_tarski(X0,k2_struct_0(X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2891])).

cnf(c_18,plain,
    ( v2_compts_1(X0,X1)
    | ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_compts_1(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_999,plain,
    ( v2_compts_1(X0,X1) = iProver_top
    | v4_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v1_compts_1(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2905,plain,
    ( v2_compts_1(X0,sK1) = iProver_top
    | v2_compts_1(sK0(X1,X0),X1) = iProver_top
    | v4_pre_topc(sK0(X1,X0),X1) != iProver_top
    | m1_pre_topc(X1,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | r1_tarski(X0,k2_struct_0(X1)) != iProver_top
    | v1_compts_1(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2892,c_999])).

cnf(c_14,plain,
    ( v2_compts_1(X0,X1)
    | ~ v2_compts_1(sK0(X2,X0),X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,k2_struct_0(X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1003,plain,
    ( v2_compts_1(X0,X1) = iProver_top
    | v2_compts_1(sK0(X2,X0),X2) != iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(X0,k2_struct_0(X2)) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3548,plain,
    ( v2_compts_1(X0,sK1) = iProver_top
    | v2_compts_1(sK0(X1,X0),X1) != iProver_top
    | m1_pre_topc(X1,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | r1_tarski(X0,k2_struct_0(X1)) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1760,c_1003])).

cnf(c_14100,plain,
    ( v2_compts_1(X0,sK1) = iProver_top
    | v4_pre_topc(sK0(X1,X0),X1) != iProver_top
    | m1_pre_topc(X1,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | r1_tarski(X0,k2_struct_0(X1)) != iProver_top
    | v1_compts_1(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2905,c_26,c_3548])).

cnf(c_14112,plain,
    ( v2_compts_1(sK3,sK1) = iProver_top
    | v4_pre_topc(sK0(X0,sK3),X0) != iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | r1_tarski(sK3,k2_struct_0(X0)) != iProver_top
    | v1_compts_1(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2057,c_14100])).

cnf(c_32,plain,
    ( v2_compts_1(sK3,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_14735,plain,
    ( v4_pre_topc(sK0(X0,sK3),X0) != iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | r1_tarski(sK3,k2_struct_0(X0)) != iProver_top
    | v1_compts_1(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14112,c_32])).

cnf(c_26952,plain,
    ( v4_pre_topc(sK3,k1_pre_topc(sK1,sK2)) != iProver_top
    | m1_pre_topc(k1_pre_topc(sK1,sK2),sK1) != iProver_top
    | r1_tarski(sK3,k2_struct_0(k1_pre_topc(sK1,sK2))) != iProver_top
    | v1_compts_1(k1_pre_topc(sK1,sK2)) != iProver_top
    | l1_pre_topc(k1_pre_topc(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_26943,c_14735])).

cnf(c_26958,plain,
    ( v4_pre_topc(sK3,k1_pre_topc(sK1,sK2)) != iProver_top
    | m1_pre_topc(k1_pre_topc(sK1,sK2),sK1) != iProver_top
    | r1_tarski(sK3,sK2) != iProver_top
    | v1_compts_1(k1_pre_topc(sK1,sK2)) != iProver_top
    | l1_pre_topc(k1_pre_topc(sK1,sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_26952,c_4882])).

cnf(c_27036,plain,
    ( ~ v4_pre_topc(sK3,k1_pre_topc(sK1,sK2))
    | ~ m1_pre_topc(k1_pre_topc(sK1,sK2),sK1)
    | ~ r1_tarski(sK3,sK2)
    | ~ v1_compts_1(k1_pre_topc(sK1,sK2))
    | ~ l1_pre_topc(k1_pre_topc(sK1,sK2)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_26958])).

cnf(c_437,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3269,plain,
    ( X0 != X1
    | k2_struct_0(k1_pre_topc(sK1,sK2)) != X1
    | k2_struct_0(k1_pre_topc(sK1,sK2)) = X0 ),
    inference(instantiation,[status(thm)],[c_437])).

cnf(c_4874,plain,
    ( X0 != k2_struct_0(k1_pre_topc(sK1,sK2))
    | k2_struct_0(k1_pre_topc(sK1,sK2)) = X0
    | k2_struct_0(k1_pre_topc(sK1,sK2)) != k2_struct_0(k1_pre_topc(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_3269])).

cnf(c_15159,plain,
    ( u1_struct_0(k1_pre_topc(sK1,sK2)) != k2_struct_0(k1_pre_topc(sK1,sK2))
    | k2_struct_0(k1_pre_topc(sK1,sK2)) = u1_struct_0(k1_pre_topc(sK1,sK2))
    | k2_struct_0(k1_pre_topc(sK1,sK2)) != k2_struct_0(k1_pre_topc(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_4874])).

cnf(c_5760,plain,
    ( ~ l1_struct_0(k1_pre_topc(sK1,sK2))
    | u1_struct_0(k1_pre_topc(sK1,sK2)) = k2_struct_0(k1_pre_topc(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_12,plain,
    ( ~ v2_compts_1(k2_struct_0(X0),X0)
    | v1_compts_1(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1005,plain,
    ( v2_compts_1(k2_struct_0(X0),X0) != iProver_top
    | v1_compts_1(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_5406,plain,
    ( v2_compts_1(sK2,k1_pre_topc(sK1,sK2)) != iProver_top
    | v1_compts_1(k1_pre_topc(sK1,sK2)) = iProver_top
    | l1_pre_topc(k1_pre_topc(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4882,c_1005])).

cnf(c_5420,plain,
    ( ~ v2_compts_1(sK2,k1_pre_topc(sK1,sK2))
    | v1_compts_1(k1_pre_topc(sK1,sK2))
    | ~ l1_pre_topc(k1_pre_topc(sK1,sK2)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5406])).

cnf(c_17,plain,
    ( ~ v2_compts_1(X0,X1)
    | v2_compts_1(X0,X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,k2_struct_0(X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1369,plain,
    ( v2_compts_1(X0,k1_pre_topc(sK1,sK2))
    | ~ v2_compts_1(X0,sK1)
    | ~ m1_pre_topc(k1_pre_topc(sK1,sK2),sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X0,k2_struct_0(k1_pre_topc(sK1,sK2)))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_4998,plain,
    ( v2_compts_1(sK2,k1_pre_topc(sK1,sK2))
    | ~ v2_compts_1(sK2,sK1)
    | ~ m1_pre_topc(k1_pre_topc(sK1,sK2),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(sK2,k2_struct_0(k1_pre_topc(sK1,sK2)))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_1369])).

cnf(c_11,plain,
    ( ~ v4_pre_topc(X0,X1)
    | v4_pre_topc(X0,X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1372,plain,
    ( v4_pre_topc(X0,k1_pre_topc(sK1,sK2))
    | ~ v4_pre_topc(X0,sK1)
    | ~ m1_pre_topc(k1_pre_topc(sK1,sK2),sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_4384,plain,
    ( v4_pre_topc(sK3,k1_pre_topc(sK1,sK2))
    | ~ v4_pre_topc(sK3,sK1)
    | ~ m1_pre_topc(k1_pre_topc(sK1,sK2),sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_1372])).

cnf(c_3,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1249,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,u1_struct_0(X1)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3307,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2))))
    | ~ r1_tarski(sK2,u1_struct_0(k1_pre_topc(sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_1249])).

cnf(c_436,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3264,plain,
    ( k2_struct_0(k1_pre_topc(sK1,sK2)) = k2_struct_0(k1_pre_topc(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_436])).

cnf(c_3048,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2))))
    | ~ r1_tarski(sK3,u1_struct_0(k1_pre_topc(sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_1249])).

cnf(c_2144,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k1_pre_topc(X1,X0)) ),
    inference(resolution,[status(thm)],[c_8,c_6])).

cnf(c_2162,plain,
    ( l1_pre_topc(k1_pre_topc(sK1,sK2))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[status(thm)],[c_2144,c_24])).

cnf(c_2108,plain,
    ( ~ m1_pre_topc(k1_pre_topc(sK1,sK2),sK1)
    | l1_pre_topc(k1_pre_topc(sK1,sK2))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_2106])).

cnf(c_2530,plain,
    ( l1_pre_topc(k1_pre_topc(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2162,c_25,c_24,c_1257,c_2108])).

cnf(c_2542,plain,
    ( l1_struct_0(k1_pre_topc(sK1,sK2)) ),
    inference(resolution,[status(thm)],[c_2530,c_7])).

cnf(c_1454,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,u1_struct_0(X3))
    | X2 != X0
    | u1_struct_0(X3) != X1 ),
    inference(instantiation,[status(thm)],[c_438])).

cnf(c_1827,plain,
    ( r1_tarski(X0,u1_struct_0(k1_pre_topc(sK1,sK2)))
    | ~ r1_tarski(X1,sK2)
    | X0 != X1
    | u1_struct_0(k1_pre_topc(sK1,sK2)) != sK2 ),
    inference(instantiation,[status(thm)],[c_1454])).

cnf(c_1969,plain,
    ( r1_tarski(X0,u1_struct_0(k1_pre_topc(sK1,sK2)))
    | ~ r1_tarski(sK2,sK2)
    | X0 != sK2
    | u1_struct_0(k1_pre_topc(sK1,sK2)) != sK2 ),
    inference(instantiation,[status(thm)],[c_1827])).

cnf(c_2447,plain,
    ( r1_tarski(sK2,u1_struct_0(k1_pre_topc(sK1,sK2)))
    | ~ r1_tarski(sK2,sK2)
    | u1_struct_0(k1_pre_topc(sK1,sK2)) != sK2
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1969])).

cnf(c_1977,plain,
    ( r1_tarski(X0,u1_struct_0(k1_pre_topc(sK1,sK2)))
    | ~ r1_tarski(sK3,sK2)
    | X0 != sK3
    | u1_struct_0(k1_pre_topc(sK1,sK2)) != sK2 ),
    inference(instantiation,[status(thm)],[c_1827])).

cnf(c_2019,plain,
    ( r1_tarski(sK3,u1_struct_0(k1_pre_topc(sK1,sK2)))
    | ~ r1_tarski(sK3,sK2)
    | u1_struct_0(k1_pre_topc(sK1,sK2)) != sK2
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1977])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1970,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1429,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_436])).

cnf(c_1413,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_436])).

cnf(c_1284,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | u1_struct_0(k1_pre_topc(sK1,sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_20,negated_conjecture,
    ( v4_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_22,negated_conjecture,
    ( v2_compts_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f67])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_33024,c_27036,c_15159,c_5760,c_5420,c_4998,c_4384,c_3307,c_3264,c_3048,c_2542,c_2447,c_2108,c_2019,c_1970,c_1429,c_1413,c_1284,c_1257,c_20,c_21,c_22,c_23,c_24,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:11:35 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  % Running in FOF mode
% 7.92/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.92/1.49  
% 7.92/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.92/1.49  
% 7.92/1.49  ------  iProver source info
% 7.92/1.49  
% 7.92/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.92/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.92/1.49  git: non_committed_changes: false
% 7.92/1.49  git: last_make_outside_of_git: false
% 7.92/1.49  
% 7.92/1.49  ------ 
% 7.92/1.49  ------ Parsing...
% 7.92/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.92/1.49  
% 7.92/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 7.92/1.49  
% 7.92/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.92/1.49  
% 7.92/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.92/1.49  ------ Proving...
% 7.92/1.49  ------ Problem Properties 
% 7.92/1.49  
% 7.92/1.49  
% 7.92/1.49  clauses                                 25
% 7.92/1.49  conjectures                             7
% 7.92/1.49  EPR                                     9
% 7.92/1.49  Horn                                    23
% 7.92/1.49  unary                                   8
% 7.92/1.49  binary                                  4
% 7.92/1.49  lits                                    74
% 7.92/1.49  lits eq                                 4
% 7.92/1.49  fd_pure                                 0
% 7.92/1.49  fd_pseudo                               0
% 7.92/1.49  fd_cond                                 0
% 7.92/1.49  fd_pseudo_cond                          1
% 7.92/1.49  AC symbols                              0
% 7.92/1.49  
% 7.92/1.49  ------ Input Options Time Limit: Unbounded
% 7.92/1.49  
% 7.92/1.49  
% 7.92/1.49  ------ 
% 7.92/1.49  Current options:
% 7.92/1.49  ------ 
% 7.92/1.49  
% 7.92/1.49  
% 7.92/1.49  
% 7.92/1.49  
% 7.92/1.49  ------ Proving...
% 7.92/1.49  
% 7.92/1.49  
% 7.92/1.49  % SZS status Theorem for theBenchmark.p
% 7.92/1.49  
% 7.92/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.92/1.49  
% 7.92/1.49  fof(f13,conjecture,(
% 7.92/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X2,X0) & r1_tarski(X2,X1) & v2_compts_1(X1,X0)) => v2_compts_1(X2,X0)))))),
% 7.92/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.92/1.49  
% 7.92/1.49  fof(f14,negated_conjecture,(
% 7.92/1.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X2,X0) & r1_tarski(X2,X1) & v2_compts_1(X1,X0)) => v2_compts_1(X2,X0)))))),
% 7.92/1.49    inference(negated_conjecture,[],[f13])).
% 7.92/1.49  
% 7.92/1.49  fof(f15,plain,(
% 7.92/1.49    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X2,X0) & r1_tarski(X2,X1) & v2_compts_1(X1,X0)) => v2_compts_1(X2,X0)))))),
% 7.92/1.49    inference(pure_predicate_removal,[],[f14])).
% 7.92/1.49  
% 7.92/1.49  fof(f31,plain,(
% 7.92/1.49    ? [X0] : (? [X1] : (? [X2] : ((~v2_compts_1(X2,X0) & (v4_pre_topc(X2,X0) & r1_tarski(X2,X1) & v2_compts_1(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 7.92/1.49    inference(ennf_transformation,[],[f15])).
% 7.92/1.49  
% 7.92/1.49  fof(f32,plain,(
% 7.92/1.49    ? [X0] : (? [X1] : (? [X2] : (~v2_compts_1(X2,X0) & v4_pre_topc(X2,X0) & r1_tarski(X2,X1) & v2_compts_1(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 7.92/1.49    inference(flattening,[],[f31])).
% 7.92/1.49  
% 7.92/1.49  fof(f43,plain,(
% 7.92/1.49    ( ! [X0,X1] : (? [X2] : (~v2_compts_1(X2,X0) & v4_pre_topc(X2,X0) & r1_tarski(X2,X1) & v2_compts_1(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v2_compts_1(sK3,X0) & v4_pre_topc(sK3,X0) & r1_tarski(sK3,X1) & v2_compts_1(X1,X0) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 7.92/1.49    introduced(choice_axiom,[])).
% 7.92/1.49  
% 7.92/1.49  fof(f42,plain,(
% 7.92/1.49    ( ! [X0] : (? [X1] : (? [X2] : (~v2_compts_1(X2,X0) & v4_pre_topc(X2,X0) & r1_tarski(X2,X1) & v2_compts_1(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~v2_compts_1(X2,X0) & v4_pre_topc(X2,X0) & r1_tarski(X2,sK2) & v2_compts_1(sK2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 7.92/1.49    introduced(choice_axiom,[])).
% 7.92/1.49  
% 7.92/1.49  fof(f41,plain,(
% 7.92/1.49    ? [X0] : (? [X1] : (? [X2] : (~v2_compts_1(X2,X0) & v4_pre_topc(X2,X0) & r1_tarski(X2,X1) & v2_compts_1(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v2_compts_1(X2,sK1) & v4_pre_topc(X2,sK1) & r1_tarski(X2,X1) & v2_compts_1(X1,sK1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1))),
% 7.92/1.49    introduced(choice_axiom,[])).
% 7.92/1.49  
% 7.92/1.49  fof(f44,plain,(
% 7.92/1.49    ((~v2_compts_1(sK3,sK1) & v4_pre_topc(sK3,sK1) & r1_tarski(sK3,sK2) & v2_compts_1(sK2,sK1) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1)),
% 7.92/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f32,f43,f42,f41])).
% 7.92/1.49  
% 7.92/1.49  fof(f64,plain,(
% 7.92/1.49    l1_pre_topc(sK1)),
% 7.92/1.49    inference(cnf_transformation,[],[f44])).
% 7.92/1.49  
% 7.92/1.49  fof(f5,axiom,(
% 7.92/1.49    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 7.92/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.92/1.49  
% 7.92/1.49  fof(f20,plain,(
% 7.92/1.49    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 7.92/1.49    inference(ennf_transformation,[],[f5])).
% 7.92/1.49  
% 7.92/1.49  fof(f52,plain,(
% 7.92/1.49    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 7.92/1.49    inference(cnf_transformation,[],[f20])).
% 7.92/1.49  
% 7.92/1.49  fof(f3,axiom,(
% 7.92/1.49    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 7.92/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.92/1.49  
% 7.92/1.49  fof(f17,plain,(
% 7.92/1.49    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 7.92/1.49    inference(ennf_transformation,[],[f3])).
% 7.92/1.49  
% 7.92/1.49  fof(f50,plain,(
% 7.92/1.49    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 7.92/1.49    inference(cnf_transformation,[],[f17])).
% 7.92/1.49  
% 7.92/1.49  fof(f65,plain,(
% 7.92/1.49    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 7.92/1.49    inference(cnf_transformation,[],[f44])).
% 7.92/1.49  
% 7.92/1.49  fof(f4,axiom,(
% 7.92/1.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => (m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))))),
% 7.92/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.92/1.49  
% 7.92/1.49  fof(f16,plain,(
% 7.92/1.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_pre_topc(k1_pre_topc(X0,X1),X0))),
% 7.92/1.49    inference(pure_predicate_removal,[],[f4])).
% 7.92/1.49  
% 7.92/1.49  fof(f18,plain,(
% 7.92/1.49    ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 7.92/1.49    inference(ennf_transformation,[],[f16])).
% 7.92/1.49  
% 7.92/1.49  fof(f19,plain,(
% 7.92/1.49    ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 7.92/1.49    inference(flattening,[],[f18])).
% 7.92/1.49  
% 7.92/1.49  fof(f51,plain,(
% 7.92/1.49    ( ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.92/1.49    inference(cnf_transformation,[],[f19])).
% 7.92/1.49  
% 7.92/1.49  fof(f6,axiom,(
% 7.92/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 7.92/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.92/1.49  
% 7.92/1.49  fof(f21,plain,(
% 7.92/1.49    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.92/1.49    inference(ennf_transformation,[],[f6])).
% 7.92/1.49  
% 7.92/1.49  fof(f53,plain,(
% 7.92/1.49    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.92/1.49    inference(cnf_transformation,[],[f21])).
% 7.92/1.49  
% 7.92/1.49  fof(f7,axiom,(
% 7.92/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => u1_struct_0(k1_pre_topc(X0,X1)) = X1))),
% 7.92/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.92/1.49  
% 7.92/1.49  fof(f22,plain,(
% 7.92/1.49    ! [X0] : (! [X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.92/1.49    inference(ennf_transformation,[],[f7])).
% 7.92/1.49  
% 7.92/1.49  fof(f54,plain,(
% 7.92/1.49    ( ! [X0,X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.92/1.49    inference(cnf_transformation,[],[f22])).
% 7.92/1.49  
% 7.92/1.49  fof(f66,plain,(
% 7.92/1.49    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 7.92/1.49    inference(cnf_transformation,[],[f44])).
% 7.92/1.49  
% 7.92/1.49  fof(f11,axiom,(
% 7.92/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X2,k2_struct_0(X1)) => (v2_compts_1(X2,X0) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (X2 = X3 => v2_compts_1(X3,X1))))))))),
% 7.92/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.92/1.49  
% 7.92/1.49  fof(f27,plain,(
% 7.92/1.49    ! [X0] : (! [X1] : (! [X2] : (((v2_compts_1(X2,X0) <=> ! [X3] : ((v2_compts_1(X3,X1) | X2 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~r1_tarski(X2,k2_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.92/1.49    inference(ennf_transformation,[],[f11])).
% 7.92/1.49  
% 7.92/1.49  fof(f28,plain,(
% 7.92/1.49    ! [X0] : (! [X1] : (! [X2] : ((v2_compts_1(X2,X0) <=> ! [X3] : (v2_compts_1(X3,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.92/1.49    inference(flattening,[],[f27])).
% 7.92/1.49  
% 7.92/1.49  fof(f37,plain,(
% 7.92/1.49    ! [X0] : (! [X1] : (! [X2] : (((v2_compts_1(X2,X0) | ? [X3] : (~v2_compts_1(X3,X1) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (v2_compts_1(X3,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_compts_1(X2,X0))) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.92/1.49    inference(nnf_transformation,[],[f28])).
% 7.92/1.49  
% 7.92/1.49  fof(f38,plain,(
% 7.92/1.49    ! [X0] : (! [X1] : (! [X2] : (((v2_compts_1(X2,X0) | ? [X3] : (~v2_compts_1(X3,X1) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v2_compts_1(X4,X1) | X2 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_compts_1(X2,X0))) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.92/1.49    inference(rectify,[],[f37])).
% 7.92/1.49  
% 7.92/1.49  fof(f39,plain,(
% 7.92/1.49    ! [X2,X1] : (? [X3] : (~v2_compts_1(X3,X1) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => (~v2_compts_1(sK0(X1,X2),X1) & sK0(X1,X2) = X2 & m1_subset_1(sK0(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))))),
% 7.92/1.49    introduced(choice_axiom,[])).
% 7.92/1.49  
% 7.92/1.49  fof(f40,plain,(
% 7.92/1.49    ! [X0] : (! [X1] : (! [X2] : (((v2_compts_1(X2,X0) | (~v2_compts_1(sK0(X1,X2),X1) & sK0(X1,X2) = X2 & m1_subset_1(sK0(X1,X2),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v2_compts_1(X4,X1) | X2 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_compts_1(X2,X0))) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.92/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f38,f39])).
% 7.92/1.49  
% 7.92/1.49  fof(f61,plain,(
% 7.92/1.49    ( ! [X2,X0,X1] : (v2_compts_1(X2,X0) | sK0(X1,X2) = X2 | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.92/1.49    inference(cnf_transformation,[],[f40])).
% 7.92/1.49  
% 7.92/1.49  fof(f70,plain,(
% 7.92/1.49    ~v2_compts_1(sK3,sK1)),
% 7.92/1.49    inference(cnf_transformation,[],[f44])).
% 7.92/1.49  
% 7.92/1.49  fof(f68,plain,(
% 7.92/1.49    r1_tarski(sK3,sK2)),
% 7.92/1.49    inference(cnf_transformation,[],[f44])).
% 7.92/1.49  
% 7.92/1.49  fof(f60,plain,(
% 7.92/1.49    ( ! [X2,X0,X1] : (v2_compts_1(X2,X0) | m1_subset_1(sK0(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.92/1.49    inference(cnf_transformation,[],[f40])).
% 7.92/1.49  
% 7.92/1.49  fof(f12,axiom,(
% 7.92/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X1,X0) & v1_compts_1(X0)) => v2_compts_1(X1,X0))))),
% 7.92/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.92/1.49  
% 7.92/1.49  fof(f29,plain,(
% 7.92/1.49    ! [X0] : (! [X1] : ((v2_compts_1(X1,X0) | (~v4_pre_topc(X1,X0) | ~v1_compts_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.92/1.49    inference(ennf_transformation,[],[f12])).
% 7.92/1.49  
% 7.92/1.49  fof(f30,plain,(
% 7.92/1.49    ! [X0] : (! [X1] : (v2_compts_1(X1,X0) | ~v4_pre_topc(X1,X0) | ~v1_compts_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.92/1.49    inference(flattening,[],[f29])).
% 7.92/1.49  
% 7.92/1.49  fof(f63,plain,(
% 7.92/1.49    ( ! [X0,X1] : (v2_compts_1(X1,X0) | ~v4_pre_topc(X1,X0) | ~v1_compts_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.92/1.49    inference(cnf_transformation,[],[f30])).
% 7.92/1.49  
% 7.92/1.49  fof(f62,plain,(
% 7.92/1.49    ( ! [X2,X0,X1] : (v2_compts_1(X2,X0) | ~v2_compts_1(sK0(X1,X2),X1) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.92/1.49    inference(cnf_transformation,[],[f40])).
% 7.92/1.49  
% 7.92/1.49  fof(f10,axiom,(
% 7.92/1.49    ! [X0] : (l1_pre_topc(X0) => (v1_compts_1(X0) <=> v2_compts_1(k2_struct_0(X0),X0)))),
% 7.92/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.92/1.49  
% 7.92/1.49  fof(f26,plain,(
% 7.92/1.49    ! [X0] : ((v1_compts_1(X0) <=> v2_compts_1(k2_struct_0(X0),X0)) | ~l1_pre_topc(X0))),
% 7.92/1.49    inference(ennf_transformation,[],[f10])).
% 7.92/1.49  
% 7.92/1.49  fof(f36,plain,(
% 7.92/1.49    ! [X0] : (((v1_compts_1(X0) | ~v2_compts_1(k2_struct_0(X0),X0)) & (v2_compts_1(k2_struct_0(X0),X0) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0))),
% 7.92/1.49    inference(nnf_transformation,[],[f26])).
% 7.92/1.49  
% 7.92/1.49  fof(f58,plain,(
% 7.92/1.49    ( ! [X0] : (v1_compts_1(X0) | ~v2_compts_1(k2_struct_0(X0),X0) | ~l1_pre_topc(X0)) )),
% 7.92/1.49    inference(cnf_transformation,[],[f36])).
% 7.92/1.49  
% 7.92/1.49  fof(f59,plain,(
% 7.92/1.49    ( ! [X4,X2,X0,X1] : (v2_compts_1(X4,X1) | X2 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v2_compts_1(X2,X0) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.92/1.49    inference(cnf_transformation,[],[f40])).
% 7.92/1.49  
% 7.92/1.49  fof(f74,plain,(
% 7.92/1.49    ( ! [X4,X0,X1] : (v2_compts_1(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v2_compts_1(X4,X0) | ~r1_tarski(X4,k2_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.92/1.49    inference(equality_resolution,[],[f59])).
% 7.92/1.49  
% 7.92/1.49  fof(f9,axiom,(
% 7.92/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v4_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v4_pre_topc(X3,X2)))))))),
% 7.92/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.92/1.49  
% 7.92/1.49  fof(f24,plain,(
% 7.92/1.49    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((v4_pre_topc(X3,X2) | X1 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v4_pre_topc(X1,X0)) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.92/1.49    inference(ennf_transformation,[],[f9])).
% 7.92/1.49  
% 7.92/1.49  fof(f25,plain,(
% 7.92/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v4_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v4_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.92/1.49    inference(flattening,[],[f24])).
% 7.92/1.49  
% 7.92/1.49  fof(f56,plain,(
% 7.92/1.49    ( ! [X2,X0,X3,X1] : (v4_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~v4_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.92/1.49    inference(cnf_transformation,[],[f25])).
% 7.92/1.49  
% 7.92/1.49  fof(f73,plain,(
% 7.92/1.49    ( ! [X2,X0,X3] : (v4_pre_topc(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~v4_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.92/1.49    inference(equality_resolution,[],[f56])).
% 7.92/1.49  
% 7.92/1.49  fof(f2,axiom,(
% 7.92/1.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.92/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.92/1.49  
% 7.92/1.49  fof(f35,plain,(
% 7.92/1.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.92/1.49    inference(nnf_transformation,[],[f2])).
% 7.92/1.49  
% 7.92/1.49  fof(f49,plain,(
% 7.92/1.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.92/1.49    inference(cnf_transformation,[],[f35])).
% 7.92/1.49  
% 7.92/1.49  fof(f1,axiom,(
% 7.92/1.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.92/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.92/1.49  
% 7.92/1.49  fof(f33,plain,(
% 7.92/1.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.92/1.49    inference(nnf_transformation,[],[f1])).
% 7.92/1.49  
% 7.92/1.49  fof(f34,plain,(
% 7.92/1.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.92/1.49    inference(flattening,[],[f33])).
% 7.92/1.49  
% 7.92/1.49  fof(f45,plain,(
% 7.92/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.92/1.49    inference(cnf_transformation,[],[f34])).
% 7.92/1.49  
% 7.92/1.49  fof(f72,plain,(
% 7.92/1.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.92/1.49    inference(equality_resolution,[],[f45])).
% 7.92/1.49  
% 7.92/1.49  fof(f69,plain,(
% 7.92/1.49    v4_pre_topc(sK3,sK1)),
% 7.92/1.49    inference(cnf_transformation,[],[f44])).
% 7.92/1.49  
% 7.92/1.49  fof(f67,plain,(
% 7.92/1.49    v2_compts_1(sK2,sK1)),
% 7.92/1.49    inference(cnf_transformation,[],[f44])).
% 7.92/1.49  
% 7.92/1.49  cnf(c_438,plain,
% 7.92/1.49      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.92/1.49      theory(equality) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_1594,plain,
% 7.92/1.49      ( ~ r1_tarski(X0,X1) | r1_tarski(sK2,X2) | X2 != X1 | sK2 != X0 ),
% 7.92/1.49      inference(instantiation,[status(thm)],[c_438]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_2679,plain,
% 7.92/1.49      ( ~ r1_tarski(sK2,X0) | r1_tarski(sK2,X1) | X1 != X0 | sK2 != sK2 ),
% 7.92/1.49      inference(instantiation,[status(thm)],[c_1594]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_3668,plain,
% 7.92/1.49      ( r1_tarski(sK2,X0)
% 7.92/1.49      | ~ r1_tarski(sK2,u1_struct_0(k1_pre_topc(sK1,sK2)))
% 7.92/1.49      | X0 != u1_struct_0(k1_pre_topc(sK1,sK2))
% 7.92/1.49      | sK2 != sK2 ),
% 7.92/1.49      inference(instantiation,[status(thm)],[c_2679]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_33024,plain,
% 7.92/1.49      ( ~ r1_tarski(sK2,u1_struct_0(k1_pre_topc(sK1,sK2)))
% 7.92/1.49      | r1_tarski(sK2,k2_struct_0(k1_pre_topc(sK1,sK2)))
% 7.92/1.49      | k2_struct_0(k1_pre_topc(sK1,sK2)) != u1_struct_0(k1_pre_topc(sK1,sK2))
% 7.92/1.49      | sK2 != sK2 ),
% 7.92/1.49      inference(instantiation,[status(thm)],[c_3668]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_25,negated_conjecture,
% 7.92/1.49      ( l1_pre_topc(sK1) ),
% 7.92/1.49      inference(cnf_transformation,[],[f64]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_992,plain,
% 7.92/1.49      ( l1_pre_topc(sK1) = iProver_top ),
% 7.92/1.49      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_7,plain,
% 7.92/1.49      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 7.92/1.49      inference(cnf_transformation,[],[f52]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_1010,plain,
% 7.92/1.49      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 7.92/1.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_1539,plain,
% 7.92/1.49      ( l1_struct_0(sK1) = iProver_top ),
% 7.92/1.49      inference(superposition,[status(thm)],[c_992,c_1010]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_5,plain,
% 7.92/1.49      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 7.92/1.49      inference(cnf_transformation,[],[f50]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_1012,plain,
% 7.92/1.49      ( u1_struct_0(X0) = k2_struct_0(X0)
% 7.92/1.49      | l1_struct_0(X0) != iProver_top ),
% 7.92/1.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_1760,plain,
% 7.92/1.49      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 7.92/1.49      inference(superposition,[status(thm)],[c_1539,c_1012]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_24,negated_conjecture,
% 7.92/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 7.92/1.49      inference(cnf_transformation,[],[f65]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_993,plain,
% 7.92/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 7.92/1.49      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_2058,plain,
% 7.92/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
% 7.92/1.49      inference(demodulation,[status(thm)],[c_1760,c_993]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_6,plain,
% 7.92/1.49      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
% 7.92/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 7.92/1.49      | ~ l1_pre_topc(X0) ),
% 7.92/1.49      inference(cnf_transformation,[],[f51]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_1011,plain,
% 7.92/1.49      ( m1_pre_topc(k1_pre_topc(X0,X1),X0) = iProver_top
% 7.92/1.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.92/1.49      | l1_pre_topc(X0) != iProver_top ),
% 7.92/1.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_3373,plain,
% 7.92/1.49      ( m1_pre_topc(k1_pre_topc(sK1,X0),sK1) = iProver_top
% 7.92/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 7.92/1.49      | l1_pre_topc(sK1) != iProver_top ),
% 7.92/1.49      inference(superposition,[status(thm)],[c_1760,c_1011]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_26,plain,
% 7.92/1.49      ( l1_pre_topc(sK1) = iProver_top ),
% 7.92/1.49      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_4243,plain,
% 7.92/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 7.92/1.49      | m1_pre_topc(k1_pre_topc(sK1,X0),sK1) = iProver_top ),
% 7.92/1.49      inference(global_propositional_subsumption,
% 7.92/1.49                [status(thm)],
% 7.92/1.49                [c_3373,c_26]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_4244,plain,
% 7.92/1.49      ( m1_pre_topc(k1_pre_topc(sK1,X0),sK1) = iProver_top
% 7.92/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 7.92/1.49      inference(renaming,[status(thm)],[c_4243]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_4253,plain,
% 7.92/1.49      ( m1_pre_topc(k1_pre_topc(sK1,sK2),sK1) = iProver_top ),
% 7.92/1.49      inference(superposition,[status(thm)],[c_2058,c_4244]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_8,plain,
% 7.92/1.49      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 7.92/1.49      inference(cnf_transformation,[],[f53]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_1009,plain,
% 7.92/1.49      ( m1_pre_topc(X0,X1) != iProver_top
% 7.92/1.49      | l1_pre_topc(X1) != iProver_top
% 7.92/1.49      | l1_pre_topc(X0) = iProver_top ),
% 7.92/1.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_4445,plain,
% 7.92/1.49      ( l1_pre_topc(k1_pre_topc(sK1,sK2)) = iProver_top
% 7.92/1.49      | l1_pre_topc(sK1) != iProver_top ),
% 7.92/1.49      inference(superposition,[status(thm)],[c_4253,c_1009]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_27,plain,
% 7.92/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 7.92/1.49      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_1257,plain,
% 7.92/1.49      ( m1_pre_topc(k1_pre_topc(sK1,sK2),sK1)
% 7.92/1.49      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.92/1.49      | ~ l1_pre_topc(sK1) ),
% 7.92/1.49      inference(instantiation,[status(thm)],[c_6]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_1258,plain,
% 7.92/1.49      ( m1_pre_topc(k1_pre_topc(sK1,sK2),sK1) = iProver_top
% 7.92/1.49      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 7.92/1.49      | l1_pre_topc(sK1) != iProver_top ),
% 7.92/1.49      inference(predicate_to_equality,[status(thm)],[c_1257]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_2106,plain,
% 7.92/1.49      ( ~ m1_pre_topc(k1_pre_topc(sK1,sK2),X0)
% 7.92/1.49      | ~ l1_pre_topc(X0)
% 7.92/1.49      | l1_pre_topc(k1_pre_topc(sK1,sK2)) ),
% 7.92/1.49      inference(instantiation,[status(thm)],[c_8]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_2107,plain,
% 7.92/1.49      ( m1_pre_topc(k1_pre_topc(sK1,sK2),X0) != iProver_top
% 7.92/1.49      | l1_pre_topc(X0) != iProver_top
% 7.92/1.49      | l1_pre_topc(k1_pre_topc(sK1,sK2)) = iProver_top ),
% 7.92/1.49      inference(predicate_to_equality,[status(thm)],[c_2106]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_2109,plain,
% 7.92/1.49      ( m1_pre_topc(k1_pre_topc(sK1,sK2),sK1) != iProver_top
% 7.92/1.49      | l1_pre_topc(k1_pre_topc(sK1,sK2)) = iProver_top
% 7.92/1.49      | l1_pre_topc(sK1) != iProver_top ),
% 7.92/1.49      inference(instantiation,[status(thm)],[c_2107]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_4520,plain,
% 7.92/1.49      ( l1_pre_topc(k1_pre_topc(sK1,sK2)) = iProver_top ),
% 7.92/1.49      inference(global_propositional_subsumption,
% 7.92/1.49                [status(thm)],
% 7.92/1.49                [c_4445,c_26,c_27,c_1258,c_2109]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_4525,plain,
% 7.92/1.49      ( l1_struct_0(k1_pre_topc(sK1,sK2)) = iProver_top ),
% 7.92/1.49      inference(superposition,[status(thm)],[c_4520,c_1010]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_4881,plain,
% 7.92/1.49      ( u1_struct_0(k1_pre_topc(sK1,sK2)) = k2_struct_0(k1_pre_topc(sK1,sK2)) ),
% 7.92/1.49      inference(superposition,[status(thm)],[c_4525,c_1012]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_9,plain,
% 7.92/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.92/1.49      | ~ l1_pre_topc(X1)
% 7.92/1.49      | u1_struct_0(k1_pre_topc(X1,X0)) = X0 ),
% 7.92/1.49      inference(cnf_transformation,[],[f54]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_1008,plain,
% 7.92/1.49      ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
% 7.92/1.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.92/1.49      | l1_pre_topc(X0) != iProver_top ),
% 7.92/1.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_3333,plain,
% 7.92/1.49      ( u1_struct_0(k1_pre_topc(sK1,X0)) = X0
% 7.92/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 7.92/1.49      | l1_pre_topc(sK1) != iProver_top ),
% 7.92/1.49      inference(superposition,[status(thm)],[c_1760,c_1008]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_3748,plain,
% 7.92/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 7.92/1.49      | u1_struct_0(k1_pre_topc(sK1,X0)) = X0 ),
% 7.92/1.49      inference(global_propositional_subsumption,
% 7.92/1.49                [status(thm)],
% 7.92/1.49                [c_3333,c_26]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_3749,plain,
% 7.92/1.49      ( u1_struct_0(k1_pre_topc(sK1,X0)) = X0
% 7.92/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 7.92/1.49      inference(renaming,[status(thm)],[c_3748]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_3758,plain,
% 7.92/1.49      ( u1_struct_0(k1_pre_topc(sK1,sK2)) = sK2 ),
% 7.92/1.49      inference(superposition,[status(thm)],[c_2058,c_3749]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_4882,plain,
% 7.92/1.49      ( k2_struct_0(k1_pre_topc(sK1,sK2)) = sK2 ),
% 7.92/1.49      inference(light_normalisation,[status(thm)],[c_4881,c_3758]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_23,negated_conjecture,
% 7.92/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 7.92/1.49      inference(cnf_transformation,[],[f66]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_994,plain,
% 7.92/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 7.92/1.49      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_2057,plain,
% 7.92/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
% 7.92/1.49      inference(demodulation,[status(thm)],[c_1760,c_994]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_15,plain,
% 7.92/1.49      ( v2_compts_1(X0,X1)
% 7.92/1.49      | ~ m1_pre_topc(X2,X1)
% 7.92/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.92/1.49      | ~ r1_tarski(X0,k2_struct_0(X2))
% 7.92/1.49      | ~ l1_pre_topc(X1)
% 7.92/1.49      | sK0(X2,X0) = X0 ),
% 7.92/1.49      inference(cnf_transformation,[],[f61]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_1002,plain,
% 7.92/1.49      ( sK0(X0,X1) = X1
% 7.92/1.49      | v2_compts_1(X1,X2) = iProver_top
% 7.92/1.49      | m1_pre_topc(X0,X2) != iProver_top
% 7.92/1.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
% 7.92/1.49      | r1_tarski(X1,k2_struct_0(X0)) != iProver_top
% 7.92/1.49      | l1_pre_topc(X2) != iProver_top ),
% 7.92/1.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_3173,plain,
% 7.92/1.49      ( sK0(X0,X1) = X1
% 7.92/1.49      | v2_compts_1(X1,sK1) = iProver_top
% 7.92/1.49      | m1_pre_topc(X0,sK1) != iProver_top
% 7.92/1.49      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 7.92/1.49      | r1_tarski(X1,k2_struct_0(X0)) != iProver_top
% 7.92/1.49      | l1_pre_topc(sK1) != iProver_top ),
% 7.92/1.49      inference(superposition,[status(thm)],[c_1760,c_1002]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_25487,plain,
% 7.92/1.49      ( r1_tarski(X1,k2_struct_0(X0)) != iProver_top
% 7.92/1.49      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 7.92/1.49      | m1_pre_topc(X0,sK1) != iProver_top
% 7.92/1.49      | v2_compts_1(X1,sK1) = iProver_top
% 7.92/1.49      | sK0(X0,X1) = X1 ),
% 7.92/1.49      inference(global_propositional_subsumption,
% 7.92/1.49                [status(thm)],
% 7.92/1.49                [c_3173,c_26]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_25488,plain,
% 7.92/1.49      ( sK0(X0,X1) = X1
% 7.92/1.49      | v2_compts_1(X1,sK1) = iProver_top
% 7.92/1.49      | m1_pre_topc(X0,sK1) != iProver_top
% 7.92/1.49      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 7.92/1.49      | r1_tarski(X1,k2_struct_0(X0)) != iProver_top ),
% 7.92/1.49      inference(renaming,[status(thm)],[c_25487]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_25499,plain,
% 7.92/1.49      ( sK0(X0,sK3) = sK3
% 7.92/1.49      | v2_compts_1(sK3,sK1) = iProver_top
% 7.92/1.49      | m1_pre_topc(X0,sK1) != iProver_top
% 7.92/1.49      | r1_tarski(sK3,k2_struct_0(X0)) != iProver_top ),
% 7.92/1.49      inference(superposition,[status(thm)],[c_2057,c_25488]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_4907,plain,
% 7.92/1.49      ( v2_compts_1(sK3,sK1)
% 7.92/1.49      | ~ m1_pre_topc(X0,sK1)
% 7.92/1.49      | ~ r1_tarski(sK3,k2_struct_0(X0))
% 7.92/1.49      | ~ l1_pre_topc(sK1)
% 7.92/1.49      | sK0(X0,sK3) = sK3 ),
% 7.92/1.49      inference(resolution,[status(thm)],[c_15,c_23]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_19,negated_conjecture,
% 7.92/1.49      ( ~ v2_compts_1(sK3,sK1) ),
% 7.92/1.49      inference(cnf_transformation,[],[f70]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_5234,plain,
% 7.92/1.49      ( ~ r1_tarski(sK3,k2_struct_0(X0))
% 7.92/1.49      | ~ m1_pre_topc(X0,sK1)
% 7.92/1.49      | sK0(X0,sK3) = sK3 ),
% 7.92/1.49      inference(global_propositional_subsumption,
% 7.92/1.49                [status(thm)],
% 7.92/1.49                [c_4907,c_25,c_19]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_5235,plain,
% 7.92/1.49      ( ~ m1_pre_topc(X0,sK1)
% 7.92/1.49      | ~ r1_tarski(sK3,k2_struct_0(X0))
% 7.92/1.49      | sK0(X0,sK3) = sK3 ),
% 7.92/1.49      inference(renaming,[status(thm)],[c_5234]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_5236,plain,
% 7.92/1.49      ( sK0(X0,sK3) = sK3
% 7.92/1.49      | m1_pre_topc(X0,sK1) != iProver_top
% 7.92/1.49      | r1_tarski(sK3,k2_struct_0(X0)) != iProver_top ),
% 7.92/1.49      inference(predicate_to_equality,[status(thm)],[c_5235]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_26534,plain,
% 7.92/1.49      ( sK0(X0,sK3) = sK3
% 7.92/1.49      | m1_pre_topc(X0,sK1) != iProver_top
% 7.92/1.49      | r1_tarski(sK3,k2_struct_0(X0)) != iProver_top ),
% 7.92/1.49      inference(global_propositional_subsumption,
% 7.92/1.49                [status(thm)],
% 7.92/1.49                [c_25499,c_5236]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_26545,plain,
% 7.92/1.49      ( sK0(k1_pre_topc(sK1,sK2),sK3) = sK3
% 7.92/1.49      | m1_pre_topc(k1_pre_topc(sK1,sK2),sK1) != iProver_top
% 7.92/1.49      | r1_tarski(sK3,sK2) != iProver_top ),
% 7.92/1.49      inference(superposition,[status(thm)],[c_4882,c_26534]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_21,negated_conjecture,
% 7.92/1.49      ( r1_tarski(sK3,sK2) ),
% 7.92/1.49      inference(cnf_transformation,[],[f68]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_30,plain,
% 7.92/1.49      ( r1_tarski(sK3,sK2) = iProver_top ),
% 7.92/1.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_26943,plain,
% 7.92/1.49      ( sK0(k1_pre_topc(sK1,sK2),sK3) = sK3 ),
% 7.92/1.49      inference(global_propositional_subsumption,
% 7.92/1.49                [status(thm)],
% 7.92/1.49                [c_26545,c_26,c_27,c_30,c_1258]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_16,plain,
% 7.92/1.49      ( v2_compts_1(X0,X1)
% 7.92/1.49      | ~ m1_pre_topc(X2,X1)
% 7.92/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.92/1.49      | m1_subset_1(sK0(X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
% 7.92/1.49      | ~ r1_tarski(X0,k2_struct_0(X2))
% 7.92/1.49      | ~ l1_pre_topc(X1) ),
% 7.92/1.49      inference(cnf_transformation,[],[f60]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_1001,plain,
% 7.92/1.49      ( v2_compts_1(X0,X1) = iProver_top
% 7.92/1.49      | m1_pre_topc(X2,X1) != iProver_top
% 7.92/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 7.92/1.49      | m1_subset_1(sK0(X2,X0),k1_zfmisc_1(u1_struct_0(X2))) = iProver_top
% 7.92/1.49      | r1_tarski(X0,k2_struct_0(X2)) != iProver_top
% 7.92/1.49      | l1_pre_topc(X1) != iProver_top ),
% 7.92/1.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_2216,plain,
% 7.92/1.49      ( v2_compts_1(X0,sK1) = iProver_top
% 7.92/1.49      | m1_pre_topc(X1,sK1) != iProver_top
% 7.92/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 7.92/1.49      | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 7.92/1.49      | r1_tarski(X0,k2_struct_0(X1)) != iProver_top
% 7.92/1.49      | l1_pre_topc(sK1) != iProver_top ),
% 7.92/1.49      inference(superposition,[status(thm)],[c_1760,c_1001]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_2891,plain,
% 7.92/1.49      ( r1_tarski(X0,k2_struct_0(X1)) != iProver_top
% 7.92/1.49      | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 7.92/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 7.92/1.49      | m1_pre_topc(X1,sK1) != iProver_top
% 7.92/1.49      | v2_compts_1(X0,sK1) = iProver_top ),
% 7.92/1.49      inference(global_propositional_subsumption,
% 7.92/1.49                [status(thm)],
% 7.92/1.49                [c_2216,c_26]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_2892,plain,
% 7.92/1.49      ( v2_compts_1(X0,sK1) = iProver_top
% 7.92/1.49      | m1_pre_topc(X1,sK1) != iProver_top
% 7.92/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 7.92/1.49      | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 7.92/1.49      | r1_tarski(X0,k2_struct_0(X1)) != iProver_top ),
% 7.92/1.49      inference(renaming,[status(thm)],[c_2891]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_18,plain,
% 7.92/1.49      ( v2_compts_1(X0,X1)
% 7.92/1.49      | ~ v4_pre_topc(X0,X1)
% 7.92/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.92/1.49      | ~ v1_compts_1(X1)
% 7.92/1.49      | ~ l1_pre_topc(X1) ),
% 7.92/1.49      inference(cnf_transformation,[],[f63]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_999,plain,
% 7.92/1.49      ( v2_compts_1(X0,X1) = iProver_top
% 7.92/1.49      | v4_pre_topc(X0,X1) != iProver_top
% 7.92/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 7.92/1.49      | v1_compts_1(X1) != iProver_top
% 7.92/1.49      | l1_pre_topc(X1) != iProver_top ),
% 7.92/1.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_2905,plain,
% 7.92/1.49      ( v2_compts_1(X0,sK1) = iProver_top
% 7.92/1.49      | v2_compts_1(sK0(X1,X0),X1) = iProver_top
% 7.92/1.49      | v4_pre_topc(sK0(X1,X0),X1) != iProver_top
% 7.92/1.49      | m1_pre_topc(X1,sK1) != iProver_top
% 7.92/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 7.92/1.49      | r1_tarski(X0,k2_struct_0(X1)) != iProver_top
% 7.92/1.49      | v1_compts_1(X1) != iProver_top
% 7.92/1.49      | l1_pre_topc(X1) != iProver_top ),
% 7.92/1.49      inference(superposition,[status(thm)],[c_2892,c_999]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_14,plain,
% 7.92/1.49      ( v2_compts_1(X0,X1)
% 7.92/1.49      | ~ v2_compts_1(sK0(X2,X0),X2)
% 7.92/1.49      | ~ m1_pre_topc(X2,X1)
% 7.92/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.92/1.49      | ~ r1_tarski(X0,k2_struct_0(X2))
% 7.92/1.49      | ~ l1_pre_topc(X1) ),
% 7.92/1.49      inference(cnf_transformation,[],[f62]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_1003,plain,
% 7.92/1.49      ( v2_compts_1(X0,X1) = iProver_top
% 7.92/1.49      | v2_compts_1(sK0(X2,X0),X2) != iProver_top
% 7.92/1.49      | m1_pre_topc(X2,X1) != iProver_top
% 7.92/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 7.92/1.49      | r1_tarski(X0,k2_struct_0(X2)) != iProver_top
% 7.92/1.49      | l1_pre_topc(X1) != iProver_top ),
% 7.92/1.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_3548,plain,
% 7.92/1.49      ( v2_compts_1(X0,sK1) = iProver_top
% 7.92/1.49      | v2_compts_1(sK0(X1,X0),X1) != iProver_top
% 7.92/1.49      | m1_pre_topc(X1,sK1) != iProver_top
% 7.92/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 7.92/1.49      | r1_tarski(X0,k2_struct_0(X1)) != iProver_top
% 7.92/1.49      | l1_pre_topc(sK1) != iProver_top ),
% 7.92/1.49      inference(superposition,[status(thm)],[c_1760,c_1003]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_14100,plain,
% 7.92/1.49      ( v2_compts_1(X0,sK1) = iProver_top
% 7.92/1.49      | v4_pre_topc(sK0(X1,X0),X1) != iProver_top
% 7.92/1.49      | m1_pre_topc(X1,sK1) != iProver_top
% 7.92/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 7.92/1.49      | r1_tarski(X0,k2_struct_0(X1)) != iProver_top
% 7.92/1.49      | v1_compts_1(X1) != iProver_top
% 7.92/1.49      | l1_pre_topc(X1) != iProver_top ),
% 7.92/1.49      inference(global_propositional_subsumption,
% 7.92/1.49                [status(thm)],
% 7.92/1.49                [c_2905,c_26,c_3548]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_14112,plain,
% 7.92/1.49      ( v2_compts_1(sK3,sK1) = iProver_top
% 7.92/1.49      | v4_pre_topc(sK0(X0,sK3),X0) != iProver_top
% 7.92/1.49      | m1_pre_topc(X0,sK1) != iProver_top
% 7.92/1.49      | r1_tarski(sK3,k2_struct_0(X0)) != iProver_top
% 7.92/1.49      | v1_compts_1(X0) != iProver_top
% 7.92/1.49      | l1_pre_topc(X0) != iProver_top ),
% 7.92/1.49      inference(superposition,[status(thm)],[c_2057,c_14100]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_32,plain,
% 7.92/1.49      ( v2_compts_1(sK3,sK1) != iProver_top ),
% 7.92/1.49      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_14735,plain,
% 7.92/1.49      ( v4_pre_topc(sK0(X0,sK3),X0) != iProver_top
% 7.92/1.49      | m1_pre_topc(X0,sK1) != iProver_top
% 7.92/1.49      | r1_tarski(sK3,k2_struct_0(X0)) != iProver_top
% 7.92/1.49      | v1_compts_1(X0) != iProver_top
% 7.92/1.49      | l1_pre_topc(X0) != iProver_top ),
% 7.92/1.49      inference(global_propositional_subsumption,
% 7.92/1.49                [status(thm)],
% 7.92/1.49                [c_14112,c_32]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_26952,plain,
% 7.92/1.49      ( v4_pre_topc(sK3,k1_pre_topc(sK1,sK2)) != iProver_top
% 7.92/1.49      | m1_pre_topc(k1_pre_topc(sK1,sK2),sK1) != iProver_top
% 7.92/1.49      | r1_tarski(sK3,k2_struct_0(k1_pre_topc(sK1,sK2))) != iProver_top
% 7.92/1.49      | v1_compts_1(k1_pre_topc(sK1,sK2)) != iProver_top
% 7.92/1.49      | l1_pre_topc(k1_pre_topc(sK1,sK2)) != iProver_top ),
% 7.92/1.49      inference(superposition,[status(thm)],[c_26943,c_14735]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_26958,plain,
% 7.92/1.49      ( v4_pre_topc(sK3,k1_pre_topc(sK1,sK2)) != iProver_top
% 7.92/1.49      | m1_pre_topc(k1_pre_topc(sK1,sK2),sK1) != iProver_top
% 7.92/1.49      | r1_tarski(sK3,sK2) != iProver_top
% 7.92/1.49      | v1_compts_1(k1_pre_topc(sK1,sK2)) != iProver_top
% 7.92/1.49      | l1_pre_topc(k1_pre_topc(sK1,sK2)) != iProver_top ),
% 7.92/1.49      inference(light_normalisation,[status(thm)],[c_26952,c_4882]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_27036,plain,
% 7.92/1.49      ( ~ v4_pre_topc(sK3,k1_pre_topc(sK1,sK2))
% 7.92/1.49      | ~ m1_pre_topc(k1_pre_topc(sK1,sK2),sK1)
% 7.92/1.49      | ~ r1_tarski(sK3,sK2)
% 7.92/1.49      | ~ v1_compts_1(k1_pre_topc(sK1,sK2))
% 7.92/1.49      | ~ l1_pre_topc(k1_pre_topc(sK1,sK2)) ),
% 7.92/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_26958]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_437,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_3269,plain,
% 7.92/1.49      ( X0 != X1
% 7.92/1.49      | k2_struct_0(k1_pre_topc(sK1,sK2)) != X1
% 7.92/1.49      | k2_struct_0(k1_pre_topc(sK1,sK2)) = X0 ),
% 7.92/1.49      inference(instantiation,[status(thm)],[c_437]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_4874,plain,
% 7.92/1.49      ( X0 != k2_struct_0(k1_pre_topc(sK1,sK2))
% 7.92/1.49      | k2_struct_0(k1_pre_topc(sK1,sK2)) = X0
% 7.92/1.49      | k2_struct_0(k1_pre_topc(sK1,sK2)) != k2_struct_0(k1_pre_topc(sK1,sK2)) ),
% 7.92/1.49      inference(instantiation,[status(thm)],[c_3269]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_15159,plain,
% 7.92/1.49      ( u1_struct_0(k1_pre_topc(sK1,sK2)) != k2_struct_0(k1_pre_topc(sK1,sK2))
% 7.92/1.49      | k2_struct_0(k1_pre_topc(sK1,sK2)) = u1_struct_0(k1_pre_topc(sK1,sK2))
% 7.92/1.49      | k2_struct_0(k1_pre_topc(sK1,sK2)) != k2_struct_0(k1_pre_topc(sK1,sK2)) ),
% 7.92/1.49      inference(instantiation,[status(thm)],[c_4874]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_5760,plain,
% 7.92/1.49      ( ~ l1_struct_0(k1_pre_topc(sK1,sK2))
% 7.92/1.49      | u1_struct_0(k1_pre_topc(sK1,sK2)) = k2_struct_0(k1_pre_topc(sK1,sK2)) ),
% 7.92/1.49      inference(instantiation,[status(thm)],[c_5]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_12,plain,
% 7.92/1.49      ( ~ v2_compts_1(k2_struct_0(X0),X0)
% 7.92/1.49      | v1_compts_1(X0)
% 7.92/1.49      | ~ l1_pre_topc(X0) ),
% 7.92/1.49      inference(cnf_transformation,[],[f58]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_1005,plain,
% 7.92/1.49      ( v2_compts_1(k2_struct_0(X0),X0) != iProver_top
% 7.92/1.49      | v1_compts_1(X0) = iProver_top
% 7.92/1.49      | l1_pre_topc(X0) != iProver_top ),
% 7.92/1.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_5406,plain,
% 7.92/1.49      ( v2_compts_1(sK2,k1_pre_topc(sK1,sK2)) != iProver_top
% 7.92/1.49      | v1_compts_1(k1_pre_topc(sK1,sK2)) = iProver_top
% 7.92/1.49      | l1_pre_topc(k1_pre_topc(sK1,sK2)) != iProver_top ),
% 7.92/1.49      inference(superposition,[status(thm)],[c_4882,c_1005]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_5420,plain,
% 7.92/1.49      ( ~ v2_compts_1(sK2,k1_pre_topc(sK1,sK2))
% 7.92/1.49      | v1_compts_1(k1_pre_topc(sK1,sK2))
% 7.92/1.49      | ~ l1_pre_topc(k1_pre_topc(sK1,sK2)) ),
% 7.92/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_5406]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_17,plain,
% 7.92/1.49      ( ~ v2_compts_1(X0,X1)
% 7.92/1.49      | v2_compts_1(X0,X2)
% 7.92/1.49      | ~ m1_pre_topc(X2,X1)
% 7.92/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 7.92/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.92/1.49      | ~ r1_tarski(X0,k2_struct_0(X2))
% 7.92/1.49      | ~ l1_pre_topc(X1) ),
% 7.92/1.49      inference(cnf_transformation,[],[f74]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_1369,plain,
% 7.92/1.49      ( v2_compts_1(X0,k1_pre_topc(sK1,sK2))
% 7.92/1.49      | ~ v2_compts_1(X0,sK1)
% 7.92/1.49      | ~ m1_pre_topc(k1_pre_topc(sK1,sK2),sK1)
% 7.92/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2))))
% 7.92/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.92/1.49      | ~ r1_tarski(X0,k2_struct_0(k1_pre_topc(sK1,sK2)))
% 7.92/1.49      | ~ l1_pre_topc(sK1) ),
% 7.92/1.49      inference(instantiation,[status(thm)],[c_17]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_4998,plain,
% 7.92/1.49      ( v2_compts_1(sK2,k1_pre_topc(sK1,sK2))
% 7.92/1.49      | ~ v2_compts_1(sK2,sK1)
% 7.92/1.49      | ~ m1_pre_topc(k1_pre_topc(sK1,sK2),sK1)
% 7.92/1.49      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2))))
% 7.92/1.49      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.92/1.49      | ~ r1_tarski(sK2,k2_struct_0(k1_pre_topc(sK1,sK2)))
% 7.92/1.49      | ~ l1_pre_topc(sK1) ),
% 7.92/1.49      inference(instantiation,[status(thm)],[c_1369]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_11,plain,
% 7.92/1.49      ( ~ v4_pre_topc(X0,X1)
% 7.92/1.49      | v4_pre_topc(X0,X2)
% 7.92/1.49      | ~ m1_pre_topc(X2,X1)
% 7.92/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 7.92/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.92/1.49      | ~ l1_pre_topc(X1) ),
% 7.92/1.49      inference(cnf_transformation,[],[f73]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_1372,plain,
% 7.92/1.49      ( v4_pre_topc(X0,k1_pre_topc(sK1,sK2))
% 7.92/1.49      | ~ v4_pre_topc(X0,sK1)
% 7.92/1.49      | ~ m1_pre_topc(k1_pre_topc(sK1,sK2),sK1)
% 7.92/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2))))
% 7.92/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.92/1.49      | ~ l1_pre_topc(sK1) ),
% 7.92/1.49      inference(instantiation,[status(thm)],[c_11]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_4384,plain,
% 7.92/1.49      ( v4_pre_topc(sK3,k1_pre_topc(sK1,sK2))
% 7.92/1.49      | ~ v4_pre_topc(sK3,sK1)
% 7.92/1.49      | ~ m1_pre_topc(k1_pre_topc(sK1,sK2),sK1)
% 7.92/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2))))
% 7.92/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.92/1.49      | ~ l1_pre_topc(sK1) ),
% 7.92/1.49      inference(instantiation,[status(thm)],[c_1372]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_3,plain,
% 7.92/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.92/1.49      inference(cnf_transformation,[],[f49]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_1249,plain,
% 7.92/1.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.92/1.50      | ~ r1_tarski(X0,u1_struct_0(X1)) ),
% 7.92/1.50      inference(instantiation,[status(thm)],[c_3]) ).
% 7.92/1.50  
% 7.92/1.50  cnf(c_3307,plain,
% 7.92/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2))))
% 7.92/1.50      | ~ r1_tarski(sK2,u1_struct_0(k1_pre_topc(sK1,sK2))) ),
% 7.92/1.50      inference(instantiation,[status(thm)],[c_1249]) ).
% 7.92/1.50  
% 7.92/1.50  cnf(c_436,plain,( X0 = X0 ),theory(equality) ).
% 7.92/1.50  
% 7.92/1.50  cnf(c_3264,plain,
% 7.92/1.50      ( k2_struct_0(k1_pre_topc(sK1,sK2)) = k2_struct_0(k1_pre_topc(sK1,sK2)) ),
% 7.92/1.50      inference(instantiation,[status(thm)],[c_436]) ).
% 7.92/1.50  
% 7.92/1.50  cnf(c_3048,plain,
% 7.92/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK1,sK2))))
% 7.92/1.50      | ~ r1_tarski(sK3,u1_struct_0(k1_pre_topc(sK1,sK2))) ),
% 7.92/1.50      inference(instantiation,[status(thm)],[c_1249]) ).
% 7.92/1.50  
% 7.92/1.50  cnf(c_2144,plain,
% 7.92/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.92/1.50      | ~ l1_pre_topc(X1)
% 7.92/1.50      | l1_pre_topc(k1_pre_topc(X1,X0)) ),
% 7.92/1.50      inference(resolution,[status(thm)],[c_8,c_6]) ).
% 7.92/1.50  
% 7.92/1.50  cnf(c_2162,plain,
% 7.92/1.50      ( l1_pre_topc(k1_pre_topc(sK1,sK2)) | ~ l1_pre_topc(sK1) ),
% 7.92/1.50      inference(resolution,[status(thm)],[c_2144,c_24]) ).
% 7.92/1.50  
% 7.92/1.50  cnf(c_2108,plain,
% 7.92/1.50      ( ~ m1_pre_topc(k1_pre_topc(sK1,sK2),sK1)
% 7.92/1.50      | l1_pre_topc(k1_pre_topc(sK1,sK2))
% 7.92/1.50      | ~ l1_pre_topc(sK1) ),
% 7.92/1.50      inference(instantiation,[status(thm)],[c_2106]) ).
% 7.92/1.50  
% 7.92/1.50  cnf(c_2530,plain,
% 7.92/1.50      ( l1_pre_topc(k1_pre_topc(sK1,sK2)) ),
% 7.92/1.50      inference(global_propositional_subsumption,
% 7.92/1.50                [status(thm)],
% 7.92/1.50                [c_2162,c_25,c_24,c_1257,c_2108]) ).
% 7.92/1.50  
% 7.92/1.50  cnf(c_2542,plain,
% 7.92/1.50      ( l1_struct_0(k1_pre_topc(sK1,sK2)) ),
% 7.92/1.50      inference(resolution,[status(thm)],[c_2530,c_7]) ).
% 7.92/1.50  
% 7.92/1.50  cnf(c_1454,plain,
% 7.92/1.50      ( ~ r1_tarski(X0,X1)
% 7.92/1.50      | r1_tarski(X2,u1_struct_0(X3))
% 7.92/1.50      | X2 != X0
% 7.92/1.50      | u1_struct_0(X3) != X1 ),
% 7.92/1.50      inference(instantiation,[status(thm)],[c_438]) ).
% 7.92/1.50  
% 7.92/1.50  cnf(c_1827,plain,
% 7.92/1.50      ( r1_tarski(X0,u1_struct_0(k1_pre_topc(sK1,sK2)))
% 7.92/1.50      | ~ r1_tarski(X1,sK2)
% 7.92/1.50      | X0 != X1
% 7.92/1.50      | u1_struct_0(k1_pre_topc(sK1,sK2)) != sK2 ),
% 7.92/1.50      inference(instantiation,[status(thm)],[c_1454]) ).
% 7.92/1.50  
% 7.92/1.50  cnf(c_1969,plain,
% 7.92/1.50      ( r1_tarski(X0,u1_struct_0(k1_pre_topc(sK1,sK2)))
% 7.92/1.50      | ~ r1_tarski(sK2,sK2)
% 7.92/1.50      | X0 != sK2
% 7.92/1.50      | u1_struct_0(k1_pre_topc(sK1,sK2)) != sK2 ),
% 7.92/1.50      inference(instantiation,[status(thm)],[c_1827]) ).
% 7.92/1.50  
% 7.92/1.50  cnf(c_2447,plain,
% 7.92/1.50      ( r1_tarski(sK2,u1_struct_0(k1_pre_topc(sK1,sK2)))
% 7.92/1.50      | ~ r1_tarski(sK2,sK2)
% 7.92/1.50      | u1_struct_0(k1_pre_topc(sK1,sK2)) != sK2
% 7.92/1.50      | sK2 != sK2 ),
% 7.92/1.50      inference(instantiation,[status(thm)],[c_1969]) ).
% 7.92/1.50  
% 7.92/1.50  cnf(c_1977,plain,
% 7.92/1.50      ( r1_tarski(X0,u1_struct_0(k1_pre_topc(sK1,sK2)))
% 7.92/1.50      | ~ r1_tarski(sK3,sK2)
% 7.92/1.50      | X0 != sK3
% 7.92/1.50      | u1_struct_0(k1_pre_topc(sK1,sK2)) != sK2 ),
% 7.92/1.50      inference(instantiation,[status(thm)],[c_1827]) ).
% 7.92/1.50  
% 7.92/1.50  cnf(c_2019,plain,
% 7.92/1.50      ( r1_tarski(sK3,u1_struct_0(k1_pre_topc(sK1,sK2)))
% 7.92/1.50      | ~ r1_tarski(sK3,sK2)
% 7.92/1.50      | u1_struct_0(k1_pre_topc(sK1,sK2)) != sK2
% 7.92/1.50      | sK3 != sK3 ),
% 7.92/1.50      inference(instantiation,[status(thm)],[c_1977]) ).
% 7.92/1.50  
% 7.92/1.50  cnf(c_2,plain,
% 7.92/1.50      ( r1_tarski(X0,X0) ),
% 7.92/1.50      inference(cnf_transformation,[],[f72]) ).
% 7.92/1.50  
% 7.92/1.50  cnf(c_1970,plain,
% 7.92/1.50      ( r1_tarski(sK2,sK2) ),
% 7.92/1.50      inference(instantiation,[status(thm)],[c_2]) ).
% 7.92/1.50  
% 7.92/1.50  cnf(c_1429,plain,
% 7.92/1.50      ( sK2 = sK2 ),
% 7.92/1.50      inference(instantiation,[status(thm)],[c_436]) ).
% 7.92/1.50  
% 7.92/1.50  cnf(c_1413,plain,
% 7.92/1.50      ( sK3 = sK3 ),
% 7.92/1.50      inference(instantiation,[status(thm)],[c_436]) ).
% 7.92/1.50  
% 7.92/1.50  cnf(c_1284,plain,
% 7.92/1.50      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.92/1.50      | ~ l1_pre_topc(sK1)
% 7.92/1.50      | u1_struct_0(k1_pre_topc(sK1,sK2)) = sK2 ),
% 7.92/1.50      inference(instantiation,[status(thm)],[c_9]) ).
% 7.92/1.50  
% 7.92/1.50  cnf(c_20,negated_conjecture,
% 7.92/1.50      ( v4_pre_topc(sK3,sK1) ),
% 7.92/1.50      inference(cnf_transformation,[],[f69]) ).
% 7.92/1.50  
% 7.92/1.50  cnf(c_22,negated_conjecture,
% 7.92/1.50      ( v2_compts_1(sK2,sK1) ),
% 7.92/1.50      inference(cnf_transformation,[],[f67]) ).
% 7.92/1.50  
% 7.92/1.50  cnf(contradiction,plain,
% 7.92/1.50      ( $false ),
% 7.92/1.50      inference(minisat,
% 7.92/1.50                [status(thm)],
% 7.92/1.50                [c_33024,c_27036,c_15159,c_5760,c_5420,c_4998,c_4384,
% 7.92/1.50                 c_3307,c_3264,c_3048,c_2542,c_2447,c_2108,c_2019,c_1970,
% 7.92/1.50                 c_1429,c_1413,c_1284,c_1257,c_20,c_21,c_22,c_23,c_24,
% 7.92/1.50                 c_25]) ).
% 7.92/1.50  
% 7.92/1.50  
% 7.92/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.92/1.50  
% 7.92/1.50  ------                               Statistics
% 7.92/1.50  
% 7.92/1.50  ------ Selected
% 7.92/1.50  
% 7.92/1.50  total_time:                             0.962
% 7.92/1.50  
%------------------------------------------------------------------------------
