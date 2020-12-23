%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:18:30 EST 2020

% Result     : Theorem 2.05s
% Output     : CNFRefutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :  218 (1618 expanded)
%              Number of clauses        :  128 ( 379 expanded)
%              Number of leaves         :   25 ( 430 expanded)
%              Depth                    :   24
%              Number of atoms          :  807 (10442 expanded)
%              Number of equality atoms :  127 ( 285 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))
              <=> m1_connsp_2(X2,X0,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))
                <=> m1_connsp_2(X2,X0,X1) ) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))
              <~> m1_connsp_2(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))
              <~> m1_connsp_2(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_connsp_2(X2,X0,X1)
                | ~ m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) )
              & ( m1_connsp_2(X2,X0,X1)
                | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f48,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_connsp_2(X2,X0,X1)
                | ~ m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) )
              & ( m1_connsp_2(X2,X0,X1)
                | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ m1_connsp_2(X2,X0,X1)
            | ~ m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) )
          & ( m1_connsp_2(X2,X0,X1)
            | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ~ m1_connsp_2(sK3,X0,X1)
          | ~ m2_connsp_2(sK3,X0,k6_domain_1(u1_struct_0(X0),X1)) )
        & ( m1_connsp_2(sK3,X0,X1)
          | m2_connsp_2(sK3,X0,k6_domain_1(u1_struct_0(X0),X1)) )
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_connsp_2(X2,X0,X1)
                | ~ m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) )
              & ( m1_connsp_2(X2,X0,X1)
                | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ( ~ m1_connsp_2(X2,X0,sK2)
              | ~ m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),sK2)) )
            & ( m1_connsp_2(X2,X0,sK2)
              | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),sK2)) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ m1_connsp_2(X2,X0,X1)
                  | ~ m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) )
                & ( m1_connsp_2(X2,X0,X1)
                  | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_connsp_2(X2,sK1,X1)
                | ~ m2_connsp_2(X2,sK1,k6_domain_1(u1_struct_0(sK1),X1)) )
              & ( m1_connsp_2(X2,sK1,X1)
                | m2_connsp_2(X2,sK1,k6_domain_1(u1_struct_0(sK1),X1)) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) )
          & m1_subset_1(X1,u1_struct_0(sK1)) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ( ~ m1_connsp_2(sK3,sK1,sK2)
      | ~ m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2)) )
    & ( m1_connsp_2(sK3,sK1,sK2)
      | m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2)) )
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f48,f51,f50,f49])).

fof(f79,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f52])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f7])).

fof(f83,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f58,f59])).

fof(f84,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f57,f83])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f56,f84])).

fof(f86,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f55,f85])).

fof(f87,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f54,f86])).

fof(f88,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f53,f87])).

fof(f92,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f67,f88])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X2] : m1_connsp_2(X2,X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
     => m1_connsp_2(sK0(X0,X1),X0,X1) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_connsp_2(sK0(X0,X1),X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f35,f45])).

fof(f74,plain,(
    ! [X0,X1] :
      ( m1_connsp_2(sK0(X0,X1),X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f76,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f77,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f78,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( m1_connsp_2(X1,X0,X2)
               => r2_hidden(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,X1)
              | ~ m1_connsp_2(X1,X0,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,X1)
              | ~ m1_connsp_2(X1,X0,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ m1_connsp_2(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f40])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f62,f87])).

fof(f82,plain,
    ( ~ m1_connsp_2(sK3,sK1,sK2)
    | ~ m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2)) ),
    inference(cnf_transformation,[],[f52])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m2_connsp_2(X2,X0,X1)
                  | ~ r1_tarski(X1,k1_tops_1(X0,X2)) )
                & ( r1_tarski(X1,k1_tops_1(X0,X2))
                  | ~ m2_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( m2_connsp_2(X2,X0,X1)
      | ~ r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f80,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f52])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ~ r2_hidden(X1,k1_tops_1(X0,X2)) )
                & ( r2_hidden(X1,k1_tops_1(X0,X2))
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f60,f87])).

fof(f81,plain,
    ( m1_connsp_2(sK3,sK1,sK2)
    | m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2)) ),
    inference(cnf_transformation,[],[f52])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m2_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X2] :
          ( m2_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m2_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m2_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m2_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1978,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_2444,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1978])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k6_domain_1(X1,X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1980,plain,
    ( ~ m1_subset_1(X0_46,X1_46)
    | v1_xboole_0(X1_46)
    | k6_enumset1(X0_46,X0_46,X0_46,X0_46,X0_46,X0_46,X0_46,X0_46) = k6_domain_1(X1_46,X0_46) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_2442,plain,
    ( k6_enumset1(X0_46,X0_46,X0_46,X0_46,X0_46,X0_46,X0_46,X0_46) = k6_domain_1(X1_46,X0_46)
    | m1_subset_1(X0_46,X1_46) != iProver_top
    | v1_xboole_0(X1_46) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1980])).

cnf(c_3276,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k6_domain_1(u1_struct_0(sK1),sK2)
    | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2444,c_2442])).

cnf(c_14,plain,
    ( m1_connsp_2(sK0(X0,X1),X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_22,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_376,plain,
    ( m1_connsp_2(sK0(X0,X1),X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_22])).

cnf(c_377,plain,
    ( m1_connsp_2(sK0(sK1,X0),sK1,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_376])).

cnf(c_21,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_20,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_381,plain,
    ( m1_connsp_2(sK0(sK1,X0),sK1,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_377,c_21,c_20])).

cnf(c_12,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_436,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_22])).

cnf(c_437,plain,
    ( ~ m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_436])).

cnf(c_441,plain,
    ( ~ m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_437,c_21,c_20])).

cnf(c_936,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | X1 != X0
    | sK0(sK1,X0) != X2
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_381,c_441])).

cnf(c_937,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | m1_subset_1(sK0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_936])).

cnf(c_1971,plain,
    ( ~ m1_subset_1(X0_46,u1_struct_0(sK1))
    | m1_subset_1(sK0(sK1,X0_46),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_937])).

cnf(c_2038,plain,
    ( m1_subset_1(sK0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1971])).

cnf(c_15,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_128,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X0,X1,X2)
    | r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15,c_12])).

cnf(c_129,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_128])).

cnf(c_415,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_129,c_22])).

cnf(c_416,plain,
    ( ~ m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | r2_hidden(X1,X0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_415])).

cnf(c_420,plain,
    ( ~ m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | r2_hidden(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_416,c_21,c_20])).

cnf(c_948,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | r2_hidden(X1,X2)
    | X1 != X0
    | sK0(sK1,X0) != X2
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_381,c_420])).

cnf(c_949,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | r2_hidden(X0,sK0(sK1,X0)) ),
    inference(unflattening,[status(thm)],[c_948])).

cnf(c_1970,plain,
    ( ~ m1_subset_1(X0_46,u1_struct_0(sK1))
    | r2_hidden(X0_46,sK0(sK1,X0_46)) ),
    inference(subtyping,[status(esa)],[c_949])).

cnf(c_2041,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | r2_hidden(sK2,sK0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_1970])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1982,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(X1_46))
    | r1_tarski(X0_46,X1_46) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_2598,plain,
    ( ~ m1_subset_1(sK0(sK1,X0_46),k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(sK0(sK1,X0_46),u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1982])).

cnf(c_2600,plain,
    ( ~ m1_subset_1(sK0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(sK0(sK1,sK2),u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_2598])).

cnf(c_2632,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1))
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k6_domain_1(u1_struct_0(sK1),sK2) ),
    inference(instantiation,[status(thm)],[c_1980])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_3,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_190,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_3])).

cnf(c_191,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_190])).

cnf(c_244,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(bin_hyper_res,[status(thm)],[c_5,c_191])).

cnf(c_1977,plain,
    ( ~ r2_hidden(X0_46,X1_46)
    | ~ r1_tarski(X1_46,X2_46)
    | ~ v1_xboole_0(X2_46) ),
    inference(subtyping,[status(esa)],[c_244])).

cnf(c_2686,plain,
    ( ~ r2_hidden(X0_46,X1_46)
    | ~ r1_tarski(X1_46,u1_struct_0(sK1))
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1977])).

cnf(c_2779,plain,
    ( ~ r2_hidden(X0_46,sK0(sK1,X1_46))
    | ~ r1_tarski(sK0(sK1,X1_46),u1_struct_0(sK1))
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_2686])).

cnf(c_2781,plain,
    ( ~ r2_hidden(sK2,sK0(sK1,sK2))
    | ~ r1_tarski(sK0(sK1,sK2),u1_struct_0(sK1))
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_2779])).

cnf(c_3487,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k6_domain_1(u1_struct_0(sK1),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3276,c_19,c_2038,c_2041,c_2600,c_2632,c_2781])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | r1_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0),X1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1986,plain,
    ( ~ r2_hidden(X0_46,X1_46)
    | ~ r2_hidden(X2_46,X1_46)
    | r1_tarski(k6_enumset1(X2_46,X2_46,X2_46,X2_46,X2_46,X2_46,X2_46,X0_46),X1_46) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_2436,plain,
    ( r2_hidden(X0_46,X1_46) != iProver_top
    | r2_hidden(X2_46,X1_46) != iProver_top
    | r1_tarski(k6_enumset1(X2_46,X2_46,X2_46,X2_46,X2_46,X2_46,X2_46,X0_46),X1_46) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1986])).

cnf(c_3491,plain,
    ( r2_hidden(sK2,X0_46) != iProver_top
    | r1_tarski(k6_domain_1(u1_struct_0(sK1),sK2),X0_46) = iProver_top ),
    inference(superposition,[status(thm)],[c_3487,c_2436])).

cnf(c_16,negated_conjecture,
    ( ~ m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2))
    | ~ m1_connsp_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_192,plain,
    ( ~ m1_connsp_2(sK3,sK1,sK2)
    | ~ m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2)) ),
    inference(prop_impl,[status(thm)],[c_16])).

cnf(c_193,plain,
    ( ~ m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2))
    | ~ m1_connsp_2(sK3,sK1,sK2) ),
    inference(renaming,[status(thm)],[c_192])).

cnf(c_10,plain,
    ( m2_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_539,plain,
    ( m2_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_20])).

cnf(c_540,plain,
    ( m2_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X1,k1_tops_1(sK1,X0))
    | ~ v2_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_539])).

cnf(c_544,plain,
    ( ~ r1_tarski(X1,k1_tops_1(sK1,X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m2_connsp_2(X0,sK1,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_540,c_21])).

cnf(c_545,plain,
    ( m2_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X1,k1_tops_1(sK1,X0)) ),
    inference(renaming,[status(thm)],[c_544])).

cnf(c_594,plain,
    ( ~ m1_connsp_2(sK3,sK1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X1,k1_tops_1(sK1,X0))
    | k6_domain_1(u1_struct_0(sK1),sK2) != X1
    | sK1 != sK1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_193,c_545])).

cnf(c_595,plain,
    ( ~ m1_connsp_2(sK3,sK1,sK2)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(k6_domain_1(u1_struct_0(sK1),sK2),k1_tops_1(sK1,sK3)) ),
    inference(unflattening,[status(thm)],[c_594])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_597,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_connsp_2(sK3,sK1,sK2)
    | ~ r1_tarski(k6_domain_1(u1_struct_0(sK1),sK2),k1_tops_1(sK1,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_595,c_18])).

cnf(c_598,plain,
    ( ~ m1_connsp_2(sK3,sK1,sK2)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(k6_domain_1(u1_struct_0(sK1),sK2),k1_tops_1(sK1,sK3)) ),
    inference(renaming,[status(thm)],[c_597])).

cnf(c_8,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_457,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_22])).

cnf(c_458,plain,
    ( m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X1,k1_tops_1(sK1,X0))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_457])).

cnf(c_462,plain,
    ( m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X1,k1_tops_1(sK1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_458,c_21,c_20])).

cnf(c_919,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X0,k1_tops_1(sK1,X1))
    | ~ r1_tarski(k6_domain_1(u1_struct_0(sK1),sK2),k1_tops_1(sK1,sK3))
    | sK2 != X0
    | sK1 != sK1
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_598,c_462])).

cnf(c_920,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | ~ r1_tarski(k6_domain_1(u1_struct_0(sK1),sK2),k1_tops_1(sK1,sK3)) ),
    inference(unflattening,[status(thm)],[c_919])).

cnf(c_922,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | ~ r1_tarski(k6_domain_1(u1_struct_0(sK1),sK2),k1_tops_1(sK1,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_920,c_19,c_18])).

cnf(c_1972,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | ~ r1_tarski(k6_domain_1(u1_struct_0(sK1),sK2),k1_tops_1(sK1,sK3)) ),
    inference(subtyping,[status(esa)],[c_922])).

cnf(c_2450,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) != iProver_top
    | r1_tarski(k6_domain_1(u1_struct_0(sK1),sK2),k1_tops_1(sK1,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1972])).

cnf(c_26,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_924,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) != iProver_top
    | r1_tarski(k6_domain_1(u1_struct_0(sK1),sK2),k1_tops_1(sK1,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_922])).

cnf(c_2037,plain,
    ( m1_subset_1(X0_46,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK0(sK1,X0_46),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1971])).

cnf(c_2039,plain,
    ( m1_subset_1(sK0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2037])).

cnf(c_2040,plain,
    ( m1_subset_1(X0_46,u1_struct_0(sK1)) != iProver_top
    | r2_hidden(X0_46,sK0(sK1,X0_46)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1970])).

cnf(c_2042,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | r2_hidden(sK2,sK0(sK1,sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2040])).

cnf(c_2599,plain,
    ( m1_subset_1(sK0(sK1,X0_46),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(sK0(sK1,X0_46),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2598])).

cnf(c_2601,plain,
    ( m1_subset_1(sK0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(sK0(sK1,sK2),u1_struct_0(sK1)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2599])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1981,plain,
    ( ~ m1_subset_1(X0_46,X1_46)
    | m1_subset_1(k6_domain_1(X1_46,X0_46),k1_zfmisc_1(X1_46))
    | v1_xboole_0(X1_46) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_2606,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1981])).

cnf(c_2607,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2606])).

cnf(c_2780,plain,
    ( r2_hidden(X0_46,sK0(sK1,X1_46)) != iProver_top
    | r1_tarski(sK0(sK1,X1_46),u1_struct_0(sK1)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2779])).

cnf(c_2782,plain,
    ( r2_hidden(sK2,sK0(sK1,sK2)) != iProver_top
    | r1_tarski(sK0(sK1,sK2),u1_struct_0(sK1)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2780])).

cnf(c_3111,plain,
    ( r2_hidden(sK2,k1_tops_1(sK1,sK3)) != iProver_top
    | r1_tarski(k6_domain_1(u1_struct_0(sK1),sK2),k1_tops_1(sK1,sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2450,c_26,c_924,c_2039,c_2042,c_2601,c_2607,c_2782])).

cnf(c_3572,plain,
    ( r2_hidden(sK2,k1_tops_1(sK1,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3491,c_3111])).

cnf(c_2,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),X1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1984,plain,
    ( r2_hidden(X0_46,X1_46)
    | ~ r1_tarski(k6_enumset1(X0_46,X0_46,X0_46,X0_46,X0_46,X0_46,X0_46,X2_46),X1_46) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_3552,plain,
    ( r2_hidden(X0_46,k1_tops_1(sK1,sK3))
    | ~ r1_tarski(k6_enumset1(X0_46,X0_46,X0_46,X0_46,X0_46,X0_46,X0_46,X1_46),k1_tops_1(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_1984])).

cnf(c_3557,plain,
    ( r2_hidden(X0_46,k1_tops_1(sK1,sK3)) = iProver_top
    | r1_tarski(k6_enumset1(X0_46,X0_46,X0_46,X0_46,X0_46,X0_46,X0_46,X1_46),k1_tops_1(sK1,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3552])).

cnf(c_3559,plain,
    ( r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top
    | r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k1_tops_1(sK1,sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3557])).

cnf(c_1990,plain,
    ( ~ r1_tarski(X0_46,X1_46)
    | r1_tarski(X2_46,X3_46)
    | X2_46 != X0_46
    | X3_46 != X1_46 ),
    theory(equality)).

cnf(c_2987,plain,
    ( r1_tarski(X0_46,X1_46)
    | ~ r1_tarski(k6_domain_1(u1_struct_0(sK1),sK2),k1_tops_1(sK1,sK3))
    | X1_46 != k1_tops_1(sK1,sK3)
    | X0_46 != k6_domain_1(u1_struct_0(sK1),sK2) ),
    inference(instantiation,[status(thm)],[c_1990])).

cnf(c_3146,plain,
    ( r1_tarski(X0_46,k1_tops_1(sK1,sK3))
    | ~ r1_tarski(k6_domain_1(u1_struct_0(sK1),sK2),k1_tops_1(sK1,sK3))
    | X0_46 != k6_domain_1(u1_struct_0(sK1),sK2)
    | k1_tops_1(sK1,sK3) != k1_tops_1(sK1,sK3) ),
    inference(instantiation,[status(thm)],[c_2987])).

cnf(c_3551,plain,
    ( r1_tarski(k6_enumset1(X0_46,X0_46,X0_46,X0_46,X0_46,X0_46,X0_46,X1_46),k1_tops_1(sK1,sK3))
    | ~ r1_tarski(k6_domain_1(u1_struct_0(sK1),sK2),k1_tops_1(sK1,sK3))
    | k6_enumset1(X0_46,X0_46,X0_46,X0_46,X0_46,X0_46,X0_46,X1_46) != k6_domain_1(u1_struct_0(sK1),sK2)
    | k1_tops_1(sK1,sK3) != k1_tops_1(sK1,sK3) ),
    inference(instantiation,[status(thm)],[c_3146])).

cnf(c_3553,plain,
    ( k6_enumset1(X0_46,X0_46,X0_46,X0_46,X0_46,X0_46,X0_46,X1_46) != k6_domain_1(u1_struct_0(sK1),sK2)
    | k1_tops_1(sK1,sK3) != k1_tops_1(sK1,sK3)
    | r1_tarski(k6_enumset1(X0_46,X0_46,X0_46,X0_46,X0_46,X0_46,X0_46,X1_46),k1_tops_1(sK1,sK3)) = iProver_top
    | r1_tarski(k6_domain_1(u1_struct_0(sK1),sK2),k1_tops_1(sK1,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3551])).

cnf(c_3555,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k6_domain_1(u1_struct_0(sK1),sK2)
    | k1_tops_1(sK1,sK3) != k1_tops_1(sK1,sK3)
    | r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k1_tops_1(sK1,sK3)) = iProver_top
    | r1_tarski(k6_domain_1(u1_struct_0(sK1),sK2),k1_tops_1(sK1,sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3553])).

cnf(c_17,negated_conjecture,
    ( m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2))
    | m1_connsp_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_194,plain,
    ( m1_connsp_2(sK3,sK1,sK2)
    | m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2)) ),
    inference(prop_impl,[status(thm)],[c_17])).

cnf(c_195,plain,
    ( m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2))
    | m1_connsp_2(sK3,sK1,sK2) ),
    inference(renaming,[status(thm)],[c_194])).

cnf(c_11,plain,
    ( ~ m2_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_13,plain,
    ( ~ m2_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_138,plain,
    ( ~ m2_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11,c_13])).

cnf(c_501,plain,
    ( ~ m2_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_138,c_20])).

cnf(c_502,plain,
    ( ~ m2_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(X1,k1_tops_1(sK1,X0))
    | ~ v2_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_501])).

cnf(c_506,plain,
    ( r1_tarski(X1,k1_tops_1(sK1,X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m2_connsp_2(X0,sK1,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_502,c_21])).

cnf(c_507,plain,
    ( ~ m2_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(X1,k1_tops_1(sK1,X0)) ),
    inference(renaming,[status(thm)],[c_506])).

cnf(c_581,plain,
    ( m1_connsp_2(sK3,sK1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(X0,k1_tops_1(sK1,X1))
    | k6_domain_1(u1_struct_0(sK1),sK2) != X0
    | sK1 != sK1
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_195,c_507])).

cnf(c_582,plain,
    ( m1_connsp_2(sK3,sK1,sK2)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(k6_domain_1(u1_struct_0(sK1),sK2),k1_tops_1(sK1,sK3)) ),
    inference(unflattening,[status(thm)],[c_581])).

cnf(c_9,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_144,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X0,X1,X2)
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9,c_12])).

cnf(c_145,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_144])).

cnf(c_394,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_145,c_22])).

cnf(c_395,plain,
    ( ~ m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | r2_hidden(X1,k1_tops_1(sK1,X0))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_394])).

cnf(c_399,plain,
    ( ~ m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | r2_hidden(X1,k1_tops_1(sK1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_395,c_21,c_20])).

cnf(c_902,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(X0,k1_tops_1(sK1,X1))
    | r1_tarski(k6_domain_1(u1_struct_0(sK1),sK2),k1_tops_1(sK1,sK3))
    | sK2 != X0
    | sK1 != sK1
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_582,c_399])).

cnf(c_903,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | r1_tarski(k6_domain_1(u1_struct_0(sK1),sK2),k1_tops_1(sK1,sK3)) ),
    inference(unflattening,[status(thm)],[c_902])).

cnf(c_905,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | r1_tarski(k6_domain_1(u1_struct_0(sK1),sK2),k1_tops_1(sK1,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_903,c_19])).

cnf(c_1973,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | r1_tarski(k6_domain_1(u1_struct_0(sK1),sK2),k1_tops_1(sK1,sK3)) ),
    inference(subtyping,[status(esa)],[c_905])).

cnf(c_2449,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top
    | r1_tarski(k6_domain_1(u1_struct_0(sK1),sK2),k1_tops_1(sK1,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1973])).

cnf(c_904,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top
    | r1_tarski(k6_domain_1(u1_struct_0(sK1),sK2),k1_tops_1(sK1,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_903])).

cnf(c_3173,plain,
    ( r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top
    | r1_tarski(k6_domain_1(u1_struct_0(sK1),sK2),k1_tops_1(sK1,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2449,c_26,c_904,c_2039,c_2042,c_2601,c_2607,c_2782])).

cnf(c_1988,plain,
    ( X0_46 = X0_46 ),
    theory(equality)).

cnf(c_3147,plain,
    ( k1_tops_1(sK1,sK3) = k1_tops_1(sK1,sK3) ),
    inference(instantiation,[status(thm)],[c_1988])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3572,c_3559,c_3555,c_3173,c_3147,c_2781,c_2632,c_2600,c_2041,c_2038,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 15:38:57 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.05/0.96  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/0.96  
% 2.05/0.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.05/0.96  
% 2.05/0.96  ------  iProver source info
% 2.05/0.96  
% 2.05/0.96  git: date: 2020-06-30 10:37:57 +0100
% 2.05/0.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.05/0.96  git: non_committed_changes: false
% 2.05/0.96  git: last_make_outside_of_git: false
% 2.05/0.96  
% 2.05/0.96  ------ 
% 2.05/0.96  
% 2.05/0.96  ------ Input Options
% 2.05/0.96  
% 2.05/0.96  --out_options                           all
% 2.05/0.96  --tptp_safe_out                         true
% 2.05/0.96  --problem_path                          ""
% 2.05/0.96  --include_path                          ""
% 2.05/0.96  --clausifier                            res/vclausify_rel
% 2.05/0.96  --clausifier_options                    --mode clausify
% 2.05/0.96  --stdin                                 false
% 2.05/0.96  --stats_out                             all
% 2.05/0.96  
% 2.05/0.96  ------ General Options
% 2.05/0.96  
% 2.05/0.96  --fof                                   false
% 2.05/0.96  --time_out_real                         305.
% 2.05/0.96  --time_out_virtual                      -1.
% 2.05/0.96  --symbol_type_check                     false
% 2.05/0.96  --clausify_out                          false
% 2.05/0.96  --sig_cnt_out                           false
% 2.05/0.96  --trig_cnt_out                          false
% 2.05/0.96  --trig_cnt_out_tolerance                1.
% 2.05/0.96  --trig_cnt_out_sk_spl                   false
% 2.05/0.96  --abstr_cl_out                          false
% 2.05/0.96  
% 2.05/0.96  ------ Global Options
% 2.05/0.96  
% 2.05/0.96  --schedule                              default
% 2.05/0.96  --add_important_lit                     false
% 2.05/0.96  --prop_solver_per_cl                    1000
% 2.05/0.96  --min_unsat_core                        false
% 2.05/0.96  --soft_assumptions                      false
% 2.05/0.96  --soft_lemma_size                       3
% 2.05/0.96  --prop_impl_unit_size                   0
% 2.05/0.96  --prop_impl_unit                        []
% 2.05/0.96  --share_sel_clauses                     true
% 2.05/0.96  --reset_solvers                         false
% 2.05/0.96  --bc_imp_inh                            [conj_cone]
% 2.05/0.96  --conj_cone_tolerance                   3.
% 2.05/0.96  --extra_neg_conj                        none
% 2.05/0.96  --large_theory_mode                     true
% 2.05/0.96  --prolific_symb_bound                   200
% 2.05/0.96  --lt_threshold                          2000
% 2.05/0.96  --clause_weak_htbl                      true
% 2.05/0.96  --gc_record_bc_elim                     false
% 2.05/0.96  
% 2.05/0.96  ------ Preprocessing Options
% 2.05/0.96  
% 2.05/0.96  --preprocessing_flag                    true
% 2.05/0.96  --time_out_prep_mult                    0.1
% 2.05/0.96  --splitting_mode                        input
% 2.05/0.96  --splitting_grd                         true
% 2.05/0.96  --splitting_cvd                         false
% 2.05/0.96  --splitting_cvd_svl                     false
% 2.05/0.96  --splitting_nvd                         32
% 2.05/0.96  --sub_typing                            true
% 2.05/0.96  --prep_gs_sim                           true
% 2.05/0.96  --prep_unflatten                        true
% 2.05/0.96  --prep_res_sim                          true
% 2.05/0.96  --prep_upred                            true
% 2.05/0.96  --prep_sem_filter                       exhaustive
% 2.05/0.96  --prep_sem_filter_out                   false
% 2.05/0.96  --pred_elim                             true
% 2.05/0.96  --res_sim_input                         true
% 2.05/0.96  --eq_ax_congr_red                       true
% 2.05/0.96  --pure_diseq_elim                       true
% 2.05/0.96  --brand_transform                       false
% 2.05/0.96  --non_eq_to_eq                          false
% 2.05/0.96  --prep_def_merge                        true
% 2.05/0.96  --prep_def_merge_prop_impl              false
% 2.05/0.96  --prep_def_merge_mbd                    true
% 2.05/0.96  --prep_def_merge_tr_red                 false
% 2.05/0.96  --prep_def_merge_tr_cl                  false
% 2.05/0.96  --smt_preprocessing                     true
% 2.05/0.96  --smt_ac_axioms                         fast
% 2.05/0.96  --preprocessed_out                      false
% 2.05/0.96  --preprocessed_stats                    false
% 2.05/0.96  
% 2.05/0.96  ------ Abstraction refinement Options
% 2.05/0.96  
% 2.05/0.96  --abstr_ref                             []
% 2.05/0.96  --abstr_ref_prep                        false
% 2.05/0.96  --abstr_ref_until_sat                   false
% 2.05/0.96  --abstr_ref_sig_restrict                funpre
% 2.05/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 2.05/0.96  --abstr_ref_under                       []
% 2.05/0.96  
% 2.05/0.96  ------ SAT Options
% 2.05/0.96  
% 2.05/0.96  --sat_mode                              false
% 2.05/0.96  --sat_fm_restart_options                ""
% 2.05/0.96  --sat_gr_def                            false
% 2.05/0.96  --sat_epr_types                         true
% 2.05/0.96  --sat_non_cyclic_types                  false
% 2.05/0.96  --sat_finite_models                     false
% 2.05/0.96  --sat_fm_lemmas                         false
% 2.05/0.96  --sat_fm_prep                           false
% 2.05/0.96  --sat_fm_uc_incr                        true
% 2.05/0.96  --sat_out_model                         small
% 2.05/0.96  --sat_out_clauses                       false
% 2.05/0.96  
% 2.05/0.96  ------ QBF Options
% 2.05/0.96  
% 2.05/0.96  --qbf_mode                              false
% 2.05/0.96  --qbf_elim_univ                         false
% 2.05/0.96  --qbf_dom_inst                          none
% 2.05/0.96  --qbf_dom_pre_inst                      false
% 2.05/0.96  --qbf_sk_in                             false
% 2.05/0.96  --qbf_pred_elim                         true
% 2.05/0.96  --qbf_split                             512
% 2.05/0.96  
% 2.05/0.96  ------ BMC1 Options
% 2.05/0.96  
% 2.05/0.96  --bmc1_incremental                      false
% 2.05/0.96  --bmc1_axioms                           reachable_all
% 2.05/0.96  --bmc1_min_bound                        0
% 2.05/0.96  --bmc1_max_bound                        -1
% 2.05/0.96  --bmc1_max_bound_default                -1
% 2.05/0.96  --bmc1_symbol_reachability              true
% 2.05/0.96  --bmc1_property_lemmas                  false
% 2.05/0.96  --bmc1_k_induction                      false
% 2.05/0.96  --bmc1_non_equiv_states                 false
% 2.05/0.96  --bmc1_deadlock                         false
% 2.05/0.96  --bmc1_ucm                              false
% 2.05/0.96  --bmc1_add_unsat_core                   none
% 2.05/0.96  --bmc1_unsat_core_children              false
% 2.05/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 2.05/0.96  --bmc1_out_stat                         full
% 2.05/0.96  --bmc1_ground_init                      false
% 2.05/0.96  --bmc1_pre_inst_next_state              false
% 2.05/0.96  --bmc1_pre_inst_state                   false
% 2.05/0.96  --bmc1_pre_inst_reach_state             false
% 2.05/0.96  --bmc1_out_unsat_core                   false
% 2.05/0.96  --bmc1_aig_witness_out                  false
% 2.05/0.96  --bmc1_verbose                          false
% 2.05/0.96  --bmc1_dump_clauses_tptp                false
% 2.05/0.96  --bmc1_dump_unsat_core_tptp             false
% 2.05/0.96  --bmc1_dump_file                        -
% 2.05/0.96  --bmc1_ucm_expand_uc_limit              128
% 2.05/0.96  --bmc1_ucm_n_expand_iterations          6
% 2.05/0.96  --bmc1_ucm_extend_mode                  1
% 2.05/0.96  --bmc1_ucm_init_mode                    2
% 2.05/0.96  --bmc1_ucm_cone_mode                    none
% 2.05/0.96  --bmc1_ucm_reduced_relation_type        0
% 2.05/0.96  --bmc1_ucm_relax_model                  4
% 2.05/0.96  --bmc1_ucm_full_tr_after_sat            true
% 2.05/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 2.05/0.96  --bmc1_ucm_layered_model                none
% 2.05/0.96  --bmc1_ucm_max_lemma_size               10
% 2.05/0.96  
% 2.05/0.96  ------ AIG Options
% 2.05/0.96  
% 2.05/0.96  --aig_mode                              false
% 2.05/0.96  
% 2.05/0.96  ------ Instantiation Options
% 2.05/0.96  
% 2.05/0.96  --instantiation_flag                    true
% 2.05/0.96  --inst_sos_flag                         false
% 2.05/0.96  --inst_sos_phase                        true
% 2.05/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.05/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.05/0.96  --inst_lit_sel_side                     num_symb
% 2.05/0.96  --inst_solver_per_active                1400
% 2.05/0.96  --inst_solver_calls_frac                1.
% 2.05/0.96  --inst_passive_queue_type               priority_queues
% 2.05/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.05/0.96  --inst_passive_queues_freq              [25;2]
% 2.05/0.96  --inst_dismatching                      true
% 2.05/0.96  --inst_eager_unprocessed_to_passive     true
% 2.05/0.96  --inst_prop_sim_given                   true
% 2.05/0.96  --inst_prop_sim_new                     false
% 2.05/0.96  --inst_subs_new                         false
% 2.05/0.96  --inst_eq_res_simp                      false
% 2.05/0.96  --inst_subs_given                       false
% 2.05/0.96  --inst_orphan_elimination               true
% 2.05/0.96  --inst_learning_loop_flag               true
% 2.05/0.96  --inst_learning_start                   3000
% 2.05/0.96  --inst_learning_factor                  2
% 2.05/0.96  --inst_start_prop_sim_after_learn       3
% 2.05/0.96  --inst_sel_renew                        solver
% 2.05/0.96  --inst_lit_activity_flag                true
% 2.05/0.96  --inst_restr_to_given                   false
% 2.05/0.96  --inst_activity_threshold               500
% 2.05/0.96  --inst_out_proof                        true
% 2.05/0.96  
% 2.05/0.96  ------ Resolution Options
% 2.05/0.96  
% 2.05/0.96  --resolution_flag                       true
% 2.05/0.96  --res_lit_sel                           adaptive
% 2.05/0.96  --res_lit_sel_side                      none
% 2.05/0.96  --res_ordering                          kbo
% 2.05/0.96  --res_to_prop_solver                    active
% 2.05/0.96  --res_prop_simpl_new                    false
% 2.05/0.96  --res_prop_simpl_given                  true
% 2.05/0.96  --res_passive_queue_type                priority_queues
% 2.05/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.05/0.96  --res_passive_queues_freq               [15;5]
% 2.05/0.96  --res_forward_subs                      full
% 2.05/0.96  --res_backward_subs                     full
% 2.05/0.96  --res_forward_subs_resolution           true
% 2.05/0.96  --res_backward_subs_resolution          true
% 2.05/0.96  --res_orphan_elimination                true
% 2.05/0.96  --res_time_limit                        2.
% 2.05/0.96  --res_out_proof                         true
% 2.05/0.96  
% 2.05/0.96  ------ Superposition Options
% 2.05/0.96  
% 2.05/0.96  --superposition_flag                    true
% 2.05/0.96  --sup_passive_queue_type                priority_queues
% 2.05/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.05/0.96  --sup_passive_queues_freq               [8;1;4]
% 2.05/0.96  --demod_completeness_check              fast
% 2.05/0.96  --demod_use_ground                      true
% 2.05/0.96  --sup_to_prop_solver                    passive
% 2.05/0.96  --sup_prop_simpl_new                    true
% 2.05/0.96  --sup_prop_simpl_given                  true
% 2.05/0.96  --sup_fun_splitting                     false
% 2.05/0.96  --sup_smt_interval                      50000
% 2.05/0.96  
% 2.05/0.96  ------ Superposition Simplification Setup
% 2.05/0.96  
% 2.05/0.96  --sup_indices_passive                   []
% 2.05/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.05/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.05/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.05/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 2.05/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.05/0.96  --sup_full_bw                           [BwDemod]
% 2.05/0.96  --sup_immed_triv                        [TrivRules]
% 2.05/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.05/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.05/0.96  --sup_immed_bw_main                     []
% 2.05/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.05/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 2.05/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.05/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.05/0.96  
% 2.05/0.96  ------ Combination Options
% 2.05/0.96  
% 2.05/0.96  --comb_res_mult                         3
% 2.05/0.96  --comb_sup_mult                         2
% 2.05/0.96  --comb_inst_mult                        10
% 2.05/0.96  
% 2.05/0.96  ------ Debug Options
% 2.05/0.96  
% 2.05/0.96  --dbg_backtrace                         false
% 2.05/0.96  --dbg_dump_prop_clauses                 false
% 2.05/0.96  --dbg_dump_prop_clauses_file            -
% 2.05/0.96  --dbg_out_stat                          false
% 2.05/0.96  ------ Parsing...
% 2.05/0.96  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.05/0.96  
% 2.05/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 2.05/0.96  
% 2.05/0.96  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.05/0.96  
% 2.05/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.05/0.96  ------ Proving...
% 2.05/0.96  ------ Problem Properties 
% 2.05/0.96  
% 2.05/0.96  
% 2.05/0.96  clauses                                 18
% 2.05/0.96  conjectures                             2
% 2.05/0.96  EPR                                     1
% 2.05/0.96  Horn                                    14
% 2.05/0.96  unary                                   2
% 2.05/0.96  binary                                  7
% 2.05/0.96  lits                                    44
% 2.05/0.96  lits eq                                 2
% 2.05/0.96  fd_pure                                 0
% 2.05/0.96  fd_pseudo                               0
% 2.05/0.96  fd_cond                                 0
% 2.05/0.96  fd_pseudo_cond                          0
% 2.05/0.96  AC symbols                              0
% 2.05/0.96  
% 2.05/0.96  ------ Schedule dynamic 5 is on 
% 2.05/0.96  
% 2.05/0.96  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.05/0.96  
% 2.05/0.96  
% 2.05/0.96  ------ 
% 2.05/0.96  Current options:
% 2.05/0.96  ------ 
% 2.05/0.96  
% 2.05/0.96  ------ Input Options
% 2.05/0.96  
% 2.05/0.96  --out_options                           all
% 2.05/0.96  --tptp_safe_out                         true
% 2.05/0.96  --problem_path                          ""
% 2.05/0.96  --include_path                          ""
% 2.05/0.96  --clausifier                            res/vclausify_rel
% 2.05/0.96  --clausifier_options                    --mode clausify
% 2.05/0.96  --stdin                                 false
% 2.05/0.96  --stats_out                             all
% 2.05/0.96  
% 2.05/0.96  ------ General Options
% 2.05/0.96  
% 2.05/0.96  --fof                                   false
% 2.05/0.96  --time_out_real                         305.
% 2.05/0.96  --time_out_virtual                      -1.
% 2.05/0.96  --symbol_type_check                     false
% 2.05/0.96  --clausify_out                          false
% 2.05/0.96  --sig_cnt_out                           false
% 2.05/0.96  --trig_cnt_out                          false
% 2.05/0.96  --trig_cnt_out_tolerance                1.
% 2.05/0.96  --trig_cnt_out_sk_spl                   false
% 2.05/0.96  --abstr_cl_out                          false
% 2.05/0.96  
% 2.05/0.96  ------ Global Options
% 2.05/0.96  
% 2.05/0.96  --schedule                              default
% 2.05/0.96  --add_important_lit                     false
% 2.05/0.96  --prop_solver_per_cl                    1000
% 2.05/0.96  --min_unsat_core                        false
% 2.05/0.96  --soft_assumptions                      false
% 2.05/0.96  --soft_lemma_size                       3
% 2.05/0.96  --prop_impl_unit_size                   0
% 2.05/0.96  --prop_impl_unit                        []
% 2.05/0.96  --share_sel_clauses                     true
% 2.05/0.96  --reset_solvers                         false
% 2.05/0.96  --bc_imp_inh                            [conj_cone]
% 2.05/0.96  --conj_cone_tolerance                   3.
% 2.05/0.96  --extra_neg_conj                        none
% 2.05/0.96  --large_theory_mode                     true
% 2.05/0.96  --prolific_symb_bound                   200
% 2.05/0.96  --lt_threshold                          2000
% 2.05/0.96  --clause_weak_htbl                      true
% 2.05/0.96  --gc_record_bc_elim                     false
% 2.05/0.96  
% 2.05/0.96  ------ Preprocessing Options
% 2.05/0.96  
% 2.05/0.96  --preprocessing_flag                    true
% 2.05/0.96  --time_out_prep_mult                    0.1
% 2.05/0.96  --splitting_mode                        input
% 2.05/0.96  --splitting_grd                         true
% 2.05/0.96  --splitting_cvd                         false
% 2.05/0.96  --splitting_cvd_svl                     false
% 2.05/0.96  --splitting_nvd                         32
% 2.05/0.96  --sub_typing                            true
% 2.05/0.96  --prep_gs_sim                           true
% 2.05/0.96  --prep_unflatten                        true
% 2.05/0.96  --prep_res_sim                          true
% 2.05/0.96  --prep_upred                            true
% 2.05/0.96  --prep_sem_filter                       exhaustive
% 2.05/0.96  --prep_sem_filter_out                   false
% 2.05/0.96  --pred_elim                             true
% 2.05/0.96  --res_sim_input                         true
% 2.05/0.96  --eq_ax_congr_red                       true
% 2.05/0.96  --pure_diseq_elim                       true
% 2.05/0.96  --brand_transform                       false
% 2.05/0.96  --non_eq_to_eq                          false
% 2.05/0.96  --prep_def_merge                        true
% 2.05/0.96  --prep_def_merge_prop_impl              false
% 2.05/0.96  --prep_def_merge_mbd                    true
% 2.05/0.96  --prep_def_merge_tr_red                 false
% 2.05/0.96  --prep_def_merge_tr_cl                  false
% 2.05/0.96  --smt_preprocessing                     true
% 2.05/0.96  --smt_ac_axioms                         fast
% 2.05/0.96  --preprocessed_out                      false
% 2.05/0.96  --preprocessed_stats                    false
% 2.05/0.96  
% 2.05/0.96  ------ Abstraction refinement Options
% 2.05/0.96  
% 2.05/0.96  --abstr_ref                             []
% 2.05/0.96  --abstr_ref_prep                        false
% 2.05/0.96  --abstr_ref_until_sat                   false
% 2.05/0.96  --abstr_ref_sig_restrict                funpre
% 2.05/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 2.05/0.96  --abstr_ref_under                       []
% 2.05/0.96  
% 2.05/0.96  ------ SAT Options
% 2.05/0.96  
% 2.05/0.96  --sat_mode                              false
% 2.05/0.96  --sat_fm_restart_options                ""
% 2.05/0.97  --sat_gr_def                            false
% 2.05/0.97  --sat_epr_types                         true
% 2.05/0.97  --sat_non_cyclic_types                  false
% 2.05/0.97  --sat_finite_models                     false
% 2.05/0.97  --sat_fm_lemmas                         false
% 2.05/0.97  --sat_fm_prep                           false
% 2.05/0.97  --sat_fm_uc_incr                        true
% 2.05/0.97  --sat_out_model                         small
% 2.05/0.97  --sat_out_clauses                       false
% 2.05/0.97  
% 2.05/0.97  ------ QBF Options
% 2.05/0.97  
% 2.05/0.97  --qbf_mode                              false
% 2.05/0.97  --qbf_elim_univ                         false
% 2.05/0.97  --qbf_dom_inst                          none
% 2.05/0.97  --qbf_dom_pre_inst                      false
% 2.05/0.97  --qbf_sk_in                             false
% 2.05/0.97  --qbf_pred_elim                         true
% 2.05/0.97  --qbf_split                             512
% 2.05/0.97  
% 2.05/0.97  ------ BMC1 Options
% 2.05/0.97  
% 2.05/0.97  --bmc1_incremental                      false
% 2.05/0.97  --bmc1_axioms                           reachable_all
% 2.05/0.97  --bmc1_min_bound                        0
% 2.05/0.97  --bmc1_max_bound                        -1
% 2.05/0.97  --bmc1_max_bound_default                -1
% 2.05/0.97  --bmc1_symbol_reachability              true
% 2.05/0.97  --bmc1_property_lemmas                  false
% 2.05/0.97  --bmc1_k_induction                      false
% 2.05/0.97  --bmc1_non_equiv_states                 false
% 2.05/0.97  --bmc1_deadlock                         false
% 2.05/0.97  --bmc1_ucm                              false
% 2.05/0.97  --bmc1_add_unsat_core                   none
% 2.05/0.97  --bmc1_unsat_core_children              false
% 2.05/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.05/0.97  --bmc1_out_stat                         full
% 2.05/0.97  --bmc1_ground_init                      false
% 2.05/0.97  --bmc1_pre_inst_next_state              false
% 2.05/0.97  --bmc1_pre_inst_state                   false
% 2.05/0.97  --bmc1_pre_inst_reach_state             false
% 2.05/0.97  --bmc1_out_unsat_core                   false
% 2.05/0.97  --bmc1_aig_witness_out                  false
% 2.05/0.97  --bmc1_verbose                          false
% 2.05/0.97  --bmc1_dump_clauses_tptp                false
% 2.05/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.05/0.97  --bmc1_dump_file                        -
% 2.05/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.05/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.05/0.97  --bmc1_ucm_extend_mode                  1
% 2.05/0.97  --bmc1_ucm_init_mode                    2
% 2.05/0.97  --bmc1_ucm_cone_mode                    none
% 2.05/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.05/0.97  --bmc1_ucm_relax_model                  4
% 2.05/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.05/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.05/0.97  --bmc1_ucm_layered_model                none
% 2.05/0.97  --bmc1_ucm_max_lemma_size               10
% 2.05/0.97  
% 2.05/0.97  ------ AIG Options
% 2.05/0.97  
% 2.05/0.97  --aig_mode                              false
% 2.05/0.97  
% 2.05/0.97  ------ Instantiation Options
% 2.05/0.97  
% 2.05/0.97  --instantiation_flag                    true
% 2.05/0.97  --inst_sos_flag                         false
% 2.05/0.97  --inst_sos_phase                        true
% 2.05/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.05/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.05/0.97  --inst_lit_sel_side                     none
% 2.05/0.97  --inst_solver_per_active                1400
% 2.05/0.97  --inst_solver_calls_frac                1.
% 2.05/0.97  --inst_passive_queue_type               priority_queues
% 2.05/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.05/0.97  --inst_passive_queues_freq              [25;2]
% 2.05/0.97  --inst_dismatching                      true
% 2.05/0.97  --inst_eager_unprocessed_to_passive     true
% 2.05/0.97  --inst_prop_sim_given                   true
% 2.05/0.97  --inst_prop_sim_new                     false
% 2.05/0.97  --inst_subs_new                         false
% 2.05/0.97  --inst_eq_res_simp                      false
% 2.05/0.97  --inst_subs_given                       false
% 2.05/0.97  --inst_orphan_elimination               true
% 2.05/0.97  --inst_learning_loop_flag               true
% 2.05/0.97  --inst_learning_start                   3000
% 2.05/0.97  --inst_learning_factor                  2
% 2.05/0.97  --inst_start_prop_sim_after_learn       3
% 2.05/0.97  --inst_sel_renew                        solver
% 2.05/0.97  --inst_lit_activity_flag                true
% 2.05/0.97  --inst_restr_to_given                   false
% 2.05/0.97  --inst_activity_threshold               500
% 2.05/0.97  --inst_out_proof                        true
% 2.05/0.97  
% 2.05/0.97  ------ Resolution Options
% 2.05/0.97  
% 2.05/0.97  --resolution_flag                       false
% 2.05/0.97  --res_lit_sel                           adaptive
% 2.05/0.97  --res_lit_sel_side                      none
% 2.05/0.97  --res_ordering                          kbo
% 2.05/0.97  --res_to_prop_solver                    active
% 2.05/0.97  --res_prop_simpl_new                    false
% 2.05/0.97  --res_prop_simpl_given                  true
% 2.05/0.97  --res_passive_queue_type                priority_queues
% 2.05/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.05/0.97  --res_passive_queues_freq               [15;5]
% 2.05/0.97  --res_forward_subs                      full
% 2.05/0.97  --res_backward_subs                     full
% 2.05/0.97  --res_forward_subs_resolution           true
% 2.05/0.97  --res_backward_subs_resolution          true
% 2.05/0.97  --res_orphan_elimination                true
% 2.05/0.97  --res_time_limit                        2.
% 2.05/0.97  --res_out_proof                         true
% 2.05/0.97  
% 2.05/0.97  ------ Superposition Options
% 2.05/0.97  
% 2.05/0.97  --superposition_flag                    true
% 2.05/0.97  --sup_passive_queue_type                priority_queues
% 2.05/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.05/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.05/0.97  --demod_completeness_check              fast
% 2.05/0.97  --demod_use_ground                      true
% 2.05/0.97  --sup_to_prop_solver                    passive
% 2.05/0.97  --sup_prop_simpl_new                    true
% 2.05/0.97  --sup_prop_simpl_given                  true
% 2.05/0.97  --sup_fun_splitting                     false
% 2.05/0.97  --sup_smt_interval                      50000
% 2.05/0.97  
% 2.05/0.97  ------ Superposition Simplification Setup
% 2.05/0.97  
% 2.05/0.97  --sup_indices_passive                   []
% 2.05/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.05/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.05/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.05/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.05/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.05/0.97  --sup_full_bw                           [BwDemod]
% 2.05/0.97  --sup_immed_triv                        [TrivRules]
% 2.05/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.05/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.05/0.97  --sup_immed_bw_main                     []
% 2.05/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.05/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.05/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.05/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.05/0.97  
% 2.05/0.97  ------ Combination Options
% 2.05/0.97  
% 2.05/0.97  --comb_res_mult                         3
% 2.05/0.97  --comb_sup_mult                         2
% 2.05/0.97  --comb_inst_mult                        10
% 2.05/0.97  
% 2.05/0.97  ------ Debug Options
% 2.05/0.97  
% 2.05/0.97  --dbg_backtrace                         false
% 2.05/0.97  --dbg_dump_prop_clauses                 false
% 2.05/0.97  --dbg_dump_prop_clauses_file            -
% 2.05/0.97  --dbg_out_stat                          false
% 2.05/0.97  
% 2.05/0.97  
% 2.05/0.97  
% 2.05/0.97  
% 2.05/0.97  ------ Proving...
% 2.05/0.97  
% 2.05/0.97  
% 2.05/0.97  % SZS status Theorem for theBenchmark.p
% 2.05/0.97  
% 2.05/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 2.05/0.97  
% 2.05/0.97  fof(f19,conjecture,(
% 2.05/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) <=> m1_connsp_2(X2,X0,X1)))))),
% 2.05/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/0.97  
% 2.05/0.97  fof(f20,negated_conjecture,(
% 2.05/0.97    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) <=> m1_connsp_2(X2,X0,X1)))))),
% 2.05/0.97    inference(negated_conjecture,[],[f19])).
% 2.05/0.97  
% 2.05/0.97  fof(f38,plain,(
% 2.05/0.97    ? [X0] : (? [X1] : (? [X2] : ((m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) <~> m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.05/0.97    inference(ennf_transformation,[],[f20])).
% 2.05/0.97  
% 2.05/0.97  fof(f39,plain,(
% 2.05/0.97    ? [X0] : (? [X1] : (? [X2] : ((m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) <~> m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.05/0.97    inference(flattening,[],[f38])).
% 2.05/0.97  
% 2.05/0.97  fof(f47,plain,(
% 2.05/0.97    ? [X0] : (? [X1] : (? [X2] : (((~m1_connsp_2(X2,X0,X1) | ~m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & (m1_connsp_2(X2,X0,X1) | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.05/0.97    inference(nnf_transformation,[],[f39])).
% 2.05/0.97  
% 2.05/0.97  fof(f48,plain,(
% 2.05/0.97    ? [X0] : (? [X1] : (? [X2] : ((~m1_connsp_2(X2,X0,X1) | ~m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & (m1_connsp_2(X2,X0,X1) | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.05/0.97    inference(flattening,[],[f47])).
% 2.05/0.97  
% 2.05/0.97  fof(f51,plain,(
% 2.05/0.97    ( ! [X0,X1] : (? [X2] : ((~m1_connsp_2(X2,X0,X1) | ~m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & (m1_connsp_2(X2,X0,X1) | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => ((~m1_connsp_2(sK3,X0,X1) | ~m2_connsp_2(sK3,X0,k6_domain_1(u1_struct_0(X0),X1))) & (m1_connsp_2(sK3,X0,X1) | m2_connsp_2(sK3,X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.05/0.97    introduced(choice_axiom,[])).
% 2.05/0.97  
% 2.05/0.97  fof(f50,plain,(
% 2.05/0.97    ( ! [X0] : (? [X1] : (? [X2] : ((~m1_connsp_2(X2,X0,X1) | ~m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & (m1_connsp_2(X2,X0,X1) | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : ((~m1_connsp_2(X2,X0,sK2) | ~m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),sK2))) & (m1_connsp_2(X2,X0,sK2) | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),sK2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK2,u1_struct_0(X0)))) )),
% 2.05/0.97    introduced(choice_axiom,[])).
% 2.05/0.97  
% 2.05/0.97  fof(f49,plain,(
% 2.05/0.97    ? [X0] : (? [X1] : (? [X2] : ((~m1_connsp_2(X2,X0,X1) | ~m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & (m1_connsp_2(X2,X0,X1) | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~m1_connsp_2(X2,sK1,X1) | ~m2_connsp_2(X2,sK1,k6_domain_1(u1_struct_0(sK1),X1))) & (m1_connsp_2(X2,sK1,X1) | m2_connsp_2(X2,sK1,k6_domain_1(u1_struct_0(sK1),X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X1,u1_struct_0(sK1))) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 2.05/0.97    introduced(choice_axiom,[])).
% 2.05/0.97  
% 2.05/0.97  fof(f52,plain,(
% 2.05/0.97    (((~m1_connsp_2(sK3,sK1,sK2) | ~m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2))) & (m1_connsp_2(sK3,sK1,sK2) | m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK2,u1_struct_0(sK1))) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 2.05/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f48,f51,f50,f49])).
% 2.05/0.97  
% 2.05/0.97  fof(f79,plain,(
% 2.05/0.97    m1_subset_1(sK2,u1_struct_0(sK1))),
% 2.05/0.97    inference(cnf_transformation,[],[f52])).
% 2.05/0.97  
% 2.05/0.97  fof(f12,axiom,(
% 2.05/0.97    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 2.05/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/0.97  
% 2.05/0.97  fof(f24,plain,(
% 2.05/0.97    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.05/0.97    inference(ennf_transformation,[],[f12])).
% 2.05/0.97  
% 2.05/0.97  fof(f25,plain,(
% 2.05/0.97    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.05/0.97    inference(flattening,[],[f24])).
% 2.05/0.97  
% 2.05/0.97  fof(f67,plain,(
% 2.05/0.97    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.05/0.97    inference(cnf_transformation,[],[f25])).
% 2.05/0.97  
% 2.05/0.97  fof(f1,axiom,(
% 2.05/0.97    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.05/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/0.97  
% 2.05/0.97  fof(f53,plain,(
% 2.05/0.97    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.05/0.97    inference(cnf_transformation,[],[f1])).
% 2.05/0.97  
% 2.05/0.97  fof(f2,axiom,(
% 2.05/0.97    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.05/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/0.97  
% 2.05/0.97  fof(f54,plain,(
% 2.05/0.97    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.05/0.97    inference(cnf_transformation,[],[f2])).
% 2.05/0.97  
% 2.05/0.97  fof(f3,axiom,(
% 2.05/0.97    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.05/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/0.97  
% 2.05/0.97  fof(f55,plain,(
% 2.05/0.97    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.05/0.97    inference(cnf_transformation,[],[f3])).
% 2.05/0.97  
% 2.05/0.97  fof(f4,axiom,(
% 2.05/0.97    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.05/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/0.97  
% 2.05/0.97  fof(f56,plain,(
% 2.05/0.97    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.05/0.97    inference(cnf_transformation,[],[f4])).
% 2.05/0.97  
% 2.05/0.97  fof(f5,axiom,(
% 2.05/0.97    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 2.05/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/0.97  
% 2.05/0.97  fof(f57,plain,(
% 2.05/0.97    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 2.05/0.97    inference(cnf_transformation,[],[f5])).
% 2.05/0.97  
% 2.05/0.97  fof(f6,axiom,(
% 2.05/0.97    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 2.05/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/0.97  
% 2.05/0.97  fof(f58,plain,(
% 2.05/0.97    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 2.05/0.97    inference(cnf_transformation,[],[f6])).
% 2.05/0.97  
% 2.05/0.97  fof(f7,axiom,(
% 2.05/0.97    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 2.05/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/0.97  
% 2.05/0.97  fof(f59,plain,(
% 2.05/0.97    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 2.05/0.97    inference(cnf_transformation,[],[f7])).
% 2.05/0.97  
% 2.05/0.97  fof(f83,plain,(
% 2.05/0.97    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.05/0.97    inference(definition_unfolding,[],[f58,f59])).
% 2.05/0.97  
% 2.05/0.97  fof(f84,plain,(
% 2.05/0.97    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.05/0.97    inference(definition_unfolding,[],[f57,f83])).
% 2.05/0.97  
% 2.05/0.97  fof(f85,plain,(
% 2.05/0.97    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.05/0.97    inference(definition_unfolding,[],[f56,f84])).
% 2.05/0.97  
% 2.05/0.97  fof(f86,plain,(
% 2.05/0.97    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.05/0.97    inference(definition_unfolding,[],[f55,f85])).
% 2.05/0.97  
% 2.05/0.97  fof(f87,plain,(
% 2.05/0.97    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.05/0.97    inference(definition_unfolding,[],[f54,f86])).
% 2.05/0.97  
% 2.05/0.97  fof(f88,plain,(
% 2.05/0.97    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 2.05/0.97    inference(definition_unfolding,[],[f53,f87])).
% 2.05/0.97  
% 2.05/0.97  fof(f92,plain,(
% 2.05/0.97    ( ! [X0,X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.05/0.97    inference(definition_unfolding,[],[f67,f88])).
% 2.05/0.97  
% 2.05/0.97  fof(f17,axiom,(
% 2.05/0.97    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X2] : m1_connsp_2(X2,X0,X1))),
% 2.05/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/0.97  
% 2.05/0.97  fof(f34,plain,(
% 2.05/0.97    ! [X0,X1] : (? [X2] : m1_connsp_2(X2,X0,X1) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.05/0.97    inference(ennf_transformation,[],[f17])).
% 2.05/0.97  
% 2.05/0.97  fof(f35,plain,(
% 2.05/0.97    ! [X0,X1] : (? [X2] : m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.05/0.97    inference(flattening,[],[f34])).
% 2.05/0.97  
% 2.05/0.97  fof(f45,plain,(
% 2.05/0.97    ! [X1,X0] : (? [X2] : m1_connsp_2(X2,X0,X1) => m1_connsp_2(sK0(X0,X1),X0,X1))),
% 2.05/0.97    introduced(choice_axiom,[])).
% 2.05/0.97  
% 2.05/0.97  fof(f46,plain,(
% 2.05/0.97    ! [X0,X1] : (m1_connsp_2(sK0(X0,X1),X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.05/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f35,f45])).
% 2.05/0.97  
% 2.05/0.97  fof(f74,plain,(
% 2.05/0.97    ( ! [X0,X1] : (m1_connsp_2(sK0(X0,X1),X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.05/0.97    inference(cnf_transformation,[],[f46])).
% 2.05/0.97  
% 2.05/0.97  fof(f76,plain,(
% 2.05/0.97    ~v2_struct_0(sK1)),
% 2.05/0.97    inference(cnf_transformation,[],[f52])).
% 2.05/0.97  
% 2.05/0.97  fof(f77,plain,(
% 2.05/0.97    v2_pre_topc(sK1)),
% 2.05/0.97    inference(cnf_transformation,[],[f52])).
% 2.05/0.97  
% 2.05/0.97  fof(f78,plain,(
% 2.05/0.97    l1_pre_topc(sK1)),
% 2.05/0.97    inference(cnf_transformation,[],[f52])).
% 2.05/0.97  
% 2.05/0.97  fof(f15,axiom,(
% 2.05/0.97    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.05/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/0.97  
% 2.05/0.97  fof(f30,plain,(
% 2.05/0.97    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.05/0.97    inference(ennf_transformation,[],[f15])).
% 2.05/0.97  
% 2.05/0.97  fof(f31,plain,(
% 2.05/0.97    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.05/0.97    inference(flattening,[],[f30])).
% 2.05/0.97  
% 2.05/0.97  fof(f72,plain,(
% 2.05/0.97    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.05/0.97    inference(cnf_transformation,[],[f31])).
% 2.05/0.97  
% 2.05/0.97  fof(f18,axiom,(
% 2.05/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (m1_connsp_2(X1,X0,X2) => r2_hidden(X2,X1)))))),
% 2.05/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/0.97  
% 2.05/0.97  fof(f36,plain,(
% 2.05/0.97    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.05/0.97    inference(ennf_transformation,[],[f18])).
% 2.05/0.97  
% 2.05/0.97  fof(f37,plain,(
% 2.05/0.97    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.05/0.97    inference(flattening,[],[f36])).
% 2.05/0.97  
% 2.05/0.97  fof(f75,plain,(
% 2.05/0.97    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.05/0.97    inference(cnf_transformation,[],[f37])).
% 2.05/0.97  
% 2.05/0.97  fof(f9,axiom,(
% 2.05/0.97    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.05/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/0.97  
% 2.05/0.97  fof(f42,plain,(
% 2.05/0.97    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.05/0.97    inference(nnf_transformation,[],[f9])).
% 2.05/0.97  
% 2.05/0.97  fof(f63,plain,(
% 2.05/0.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.05/0.97    inference(cnf_transformation,[],[f42])).
% 2.05/0.97  
% 2.05/0.97  fof(f10,axiom,(
% 2.05/0.97    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.05/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/0.97  
% 2.05/0.97  fof(f21,plain,(
% 2.05/0.97    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.05/0.97    inference(ennf_transformation,[],[f10])).
% 2.05/0.97  
% 2.05/0.97  fof(f65,plain,(
% 2.05/0.97    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.05/0.97    inference(cnf_transformation,[],[f21])).
% 2.05/0.97  
% 2.05/0.97  fof(f64,plain,(
% 2.05/0.97    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.05/0.97    inference(cnf_transformation,[],[f42])).
% 2.05/0.97  
% 2.05/0.97  fof(f8,axiom,(
% 2.05/0.97    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 2.05/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/0.97  
% 2.05/0.97  fof(f40,plain,(
% 2.05/0.97    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 2.05/0.97    inference(nnf_transformation,[],[f8])).
% 2.05/0.97  
% 2.05/0.97  fof(f41,plain,(
% 2.05/0.97    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 2.05/0.97    inference(flattening,[],[f40])).
% 2.05/0.97  
% 2.05/0.97  fof(f62,plain,(
% 2.05/0.97    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 2.05/0.97    inference(cnf_transformation,[],[f41])).
% 2.05/0.97  
% 2.05/0.97  fof(f89,plain,(
% 2.05/0.97    ( ! [X2,X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 2.05/0.97    inference(definition_unfolding,[],[f62,f87])).
% 2.05/0.97  
% 2.05/0.97  fof(f82,plain,(
% 2.05/0.97    ~m1_connsp_2(sK3,sK1,sK2) | ~m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2))),
% 2.05/0.97    inference(cnf_transformation,[],[f52])).
% 2.05/0.97  
% 2.05/0.97  fof(f14,axiom,(
% 2.05/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 2.05/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/0.97  
% 2.05/0.97  fof(f28,plain,(
% 2.05/0.97    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.05/0.97    inference(ennf_transformation,[],[f14])).
% 2.05/0.97  
% 2.05/0.97  fof(f29,plain,(
% 2.05/0.97    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.05/0.97    inference(flattening,[],[f28])).
% 2.05/0.97  
% 2.05/0.97  fof(f44,plain,(
% 2.05/0.97    ! [X0] : (! [X1] : (! [X2] : (((m2_connsp_2(X2,X0,X1) | ~r1_tarski(X1,k1_tops_1(X0,X2))) & (r1_tarski(X1,k1_tops_1(X0,X2)) | ~m2_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.05/0.97    inference(nnf_transformation,[],[f29])).
% 2.05/0.97  
% 2.05/0.97  fof(f71,plain,(
% 2.05/0.97    ( ! [X2,X0,X1] : (m2_connsp_2(X2,X0,X1) | ~r1_tarski(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.05/0.97    inference(cnf_transformation,[],[f44])).
% 2.05/0.97  
% 2.05/0.97  fof(f80,plain,(
% 2.05/0.97    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 2.05/0.97    inference(cnf_transformation,[],[f52])).
% 2.05/0.97  
% 2.05/0.97  fof(f13,axiom,(
% 2.05/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 2.05/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/0.97  
% 2.05/0.97  fof(f26,plain,(
% 2.05/0.97    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.05/0.97    inference(ennf_transformation,[],[f13])).
% 2.05/0.97  
% 2.05/0.97  fof(f27,plain,(
% 2.05/0.97    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.05/0.97    inference(flattening,[],[f26])).
% 2.05/0.97  
% 2.05/0.97  fof(f43,plain,(
% 2.05/0.97    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.05/0.97    inference(nnf_transformation,[],[f27])).
% 2.05/0.97  
% 2.05/0.97  fof(f69,plain,(
% 2.05/0.97    ( ! [X2,X0,X1] : (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.05/0.97    inference(cnf_transformation,[],[f43])).
% 2.05/0.97  
% 2.05/0.97  fof(f11,axiom,(
% 2.05/0.97    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.05/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/0.97  
% 2.05/0.97  fof(f22,plain,(
% 2.05/0.97    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.05/0.97    inference(ennf_transformation,[],[f11])).
% 2.05/0.97  
% 2.05/0.97  fof(f23,plain,(
% 2.05/0.97    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.05/0.97    inference(flattening,[],[f22])).
% 2.05/0.97  
% 2.05/0.97  fof(f66,plain,(
% 2.05/0.97    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.05/0.97    inference(cnf_transformation,[],[f23])).
% 2.05/0.97  
% 2.05/0.97  fof(f60,plain,(
% 2.05/0.97    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 2.05/0.97    inference(cnf_transformation,[],[f41])).
% 2.05/0.97  
% 2.05/0.97  fof(f91,plain,(
% 2.05/0.97    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)) )),
% 2.05/0.97    inference(definition_unfolding,[],[f60,f87])).
% 2.05/0.97  
% 2.05/0.97  fof(f81,plain,(
% 2.05/0.97    m1_connsp_2(sK3,sK1,sK2) | m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2))),
% 2.05/0.97    inference(cnf_transformation,[],[f52])).
% 2.05/0.97  
% 2.05/0.97  fof(f70,plain,(
% 2.05/0.97    ( ! [X2,X0,X1] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~m2_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.05/0.97    inference(cnf_transformation,[],[f44])).
% 2.05/0.97  
% 2.05/0.97  fof(f16,axiom,(
% 2.05/0.97    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X2] : (m2_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.05/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/0.97  
% 2.05/0.97  fof(f32,plain,(
% 2.05/0.97    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.05/0.97    inference(ennf_transformation,[],[f16])).
% 2.05/0.97  
% 2.05/0.97  fof(f33,plain,(
% 2.05/0.97    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.05/0.97    inference(flattening,[],[f32])).
% 2.05/0.97  
% 2.05/0.97  fof(f73,plain,(
% 2.05/0.97    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.05/0.97    inference(cnf_transformation,[],[f33])).
% 2.05/0.97  
% 2.05/0.97  fof(f68,plain,(
% 2.05/0.97    ( ! [X2,X0,X1] : (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.05/0.97    inference(cnf_transformation,[],[f43])).
% 2.05/0.97  
% 2.05/0.97  cnf(c_19,negated_conjecture,
% 2.05/0.97      ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 2.05/0.97      inference(cnf_transformation,[],[f79]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_1978,negated_conjecture,
% 2.05/0.97      ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 2.05/0.97      inference(subtyping,[status(esa)],[c_19]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_2444,plain,
% 2.05/0.97      ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
% 2.05/0.97      inference(predicate_to_equality,[status(thm)],[c_1978]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_7,plain,
% 2.05/0.97      ( ~ m1_subset_1(X0,X1)
% 2.05/0.97      | v1_xboole_0(X1)
% 2.05/0.97      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k6_domain_1(X1,X0) ),
% 2.05/0.97      inference(cnf_transformation,[],[f92]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_1980,plain,
% 2.05/0.97      ( ~ m1_subset_1(X0_46,X1_46)
% 2.05/0.97      | v1_xboole_0(X1_46)
% 2.05/0.97      | k6_enumset1(X0_46,X0_46,X0_46,X0_46,X0_46,X0_46,X0_46,X0_46) = k6_domain_1(X1_46,X0_46) ),
% 2.05/0.97      inference(subtyping,[status(esa)],[c_7]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_2442,plain,
% 2.05/0.97      ( k6_enumset1(X0_46,X0_46,X0_46,X0_46,X0_46,X0_46,X0_46,X0_46) = k6_domain_1(X1_46,X0_46)
% 2.05/0.97      | m1_subset_1(X0_46,X1_46) != iProver_top
% 2.05/0.97      | v1_xboole_0(X1_46) = iProver_top ),
% 2.05/0.97      inference(predicate_to_equality,[status(thm)],[c_1980]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_3276,plain,
% 2.05/0.97      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k6_domain_1(u1_struct_0(sK1),sK2)
% 2.05/0.97      | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
% 2.05/0.97      inference(superposition,[status(thm)],[c_2444,c_2442]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_14,plain,
% 2.05/0.97      ( m1_connsp_2(sK0(X0,X1),X0,X1)
% 2.05/0.97      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.05/0.97      | v2_struct_0(X0)
% 2.05/0.97      | ~ v2_pre_topc(X0)
% 2.05/0.97      | ~ l1_pre_topc(X0) ),
% 2.05/0.97      inference(cnf_transformation,[],[f74]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_22,negated_conjecture,
% 2.05/0.97      ( ~ v2_struct_0(sK1) ),
% 2.05/0.97      inference(cnf_transformation,[],[f76]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_376,plain,
% 2.05/0.97      ( m1_connsp_2(sK0(X0,X1),X0,X1)
% 2.05/0.97      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.05/0.97      | ~ v2_pre_topc(X0)
% 2.05/0.97      | ~ l1_pre_topc(X0)
% 2.05/0.97      | sK1 != X0 ),
% 2.05/0.97      inference(resolution_lifted,[status(thm)],[c_14,c_22]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_377,plain,
% 2.05/0.97      ( m1_connsp_2(sK0(sK1,X0),sK1,X0)
% 2.05/0.97      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.05/0.97      | ~ v2_pre_topc(sK1)
% 2.05/0.97      | ~ l1_pre_topc(sK1) ),
% 2.05/0.97      inference(unflattening,[status(thm)],[c_376]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_21,negated_conjecture,
% 2.05/0.97      ( v2_pre_topc(sK1) ),
% 2.05/0.97      inference(cnf_transformation,[],[f77]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_20,negated_conjecture,
% 2.05/0.97      ( l1_pre_topc(sK1) ),
% 2.05/0.97      inference(cnf_transformation,[],[f78]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_381,plain,
% 2.05/0.97      ( m1_connsp_2(sK0(sK1,X0),sK1,X0)
% 2.05/0.97      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
% 2.05/0.97      inference(global_propositional_subsumption,
% 2.05/0.97                [status(thm)],
% 2.05/0.97                [c_377,c_21,c_20]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_12,plain,
% 2.05/0.97      ( ~ m1_connsp_2(X0,X1,X2)
% 2.05/0.97      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.05/0.97      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/0.97      | v2_struct_0(X1)
% 2.05/0.97      | ~ v2_pre_topc(X1)
% 2.05/0.97      | ~ l1_pre_topc(X1) ),
% 2.05/0.97      inference(cnf_transformation,[],[f72]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_436,plain,
% 2.05/0.97      ( ~ m1_connsp_2(X0,X1,X2)
% 2.05/0.97      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.05/0.97      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/0.97      | ~ v2_pre_topc(X1)
% 2.05/0.97      | ~ l1_pre_topc(X1)
% 2.05/0.97      | sK1 != X1 ),
% 2.05/0.97      inference(resolution_lifted,[status(thm)],[c_12,c_22]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_437,plain,
% 2.05/0.97      ( ~ m1_connsp_2(X0,sK1,X1)
% 2.05/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.05/0.97      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.97      | ~ v2_pre_topc(sK1)
% 2.05/0.97      | ~ l1_pre_topc(sK1) ),
% 2.05/0.97      inference(unflattening,[status(thm)],[c_436]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_441,plain,
% 2.05/0.97      ( ~ m1_connsp_2(X0,sK1,X1)
% 2.05/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.05/0.97      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.05/0.97      inference(global_propositional_subsumption,
% 2.05/0.97                [status(thm)],
% 2.05/0.97                [c_437,c_21,c_20]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_936,plain,
% 2.05/0.97      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.05/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.05/0.97      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.97      | X1 != X0
% 2.05/0.97      | sK0(sK1,X0) != X2
% 2.05/0.97      | sK1 != sK1 ),
% 2.05/0.97      inference(resolution_lifted,[status(thm)],[c_381,c_441]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_937,plain,
% 2.05/0.97      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.05/0.97      | m1_subset_1(sK0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.05/0.97      inference(unflattening,[status(thm)],[c_936]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_1971,plain,
% 2.05/0.97      ( ~ m1_subset_1(X0_46,u1_struct_0(sK1))
% 2.05/0.97      | m1_subset_1(sK0(sK1,X0_46),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.05/0.97      inference(subtyping,[status(esa)],[c_937]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_2038,plain,
% 2.05/0.97      ( m1_subset_1(sK0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.97      | ~ m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 2.05/0.97      inference(instantiation,[status(thm)],[c_1971]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_15,plain,
% 2.05/0.97      ( ~ m1_connsp_2(X0,X1,X2)
% 2.05/0.97      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.05/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/0.97      | r2_hidden(X2,X0)
% 2.05/0.97      | v2_struct_0(X1)
% 2.05/0.97      | ~ v2_pre_topc(X1)
% 2.05/0.97      | ~ l1_pre_topc(X1) ),
% 2.05/0.97      inference(cnf_transformation,[],[f75]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_128,plain,
% 2.05/0.97      ( ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.05/0.97      | ~ m1_connsp_2(X0,X1,X2)
% 2.05/0.97      | r2_hidden(X2,X0)
% 2.05/0.97      | v2_struct_0(X1)
% 2.05/0.97      | ~ v2_pre_topc(X1)
% 2.05/0.97      | ~ l1_pre_topc(X1) ),
% 2.05/0.97      inference(global_propositional_subsumption,
% 2.05/0.97                [status(thm)],
% 2.05/0.97                [c_15,c_12]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_129,plain,
% 2.05/0.97      ( ~ m1_connsp_2(X0,X1,X2)
% 2.05/0.97      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.05/0.97      | r2_hidden(X2,X0)
% 2.05/0.97      | v2_struct_0(X1)
% 2.05/0.97      | ~ v2_pre_topc(X1)
% 2.05/0.97      | ~ l1_pre_topc(X1) ),
% 2.05/0.97      inference(renaming,[status(thm)],[c_128]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_415,plain,
% 2.05/0.97      ( ~ m1_connsp_2(X0,X1,X2)
% 2.05/0.97      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.05/0.97      | r2_hidden(X2,X0)
% 2.05/0.97      | ~ v2_pre_topc(X1)
% 2.05/0.97      | ~ l1_pre_topc(X1)
% 2.05/0.97      | sK1 != X1 ),
% 2.05/0.97      inference(resolution_lifted,[status(thm)],[c_129,c_22]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_416,plain,
% 2.05/0.97      ( ~ m1_connsp_2(X0,sK1,X1)
% 2.05/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.05/0.97      | r2_hidden(X1,X0)
% 2.05/0.97      | ~ v2_pre_topc(sK1)
% 2.05/0.97      | ~ l1_pre_topc(sK1) ),
% 2.05/0.97      inference(unflattening,[status(thm)],[c_415]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_420,plain,
% 2.05/0.97      ( ~ m1_connsp_2(X0,sK1,X1)
% 2.05/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.05/0.97      | r2_hidden(X1,X0) ),
% 2.05/0.97      inference(global_propositional_subsumption,
% 2.05/0.97                [status(thm)],
% 2.05/0.97                [c_416,c_21,c_20]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_948,plain,
% 2.05/0.97      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.05/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.05/0.97      | r2_hidden(X1,X2)
% 2.05/0.97      | X1 != X0
% 2.05/0.97      | sK0(sK1,X0) != X2
% 2.05/0.97      | sK1 != sK1 ),
% 2.05/0.97      inference(resolution_lifted,[status(thm)],[c_381,c_420]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_949,plain,
% 2.05/0.97      ( ~ m1_subset_1(X0,u1_struct_0(sK1)) | r2_hidden(X0,sK0(sK1,X0)) ),
% 2.05/0.97      inference(unflattening,[status(thm)],[c_948]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_1970,plain,
% 2.05/0.97      ( ~ m1_subset_1(X0_46,u1_struct_0(sK1))
% 2.05/0.97      | r2_hidden(X0_46,sK0(sK1,X0_46)) ),
% 2.05/0.97      inference(subtyping,[status(esa)],[c_949]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_2041,plain,
% 2.05/0.97      ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 2.05/0.97      | r2_hidden(sK2,sK0(sK1,sK2)) ),
% 2.05/0.97      inference(instantiation,[status(thm)],[c_1970]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_4,plain,
% 2.05/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.05/0.97      inference(cnf_transformation,[],[f63]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_1982,plain,
% 2.05/0.97      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(X1_46))
% 2.05/0.97      | r1_tarski(X0_46,X1_46) ),
% 2.05/0.97      inference(subtyping,[status(esa)],[c_4]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_2598,plain,
% 2.05/0.97      ( ~ m1_subset_1(sK0(sK1,X0_46),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.97      | r1_tarski(sK0(sK1,X0_46),u1_struct_0(sK1)) ),
% 2.05/0.97      inference(instantiation,[status(thm)],[c_1982]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_2600,plain,
% 2.05/0.97      ( ~ m1_subset_1(sK0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.97      | r1_tarski(sK0(sK1,sK2),u1_struct_0(sK1)) ),
% 2.05/0.97      inference(instantiation,[status(thm)],[c_2598]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_2632,plain,
% 2.05/0.97      ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 2.05/0.97      | v1_xboole_0(u1_struct_0(sK1))
% 2.05/0.97      | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k6_domain_1(u1_struct_0(sK1),sK2) ),
% 2.05/0.97      inference(instantiation,[status(thm)],[c_1980]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_5,plain,
% 2.05/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.05/0.97      | ~ r2_hidden(X2,X0)
% 2.05/0.97      | ~ v1_xboole_0(X1) ),
% 2.05/0.97      inference(cnf_transformation,[],[f65]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_3,plain,
% 2.05/0.97      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.05/0.97      inference(cnf_transformation,[],[f64]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_190,plain,
% 2.05/0.97      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.05/0.97      inference(prop_impl,[status(thm)],[c_3]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_191,plain,
% 2.05/0.97      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.05/0.97      inference(renaming,[status(thm)],[c_190]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_244,plain,
% 2.05/0.97      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X2) | ~ v1_xboole_0(X2) ),
% 2.05/0.97      inference(bin_hyper_res,[status(thm)],[c_5,c_191]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_1977,plain,
% 2.05/0.97      ( ~ r2_hidden(X0_46,X1_46)
% 2.05/0.97      | ~ r1_tarski(X1_46,X2_46)
% 2.05/0.97      | ~ v1_xboole_0(X2_46) ),
% 2.05/0.97      inference(subtyping,[status(esa)],[c_244]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_2686,plain,
% 2.05/0.97      ( ~ r2_hidden(X0_46,X1_46)
% 2.05/0.97      | ~ r1_tarski(X1_46,u1_struct_0(sK1))
% 2.05/0.97      | ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 2.05/0.97      inference(instantiation,[status(thm)],[c_1977]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_2779,plain,
% 2.05/0.97      ( ~ r2_hidden(X0_46,sK0(sK1,X1_46))
% 2.05/0.97      | ~ r1_tarski(sK0(sK1,X1_46),u1_struct_0(sK1))
% 2.05/0.97      | ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 2.05/0.97      inference(instantiation,[status(thm)],[c_2686]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_2781,plain,
% 2.05/0.97      ( ~ r2_hidden(sK2,sK0(sK1,sK2))
% 2.05/0.97      | ~ r1_tarski(sK0(sK1,sK2),u1_struct_0(sK1))
% 2.05/0.97      | ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 2.05/0.97      inference(instantiation,[status(thm)],[c_2779]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_3487,plain,
% 2.05/0.97      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k6_domain_1(u1_struct_0(sK1),sK2) ),
% 2.05/0.97      inference(global_propositional_subsumption,
% 2.05/0.97                [status(thm)],
% 2.05/0.97                [c_3276,c_19,c_2038,c_2041,c_2600,c_2632,c_2781]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_0,plain,
% 2.05/0.97      ( ~ r2_hidden(X0,X1)
% 2.05/0.97      | ~ r2_hidden(X2,X1)
% 2.05/0.97      | r1_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0),X1) ),
% 2.05/0.97      inference(cnf_transformation,[],[f89]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_1986,plain,
% 2.05/0.97      ( ~ r2_hidden(X0_46,X1_46)
% 2.05/0.97      | ~ r2_hidden(X2_46,X1_46)
% 2.05/0.97      | r1_tarski(k6_enumset1(X2_46,X2_46,X2_46,X2_46,X2_46,X2_46,X2_46,X0_46),X1_46) ),
% 2.05/0.97      inference(subtyping,[status(esa)],[c_0]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_2436,plain,
% 2.05/0.97      ( r2_hidden(X0_46,X1_46) != iProver_top
% 2.05/0.97      | r2_hidden(X2_46,X1_46) != iProver_top
% 2.05/0.97      | r1_tarski(k6_enumset1(X2_46,X2_46,X2_46,X2_46,X2_46,X2_46,X2_46,X0_46),X1_46) = iProver_top ),
% 2.05/0.97      inference(predicate_to_equality,[status(thm)],[c_1986]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_3491,plain,
% 2.05/0.97      ( r2_hidden(sK2,X0_46) != iProver_top
% 2.05/0.97      | r1_tarski(k6_domain_1(u1_struct_0(sK1),sK2),X0_46) = iProver_top ),
% 2.05/0.97      inference(superposition,[status(thm)],[c_3487,c_2436]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_16,negated_conjecture,
% 2.05/0.97      ( ~ m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2))
% 2.05/0.97      | ~ m1_connsp_2(sK3,sK1,sK2) ),
% 2.05/0.97      inference(cnf_transformation,[],[f82]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_192,plain,
% 2.05/0.97      ( ~ m1_connsp_2(sK3,sK1,sK2)
% 2.05/0.97      | ~ m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2)) ),
% 2.05/0.97      inference(prop_impl,[status(thm)],[c_16]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_193,plain,
% 2.05/0.97      ( ~ m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2))
% 2.05/0.97      | ~ m1_connsp_2(sK3,sK1,sK2) ),
% 2.05/0.97      inference(renaming,[status(thm)],[c_192]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_10,plain,
% 2.05/0.97      ( m2_connsp_2(X0,X1,X2)
% 2.05/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/0.97      | ~ r1_tarski(X2,k1_tops_1(X1,X0))
% 2.05/0.97      | ~ v2_pre_topc(X1)
% 2.05/0.97      | ~ l1_pre_topc(X1) ),
% 2.05/0.97      inference(cnf_transformation,[],[f71]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_539,plain,
% 2.05/0.97      ( m2_connsp_2(X0,X1,X2)
% 2.05/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/0.97      | ~ r1_tarski(X2,k1_tops_1(X1,X0))
% 2.05/0.97      | ~ v2_pre_topc(X1)
% 2.05/0.97      | sK1 != X1 ),
% 2.05/0.97      inference(resolution_lifted,[status(thm)],[c_10,c_20]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_540,plain,
% 2.05/0.97      ( m2_connsp_2(X0,sK1,X1)
% 2.05/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.97      | ~ r1_tarski(X1,k1_tops_1(sK1,X0))
% 2.05/0.97      | ~ v2_pre_topc(sK1) ),
% 2.05/0.97      inference(unflattening,[status(thm)],[c_539]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_544,plain,
% 2.05/0.97      ( ~ r1_tarski(X1,k1_tops_1(sK1,X0))
% 2.05/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.97      | m2_connsp_2(X0,sK1,X1) ),
% 2.05/0.97      inference(global_propositional_subsumption,
% 2.05/0.97                [status(thm)],
% 2.05/0.97                [c_540,c_21]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_545,plain,
% 2.05/0.97      ( m2_connsp_2(X0,sK1,X1)
% 2.05/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.97      | ~ r1_tarski(X1,k1_tops_1(sK1,X0)) ),
% 2.05/0.97      inference(renaming,[status(thm)],[c_544]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_594,plain,
% 2.05/0.97      ( ~ m1_connsp_2(sK3,sK1,sK2)
% 2.05/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.97      | ~ r1_tarski(X1,k1_tops_1(sK1,X0))
% 2.05/0.97      | k6_domain_1(u1_struct_0(sK1),sK2) != X1
% 2.05/0.97      | sK1 != sK1
% 2.05/0.97      | sK3 != X0 ),
% 2.05/0.97      inference(resolution_lifted,[status(thm)],[c_193,c_545]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_595,plain,
% 2.05/0.97      ( ~ m1_connsp_2(sK3,sK1,sK2)
% 2.05/0.97      | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.97      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.97      | ~ r1_tarski(k6_domain_1(u1_struct_0(sK1),sK2),k1_tops_1(sK1,sK3)) ),
% 2.05/0.97      inference(unflattening,[status(thm)],[c_594]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_18,negated_conjecture,
% 2.05/0.97      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.05/0.97      inference(cnf_transformation,[],[f80]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_597,plain,
% 2.05/0.97      ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.97      | ~ m1_connsp_2(sK3,sK1,sK2)
% 2.05/0.97      | ~ r1_tarski(k6_domain_1(u1_struct_0(sK1),sK2),k1_tops_1(sK1,sK3)) ),
% 2.05/0.97      inference(global_propositional_subsumption,
% 2.05/0.97                [status(thm)],
% 2.05/0.97                [c_595,c_18]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_598,plain,
% 2.05/0.97      ( ~ m1_connsp_2(sK3,sK1,sK2)
% 2.05/0.97      | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.97      | ~ r1_tarski(k6_domain_1(u1_struct_0(sK1),sK2),k1_tops_1(sK1,sK3)) ),
% 2.05/0.97      inference(renaming,[status(thm)],[c_597]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_8,plain,
% 2.05/0.97      ( m1_connsp_2(X0,X1,X2)
% 2.05/0.97      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.05/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/0.97      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 2.05/0.97      | v2_struct_0(X1)
% 2.05/0.97      | ~ v2_pre_topc(X1)
% 2.05/0.97      | ~ l1_pre_topc(X1) ),
% 2.05/0.97      inference(cnf_transformation,[],[f69]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_457,plain,
% 2.05/0.97      ( m1_connsp_2(X0,X1,X2)
% 2.05/0.97      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.05/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/0.97      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 2.05/0.97      | ~ v2_pre_topc(X1)
% 2.05/0.97      | ~ l1_pre_topc(X1)
% 2.05/0.97      | sK1 != X1 ),
% 2.05/0.97      inference(resolution_lifted,[status(thm)],[c_8,c_22]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_458,plain,
% 2.05/0.97      ( m1_connsp_2(X0,sK1,X1)
% 2.05/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.05/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.97      | ~ r2_hidden(X1,k1_tops_1(sK1,X0))
% 2.05/0.97      | ~ v2_pre_topc(sK1)
% 2.05/0.97      | ~ l1_pre_topc(sK1) ),
% 2.05/0.97      inference(unflattening,[status(thm)],[c_457]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_462,plain,
% 2.05/0.97      ( m1_connsp_2(X0,sK1,X1)
% 2.05/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.05/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.97      | ~ r2_hidden(X1,k1_tops_1(sK1,X0)) ),
% 2.05/0.97      inference(global_propositional_subsumption,
% 2.05/0.97                [status(thm)],
% 2.05/0.97                [c_458,c_21,c_20]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_919,plain,
% 2.05/0.97      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.05/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.97      | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.97      | ~ r2_hidden(X0,k1_tops_1(sK1,X1))
% 2.05/0.97      | ~ r1_tarski(k6_domain_1(u1_struct_0(sK1),sK2),k1_tops_1(sK1,sK3))
% 2.05/0.97      | sK2 != X0
% 2.05/0.97      | sK1 != sK1
% 2.05/0.97      | sK3 != X1 ),
% 2.05/0.97      inference(resolution_lifted,[status(thm)],[c_598,c_462]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_920,plain,
% 2.05/0.97      ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.97      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 2.05/0.97      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.97      | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3))
% 2.05/0.97      | ~ r1_tarski(k6_domain_1(u1_struct_0(sK1),sK2),k1_tops_1(sK1,sK3)) ),
% 2.05/0.97      inference(unflattening,[status(thm)],[c_919]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_922,plain,
% 2.05/0.97      ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.97      | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3))
% 2.05/0.97      | ~ r1_tarski(k6_domain_1(u1_struct_0(sK1),sK2),k1_tops_1(sK1,sK3)) ),
% 2.05/0.97      inference(global_propositional_subsumption,
% 2.05/0.97                [status(thm)],
% 2.05/0.97                [c_920,c_19,c_18]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_1972,plain,
% 2.05/0.97      ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.97      | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3))
% 2.05/0.97      | ~ r1_tarski(k6_domain_1(u1_struct_0(sK1),sK2),k1_tops_1(sK1,sK3)) ),
% 2.05/0.97      inference(subtyping,[status(esa)],[c_922]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_2450,plain,
% 2.05/0.97      ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.05/0.97      | r2_hidden(sK2,k1_tops_1(sK1,sK3)) != iProver_top
% 2.05/0.97      | r1_tarski(k6_domain_1(u1_struct_0(sK1),sK2),k1_tops_1(sK1,sK3)) != iProver_top ),
% 2.05/0.97      inference(predicate_to_equality,[status(thm)],[c_1972]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_26,plain,
% 2.05/0.97      ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
% 2.05/0.97      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_924,plain,
% 2.05/0.97      ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.05/0.97      | r2_hidden(sK2,k1_tops_1(sK1,sK3)) != iProver_top
% 2.05/0.97      | r1_tarski(k6_domain_1(u1_struct_0(sK1),sK2),k1_tops_1(sK1,sK3)) != iProver_top ),
% 2.05/0.97      inference(predicate_to_equality,[status(thm)],[c_922]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_2037,plain,
% 2.05/0.97      ( m1_subset_1(X0_46,u1_struct_0(sK1)) != iProver_top
% 2.05/0.97      | m1_subset_1(sK0(sK1,X0_46),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.05/0.97      inference(predicate_to_equality,[status(thm)],[c_1971]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_2039,plain,
% 2.05/0.97      ( m1_subset_1(sK0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 2.05/0.97      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
% 2.05/0.97      inference(instantiation,[status(thm)],[c_2037]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_2040,plain,
% 2.05/0.97      ( m1_subset_1(X0_46,u1_struct_0(sK1)) != iProver_top
% 2.05/0.97      | r2_hidden(X0_46,sK0(sK1,X0_46)) = iProver_top ),
% 2.05/0.97      inference(predicate_to_equality,[status(thm)],[c_1970]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_2042,plain,
% 2.05/0.97      ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 2.05/0.97      | r2_hidden(sK2,sK0(sK1,sK2)) = iProver_top ),
% 2.05/0.97      inference(instantiation,[status(thm)],[c_2040]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_2599,plain,
% 2.05/0.97      ( m1_subset_1(sK0(sK1,X0_46),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.05/0.97      | r1_tarski(sK0(sK1,X0_46),u1_struct_0(sK1)) = iProver_top ),
% 2.05/0.97      inference(predicate_to_equality,[status(thm)],[c_2598]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_2601,plain,
% 2.05/0.97      ( m1_subset_1(sK0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.05/0.97      | r1_tarski(sK0(sK1,sK2),u1_struct_0(sK1)) = iProver_top ),
% 2.05/0.97      inference(instantiation,[status(thm)],[c_2599]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_6,plain,
% 2.05/0.97      ( ~ m1_subset_1(X0,X1)
% 2.05/0.97      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
% 2.05/0.97      | v1_xboole_0(X1) ),
% 2.05/0.97      inference(cnf_transformation,[],[f66]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_1981,plain,
% 2.05/0.97      ( ~ m1_subset_1(X0_46,X1_46)
% 2.05/0.97      | m1_subset_1(k6_domain_1(X1_46,X0_46),k1_zfmisc_1(X1_46))
% 2.05/0.97      | v1_xboole_0(X1_46) ),
% 2.05/0.97      inference(subtyping,[status(esa)],[c_6]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_2606,plain,
% 2.05/0.97      ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.97      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 2.05/0.97      | v1_xboole_0(u1_struct_0(sK1)) ),
% 2.05/0.97      inference(instantiation,[status(thm)],[c_1981]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_2607,plain,
% 2.05/0.97      ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 2.05/0.97      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 2.05/0.97      | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
% 2.05/0.97      inference(predicate_to_equality,[status(thm)],[c_2606]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_2780,plain,
% 2.05/0.97      ( r2_hidden(X0_46,sK0(sK1,X1_46)) != iProver_top
% 2.05/0.97      | r1_tarski(sK0(sK1,X1_46),u1_struct_0(sK1)) != iProver_top
% 2.05/0.97      | v1_xboole_0(u1_struct_0(sK1)) != iProver_top ),
% 2.05/0.97      inference(predicate_to_equality,[status(thm)],[c_2779]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_2782,plain,
% 2.05/0.97      ( r2_hidden(sK2,sK0(sK1,sK2)) != iProver_top
% 2.05/0.97      | r1_tarski(sK0(sK1,sK2),u1_struct_0(sK1)) != iProver_top
% 2.05/0.97      | v1_xboole_0(u1_struct_0(sK1)) != iProver_top ),
% 2.05/0.97      inference(instantiation,[status(thm)],[c_2780]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_3111,plain,
% 2.05/0.97      ( r2_hidden(sK2,k1_tops_1(sK1,sK3)) != iProver_top
% 2.05/0.97      | r1_tarski(k6_domain_1(u1_struct_0(sK1),sK2),k1_tops_1(sK1,sK3)) != iProver_top ),
% 2.05/0.97      inference(global_propositional_subsumption,
% 2.05/0.97                [status(thm)],
% 2.05/0.97                [c_2450,c_26,c_924,c_2039,c_2042,c_2601,c_2607,c_2782]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_3572,plain,
% 2.05/0.97      ( r2_hidden(sK2,k1_tops_1(sK1,sK3)) != iProver_top ),
% 2.05/0.97      inference(superposition,[status(thm)],[c_3491,c_3111]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_2,plain,
% 2.05/0.97      ( r2_hidden(X0,X1)
% 2.05/0.97      | ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),X1) ),
% 2.05/0.97      inference(cnf_transformation,[],[f91]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_1984,plain,
% 2.05/0.97      ( r2_hidden(X0_46,X1_46)
% 2.05/0.97      | ~ r1_tarski(k6_enumset1(X0_46,X0_46,X0_46,X0_46,X0_46,X0_46,X0_46,X2_46),X1_46) ),
% 2.05/0.97      inference(subtyping,[status(esa)],[c_2]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_3552,plain,
% 2.05/0.97      ( r2_hidden(X0_46,k1_tops_1(sK1,sK3))
% 2.05/0.97      | ~ r1_tarski(k6_enumset1(X0_46,X0_46,X0_46,X0_46,X0_46,X0_46,X0_46,X1_46),k1_tops_1(sK1,sK3)) ),
% 2.05/0.97      inference(instantiation,[status(thm)],[c_1984]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_3557,plain,
% 2.05/0.97      ( r2_hidden(X0_46,k1_tops_1(sK1,sK3)) = iProver_top
% 2.05/0.97      | r1_tarski(k6_enumset1(X0_46,X0_46,X0_46,X0_46,X0_46,X0_46,X0_46,X1_46),k1_tops_1(sK1,sK3)) != iProver_top ),
% 2.05/0.97      inference(predicate_to_equality,[status(thm)],[c_3552]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_3559,plain,
% 2.05/0.97      ( r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top
% 2.05/0.97      | r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k1_tops_1(sK1,sK3)) != iProver_top ),
% 2.05/0.97      inference(instantiation,[status(thm)],[c_3557]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_1990,plain,
% 2.05/0.97      ( ~ r1_tarski(X0_46,X1_46)
% 2.05/0.97      | r1_tarski(X2_46,X3_46)
% 2.05/0.97      | X2_46 != X0_46
% 2.05/0.97      | X3_46 != X1_46 ),
% 2.05/0.97      theory(equality) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_2987,plain,
% 2.05/0.97      ( r1_tarski(X0_46,X1_46)
% 2.05/0.97      | ~ r1_tarski(k6_domain_1(u1_struct_0(sK1),sK2),k1_tops_1(sK1,sK3))
% 2.05/0.97      | X1_46 != k1_tops_1(sK1,sK3)
% 2.05/0.97      | X0_46 != k6_domain_1(u1_struct_0(sK1),sK2) ),
% 2.05/0.97      inference(instantiation,[status(thm)],[c_1990]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_3146,plain,
% 2.05/0.97      ( r1_tarski(X0_46,k1_tops_1(sK1,sK3))
% 2.05/0.97      | ~ r1_tarski(k6_domain_1(u1_struct_0(sK1),sK2),k1_tops_1(sK1,sK3))
% 2.05/0.97      | X0_46 != k6_domain_1(u1_struct_0(sK1),sK2)
% 2.05/0.97      | k1_tops_1(sK1,sK3) != k1_tops_1(sK1,sK3) ),
% 2.05/0.97      inference(instantiation,[status(thm)],[c_2987]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_3551,plain,
% 2.05/0.97      ( r1_tarski(k6_enumset1(X0_46,X0_46,X0_46,X0_46,X0_46,X0_46,X0_46,X1_46),k1_tops_1(sK1,sK3))
% 2.05/0.97      | ~ r1_tarski(k6_domain_1(u1_struct_0(sK1),sK2),k1_tops_1(sK1,sK3))
% 2.05/0.97      | k6_enumset1(X0_46,X0_46,X0_46,X0_46,X0_46,X0_46,X0_46,X1_46) != k6_domain_1(u1_struct_0(sK1),sK2)
% 2.05/0.97      | k1_tops_1(sK1,sK3) != k1_tops_1(sK1,sK3) ),
% 2.05/0.97      inference(instantiation,[status(thm)],[c_3146]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_3553,plain,
% 2.05/0.97      ( k6_enumset1(X0_46,X0_46,X0_46,X0_46,X0_46,X0_46,X0_46,X1_46) != k6_domain_1(u1_struct_0(sK1),sK2)
% 2.05/0.97      | k1_tops_1(sK1,sK3) != k1_tops_1(sK1,sK3)
% 2.05/0.97      | r1_tarski(k6_enumset1(X0_46,X0_46,X0_46,X0_46,X0_46,X0_46,X0_46,X1_46),k1_tops_1(sK1,sK3)) = iProver_top
% 2.05/0.97      | r1_tarski(k6_domain_1(u1_struct_0(sK1),sK2),k1_tops_1(sK1,sK3)) != iProver_top ),
% 2.05/0.97      inference(predicate_to_equality,[status(thm)],[c_3551]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_3555,plain,
% 2.05/0.97      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k6_domain_1(u1_struct_0(sK1),sK2)
% 2.05/0.97      | k1_tops_1(sK1,sK3) != k1_tops_1(sK1,sK3)
% 2.05/0.97      | r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k1_tops_1(sK1,sK3)) = iProver_top
% 2.05/0.97      | r1_tarski(k6_domain_1(u1_struct_0(sK1),sK2),k1_tops_1(sK1,sK3)) != iProver_top ),
% 2.05/0.97      inference(instantiation,[status(thm)],[c_3553]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_17,negated_conjecture,
% 2.05/0.97      ( m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2))
% 2.05/0.97      | m1_connsp_2(sK3,sK1,sK2) ),
% 2.05/0.97      inference(cnf_transformation,[],[f81]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_194,plain,
% 2.05/0.97      ( m1_connsp_2(sK3,sK1,sK2)
% 2.05/0.97      | m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2)) ),
% 2.05/0.97      inference(prop_impl,[status(thm)],[c_17]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_195,plain,
% 2.05/0.97      ( m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2))
% 2.05/0.97      | m1_connsp_2(sK3,sK1,sK2) ),
% 2.05/0.97      inference(renaming,[status(thm)],[c_194]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_11,plain,
% 2.05/0.97      ( ~ m2_connsp_2(X0,X1,X2)
% 2.05/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/0.97      | r1_tarski(X2,k1_tops_1(X1,X0))
% 2.05/0.97      | ~ v2_pre_topc(X1)
% 2.05/0.97      | ~ l1_pre_topc(X1) ),
% 2.05/0.97      inference(cnf_transformation,[],[f70]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_13,plain,
% 2.05/0.97      ( ~ m2_connsp_2(X0,X1,X2)
% 2.05/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/0.97      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/0.97      | ~ v2_pre_topc(X1)
% 2.05/0.97      | ~ l1_pre_topc(X1) ),
% 2.05/0.97      inference(cnf_transformation,[],[f73]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_138,plain,
% 2.05/0.97      ( ~ m2_connsp_2(X0,X1,X2)
% 2.05/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/0.97      | r1_tarski(X2,k1_tops_1(X1,X0))
% 2.05/0.97      | ~ v2_pre_topc(X1)
% 2.05/0.97      | ~ l1_pre_topc(X1) ),
% 2.05/0.97      inference(global_propositional_subsumption,
% 2.05/0.97                [status(thm)],
% 2.05/0.97                [c_11,c_13]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_501,plain,
% 2.05/0.97      ( ~ m2_connsp_2(X0,X1,X2)
% 2.05/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/0.97      | r1_tarski(X2,k1_tops_1(X1,X0))
% 2.05/0.97      | ~ v2_pre_topc(X1)
% 2.05/0.97      | sK1 != X1 ),
% 2.05/0.97      inference(resolution_lifted,[status(thm)],[c_138,c_20]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_502,plain,
% 2.05/0.97      ( ~ m2_connsp_2(X0,sK1,X1)
% 2.05/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.97      | r1_tarski(X1,k1_tops_1(sK1,X0))
% 2.05/0.97      | ~ v2_pre_topc(sK1) ),
% 2.05/0.97      inference(unflattening,[status(thm)],[c_501]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_506,plain,
% 2.05/0.97      ( r1_tarski(X1,k1_tops_1(sK1,X0))
% 2.05/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.97      | ~ m2_connsp_2(X0,sK1,X1) ),
% 2.05/0.97      inference(global_propositional_subsumption,
% 2.05/0.97                [status(thm)],
% 2.05/0.97                [c_502,c_21]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_507,plain,
% 2.05/0.97      ( ~ m2_connsp_2(X0,sK1,X1)
% 2.05/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.97      | r1_tarski(X1,k1_tops_1(sK1,X0)) ),
% 2.05/0.97      inference(renaming,[status(thm)],[c_506]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_581,plain,
% 2.05/0.97      ( m1_connsp_2(sK3,sK1,sK2)
% 2.05/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.97      | r1_tarski(X0,k1_tops_1(sK1,X1))
% 2.05/0.97      | k6_domain_1(u1_struct_0(sK1),sK2) != X0
% 2.05/0.97      | sK1 != sK1
% 2.05/0.97      | sK3 != X1 ),
% 2.05/0.97      inference(resolution_lifted,[status(thm)],[c_195,c_507]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_582,plain,
% 2.05/0.97      ( m1_connsp_2(sK3,sK1,sK2)
% 2.05/0.97      | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.97      | r1_tarski(k6_domain_1(u1_struct_0(sK1),sK2),k1_tops_1(sK1,sK3)) ),
% 2.05/0.97      inference(unflattening,[status(thm)],[c_581]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_9,plain,
% 2.05/0.97      ( ~ m1_connsp_2(X0,X1,X2)
% 2.05/0.97      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.05/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/0.97      | r2_hidden(X2,k1_tops_1(X1,X0))
% 2.05/0.97      | v2_struct_0(X1)
% 2.05/0.97      | ~ v2_pre_topc(X1)
% 2.05/0.97      | ~ l1_pre_topc(X1) ),
% 2.05/0.97      inference(cnf_transformation,[],[f68]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_144,plain,
% 2.05/0.97      ( ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.05/0.97      | ~ m1_connsp_2(X0,X1,X2)
% 2.05/0.97      | r2_hidden(X2,k1_tops_1(X1,X0))
% 2.05/0.97      | v2_struct_0(X1)
% 2.05/0.97      | ~ v2_pre_topc(X1)
% 2.05/0.97      | ~ l1_pre_topc(X1) ),
% 2.05/0.97      inference(global_propositional_subsumption,
% 2.05/0.97                [status(thm)],
% 2.05/0.97                [c_9,c_12]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_145,plain,
% 2.05/0.97      ( ~ m1_connsp_2(X0,X1,X2)
% 2.05/0.97      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.05/0.97      | r2_hidden(X2,k1_tops_1(X1,X0))
% 2.05/0.97      | v2_struct_0(X1)
% 2.05/0.97      | ~ v2_pre_topc(X1)
% 2.05/0.97      | ~ l1_pre_topc(X1) ),
% 2.05/0.97      inference(renaming,[status(thm)],[c_144]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_394,plain,
% 2.05/0.97      ( ~ m1_connsp_2(X0,X1,X2)
% 2.05/0.97      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.05/0.97      | r2_hidden(X2,k1_tops_1(X1,X0))
% 2.05/0.97      | ~ v2_pre_topc(X1)
% 2.05/0.97      | ~ l1_pre_topc(X1)
% 2.05/0.97      | sK1 != X1 ),
% 2.05/0.97      inference(resolution_lifted,[status(thm)],[c_145,c_22]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_395,plain,
% 2.05/0.97      ( ~ m1_connsp_2(X0,sK1,X1)
% 2.05/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.05/0.97      | r2_hidden(X1,k1_tops_1(sK1,X0))
% 2.05/0.97      | ~ v2_pre_topc(sK1)
% 2.05/0.97      | ~ l1_pre_topc(sK1) ),
% 2.05/0.97      inference(unflattening,[status(thm)],[c_394]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_399,plain,
% 2.05/0.97      ( ~ m1_connsp_2(X0,sK1,X1)
% 2.05/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.05/0.97      | r2_hidden(X1,k1_tops_1(sK1,X0)) ),
% 2.05/0.97      inference(global_propositional_subsumption,
% 2.05/0.97                [status(thm)],
% 2.05/0.97                [c_395,c_21,c_20]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_902,plain,
% 2.05/0.97      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.05/0.97      | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.97      | r2_hidden(X0,k1_tops_1(sK1,X1))
% 2.05/0.97      | r1_tarski(k6_domain_1(u1_struct_0(sK1),sK2),k1_tops_1(sK1,sK3))
% 2.05/0.97      | sK2 != X0
% 2.05/0.97      | sK1 != sK1
% 2.05/0.97      | sK3 != X1 ),
% 2.05/0.97      inference(resolution_lifted,[status(thm)],[c_582,c_399]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_903,plain,
% 2.05/0.97      ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.97      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 2.05/0.97      | r2_hidden(sK2,k1_tops_1(sK1,sK3))
% 2.05/0.97      | r1_tarski(k6_domain_1(u1_struct_0(sK1),sK2),k1_tops_1(sK1,sK3)) ),
% 2.05/0.97      inference(unflattening,[status(thm)],[c_902]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_905,plain,
% 2.05/0.97      ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.97      | r2_hidden(sK2,k1_tops_1(sK1,sK3))
% 2.05/0.97      | r1_tarski(k6_domain_1(u1_struct_0(sK1),sK2),k1_tops_1(sK1,sK3)) ),
% 2.05/0.97      inference(global_propositional_subsumption,
% 2.05/0.97                [status(thm)],
% 2.05/0.97                [c_903,c_19]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_1973,plain,
% 2.05/0.97      ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.97      | r2_hidden(sK2,k1_tops_1(sK1,sK3))
% 2.05/0.97      | r1_tarski(k6_domain_1(u1_struct_0(sK1),sK2),k1_tops_1(sK1,sK3)) ),
% 2.05/0.97      inference(subtyping,[status(esa)],[c_905]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_2449,plain,
% 2.05/0.97      ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.05/0.97      | r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top
% 2.05/0.97      | r1_tarski(k6_domain_1(u1_struct_0(sK1),sK2),k1_tops_1(sK1,sK3)) = iProver_top ),
% 2.05/0.97      inference(predicate_to_equality,[status(thm)],[c_1973]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_904,plain,
% 2.05/0.97      ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.05/0.97      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 2.05/0.97      | r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top
% 2.05/0.97      | r1_tarski(k6_domain_1(u1_struct_0(sK1),sK2),k1_tops_1(sK1,sK3)) = iProver_top ),
% 2.05/0.97      inference(predicate_to_equality,[status(thm)],[c_903]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_3173,plain,
% 2.05/0.97      ( r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top
% 2.05/0.97      | r1_tarski(k6_domain_1(u1_struct_0(sK1),sK2),k1_tops_1(sK1,sK3)) = iProver_top ),
% 2.05/0.97      inference(global_propositional_subsumption,
% 2.05/0.97                [status(thm)],
% 2.05/0.97                [c_2449,c_26,c_904,c_2039,c_2042,c_2601,c_2607,c_2782]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_1988,plain,( X0_46 = X0_46 ),theory(equality) ).
% 2.05/0.97  
% 2.05/0.97  cnf(c_3147,plain,
% 2.05/0.97      ( k1_tops_1(sK1,sK3) = k1_tops_1(sK1,sK3) ),
% 2.05/0.97      inference(instantiation,[status(thm)],[c_1988]) ).
% 2.05/0.97  
% 2.05/0.97  cnf(contradiction,plain,
% 2.05/0.97      ( $false ),
% 2.05/0.97      inference(minisat,
% 2.05/0.97                [status(thm)],
% 2.05/0.97                [c_3572,c_3559,c_3555,c_3173,c_3147,c_2781,c_2632,c_2600,
% 2.05/0.97                 c_2041,c_2038,c_19]) ).
% 2.05/0.97  
% 2.05/0.97  
% 2.05/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 2.05/0.97  
% 2.05/0.97  ------                               Statistics
% 2.05/0.97  
% 2.05/0.97  ------ General
% 2.05/0.97  
% 2.05/0.97  abstr_ref_over_cycles:                  0
% 2.05/0.97  abstr_ref_under_cycles:                 0
% 2.05/0.97  gc_basic_clause_elim:                   0
% 2.05/0.97  forced_gc_time:                         0
% 2.05/0.97  parsing_time:                           0.01
% 2.05/0.97  unif_index_cands_time:                  0.
% 2.05/0.97  unif_index_add_time:                    0.
% 2.05/0.97  orderings_time:                         0.
% 2.05/0.97  out_proof_time:                         0.013
% 2.05/0.97  total_time:                             0.123
% 2.05/0.97  num_of_symbols:                         51
% 2.05/0.97  num_of_terms:                           1968
% 2.05/0.97  
% 2.05/0.97  ------ Preprocessing
% 2.05/0.97  
% 2.05/0.97  num_of_splits:                          0
% 2.05/0.97  num_of_split_atoms:                     0
% 2.05/0.97  num_of_reused_defs:                     0
% 2.05/0.97  num_eq_ax_congr_red:                    35
% 2.05/0.97  num_of_sem_filtered_clauses:            1
% 2.05/0.97  num_of_subtypes:                        2
% 2.05/0.97  monotx_restored_types:                  0
% 2.05/0.97  sat_num_of_epr_types:                   0
% 2.05/0.97  sat_num_of_non_cyclic_types:            0
% 2.05/0.97  sat_guarded_non_collapsed_types:        0
% 2.05/0.97  num_pure_diseq_elim:                    0
% 2.05/0.97  simp_replaced_by:                       0
% 2.05/0.97  res_preprocessed:                       96
% 2.05/0.97  prep_upred:                             0
% 2.05/0.97  prep_unflattend:                        111
% 2.05/0.97  smt_new_axioms:                         0
% 2.05/0.97  pred_elim_cands:                        4
% 2.05/0.97  pred_elim:                              5
% 2.05/0.97  pred_elim_cl:                           5
% 2.05/0.97  pred_elim_cycles:                       10
% 2.05/0.97  merged_defs:                            10
% 2.05/0.97  merged_defs_ncl:                        0
% 2.05/0.97  bin_hyper_res:                          11
% 2.05/0.97  prep_cycles:                            4
% 2.05/0.97  pred_elim_time:                         0.026
% 2.05/0.97  splitting_time:                         0.
% 2.05/0.97  sem_filter_time:                        0.
% 2.05/0.97  monotx_time:                            0.
% 2.05/0.97  subtype_inf_time:                       0.
% 2.05/0.97  
% 2.05/0.97  ------ Problem properties
% 2.05/0.97  
% 2.05/0.97  clauses:                                18
% 2.05/0.97  conjectures:                            2
% 2.05/0.97  epr:                                    1
% 2.05/0.97  horn:                                   14
% 2.05/0.97  ground:                                 6
% 2.05/0.97  unary:                                  2
% 2.05/0.97  binary:                                 7
% 2.05/0.97  lits:                                   44
% 2.05/0.97  lits_eq:                                2
% 2.05/0.97  fd_pure:                                0
% 2.05/0.97  fd_pseudo:                              0
% 2.05/0.97  fd_cond:                                0
% 2.05/0.97  fd_pseudo_cond:                         0
% 2.05/0.97  ac_symbols:                             0
% 2.05/0.97  
% 2.05/0.97  ------ Propositional Solver
% 2.05/0.97  
% 2.05/0.97  prop_solver_calls:                      26
% 2.05/0.97  prop_fast_solver_calls:                 923
% 2.05/0.97  smt_solver_calls:                       0
% 2.05/0.97  smt_fast_solver_calls:                  0
% 2.05/0.97  prop_num_of_clauses:                    816
% 2.05/0.97  prop_preprocess_simplified:             3558
% 2.05/0.97  prop_fo_subsumed:                       26
% 2.05/0.97  prop_solver_time:                       0.
% 2.05/0.97  smt_solver_time:                        0.
% 2.05/0.97  smt_fast_solver_time:                   0.
% 2.05/0.97  prop_fast_solver_time:                  0.
% 2.05/0.97  prop_unsat_core_time:                   0.
% 2.05/0.97  
% 2.05/0.97  ------ QBF
% 2.05/0.97  
% 2.05/0.97  qbf_q_res:                              0
% 2.05/0.97  qbf_num_tautologies:                    0
% 2.05/0.97  qbf_prep_cycles:                        0
% 2.05/0.97  
% 2.05/0.97  ------ BMC1
% 2.05/0.97  
% 2.05/0.97  bmc1_current_bound:                     -1
% 2.05/0.97  bmc1_last_solved_bound:                 -1
% 2.05/0.97  bmc1_unsat_core_size:                   -1
% 2.05/0.97  bmc1_unsat_core_parents_size:           -1
% 2.05/0.97  bmc1_merge_next_fun:                    0
% 2.05/0.97  bmc1_unsat_core_clauses_time:           0.
% 2.05/0.97  
% 2.05/0.97  ------ Instantiation
% 2.05/0.97  
% 2.05/0.97  inst_num_of_clauses:                    175
% 2.05/0.97  inst_num_in_passive:                    33
% 2.05/0.97  inst_num_in_active:                     129
% 2.05/0.97  inst_num_in_unprocessed:                13
% 2.05/0.97  inst_num_of_loops:                      140
% 2.05/0.97  inst_num_of_learning_restarts:          0
% 2.05/0.97  inst_num_moves_active_passive:          8
% 2.05/0.97  inst_lit_activity:                      0
% 2.05/0.97  inst_lit_activity_moves:                0
% 2.05/0.97  inst_num_tautologies:                   0
% 2.05/0.97  inst_num_prop_implied:                  0
% 2.05/0.97  inst_num_existing_simplified:           0
% 2.05/0.97  inst_num_eq_res_simplified:             0
% 2.05/0.97  inst_num_child_elim:                    0
% 2.05/0.97  inst_num_of_dismatching_blockings:      5
% 2.05/0.97  inst_num_of_non_proper_insts:           159
% 2.05/0.97  inst_num_of_duplicates:                 0
% 2.05/0.97  inst_inst_num_from_inst_to_res:         0
% 2.05/0.97  inst_dismatching_checking_time:         0.
% 2.05/0.97  
% 2.05/0.97  ------ Resolution
% 2.05/0.97  
% 2.05/0.97  res_num_of_clauses:                     0
% 2.05/0.97  res_num_in_passive:                     0
% 2.05/0.97  res_num_in_active:                      0
% 2.05/0.97  res_num_of_loops:                       100
% 2.05/0.97  res_forward_subset_subsumed:            19
% 2.05/0.97  res_backward_subset_subsumed:           0
% 2.05/0.97  res_forward_subsumed:                   0
% 2.05/0.97  res_backward_subsumed:                  0
% 2.05/0.97  res_forward_subsumption_resolution:     0
% 2.05/0.97  res_backward_subsumption_resolution:    0
% 2.05/0.97  res_clause_to_clause_subsumption:       208
% 2.05/0.97  res_orphan_elimination:                 0
% 2.05/0.97  res_tautology_del:                      57
% 2.05/0.97  res_num_eq_res_simplified:              0
% 2.05/0.97  res_num_sel_changes:                    0
% 2.05/0.97  res_moves_from_active_to_pass:          0
% 2.05/0.97  
% 2.05/0.97  ------ Superposition
% 2.05/0.97  
% 2.05/0.97  sup_time_total:                         0.
% 2.05/0.97  sup_time_generating:                    0.
% 2.05/0.97  sup_time_sim_full:                      0.
% 2.05/0.97  sup_time_sim_immed:                     0.
% 2.05/0.97  
% 2.05/0.97  sup_num_of_clauses:                     34
% 2.05/0.97  sup_num_in_active:                      25
% 2.05/0.97  sup_num_in_passive:                     9
% 2.05/0.97  sup_num_of_loops:                       26
% 2.05/0.97  sup_fw_superposition:                   13
% 2.05/0.97  sup_bw_superposition:                   11
% 2.05/0.97  sup_immediate_simplified:               1
% 2.05/0.97  sup_given_eliminated:                   0
% 2.05/0.97  comparisons_done:                       0
% 2.05/0.97  comparisons_avoided:                    0
% 2.05/0.97  
% 2.05/0.97  ------ Simplifications
% 2.05/0.97  
% 2.05/0.97  
% 2.05/0.97  sim_fw_subset_subsumed:                 1
% 2.05/0.97  sim_bw_subset_subsumed:                 3
% 2.05/0.97  sim_fw_subsumed:                        0
% 2.05/0.97  sim_bw_subsumed:                        0
% 2.05/0.97  sim_fw_subsumption_res:                 0
% 2.05/0.97  sim_bw_subsumption_res:                 0
% 2.05/0.97  sim_tautology_del:                      4
% 2.05/0.97  sim_eq_tautology_del:                   0
% 2.05/0.97  sim_eq_res_simp:                        0
% 2.05/0.97  sim_fw_demodulated:                     0
% 2.05/0.97  sim_bw_demodulated:                     0
% 2.05/0.97  sim_light_normalised:                   0
% 2.05/0.97  sim_joinable_taut:                      0
% 2.05/0.97  sim_joinable_simp:                      0
% 2.05/0.97  sim_ac_normalised:                      0
% 2.05/0.97  sim_smt_subsumption:                    0
% 2.05/0.97  
%------------------------------------------------------------------------------
