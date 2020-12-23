%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:18:27 EST 2020

% Result     : Theorem 1.79s
% Output     : CNFRefutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :  162 ( 904 expanded)
%              Number of clauses        :   88 ( 212 expanded)
%              Number of leaves         :   18 ( 236 expanded)
%              Depth                    :   24
%              Number of atoms          :  640 (5949 expanded)
%              Number of equality atoms :   97 ( 139 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f3,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f80,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f57,f56])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f13,conjecture,(
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

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ m1_connsp_2(X2,X0,X1)
            | ~ m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) )
          & ( m1_connsp_2(X2,X0,X1)
            | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ~ m1_connsp_2(sK4,X0,X1)
          | ~ m2_connsp_2(sK4,X0,k6_domain_1(u1_struct_0(X0),X1)) )
        & ( m1_connsp_2(sK4,X0,X1)
          | m2_connsp_2(sK4,X0,k6_domain_1(u1_struct_0(X0),X1)) )
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
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
            ( ( ~ m1_connsp_2(X2,X0,sK3)
              | ~ m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),sK3)) )
            & ( m1_connsp_2(X2,X0,sK3)
              | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),sK3)) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
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
              ( ( ~ m1_connsp_2(X2,sK2,X1)
                | ~ m2_connsp_2(X2,sK2,k6_domain_1(u1_struct_0(sK2),X1)) )
              & ( m1_connsp_2(X2,sK2,X1)
                | m2_connsp_2(X2,sK2,k6_domain_1(u1_struct_0(sK2),X1)) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
          & m1_subset_1(X1,u1_struct_0(sK2)) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ( ~ m1_connsp_2(sK4,sK2,sK3)
      | ~ m2_connsp_2(sK4,sK2,k6_domain_1(u1_struct_0(sK2),sK3)) )
    & ( m1_connsp_2(sK4,sK2,sK3)
      | m2_connsp_2(sK4,sK2,k6_domain_1(u1_struct_0(sK2),sK3)) )
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f44,f47,f46,f45])).

fof(f75,plain,
    ( ~ m1_connsp_2(sK4,sK2,sK3)
    | ~ m2_connsp_2(sK4,sK2,k6_domain_1(u1_struct_0(sK2),sK3)) ),
    inference(cnf_transformation,[],[f48])).

fof(f11,axiom,(
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

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( m2_connsp_2(X2,X0,X1)
      | ~ r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f71,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f70,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f73,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f48])).

fof(f10,axiom,(
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

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f69,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f72,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f48])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f60,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k2_tarski(X1,X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f63,f56])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f32])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f74,plain,
    ( m1_connsp_2(sK4,sK2,sK3)
    | m2_connsp_2(sK4,sK2,k6_domain_1(u1_struct_0(sK2),sK3)) ),
    inference(cnf_transformation,[],[f48])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m2_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f36])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK1(X0,X1) != X0
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( sK1(X0,X1) = X0
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK1(X0,X1) != X0
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( sK1(X0,X1) = X0
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f37,f38])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f78,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f53,f56])).

fof(f82,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_tarski(X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f78])).

fof(f83,plain,(
    ! [X3] : r2_hidden(X3,k2_tarski(X3,X3)) ),
    inference(equality_resolution,[],[f82])).

cnf(c_7,plain,
    ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1567,plain,
    ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1)) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1565,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2413,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(k2_tarski(X0,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1567,c_1565])).

cnf(c_19,negated_conjecture,
    ( ~ m2_connsp_2(sK4,sK2,k6_domain_1(u1_struct_0(sK2),sK3))
    | ~ m1_connsp_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_211,plain,
    ( ~ m1_connsp_2(sK4,sK2,sK3)
    | ~ m2_connsp_2(sK4,sK2,k6_domain_1(u1_struct_0(sK2),sK3)) ),
    inference(prop_impl,[status(thm)],[c_19])).

cnf(c_212,plain,
    ( ~ m2_connsp_2(sK4,sK2,k6_domain_1(u1_struct_0(sK2),sK3))
    | ~ m1_connsp_2(sK4,sK2,sK3) ),
    inference(renaming,[status(thm)],[c_211])).

cnf(c_16,plain,
    ( m2_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_23,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_571,plain,
    ( m2_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_23])).

cnf(c_572,plain,
    ( m2_connsp_2(X0,sK2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X1,k1_tops_1(sK2,X0))
    | ~ v2_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_571])).

cnf(c_24,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_576,plain,
    ( ~ r1_tarski(X1,k1_tops_1(sK2,X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m2_connsp_2(X0,sK2,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_572,c_24])).

cnf(c_577,plain,
    ( m2_connsp_2(X0,sK2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X1,k1_tops_1(sK2,X0)) ),
    inference(renaming,[status(thm)],[c_576])).

cnf(c_624,plain,
    ( ~ m1_connsp_2(sK4,sK2,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X1,k1_tops_1(sK2,X0))
    | k6_domain_1(u1_struct_0(sK2),sK3) != X1
    | sK2 != sK2
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_212,c_577])).

cnf(c_625,plain,
    ( ~ m1_connsp_2(sK4,sK2,sK3)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(k6_domain_1(u1_struct_0(sK2),sK3),k1_tops_1(sK2,sK4)) ),
    inference(unflattening,[status(thm)],[c_624])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_627,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_connsp_2(sK4,sK2,sK3)
    | ~ r1_tarski(k6_domain_1(u1_struct_0(sK2),sK3),k1_tops_1(sK2,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_625,c_21])).

cnf(c_628,plain,
    ( ~ m1_connsp_2(sK4,sK2,sK3)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(k6_domain_1(u1_struct_0(sK2),sK3),k1_tops_1(sK2,sK4)) ),
    inference(renaming,[status(thm)],[c_627])).

cnf(c_14,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_478,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_25])).

cnf(c_479,plain,
    ( m1_connsp_2(X0,sK2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1,k1_tops_1(sK2,X0))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_478])).

cnf(c_483,plain,
    ( m1_connsp_2(X0,sK2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1,k1_tops_1(sK2,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_479,c_24,c_23])).

cnf(c_671,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X0,k1_tops_1(sK2,X1))
    | ~ r1_tarski(k6_domain_1(u1_struct_0(sK2),sK3),k1_tops_1(sK2,sK4))
    | sK3 != X0
    | sK2 != sK2
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_628,c_483])).

cnf(c_672,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK3,k1_tops_1(sK2,sK4))
    | ~ r1_tarski(k6_domain_1(u1_struct_0(sK2),sK3),k1_tops_1(sK2,sK4)) ),
    inference(unflattening,[status(thm)],[c_671])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_674,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK3,k1_tops_1(sK2,sK4))
    | ~ r1_tarski(k6_domain_1(u1_struct_0(sK2),sK3),k1_tops_1(sK2,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_672,c_22,c_21])).

cnf(c_1559,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(sK3,k1_tops_1(sK2,sK4)) != iProver_top
    | r1_tarski(k6_domain_1(u1_struct_0(sK2),sK3),k1_tops_1(sK2,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_674])).

cnf(c_29,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_676,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(sK3,k1_tops_1(sK2,sK4)) != iProver_top
    | r1_tarski(k6_domain_1(u1_struct_0(sK2),sK3),k1_tops_1(sK2,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_674])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_10,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_11,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_363,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_10,c_11])).

cnf(c_425,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_pre_topc(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_363,c_25])).

cnf(c_426,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_425])).

cnf(c_55,plain,
    ( v2_struct_0(sK2)
    | ~ v1_xboole_0(u1_struct_0(sK2))
    | ~ l1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_58,plain,
    ( ~ l1_pre_topc(sK2)
    | l1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_428,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_426,c_25,c_23,c_55,c_58])).

cnf(c_529,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | u1_struct_0(sK2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_428])).

cnf(c_530,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | m1_subset_1(k6_domain_1(u1_struct_0(sK2),X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unflattening,[status(thm)],[c_529])).

cnf(c_1678,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_530])).

cnf(c_1679,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1678])).

cnf(c_1889,plain,
    ( r2_hidden(sK3,k1_tops_1(sK2,sK4)) != iProver_top
    | r1_tarski(k6_domain_1(u1_struct_0(sK2),sK3),k1_tops_1(sK2,sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1559,c_29,c_676,c_1679])).

cnf(c_1563,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_517,plain,
    ( ~ m1_subset_1(X0,X1)
    | k6_domain_1(X1,X0) = k2_tarski(X0,X0)
    | u1_struct_0(sK2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_428])).

cnf(c_518,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | k6_domain_1(u1_struct_0(sK2),X0) = k2_tarski(X0,X0) ),
    inference(unflattening,[status(thm)],[c_517])).

cnf(c_1562,plain,
    ( k6_domain_1(u1_struct_0(sK2),X0) = k2_tarski(X0,X0)
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_518])).

cnf(c_1715,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK3) = k2_tarski(sK3,sK3) ),
    inference(superposition,[status(thm)],[c_1563,c_1562])).

cnf(c_1893,plain,
    ( r2_hidden(sK3,k1_tops_1(sK2,sK4)) != iProver_top
    | r1_tarski(k2_tarski(sK3,sK3),k1_tops_1(sK2,sK4)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1889,c_1715])).

cnf(c_2773,plain,
    ( r2_hidden(sK3,k1_tops_1(sK2,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2413,c_1893])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1707,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k2_tarski(X0,X0))
    | ~ r1_tarski(k2_tarski(X0,X0),X1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1962,plain,
    ( r2_hidden(sK3,k1_tops_1(sK2,sK4))
    | ~ r2_hidden(sK3,k2_tarski(sK3,sK3))
    | ~ r1_tarski(k2_tarski(sK3,sK3),k1_tops_1(sK2,sK4)) ),
    inference(instantiation,[status(thm)],[c_1707])).

cnf(c_1963,plain,
    ( r2_hidden(sK3,k1_tops_1(sK2,sK4)) = iProver_top
    | r2_hidden(sK3,k2_tarski(sK3,sK3)) != iProver_top
    | r1_tarski(k2_tarski(sK3,sK3),k1_tops_1(sK2,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1962])).

cnf(c_20,negated_conjecture,
    ( m2_connsp_2(sK4,sK2,k6_domain_1(u1_struct_0(sK2),sK3))
    | m1_connsp_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_213,plain,
    ( m1_connsp_2(sK4,sK2,sK3)
    | m2_connsp_2(sK4,sK2,k6_domain_1(u1_struct_0(sK2),sK3)) ),
    inference(prop_impl,[status(thm)],[c_20])).

cnf(c_214,plain,
    ( m2_connsp_2(sK4,sK2,k6_domain_1(u1_struct_0(sK2),sK3))
    | m1_connsp_2(sK4,sK2,sK3) ),
    inference(renaming,[status(thm)],[c_213])).

cnf(c_17,plain,
    ( ~ m2_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_547,plain,
    ( ~ m2_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_23])).

cnf(c_548,plain,
    ( ~ m2_connsp_2(X0,sK2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(X1,k1_tops_1(sK2,X0))
    | ~ v2_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_547])).

cnf(c_552,plain,
    ( r1_tarski(X1,k1_tops_1(sK2,X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m2_connsp_2(X0,sK2,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_548,c_24])).

cnf(c_553,plain,
    ( ~ m2_connsp_2(X0,sK2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(X1,k1_tops_1(sK2,X0)) ),
    inference(renaming,[status(thm)],[c_552])).

cnf(c_607,plain,
    ( m1_connsp_2(sK4,sK2,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(X1,k1_tops_1(sK2,X0))
    | k6_domain_1(u1_struct_0(sK2),sK3) != X1
    | sK2 != sK2
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_214,c_553])).

cnf(c_608,plain,
    ( m1_connsp_2(sK4,sK2,sK3)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(k6_domain_1(u1_struct_0(sK2),sK3),k1_tops_1(sK2,sK4)) ),
    inference(unflattening,[status(thm)],[c_607])).

cnf(c_610,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_connsp_2(sK4,sK2,sK3)
    | r1_tarski(k6_domain_1(u1_struct_0(sK2),sK3),k1_tops_1(sK2,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_608,c_21])).

cnf(c_611,plain,
    ( m1_connsp_2(sK4,sK2,sK3)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(k6_domain_1(u1_struct_0(sK2),sK3),k1_tops_1(sK2,sK4)) ),
    inference(renaming,[status(thm)],[c_610])).

cnf(c_15,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_18,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_151,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X0,X1,X2)
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15,c_18])).

cnf(c_152,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_151])).

cnf(c_436,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_152,c_25])).

cnf(c_437,plain,
    ( ~ m1_connsp_2(X0,sK2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r2_hidden(X1,k1_tops_1(sK2,X0))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_436])).

cnf(c_441,plain,
    ( ~ m1_connsp_2(X0,sK2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r2_hidden(X1,k1_tops_1(sK2,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_437,c_24,c_23])).

cnf(c_654,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(X0,k1_tops_1(sK2,X1))
    | r1_tarski(k6_domain_1(u1_struct_0(sK2),sK3),k1_tops_1(sK2,sK4))
    | sK3 != X0
    | sK2 != sK2
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_611,c_441])).

cnf(c_655,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | r2_hidden(sK3,k1_tops_1(sK2,sK4))
    | r1_tarski(k6_domain_1(u1_struct_0(sK2),sK3),k1_tops_1(sK2,sK4)) ),
    inference(unflattening,[status(thm)],[c_654])).

cnf(c_657,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(sK3,k1_tops_1(sK2,sK4))
    | r1_tarski(k6_domain_1(u1_struct_0(sK2),sK3),k1_tops_1(sK2,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_655,c_22])).

cnf(c_1560,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(sK3,k1_tops_1(sK2,sK4)) = iProver_top
    | r1_tarski(k6_domain_1(u1_struct_0(sK2),sK3),k1_tops_1(sK2,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_657])).

cnf(c_656,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK3,k1_tops_1(sK2,sK4)) = iProver_top
    | r1_tarski(k6_domain_1(u1_struct_0(sK2),sK3),k1_tops_1(sK2,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_655])).

cnf(c_1898,plain,
    ( r2_hidden(sK3,k1_tops_1(sK2,sK4)) = iProver_top
    | r1_tarski(k6_domain_1(u1_struct_0(sK2),sK3),k1_tops_1(sK2,sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1560,c_29,c_656,c_1679])).

cnf(c_1902,plain,
    ( r2_hidden(sK3,k1_tops_1(sK2,sK4)) = iProver_top
    | r1_tarski(k2_tarski(sK3,sK3),k1_tops_1(sK2,sK4)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1898,c_1715])).

cnf(c_5,plain,
    ( r2_hidden(X0,k2_tarski(X0,X0)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1873,plain,
    ( r2_hidden(sK3,k2_tarski(sK3,sK3)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1874,plain,
    ( r2_hidden(sK3,k2_tarski(sK3,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1873])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2773,c_1963,c_1902,c_1874])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:27:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 1.79/0.95  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.79/0.95  
% 1.79/0.95  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.79/0.95  
% 1.79/0.95  ------  iProver source info
% 1.79/0.95  
% 1.79/0.95  git: date: 2020-06-30 10:37:57 +0100
% 1.79/0.95  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.79/0.95  git: non_committed_changes: false
% 1.79/0.95  git: last_make_outside_of_git: false
% 1.79/0.95  
% 1.79/0.95  ------ 
% 1.79/0.95  
% 1.79/0.95  ------ Input Options
% 1.79/0.95  
% 1.79/0.95  --out_options                           all
% 1.79/0.95  --tptp_safe_out                         true
% 1.79/0.95  --problem_path                          ""
% 1.79/0.95  --include_path                          ""
% 1.79/0.95  --clausifier                            res/vclausify_rel
% 1.79/0.95  --clausifier_options                    --mode clausify
% 1.79/0.95  --stdin                                 false
% 1.79/0.95  --stats_out                             all
% 1.79/0.95  
% 1.79/0.95  ------ General Options
% 1.79/0.95  
% 1.79/0.95  --fof                                   false
% 1.79/0.95  --time_out_real                         305.
% 1.79/0.95  --time_out_virtual                      -1.
% 1.79/0.95  --symbol_type_check                     false
% 1.79/0.95  --clausify_out                          false
% 1.79/0.95  --sig_cnt_out                           false
% 1.79/0.95  --trig_cnt_out                          false
% 1.79/0.95  --trig_cnt_out_tolerance                1.
% 1.79/0.95  --trig_cnt_out_sk_spl                   false
% 1.79/0.95  --abstr_cl_out                          false
% 1.79/0.95  
% 1.79/0.95  ------ Global Options
% 1.79/0.95  
% 1.79/0.95  --schedule                              default
% 1.79/0.95  --add_important_lit                     false
% 1.79/0.95  --prop_solver_per_cl                    1000
% 1.79/0.95  --min_unsat_core                        false
% 1.79/0.95  --soft_assumptions                      false
% 1.79/0.95  --soft_lemma_size                       3
% 1.79/0.95  --prop_impl_unit_size                   0
% 1.79/0.95  --prop_impl_unit                        []
% 1.79/0.95  --share_sel_clauses                     true
% 1.79/0.95  --reset_solvers                         false
% 1.79/0.95  --bc_imp_inh                            [conj_cone]
% 1.79/0.95  --conj_cone_tolerance                   3.
% 1.79/0.95  --extra_neg_conj                        none
% 1.79/0.95  --large_theory_mode                     true
% 1.79/0.95  --prolific_symb_bound                   200
% 1.79/0.95  --lt_threshold                          2000
% 1.79/0.95  --clause_weak_htbl                      true
% 1.79/0.95  --gc_record_bc_elim                     false
% 1.79/0.95  
% 1.79/0.95  ------ Preprocessing Options
% 1.79/0.95  
% 1.79/0.95  --preprocessing_flag                    true
% 1.79/0.95  --time_out_prep_mult                    0.1
% 1.79/0.95  --splitting_mode                        input
% 1.79/0.95  --splitting_grd                         true
% 1.79/0.95  --splitting_cvd                         false
% 1.79/0.95  --splitting_cvd_svl                     false
% 1.79/0.95  --splitting_nvd                         32
% 1.79/0.95  --sub_typing                            true
% 1.79/0.95  --prep_gs_sim                           true
% 1.79/0.95  --prep_unflatten                        true
% 1.79/0.95  --prep_res_sim                          true
% 1.79/0.95  --prep_upred                            true
% 1.79/0.95  --prep_sem_filter                       exhaustive
% 1.79/0.95  --prep_sem_filter_out                   false
% 1.79/0.95  --pred_elim                             true
% 1.79/0.95  --res_sim_input                         true
% 1.79/0.95  --eq_ax_congr_red                       true
% 1.79/0.95  --pure_diseq_elim                       true
% 1.79/0.95  --brand_transform                       false
% 1.79/0.95  --non_eq_to_eq                          false
% 1.79/0.95  --prep_def_merge                        true
% 1.79/0.95  --prep_def_merge_prop_impl              false
% 1.79/0.95  --prep_def_merge_mbd                    true
% 1.79/0.95  --prep_def_merge_tr_red                 false
% 1.79/0.95  --prep_def_merge_tr_cl                  false
% 1.79/0.95  --smt_preprocessing                     true
% 1.79/0.95  --smt_ac_axioms                         fast
% 1.79/0.95  --preprocessed_out                      false
% 1.79/0.95  --preprocessed_stats                    false
% 1.79/0.95  
% 1.79/0.95  ------ Abstraction refinement Options
% 1.79/0.95  
% 1.79/0.95  --abstr_ref                             []
% 1.79/0.95  --abstr_ref_prep                        false
% 1.79/0.95  --abstr_ref_until_sat                   false
% 1.79/0.95  --abstr_ref_sig_restrict                funpre
% 1.79/0.95  --abstr_ref_af_restrict_to_split_sk     false
% 1.79/0.95  --abstr_ref_under                       []
% 1.79/0.95  
% 1.79/0.95  ------ SAT Options
% 1.79/0.95  
% 1.79/0.95  --sat_mode                              false
% 1.79/0.95  --sat_fm_restart_options                ""
% 1.79/0.95  --sat_gr_def                            false
% 1.79/0.95  --sat_epr_types                         true
% 1.79/0.95  --sat_non_cyclic_types                  false
% 1.79/0.95  --sat_finite_models                     false
% 1.79/0.95  --sat_fm_lemmas                         false
% 1.79/0.95  --sat_fm_prep                           false
% 1.79/0.95  --sat_fm_uc_incr                        true
% 1.79/0.95  --sat_out_model                         small
% 1.79/0.95  --sat_out_clauses                       false
% 1.79/0.95  
% 1.79/0.95  ------ QBF Options
% 1.79/0.95  
% 1.79/0.95  --qbf_mode                              false
% 1.79/0.95  --qbf_elim_univ                         false
% 1.79/0.95  --qbf_dom_inst                          none
% 1.79/0.95  --qbf_dom_pre_inst                      false
% 1.79/0.95  --qbf_sk_in                             false
% 1.79/0.95  --qbf_pred_elim                         true
% 1.79/0.95  --qbf_split                             512
% 1.79/0.95  
% 1.79/0.95  ------ BMC1 Options
% 1.79/0.95  
% 1.79/0.95  --bmc1_incremental                      false
% 1.79/0.95  --bmc1_axioms                           reachable_all
% 1.79/0.95  --bmc1_min_bound                        0
% 1.79/0.95  --bmc1_max_bound                        -1
% 1.79/0.95  --bmc1_max_bound_default                -1
% 1.79/0.95  --bmc1_symbol_reachability              true
% 1.79/0.95  --bmc1_property_lemmas                  false
% 1.79/0.95  --bmc1_k_induction                      false
% 1.79/0.95  --bmc1_non_equiv_states                 false
% 1.79/0.95  --bmc1_deadlock                         false
% 1.79/0.95  --bmc1_ucm                              false
% 1.79/0.95  --bmc1_add_unsat_core                   none
% 1.79/0.95  --bmc1_unsat_core_children              false
% 1.79/0.95  --bmc1_unsat_core_extrapolate_axioms    false
% 1.79/0.95  --bmc1_out_stat                         full
% 1.79/0.95  --bmc1_ground_init                      false
% 1.79/0.95  --bmc1_pre_inst_next_state              false
% 1.79/0.95  --bmc1_pre_inst_state                   false
% 1.79/0.95  --bmc1_pre_inst_reach_state             false
% 1.79/0.95  --bmc1_out_unsat_core                   false
% 1.79/0.95  --bmc1_aig_witness_out                  false
% 1.79/0.95  --bmc1_verbose                          false
% 1.79/0.95  --bmc1_dump_clauses_tptp                false
% 1.79/0.95  --bmc1_dump_unsat_core_tptp             false
% 1.79/0.95  --bmc1_dump_file                        -
% 1.79/0.95  --bmc1_ucm_expand_uc_limit              128
% 1.79/0.95  --bmc1_ucm_n_expand_iterations          6
% 1.79/0.95  --bmc1_ucm_extend_mode                  1
% 1.79/0.95  --bmc1_ucm_init_mode                    2
% 1.79/0.95  --bmc1_ucm_cone_mode                    none
% 1.79/0.95  --bmc1_ucm_reduced_relation_type        0
% 1.79/0.95  --bmc1_ucm_relax_model                  4
% 1.79/0.95  --bmc1_ucm_full_tr_after_sat            true
% 1.79/0.95  --bmc1_ucm_expand_neg_assumptions       false
% 1.79/0.95  --bmc1_ucm_layered_model                none
% 1.79/0.95  --bmc1_ucm_max_lemma_size               10
% 1.79/0.95  
% 1.79/0.95  ------ AIG Options
% 1.79/0.95  
% 1.79/0.95  --aig_mode                              false
% 1.79/0.95  
% 1.79/0.95  ------ Instantiation Options
% 1.79/0.95  
% 1.79/0.95  --instantiation_flag                    true
% 1.79/0.95  --inst_sos_flag                         false
% 1.79/0.95  --inst_sos_phase                        true
% 1.79/0.95  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.79/0.95  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.79/0.95  --inst_lit_sel_side                     num_symb
% 1.79/0.95  --inst_solver_per_active                1400
% 1.79/0.95  --inst_solver_calls_frac                1.
% 1.79/0.95  --inst_passive_queue_type               priority_queues
% 1.79/0.95  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.79/0.95  --inst_passive_queues_freq              [25;2]
% 1.79/0.95  --inst_dismatching                      true
% 1.79/0.95  --inst_eager_unprocessed_to_passive     true
% 1.79/0.95  --inst_prop_sim_given                   true
% 1.79/0.95  --inst_prop_sim_new                     false
% 1.79/0.95  --inst_subs_new                         false
% 1.79/0.95  --inst_eq_res_simp                      false
% 1.79/0.95  --inst_subs_given                       false
% 1.79/0.95  --inst_orphan_elimination               true
% 1.79/0.95  --inst_learning_loop_flag               true
% 1.79/0.95  --inst_learning_start                   3000
% 1.79/0.95  --inst_learning_factor                  2
% 1.79/0.95  --inst_start_prop_sim_after_learn       3
% 1.79/0.95  --inst_sel_renew                        solver
% 1.79/0.95  --inst_lit_activity_flag                true
% 1.79/0.95  --inst_restr_to_given                   false
% 1.79/0.95  --inst_activity_threshold               500
% 1.79/0.95  --inst_out_proof                        true
% 1.79/0.95  
% 1.79/0.95  ------ Resolution Options
% 1.79/0.95  
% 1.79/0.95  --resolution_flag                       true
% 1.79/0.95  --res_lit_sel                           adaptive
% 1.79/0.95  --res_lit_sel_side                      none
% 1.79/0.95  --res_ordering                          kbo
% 1.79/0.95  --res_to_prop_solver                    active
% 1.79/0.95  --res_prop_simpl_new                    false
% 1.79/0.95  --res_prop_simpl_given                  true
% 1.79/0.95  --res_passive_queue_type                priority_queues
% 1.79/0.95  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.79/0.95  --res_passive_queues_freq               [15;5]
% 1.79/0.95  --res_forward_subs                      full
% 1.79/0.95  --res_backward_subs                     full
% 1.79/0.95  --res_forward_subs_resolution           true
% 1.79/0.95  --res_backward_subs_resolution          true
% 1.79/0.95  --res_orphan_elimination                true
% 1.79/0.95  --res_time_limit                        2.
% 1.79/0.95  --res_out_proof                         true
% 1.79/0.95  
% 1.79/0.95  ------ Superposition Options
% 1.79/0.95  
% 1.79/0.95  --superposition_flag                    true
% 1.79/0.95  --sup_passive_queue_type                priority_queues
% 1.79/0.95  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.79/0.95  --sup_passive_queues_freq               [8;1;4]
% 1.79/0.95  --demod_completeness_check              fast
% 1.79/0.95  --demod_use_ground                      true
% 1.79/0.95  --sup_to_prop_solver                    passive
% 1.79/0.95  --sup_prop_simpl_new                    true
% 1.79/0.95  --sup_prop_simpl_given                  true
% 1.79/0.95  --sup_fun_splitting                     false
% 1.79/0.95  --sup_smt_interval                      50000
% 1.79/0.95  
% 1.79/0.95  ------ Superposition Simplification Setup
% 1.79/0.95  
% 1.79/0.95  --sup_indices_passive                   []
% 1.79/0.95  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.79/0.95  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.79/0.95  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.79/0.95  --sup_full_triv                         [TrivRules;PropSubs]
% 1.79/0.95  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.79/0.95  --sup_full_bw                           [BwDemod]
% 1.79/0.95  --sup_immed_triv                        [TrivRules]
% 1.79/0.95  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.79/0.95  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.79/0.95  --sup_immed_bw_main                     []
% 1.79/0.95  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.79/0.95  --sup_input_triv                        [Unflattening;TrivRules]
% 1.79/0.95  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.79/0.95  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.79/0.95  
% 1.79/0.95  ------ Combination Options
% 1.79/0.95  
% 1.79/0.95  --comb_res_mult                         3
% 1.79/0.95  --comb_sup_mult                         2
% 1.79/0.95  --comb_inst_mult                        10
% 1.79/0.95  
% 1.79/0.95  ------ Debug Options
% 1.79/0.95  
% 1.79/0.95  --dbg_backtrace                         false
% 1.79/0.95  --dbg_dump_prop_clauses                 false
% 1.79/0.95  --dbg_dump_prop_clauses_file            -
% 1.79/0.95  --dbg_out_stat                          false
% 1.79/0.95  ------ Parsing...
% 1.79/0.95  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.79/0.95  
% 1.79/0.95  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 1.79/0.95  
% 1.79/0.95  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.79/0.95  
% 1.79/0.95  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.79/0.95  ------ Proving...
% 1.79/0.95  ------ Problem Properties 
% 1.79/0.95  
% 1.79/0.95  
% 1.79/0.95  clauses                                 16
% 1.79/0.95  conjectures                             2
% 1.79/0.95  EPR                                     1
% 1.79/0.95  Horn                                    13
% 1.79/0.95  unary                                   3
% 1.79/0.95  binary                                  8
% 1.79/0.95  lits                                    34
% 1.79/0.95  lits eq                                 6
% 1.79/0.95  fd_pure                                 0
% 1.79/0.95  fd_pseudo                               0
% 1.79/0.95  fd_cond                                 0
% 1.79/0.95  fd_pseudo_cond                          2
% 1.79/0.95  AC symbols                              0
% 1.79/0.95  
% 1.79/0.95  ------ Schedule dynamic 5 is on 
% 1.79/0.95  
% 1.79/0.95  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.79/0.95  
% 1.79/0.95  
% 1.79/0.95  ------ 
% 1.79/0.95  Current options:
% 1.79/0.95  ------ 
% 1.79/0.95  
% 1.79/0.95  ------ Input Options
% 1.79/0.95  
% 1.79/0.95  --out_options                           all
% 1.79/0.95  --tptp_safe_out                         true
% 1.79/0.95  --problem_path                          ""
% 1.79/0.95  --include_path                          ""
% 1.79/0.95  --clausifier                            res/vclausify_rel
% 1.79/0.95  --clausifier_options                    --mode clausify
% 1.79/0.95  --stdin                                 false
% 1.79/0.95  --stats_out                             all
% 1.79/0.95  
% 1.79/0.95  ------ General Options
% 1.79/0.95  
% 1.79/0.95  --fof                                   false
% 1.79/0.95  --time_out_real                         305.
% 1.79/0.95  --time_out_virtual                      -1.
% 1.79/0.95  --symbol_type_check                     false
% 1.79/0.95  --clausify_out                          false
% 1.79/0.95  --sig_cnt_out                           false
% 1.79/0.95  --trig_cnt_out                          false
% 1.79/0.95  --trig_cnt_out_tolerance                1.
% 1.79/0.95  --trig_cnt_out_sk_spl                   false
% 1.79/0.95  --abstr_cl_out                          false
% 1.79/0.95  
% 1.79/0.95  ------ Global Options
% 1.79/0.95  
% 1.79/0.95  --schedule                              default
% 1.79/0.95  --add_important_lit                     false
% 1.79/0.95  --prop_solver_per_cl                    1000
% 1.79/0.95  --min_unsat_core                        false
% 1.79/0.95  --soft_assumptions                      false
% 1.79/0.95  --soft_lemma_size                       3
% 1.79/0.95  --prop_impl_unit_size                   0
% 1.79/0.95  --prop_impl_unit                        []
% 1.79/0.95  --share_sel_clauses                     true
% 1.79/0.95  --reset_solvers                         false
% 1.79/0.95  --bc_imp_inh                            [conj_cone]
% 1.79/0.95  --conj_cone_tolerance                   3.
% 1.79/0.95  --extra_neg_conj                        none
% 1.79/0.95  --large_theory_mode                     true
% 1.79/0.95  --prolific_symb_bound                   200
% 1.79/0.95  --lt_threshold                          2000
% 1.79/0.95  --clause_weak_htbl                      true
% 1.79/0.95  --gc_record_bc_elim                     false
% 1.79/0.95  
% 1.79/0.95  ------ Preprocessing Options
% 1.79/0.95  
% 1.79/0.95  --preprocessing_flag                    true
% 1.79/0.95  --time_out_prep_mult                    0.1
% 1.79/0.95  --splitting_mode                        input
% 1.79/0.95  --splitting_grd                         true
% 1.79/0.95  --splitting_cvd                         false
% 1.79/0.95  --splitting_cvd_svl                     false
% 1.79/0.95  --splitting_nvd                         32
% 1.79/0.95  --sub_typing                            true
% 1.79/0.95  --prep_gs_sim                           true
% 1.79/0.95  --prep_unflatten                        true
% 1.79/0.95  --prep_res_sim                          true
% 1.79/0.95  --prep_upred                            true
% 1.79/0.95  --prep_sem_filter                       exhaustive
% 1.79/0.95  --prep_sem_filter_out                   false
% 1.79/0.95  --pred_elim                             true
% 1.79/0.95  --res_sim_input                         true
% 1.79/0.95  --eq_ax_congr_red                       true
% 1.79/0.95  --pure_diseq_elim                       true
% 1.79/0.95  --brand_transform                       false
% 1.79/0.95  --non_eq_to_eq                          false
% 1.79/0.95  --prep_def_merge                        true
% 1.79/0.95  --prep_def_merge_prop_impl              false
% 1.79/0.95  --prep_def_merge_mbd                    true
% 1.79/0.95  --prep_def_merge_tr_red                 false
% 1.79/0.95  --prep_def_merge_tr_cl                  false
% 1.79/0.95  --smt_preprocessing                     true
% 1.79/0.95  --smt_ac_axioms                         fast
% 1.79/0.95  --preprocessed_out                      false
% 1.79/0.95  --preprocessed_stats                    false
% 1.79/0.95  
% 1.79/0.95  ------ Abstraction refinement Options
% 1.79/0.95  
% 1.79/0.95  --abstr_ref                             []
% 1.79/0.95  --abstr_ref_prep                        false
% 1.79/0.95  --abstr_ref_until_sat                   false
% 1.79/0.95  --abstr_ref_sig_restrict                funpre
% 1.79/0.95  --abstr_ref_af_restrict_to_split_sk     false
% 1.79/0.95  --abstr_ref_under                       []
% 1.79/0.95  
% 1.79/0.95  ------ SAT Options
% 1.79/0.95  
% 1.79/0.95  --sat_mode                              false
% 1.79/0.95  --sat_fm_restart_options                ""
% 1.79/0.95  --sat_gr_def                            false
% 1.79/0.95  --sat_epr_types                         true
% 1.79/0.95  --sat_non_cyclic_types                  false
% 1.79/0.95  --sat_finite_models                     false
% 1.79/0.95  --sat_fm_lemmas                         false
% 1.79/0.95  --sat_fm_prep                           false
% 1.79/0.95  --sat_fm_uc_incr                        true
% 1.79/0.95  --sat_out_model                         small
% 1.79/0.95  --sat_out_clauses                       false
% 1.79/0.95  
% 1.79/0.95  ------ QBF Options
% 1.79/0.95  
% 1.79/0.95  --qbf_mode                              false
% 1.79/0.95  --qbf_elim_univ                         false
% 1.79/0.95  --qbf_dom_inst                          none
% 1.79/0.95  --qbf_dom_pre_inst                      false
% 1.79/0.95  --qbf_sk_in                             false
% 1.79/0.95  --qbf_pred_elim                         true
% 1.79/0.95  --qbf_split                             512
% 1.79/0.95  
% 1.79/0.95  ------ BMC1 Options
% 1.79/0.95  
% 1.79/0.95  --bmc1_incremental                      false
% 1.79/0.95  --bmc1_axioms                           reachable_all
% 1.79/0.95  --bmc1_min_bound                        0
% 1.79/0.95  --bmc1_max_bound                        -1
% 1.79/0.95  --bmc1_max_bound_default                -1
% 1.79/0.95  --bmc1_symbol_reachability              true
% 1.79/0.95  --bmc1_property_lemmas                  false
% 1.79/0.95  --bmc1_k_induction                      false
% 1.79/0.95  --bmc1_non_equiv_states                 false
% 1.79/0.95  --bmc1_deadlock                         false
% 1.79/0.95  --bmc1_ucm                              false
% 1.79/0.95  --bmc1_add_unsat_core                   none
% 1.79/0.95  --bmc1_unsat_core_children              false
% 1.79/0.95  --bmc1_unsat_core_extrapolate_axioms    false
% 1.79/0.95  --bmc1_out_stat                         full
% 1.79/0.95  --bmc1_ground_init                      false
% 1.79/0.95  --bmc1_pre_inst_next_state              false
% 1.79/0.95  --bmc1_pre_inst_state                   false
% 1.79/0.95  --bmc1_pre_inst_reach_state             false
% 1.79/0.95  --bmc1_out_unsat_core                   false
% 1.79/0.95  --bmc1_aig_witness_out                  false
% 1.79/0.95  --bmc1_verbose                          false
% 1.79/0.95  --bmc1_dump_clauses_tptp                false
% 1.79/0.95  --bmc1_dump_unsat_core_tptp             false
% 1.79/0.95  --bmc1_dump_file                        -
% 1.79/0.95  --bmc1_ucm_expand_uc_limit              128
% 1.79/0.95  --bmc1_ucm_n_expand_iterations          6
% 1.79/0.95  --bmc1_ucm_extend_mode                  1
% 1.79/0.95  --bmc1_ucm_init_mode                    2
% 1.79/0.95  --bmc1_ucm_cone_mode                    none
% 1.79/0.95  --bmc1_ucm_reduced_relation_type        0
% 1.79/0.95  --bmc1_ucm_relax_model                  4
% 1.79/0.95  --bmc1_ucm_full_tr_after_sat            true
% 1.79/0.95  --bmc1_ucm_expand_neg_assumptions       false
% 1.79/0.95  --bmc1_ucm_layered_model                none
% 1.79/0.95  --bmc1_ucm_max_lemma_size               10
% 1.79/0.95  
% 1.79/0.95  ------ AIG Options
% 1.79/0.95  
% 1.79/0.95  --aig_mode                              false
% 1.79/0.95  
% 1.79/0.95  ------ Instantiation Options
% 1.79/0.95  
% 1.79/0.95  --instantiation_flag                    true
% 1.79/0.95  --inst_sos_flag                         false
% 1.79/0.95  --inst_sos_phase                        true
% 1.79/0.95  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.79/0.95  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.79/0.95  --inst_lit_sel_side                     none
% 1.79/0.95  --inst_solver_per_active                1400
% 1.79/0.95  --inst_solver_calls_frac                1.
% 1.79/0.95  --inst_passive_queue_type               priority_queues
% 1.79/0.95  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.79/0.95  --inst_passive_queues_freq              [25;2]
% 1.79/0.95  --inst_dismatching                      true
% 1.79/0.95  --inst_eager_unprocessed_to_passive     true
% 1.79/0.95  --inst_prop_sim_given                   true
% 1.79/0.95  --inst_prop_sim_new                     false
% 1.79/0.95  --inst_subs_new                         false
% 1.79/0.95  --inst_eq_res_simp                      false
% 1.79/0.95  --inst_subs_given                       false
% 1.79/0.95  --inst_orphan_elimination               true
% 1.79/0.95  --inst_learning_loop_flag               true
% 1.79/0.95  --inst_learning_start                   3000
% 1.79/0.95  --inst_learning_factor                  2
% 1.79/0.95  --inst_start_prop_sim_after_learn       3
% 1.79/0.95  --inst_sel_renew                        solver
% 1.79/0.95  --inst_lit_activity_flag                true
% 1.79/0.95  --inst_restr_to_given                   false
% 1.79/0.95  --inst_activity_threshold               500
% 1.79/0.95  --inst_out_proof                        true
% 1.79/0.95  
% 1.79/0.95  ------ Resolution Options
% 1.79/0.95  
% 1.79/0.95  --resolution_flag                       false
% 1.79/0.95  --res_lit_sel                           adaptive
% 1.79/0.95  --res_lit_sel_side                      none
% 1.79/0.95  --res_ordering                          kbo
% 1.79/0.95  --res_to_prop_solver                    active
% 1.79/0.95  --res_prop_simpl_new                    false
% 1.79/0.95  --res_prop_simpl_given                  true
% 1.79/0.95  --res_passive_queue_type                priority_queues
% 1.79/0.95  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.79/0.95  --res_passive_queues_freq               [15;5]
% 1.79/0.95  --res_forward_subs                      full
% 1.79/0.95  --res_backward_subs                     full
% 1.79/0.95  --res_forward_subs_resolution           true
% 1.79/0.95  --res_backward_subs_resolution          true
% 1.79/0.95  --res_orphan_elimination                true
% 1.79/0.95  --res_time_limit                        2.
% 1.79/0.95  --res_out_proof                         true
% 1.79/0.95  
% 1.79/0.95  ------ Superposition Options
% 1.79/0.95  
% 1.79/0.95  --superposition_flag                    true
% 1.79/0.95  --sup_passive_queue_type                priority_queues
% 1.79/0.95  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.79/0.95  --sup_passive_queues_freq               [8;1;4]
% 1.79/0.95  --demod_completeness_check              fast
% 1.79/0.95  --demod_use_ground                      true
% 1.79/0.95  --sup_to_prop_solver                    passive
% 1.79/0.95  --sup_prop_simpl_new                    true
% 1.79/0.95  --sup_prop_simpl_given                  true
% 1.79/0.95  --sup_fun_splitting                     false
% 1.79/0.95  --sup_smt_interval                      50000
% 1.79/0.95  
% 1.79/0.95  ------ Superposition Simplification Setup
% 1.79/0.95  
% 1.79/0.95  --sup_indices_passive                   []
% 1.79/0.95  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.79/0.95  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.79/0.95  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.79/0.95  --sup_full_triv                         [TrivRules;PropSubs]
% 1.79/0.95  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.79/0.95  --sup_full_bw                           [BwDemod]
% 1.79/0.95  --sup_immed_triv                        [TrivRules]
% 1.79/0.95  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.79/0.95  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.79/0.95  --sup_immed_bw_main                     []
% 1.79/0.95  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.79/0.95  --sup_input_triv                        [Unflattening;TrivRules]
% 1.79/0.95  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.79/0.95  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.79/0.95  
% 1.79/0.95  ------ Combination Options
% 1.79/0.95  
% 1.79/0.95  --comb_res_mult                         3
% 1.79/0.95  --comb_sup_mult                         2
% 1.79/0.95  --comb_inst_mult                        10
% 1.79/0.95  
% 1.79/0.95  ------ Debug Options
% 1.79/0.95  
% 1.79/0.95  --dbg_backtrace                         false
% 1.79/0.95  --dbg_dump_prop_clauses                 false
% 1.79/0.95  --dbg_dump_prop_clauses_file            -
% 1.79/0.95  --dbg_out_stat                          false
% 1.79/0.95  
% 1.79/0.95  
% 1.79/0.95  
% 1.79/0.95  
% 1.79/0.95  ------ Proving...
% 1.79/0.95  
% 1.79/0.95  
% 1.79/0.95  % SZS status Theorem for theBenchmark.p
% 1.79/0.95  
% 1.79/0.95  % SZS output start CNFRefutation for theBenchmark.p
% 1.79/0.95  
% 1.79/0.95  fof(f4,axiom,(
% 1.79/0.95    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 1.79/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.79/0.95  
% 1.79/0.95  fof(f16,plain,(
% 1.79/0.95    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 1.79/0.95    inference(ennf_transformation,[],[f4])).
% 1.79/0.95  
% 1.79/0.95  fof(f57,plain,(
% 1.79/0.95    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 1.79/0.95    inference(cnf_transformation,[],[f16])).
% 1.79/0.95  
% 1.79/0.95  fof(f3,axiom,(
% 1.79/0.95    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.79/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.79/0.95  
% 1.79/0.95  fof(f56,plain,(
% 1.79/0.95    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.79/0.95    inference(cnf_transformation,[],[f3])).
% 1.79/0.95  
% 1.79/0.95  fof(f80,plain,(
% 1.79/0.95    ( ! [X0,X1] : (m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 1.79/0.95    inference(definition_unfolding,[],[f57,f56])).
% 1.79/0.95  
% 1.79/0.95  fof(f5,axiom,(
% 1.79/0.95    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.79/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.79/0.95  
% 1.79/0.95  fof(f40,plain,(
% 1.79/0.95    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.79/0.95    inference(nnf_transformation,[],[f5])).
% 1.79/0.95  
% 1.79/0.95  fof(f58,plain,(
% 1.79/0.95    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.79/0.95    inference(cnf_transformation,[],[f40])).
% 1.79/0.95  
% 1.79/0.95  fof(f13,conjecture,(
% 1.79/0.95    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) <=> m1_connsp_2(X2,X0,X1)))))),
% 1.79/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.79/0.95  
% 1.79/0.95  fof(f14,negated_conjecture,(
% 1.79/0.95    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) <=> m1_connsp_2(X2,X0,X1)))))),
% 1.79/0.95    inference(negated_conjecture,[],[f13])).
% 1.79/0.95  
% 1.79/0.95  fof(f30,plain,(
% 1.79/0.95    ? [X0] : (? [X1] : (? [X2] : ((m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) <~> m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.79/0.95    inference(ennf_transformation,[],[f14])).
% 1.79/0.95  
% 1.79/0.95  fof(f31,plain,(
% 1.79/0.95    ? [X0] : (? [X1] : (? [X2] : ((m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) <~> m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.79/0.95    inference(flattening,[],[f30])).
% 1.79/0.95  
% 1.79/0.95  fof(f43,plain,(
% 1.79/0.95    ? [X0] : (? [X1] : (? [X2] : (((~m1_connsp_2(X2,X0,X1) | ~m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & (m1_connsp_2(X2,X0,X1) | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.79/0.95    inference(nnf_transformation,[],[f31])).
% 1.79/0.95  
% 1.79/0.95  fof(f44,plain,(
% 1.79/0.95    ? [X0] : (? [X1] : (? [X2] : ((~m1_connsp_2(X2,X0,X1) | ~m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & (m1_connsp_2(X2,X0,X1) | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.79/0.95    inference(flattening,[],[f43])).
% 1.79/0.95  
% 1.79/0.95  fof(f47,plain,(
% 1.79/0.95    ( ! [X0,X1] : (? [X2] : ((~m1_connsp_2(X2,X0,X1) | ~m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & (m1_connsp_2(X2,X0,X1) | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => ((~m1_connsp_2(sK4,X0,X1) | ~m2_connsp_2(sK4,X0,k6_domain_1(u1_struct_0(X0),X1))) & (m1_connsp_2(sK4,X0,X1) | m2_connsp_2(sK4,X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 1.79/0.95    introduced(choice_axiom,[])).
% 1.79/0.95  
% 1.79/0.95  fof(f46,plain,(
% 1.79/0.95    ( ! [X0] : (? [X1] : (? [X2] : ((~m1_connsp_2(X2,X0,X1) | ~m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & (m1_connsp_2(X2,X0,X1) | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : ((~m1_connsp_2(X2,X0,sK3) | ~m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),sK3))) & (m1_connsp_2(X2,X0,sK3) | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),sK3))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK3,u1_struct_0(X0)))) )),
% 1.79/0.95    introduced(choice_axiom,[])).
% 1.79/0.95  
% 1.79/0.95  fof(f45,plain,(
% 1.79/0.95    ? [X0] : (? [X1] : (? [X2] : ((~m1_connsp_2(X2,X0,X1) | ~m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & (m1_connsp_2(X2,X0,X1) | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~m1_connsp_2(X2,sK2,X1) | ~m2_connsp_2(X2,sK2,k6_domain_1(u1_struct_0(sK2),X1))) & (m1_connsp_2(X2,sK2,X1) | m2_connsp_2(X2,sK2,k6_domain_1(u1_struct_0(sK2),X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(X1,u1_struct_0(sK2))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 1.79/0.95    introduced(choice_axiom,[])).
% 1.79/0.95  
% 1.79/0.95  fof(f48,plain,(
% 1.79/0.95    (((~m1_connsp_2(sK4,sK2,sK3) | ~m2_connsp_2(sK4,sK2,k6_domain_1(u1_struct_0(sK2),sK3))) & (m1_connsp_2(sK4,sK2,sK3) | m2_connsp_2(sK4,sK2,k6_domain_1(u1_struct_0(sK2),sK3))) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(sK3,u1_struct_0(sK2))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 1.79/0.95    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f44,f47,f46,f45])).
% 1.79/0.95  
% 1.79/0.95  fof(f75,plain,(
% 1.79/0.95    ~m1_connsp_2(sK4,sK2,sK3) | ~m2_connsp_2(sK4,sK2,k6_domain_1(u1_struct_0(sK2),sK3))),
% 1.79/0.95    inference(cnf_transformation,[],[f48])).
% 1.79/0.95  
% 1.79/0.95  fof(f11,axiom,(
% 1.79/0.95    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 1.79/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.79/0.95  
% 1.79/0.95  fof(f26,plain,(
% 1.79/0.95    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.79/0.95    inference(ennf_transformation,[],[f11])).
% 1.79/0.95  
% 1.79/0.95  fof(f27,plain,(
% 1.79/0.95    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.79/0.95    inference(flattening,[],[f26])).
% 1.79/0.95  
% 1.79/0.95  fof(f42,plain,(
% 1.79/0.95    ! [X0] : (! [X1] : (! [X2] : (((m2_connsp_2(X2,X0,X1) | ~r1_tarski(X1,k1_tops_1(X0,X2))) & (r1_tarski(X1,k1_tops_1(X0,X2)) | ~m2_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.79/0.95    inference(nnf_transformation,[],[f27])).
% 1.79/0.95  
% 1.79/0.95  fof(f67,plain,(
% 1.79/0.95    ( ! [X2,X0,X1] : (m2_connsp_2(X2,X0,X1) | ~r1_tarski(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.79/0.95    inference(cnf_transformation,[],[f42])).
% 1.79/0.95  
% 1.79/0.95  fof(f71,plain,(
% 1.79/0.95    l1_pre_topc(sK2)),
% 1.79/0.95    inference(cnf_transformation,[],[f48])).
% 1.79/0.95  
% 1.79/0.95  fof(f70,plain,(
% 1.79/0.95    v2_pre_topc(sK2)),
% 1.79/0.95    inference(cnf_transformation,[],[f48])).
% 1.79/0.95  
% 1.79/0.95  fof(f73,plain,(
% 1.79/0.95    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.79/0.95    inference(cnf_transformation,[],[f48])).
% 1.79/0.95  
% 1.79/0.95  fof(f10,axiom,(
% 1.79/0.95    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 1.79/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.79/0.95  
% 1.79/0.95  fof(f24,plain,(
% 1.79/0.95    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.79/0.95    inference(ennf_transformation,[],[f10])).
% 1.79/0.95  
% 1.79/0.95  fof(f25,plain,(
% 1.79/0.95    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.79/0.95    inference(flattening,[],[f24])).
% 1.79/0.95  
% 1.79/0.95  fof(f41,plain,(
% 1.79/0.95    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.79/0.95    inference(nnf_transformation,[],[f25])).
% 1.79/0.95  
% 1.79/0.95  fof(f65,plain,(
% 1.79/0.95    ( ! [X2,X0,X1] : (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.79/0.95    inference(cnf_transformation,[],[f41])).
% 1.79/0.95  
% 1.79/0.95  fof(f69,plain,(
% 1.79/0.95    ~v2_struct_0(sK2)),
% 1.79/0.95    inference(cnf_transformation,[],[f48])).
% 1.79/0.95  
% 1.79/0.95  fof(f72,plain,(
% 1.79/0.95    m1_subset_1(sK3,u1_struct_0(sK2))),
% 1.79/0.95    inference(cnf_transformation,[],[f48])).
% 1.79/0.95  
% 1.79/0.95  fof(f8,axiom,(
% 1.79/0.95    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.79/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.79/0.95  
% 1.79/0.95  fof(f20,plain,(
% 1.79/0.95    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.79/0.95    inference(ennf_transformation,[],[f8])).
% 1.79/0.95  
% 1.79/0.95  fof(f21,plain,(
% 1.79/0.95    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.79/0.95    inference(flattening,[],[f20])).
% 1.79/0.95  
% 1.79/0.95  fof(f62,plain,(
% 1.79/0.95    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.79/0.95    inference(cnf_transformation,[],[f21])).
% 1.79/0.95  
% 1.79/0.95  fof(f6,axiom,(
% 1.79/0.95    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.79/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.79/0.95  
% 1.79/0.95  fof(f17,plain,(
% 1.79/0.95    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.79/0.95    inference(ennf_transformation,[],[f6])).
% 1.79/0.95  
% 1.79/0.95  fof(f60,plain,(
% 1.79/0.95    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.79/0.95    inference(cnf_transformation,[],[f17])).
% 1.79/0.95  
% 1.79/0.95  fof(f7,axiom,(
% 1.79/0.95    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.79/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.79/0.95  
% 1.79/0.95  fof(f18,plain,(
% 1.79/0.95    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.79/0.95    inference(ennf_transformation,[],[f7])).
% 1.79/0.95  
% 1.79/0.95  fof(f19,plain,(
% 1.79/0.95    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.79/0.95    inference(flattening,[],[f18])).
% 1.79/0.95  
% 1.79/0.95  fof(f61,plain,(
% 1.79/0.95    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.79/0.95    inference(cnf_transformation,[],[f19])).
% 1.79/0.95  
% 1.79/0.95  fof(f9,axiom,(
% 1.79/0.95    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 1.79/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.79/0.95  
% 1.79/0.95  fof(f22,plain,(
% 1.79/0.95    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.79/0.95    inference(ennf_transformation,[],[f9])).
% 1.79/0.95  
% 1.79/0.95  fof(f23,plain,(
% 1.79/0.95    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.79/0.95    inference(flattening,[],[f22])).
% 1.79/0.95  
% 1.79/0.95  fof(f63,plain,(
% 1.79/0.95    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.79/0.95    inference(cnf_transformation,[],[f23])).
% 1.79/0.95  
% 1.79/0.95  fof(f81,plain,(
% 1.79/0.95    ( ! [X0,X1] : (k2_tarski(X1,X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.79/0.95    inference(definition_unfolding,[],[f63,f56])).
% 1.79/0.95  
% 1.79/0.95  fof(f1,axiom,(
% 1.79/0.95    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.79/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.79/0.95  
% 1.79/0.95  fof(f15,plain,(
% 1.79/0.95    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.79/0.95    inference(ennf_transformation,[],[f1])).
% 1.79/0.95  
% 1.79/0.95  fof(f32,plain,(
% 1.79/0.95    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.79/0.95    inference(nnf_transformation,[],[f15])).
% 1.79/0.95  
% 1.79/0.95  fof(f33,plain,(
% 1.79/0.95    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.79/0.95    inference(rectify,[],[f32])).
% 1.79/0.95  
% 1.79/0.95  fof(f34,plain,(
% 1.79/0.95    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 1.79/0.95    introduced(choice_axiom,[])).
% 1.79/0.95  
% 1.79/0.95  fof(f35,plain,(
% 1.79/0.95    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.79/0.95    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).
% 1.79/0.95  
% 1.79/0.95  fof(f49,plain,(
% 1.79/0.95    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.79/0.95    inference(cnf_transformation,[],[f35])).
% 1.79/0.95  
% 1.79/0.95  fof(f74,plain,(
% 1.79/0.95    m1_connsp_2(sK4,sK2,sK3) | m2_connsp_2(sK4,sK2,k6_domain_1(u1_struct_0(sK2),sK3))),
% 1.79/0.95    inference(cnf_transformation,[],[f48])).
% 1.79/0.95  
% 1.79/0.95  fof(f66,plain,(
% 1.79/0.95    ( ! [X2,X0,X1] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~m2_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.79/0.95    inference(cnf_transformation,[],[f42])).
% 1.79/0.95  
% 1.79/0.95  fof(f64,plain,(
% 1.79/0.95    ( ! [X2,X0,X1] : (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.79/0.95    inference(cnf_transformation,[],[f41])).
% 1.79/0.95  
% 1.79/0.95  fof(f12,axiom,(
% 1.79/0.95    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.79/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.79/0.95  
% 1.79/0.95  fof(f28,plain,(
% 1.79/0.95    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.79/0.95    inference(ennf_transformation,[],[f12])).
% 1.79/0.95  
% 1.79/0.95  fof(f29,plain,(
% 1.79/0.95    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.79/0.95    inference(flattening,[],[f28])).
% 1.79/0.95  
% 1.79/0.95  fof(f68,plain,(
% 1.79/0.95    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.79/0.95    inference(cnf_transformation,[],[f29])).
% 1.79/0.95  
% 1.79/0.95  fof(f2,axiom,(
% 1.79/0.95    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.79/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.79/0.95  
% 1.79/0.95  fof(f36,plain,(
% 1.79/0.95    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.79/0.95    inference(nnf_transformation,[],[f2])).
% 1.79/0.95  
% 1.79/0.95  fof(f37,plain,(
% 1.79/0.95    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.79/0.95    inference(rectify,[],[f36])).
% 1.79/0.95  
% 1.79/0.95  fof(f38,plain,(
% 1.79/0.95    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1))))),
% 1.79/0.95    introduced(choice_axiom,[])).
% 1.79/0.95  
% 1.79/0.95  fof(f39,plain,(
% 1.79/0.95    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.79/0.95    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f37,f38])).
% 1.79/0.95  
% 1.79/0.95  fof(f53,plain,(
% 1.79/0.95    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 1.79/0.95    inference(cnf_transformation,[],[f39])).
% 1.79/0.95  
% 1.79/0.95  fof(f78,plain,(
% 1.79/0.95    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_tarski(X0,X0) != X1) )),
% 1.79/0.95    inference(definition_unfolding,[],[f53,f56])).
% 1.79/0.95  
% 1.79/0.95  fof(f82,plain,(
% 1.79/0.95    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_tarski(X3,X3) != X1) )),
% 1.79/0.95    inference(equality_resolution,[],[f78])).
% 1.79/0.95  
% 1.79/0.95  fof(f83,plain,(
% 1.79/0.95    ( ! [X3] : (r2_hidden(X3,k2_tarski(X3,X3))) )),
% 1.79/0.95    inference(equality_resolution,[],[f82])).
% 1.79/0.95  
% 1.79/0.95  cnf(c_7,plain,
% 1.79/0.95      ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1))
% 1.79/0.95      | ~ r2_hidden(X0,X1) ),
% 1.79/0.95      inference(cnf_transformation,[],[f80]) ).
% 1.79/0.95  
% 1.79/0.95  cnf(c_1567,plain,
% 1.79/0.95      ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1)) = iProver_top
% 1.79/0.95      | r2_hidden(X0,X1) != iProver_top ),
% 1.79/0.95      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 1.79/0.95  
% 1.79/0.95  cnf(c_9,plain,
% 1.79/0.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 1.79/0.95      inference(cnf_transformation,[],[f58]) ).
% 1.79/0.95  
% 1.79/0.95  cnf(c_1565,plain,
% 1.79/0.95      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 1.79/0.95      | r1_tarski(X0,X1) = iProver_top ),
% 1.79/0.95      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 1.79/0.95  
% 1.79/0.95  cnf(c_2413,plain,
% 1.79/0.95      ( r2_hidden(X0,X1) != iProver_top
% 1.79/0.95      | r1_tarski(k2_tarski(X0,X0),X1) = iProver_top ),
% 1.79/0.95      inference(superposition,[status(thm)],[c_1567,c_1565]) ).
% 1.79/0.95  
% 1.79/0.95  cnf(c_19,negated_conjecture,
% 1.79/0.95      ( ~ m2_connsp_2(sK4,sK2,k6_domain_1(u1_struct_0(sK2),sK3))
% 1.79/0.95      | ~ m1_connsp_2(sK4,sK2,sK3) ),
% 1.79/0.95      inference(cnf_transformation,[],[f75]) ).
% 1.79/0.95  
% 1.79/0.95  cnf(c_211,plain,
% 1.79/0.95      ( ~ m1_connsp_2(sK4,sK2,sK3)
% 1.79/0.95      | ~ m2_connsp_2(sK4,sK2,k6_domain_1(u1_struct_0(sK2),sK3)) ),
% 1.79/0.95      inference(prop_impl,[status(thm)],[c_19]) ).
% 1.79/0.95  
% 1.79/0.95  cnf(c_212,plain,
% 1.79/0.95      ( ~ m2_connsp_2(sK4,sK2,k6_domain_1(u1_struct_0(sK2),sK3))
% 1.79/0.95      | ~ m1_connsp_2(sK4,sK2,sK3) ),
% 1.79/0.95      inference(renaming,[status(thm)],[c_211]) ).
% 1.79/0.95  
% 1.79/0.95  cnf(c_16,plain,
% 1.79/0.95      ( m2_connsp_2(X0,X1,X2)
% 1.79/0.95      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.79/0.95      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.79/0.95      | ~ r1_tarski(X2,k1_tops_1(X1,X0))
% 1.79/0.95      | ~ v2_pre_topc(X1)
% 1.79/0.95      | ~ l1_pre_topc(X1) ),
% 1.79/0.95      inference(cnf_transformation,[],[f67]) ).
% 1.79/0.95  
% 1.79/0.95  cnf(c_23,negated_conjecture,
% 1.79/0.95      ( l1_pre_topc(sK2) ),
% 1.79/0.95      inference(cnf_transformation,[],[f71]) ).
% 1.79/0.95  
% 1.79/0.95  cnf(c_571,plain,
% 1.79/0.95      ( m2_connsp_2(X0,X1,X2)
% 1.79/0.95      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.79/0.95      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.79/0.95      | ~ r1_tarski(X2,k1_tops_1(X1,X0))
% 1.79/0.95      | ~ v2_pre_topc(X1)
% 1.79/0.95      | sK2 != X1 ),
% 1.79/0.95      inference(resolution_lifted,[status(thm)],[c_16,c_23]) ).
% 1.79/0.95  
% 1.79/0.95  cnf(c_572,plain,
% 1.79/0.95      ( m2_connsp_2(X0,sK2,X1)
% 1.79/0.95      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.79/0.95      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.79/0.95      | ~ r1_tarski(X1,k1_tops_1(sK2,X0))
% 1.79/0.95      | ~ v2_pre_topc(sK2) ),
% 1.79/0.95      inference(unflattening,[status(thm)],[c_571]) ).
% 1.79/0.95  
% 1.79/0.95  cnf(c_24,negated_conjecture,
% 1.79/0.95      ( v2_pre_topc(sK2) ),
% 1.79/0.95      inference(cnf_transformation,[],[f70]) ).
% 1.79/0.95  
% 1.79/0.95  cnf(c_576,plain,
% 1.79/0.95      ( ~ r1_tarski(X1,k1_tops_1(sK2,X0))
% 1.79/0.95      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.79/0.95      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.79/0.95      | m2_connsp_2(X0,sK2,X1) ),
% 1.79/0.95      inference(global_propositional_subsumption,
% 1.79/0.95                [status(thm)],
% 1.79/0.95                [c_572,c_24]) ).
% 1.79/0.95  
% 1.79/0.95  cnf(c_577,plain,
% 1.79/0.95      ( m2_connsp_2(X0,sK2,X1)
% 1.79/0.95      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.79/0.95      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.79/0.95      | ~ r1_tarski(X1,k1_tops_1(sK2,X0)) ),
% 1.79/0.95      inference(renaming,[status(thm)],[c_576]) ).
% 1.79/0.95  
% 1.79/0.95  cnf(c_624,plain,
% 1.79/0.95      ( ~ m1_connsp_2(sK4,sK2,sK3)
% 1.79/0.95      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.79/0.95      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.79/0.95      | ~ r1_tarski(X1,k1_tops_1(sK2,X0))
% 1.79/0.95      | k6_domain_1(u1_struct_0(sK2),sK3) != X1
% 1.79/0.95      | sK2 != sK2
% 1.79/0.95      | sK4 != X0 ),
% 1.79/0.95      inference(resolution_lifted,[status(thm)],[c_212,c_577]) ).
% 1.79/0.95  
% 1.79/0.95  cnf(c_625,plain,
% 1.79/0.95      ( ~ m1_connsp_2(sK4,sK2,sK3)
% 1.79/0.95      | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.79/0.95      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.79/0.95      | ~ r1_tarski(k6_domain_1(u1_struct_0(sK2),sK3),k1_tops_1(sK2,sK4)) ),
% 1.79/0.95      inference(unflattening,[status(thm)],[c_624]) ).
% 1.79/0.95  
% 1.79/0.95  cnf(c_21,negated_conjecture,
% 1.79/0.95      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 1.79/0.95      inference(cnf_transformation,[],[f73]) ).
% 1.79/0.95  
% 1.79/0.95  cnf(c_627,plain,
% 1.79/0.95      ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.79/0.95      | ~ m1_connsp_2(sK4,sK2,sK3)
% 1.79/0.95      | ~ r1_tarski(k6_domain_1(u1_struct_0(sK2),sK3),k1_tops_1(sK2,sK4)) ),
% 1.79/0.95      inference(global_propositional_subsumption,
% 1.79/0.95                [status(thm)],
% 1.79/0.95                [c_625,c_21]) ).
% 1.79/0.95  
% 1.79/0.95  cnf(c_628,plain,
% 1.79/0.95      ( ~ m1_connsp_2(sK4,sK2,sK3)
% 1.79/0.95      | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.79/0.95      | ~ r1_tarski(k6_domain_1(u1_struct_0(sK2),sK3),k1_tops_1(sK2,sK4)) ),
% 1.79/0.95      inference(renaming,[status(thm)],[c_627]) ).
% 1.79/0.95  
% 1.79/0.95  cnf(c_14,plain,
% 1.79/0.95      ( m1_connsp_2(X0,X1,X2)
% 1.79/0.95      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.79/0.95      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.79/0.95      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 1.79/0.95      | ~ v2_pre_topc(X1)
% 1.79/0.95      | v2_struct_0(X1)
% 1.79/0.95      | ~ l1_pre_topc(X1) ),
% 1.79/0.95      inference(cnf_transformation,[],[f65]) ).
% 1.79/0.95  
% 1.79/0.95  cnf(c_25,negated_conjecture,
% 1.79/0.95      ( ~ v2_struct_0(sK2) ),
% 1.79/0.95      inference(cnf_transformation,[],[f69]) ).
% 1.79/0.95  
% 1.79/0.95  cnf(c_478,plain,
% 1.79/0.95      ( m1_connsp_2(X0,X1,X2)
% 1.79/0.95      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.79/0.95      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.79/0.95      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 1.79/0.95      | ~ v2_pre_topc(X1)
% 1.79/0.95      | ~ l1_pre_topc(X1)
% 1.79/0.95      | sK2 != X1 ),
% 1.79/0.95      inference(resolution_lifted,[status(thm)],[c_14,c_25]) ).
% 1.79/0.95  
% 1.79/0.95  cnf(c_479,plain,
% 1.79/0.95      ( m1_connsp_2(X0,sK2,X1)
% 1.79/0.95      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.79/0.95      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.79/0.95      | ~ r2_hidden(X1,k1_tops_1(sK2,X0))
% 1.79/0.95      | ~ v2_pre_topc(sK2)
% 1.79/0.95      | ~ l1_pre_topc(sK2) ),
% 1.79/0.95      inference(unflattening,[status(thm)],[c_478]) ).
% 1.79/0.95  
% 1.79/0.95  cnf(c_483,plain,
% 1.79/0.95      ( m1_connsp_2(X0,sK2,X1)
% 1.79/0.95      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.79/0.95      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.79/0.95      | ~ r2_hidden(X1,k1_tops_1(sK2,X0)) ),
% 1.79/0.95      inference(global_propositional_subsumption,
% 1.79/0.95                [status(thm)],
% 1.79/0.95                [c_479,c_24,c_23]) ).
% 1.79/0.95  
% 1.79/0.95  cnf(c_671,plain,
% 1.79/0.95      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.79/0.95      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.79/0.95      | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.79/0.95      | ~ r2_hidden(X0,k1_tops_1(sK2,X1))
% 1.79/0.95      | ~ r1_tarski(k6_domain_1(u1_struct_0(sK2),sK3),k1_tops_1(sK2,sK4))
% 1.79/0.95      | sK3 != X0
% 1.79/0.95      | sK2 != sK2
% 1.79/0.95      | sK4 != X1 ),
% 1.79/0.95      inference(resolution_lifted,[status(thm)],[c_628,c_483]) ).
% 1.79/0.95  
% 1.79/0.95  cnf(c_672,plain,
% 1.79/0.95      ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.79/0.95      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 1.79/0.95      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.79/0.95      | ~ r2_hidden(sK3,k1_tops_1(sK2,sK4))
% 1.79/0.95      | ~ r1_tarski(k6_domain_1(u1_struct_0(sK2),sK3),k1_tops_1(sK2,sK4)) ),
% 1.79/0.95      inference(unflattening,[status(thm)],[c_671]) ).
% 1.79/0.95  
% 1.79/0.95  cnf(c_22,negated_conjecture,
% 1.79/0.95      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 1.79/0.95      inference(cnf_transformation,[],[f72]) ).
% 1.79/0.95  
% 1.79/0.95  cnf(c_674,plain,
% 1.79/0.95      ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.79/0.95      | ~ r2_hidden(sK3,k1_tops_1(sK2,sK4))
% 1.79/0.95      | ~ r1_tarski(k6_domain_1(u1_struct_0(sK2),sK3),k1_tops_1(sK2,sK4)) ),
% 1.79/0.95      inference(global_propositional_subsumption,
% 1.79/0.95                [status(thm)],
% 1.79/0.95                [c_672,c_22,c_21]) ).
% 1.79/0.95  
% 1.79/0.95  cnf(c_1559,plain,
% 1.79/0.95      ( m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.79/0.95      | r2_hidden(sK3,k1_tops_1(sK2,sK4)) != iProver_top
% 1.79/0.95      | r1_tarski(k6_domain_1(u1_struct_0(sK2),sK3),k1_tops_1(sK2,sK4)) != iProver_top ),
% 1.79/0.95      inference(predicate_to_equality,[status(thm)],[c_674]) ).
% 1.79/0.95  
% 1.79/0.95  cnf(c_29,plain,
% 1.79/0.95      ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
% 1.79/0.95      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 1.79/0.95  
% 1.79/0.95  cnf(c_676,plain,
% 1.79/0.95      ( m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.79/0.95      | r2_hidden(sK3,k1_tops_1(sK2,sK4)) != iProver_top
% 1.79/0.95      | r1_tarski(k6_domain_1(u1_struct_0(sK2),sK3),k1_tops_1(sK2,sK4)) != iProver_top ),
% 1.79/0.95      inference(predicate_to_equality,[status(thm)],[c_674]) ).
% 1.79/0.95  
% 1.79/0.95  cnf(c_12,plain,
% 1.79/0.95      ( ~ m1_subset_1(X0,X1)
% 1.79/0.95      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
% 1.79/0.95      | v1_xboole_0(X1) ),
% 1.79/0.95      inference(cnf_transformation,[],[f62]) ).
% 1.79/0.95  
% 1.79/0.95  cnf(c_10,plain,
% 1.79/0.95      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 1.79/0.95      inference(cnf_transformation,[],[f60]) ).
% 1.79/0.95  
% 1.79/0.95  cnf(c_11,plain,
% 1.79/0.95      ( v2_struct_0(X0)
% 1.79/0.95      | ~ v1_xboole_0(u1_struct_0(X0))
% 1.79/0.95      | ~ l1_struct_0(X0) ),
% 1.79/0.95      inference(cnf_transformation,[],[f61]) ).
% 1.79/0.95  
% 1.79/0.95  cnf(c_363,plain,
% 1.79/0.95      ( v2_struct_0(X0)
% 1.79/0.95      | ~ v1_xboole_0(u1_struct_0(X0))
% 1.79/0.95      | ~ l1_pre_topc(X0) ),
% 1.79/0.95      inference(resolution,[status(thm)],[c_10,c_11]) ).
% 1.79/0.95  
% 1.79/0.95  cnf(c_425,plain,
% 1.79/0.95      ( ~ v1_xboole_0(u1_struct_0(X0)) | ~ l1_pre_topc(X0) | sK2 != X0 ),
% 1.79/0.95      inference(resolution_lifted,[status(thm)],[c_363,c_25]) ).
% 1.79/0.95  
% 1.79/0.95  cnf(c_426,plain,
% 1.79/0.95      ( ~ v1_xboole_0(u1_struct_0(sK2)) | ~ l1_pre_topc(sK2) ),
% 1.79/0.95      inference(unflattening,[status(thm)],[c_425]) ).
% 1.79/0.95  
% 1.79/0.95  cnf(c_55,plain,
% 1.79/0.95      ( v2_struct_0(sK2)
% 1.79/0.95      | ~ v1_xboole_0(u1_struct_0(sK2))
% 1.79/0.95      | ~ l1_struct_0(sK2) ),
% 1.79/0.95      inference(instantiation,[status(thm)],[c_11]) ).
% 1.79/0.95  
% 1.79/0.95  cnf(c_58,plain,
% 1.79/0.95      ( ~ l1_pre_topc(sK2) | l1_struct_0(sK2) ),
% 1.79/0.95      inference(instantiation,[status(thm)],[c_10]) ).
% 1.79/0.95  
% 1.79/0.95  cnf(c_428,plain,
% 1.79/0.95      ( ~ v1_xboole_0(u1_struct_0(sK2)) ),
% 1.79/0.95      inference(global_propositional_subsumption,
% 1.79/0.95                [status(thm)],
% 1.79/0.95                [c_426,c_25,c_23,c_55,c_58]) ).
% 1.79/0.95  
% 1.79/0.95  cnf(c_529,plain,
% 1.79/0.95      ( ~ m1_subset_1(X0,X1)
% 1.79/0.95      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
% 1.79/0.95      | u1_struct_0(sK2) != X1 ),
% 1.79/0.95      inference(resolution_lifted,[status(thm)],[c_12,c_428]) ).
% 1.79/0.95  
% 1.79/0.95  cnf(c_530,plain,
% 1.79/0.95      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.79/0.95      | m1_subset_1(k6_domain_1(u1_struct_0(sK2),X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 1.79/0.95      inference(unflattening,[status(thm)],[c_529]) ).
% 1.79/0.95  
% 1.79/0.95  cnf(c_1678,plain,
% 1.79/0.95      ( m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.79/0.95      | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 1.79/0.95      inference(instantiation,[status(thm)],[c_530]) ).
% 1.79/0.95  
% 1.79/0.95  cnf(c_1679,plain,
% 1.79/0.95      ( m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 1.79/0.95      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 1.79/0.95      inference(predicate_to_equality,[status(thm)],[c_1678]) ).
% 1.79/0.95  
% 1.79/0.95  cnf(c_1889,plain,
% 1.79/0.95      ( r2_hidden(sK3,k1_tops_1(sK2,sK4)) != iProver_top
% 1.79/0.95      | r1_tarski(k6_domain_1(u1_struct_0(sK2),sK3),k1_tops_1(sK2,sK4)) != iProver_top ),
% 1.79/0.95      inference(global_propositional_subsumption,
% 1.79/0.95                [status(thm)],
% 1.79/0.95                [c_1559,c_29,c_676,c_1679]) ).
% 1.79/0.95  
% 1.79/0.95  cnf(c_1563,plain,
% 1.79/0.95      ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
% 1.79/0.95      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 1.79/0.95  
% 1.79/0.95  cnf(c_13,plain,
% 1.79/0.95      ( ~ m1_subset_1(X0,X1)
% 1.79/0.95      | v1_xboole_0(X1)
% 1.79/0.95      | k6_domain_1(X1,X0) = k2_tarski(X0,X0) ),
% 1.79/0.95      inference(cnf_transformation,[],[f81]) ).
% 1.79/0.95  
% 1.79/0.95  cnf(c_517,plain,
% 1.79/0.95      ( ~ m1_subset_1(X0,X1)
% 1.79/0.95      | k6_domain_1(X1,X0) = k2_tarski(X0,X0)
% 1.79/0.95      | u1_struct_0(sK2) != X1 ),
% 1.79/0.95      inference(resolution_lifted,[status(thm)],[c_13,c_428]) ).
% 1.79/0.95  
% 1.79/0.95  cnf(c_518,plain,
% 1.79/0.95      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.79/0.95      | k6_domain_1(u1_struct_0(sK2),X0) = k2_tarski(X0,X0) ),
% 1.79/0.95      inference(unflattening,[status(thm)],[c_517]) ).
% 1.79/0.95  
% 1.79/0.95  cnf(c_1562,plain,
% 1.79/0.95      ( k6_domain_1(u1_struct_0(sK2),X0) = k2_tarski(X0,X0)
% 1.79/0.95      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
% 1.79/0.95      inference(predicate_to_equality,[status(thm)],[c_518]) ).
% 1.79/0.95  
% 1.79/0.95  cnf(c_1715,plain,
% 1.79/0.95      ( k6_domain_1(u1_struct_0(sK2),sK3) = k2_tarski(sK3,sK3) ),
% 1.79/0.95      inference(superposition,[status(thm)],[c_1563,c_1562]) ).
% 1.79/0.95  
% 1.79/0.95  cnf(c_1893,plain,
% 1.79/0.95      ( r2_hidden(sK3,k1_tops_1(sK2,sK4)) != iProver_top
% 1.79/0.96      | r1_tarski(k2_tarski(sK3,sK3),k1_tops_1(sK2,sK4)) != iProver_top ),
% 1.79/0.96      inference(light_normalisation,[status(thm)],[c_1889,c_1715]) ).
% 1.79/0.96  
% 1.79/0.96  cnf(c_2773,plain,
% 1.79/0.96      ( r2_hidden(sK3,k1_tops_1(sK2,sK4)) != iProver_top ),
% 1.79/0.96      inference(superposition,[status(thm)],[c_2413,c_1893]) ).
% 1.79/0.96  
% 1.79/0.96  cnf(c_2,plain,
% 1.79/0.96      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 1.79/0.96      inference(cnf_transformation,[],[f49]) ).
% 1.79/0.96  
% 1.79/0.96  cnf(c_1707,plain,
% 1.79/0.96      ( r2_hidden(X0,X1)
% 1.79/0.96      | ~ r2_hidden(X0,k2_tarski(X0,X0))
% 1.79/0.96      | ~ r1_tarski(k2_tarski(X0,X0),X1) ),
% 1.79/0.96      inference(instantiation,[status(thm)],[c_2]) ).
% 1.79/0.96  
% 1.79/0.96  cnf(c_1962,plain,
% 1.79/0.96      ( r2_hidden(sK3,k1_tops_1(sK2,sK4))
% 1.79/0.96      | ~ r2_hidden(sK3,k2_tarski(sK3,sK3))
% 1.79/0.96      | ~ r1_tarski(k2_tarski(sK3,sK3),k1_tops_1(sK2,sK4)) ),
% 1.79/0.96      inference(instantiation,[status(thm)],[c_1707]) ).
% 1.79/0.96  
% 1.79/0.96  cnf(c_1963,plain,
% 1.79/0.96      ( r2_hidden(sK3,k1_tops_1(sK2,sK4)) = iProver_top
% 1.79/0.96      | r2_hidden(sK3,k2_tarski(sK3,sK3)) != iProver_top
% 1.79/0.96      | r1_tarski(k2_tarski(sK3,sK3),k1_tops_1(sK2,sK4)) != iProver_top ),
% 1.79/0.96      inference(predicate_to_equality,[status(thm)],[c_1962]) ).
% 1.79/0.96  
% 1.79/0.96  cnf(c_20,negated_conjecture,
% 1.79/0.96      ( m2_connsp_2(sK4,sK2,k6_domain_1(u1_struct_0(sK2),sK3))
% 1.79/0.96      | m1_connsp_2(sK4,sK2,sK3) ),
% 1.79/0.96      inference(cnf_transformation,[],[f74]) ).
% 1.79/0.96  
% 1.79/0.96  cnf(c_213,plain,
% 1.79/0.96      ( m1_connsp_2(sK4,sK2,sK3)
% 1.79/0.96      | m2_connsp_2(sK4,sK2,k6_domain_1(u1_struct_0(sK2),sK3)) ),
% 1.79/0.96      inference(prop_impl,[status(thm)],[c_20]) ).
% 1.79/0.96  
% 1.79/0.96  cnf(c_214,plain,
% 1.79/0.96      ( m2_connsp_2(sK4,sK2,k6_domain_1(u1_struct_0(sK2),sK3))
% 1.79/0.96      | m1_connsp_2(sK4,sK2,sK3) ),
% 1.79/0.96      inference(renaming,[status(thm)],[c_213]) ).
% 1.79/0.96  
% 1.79/0.96  cnf(c_17,plain,
% 1.79/0.96      ( ~ m2_connsp_2(X0,X1,X2)
% 1.79/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.79/0.96      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.79/0.96      | r1_tarski(X2,k1_tops_1(X1,X0))
% 1.79/0.96      | ~ v2_pre_topc(X1)
% 1.79/0.96      | ~ l1_pre_topc(X1) ),
% 1.79/0.96      inference(cnf_transformation,[],[f66]) ).
% 1.79/0.96  
% 1.79/0.96  cnf(c_547,plain,
% 1.79/0.96      ( ~ m2_connsp_2(X0,X1,X2)
% 1.79/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.79/0.96      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.79/0.96      | r1_tarski(X2,k1_tops_1(X1,X0))
% 1.79/0.96      | ~ v2_pre_topc(X1)
% 1.79/0.96      | sK2 != X1 ),
% 1.79/0.96      inference(resolution_lifted,[status(thm)],[c_17,c_23]) ).
% 1.79/0.96  
% 1.79/0.96  cnf(c_548,plain,
% 1.79/0.96      ( ~ m2_connsp_2(X0,sK2,X1)
% 1.79/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.79/0.96      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.79/0.96      | r1_tarski(X1,k1_tops_1(sK2,X0))
% 1.79/0.96      | ~ v2_pre_topc(sK2) ),
% 1.79/0.96      inference(unflattening,[status(thm)],[c_547]) ).
% 1.79/0.96  
% 1.79/0.96  cnf(c_552,plain,
% 1.79/0.96      ( r1_tarski(X1,k1_tops_1(sK2,X0))
% 1.79/0.96      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.79/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.79/0.96      | ~ m2_connsp_2(X0,sK2,X1) ),
% 1.79/0.96      inference(global_propositional_subsumption,
% 1.79/0.96                [status(thm)],
% 1.79/0.96                [c_548,c_24]) ).
% 1.79/0.96  
% 1.79/0.96  cnf(c_553,plain,
% 1.79/0.96      ( ~ m2_connsp_2(X0,sK2,X1)
% 1.79/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.79/0.96      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.79/0.96      | r1_tarski(X1,k1_tops_1(sK2,X0)) ),
% 1.79/0.96      inference(renaming,[status(thm)],[c_552]) ).
% 1.79/0.96  
% 1.79/0.96  cnf(c_607,plain,
% 1.79/0.96      ( m1_connsp_2(sK4,sK2,sK3)
% 1.79/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.79/0.96      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.79/0.96      | r1_tarski(X1,k1_tops_1(sK2,X0))
% 1.79/0.96      | k6_domain_1(u1_struct_0(sK2),sK3) != X1
% 1.79/0.96      | sK2 != sK2
% 1.79/0.96      | sK4 != X0 ),
% 1.79/0.96      inference(resolution_lifted,[status(thm)],[c_214,c_553]) ).
% 1.79/0.96  
% 1.79/0.96  cnf(c_608,plain,
% 1.79/0.96      ( m1_connsp_2(sK4,sK2,sK3)
% 1.79/0.96      | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.79/0.96      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.79/0.96      | r1_tarski(k6_domain_1(u1_struct_0(sK2),sK3),k1_tops_1(sK2,sK4)) ),
% 1.79/0.96      inference(unflattening,[status(thm)],[c_607]) ).
% 1.79/0.96  
% 1.79/0.96  cnf(c_610,plain,
% 1.79/0.96      ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.79/0.96      | m1_connsp_2(sK4,sK2,sK3)
% 1.79/0.96      | r1_tarski(k6_domain_1(u1_struct_0(sK2),sK3),k1_tops_1(sK2,sK4)) ),
% 1.79/0.96      inference(global_propositional_subsumption,
% 1.79/0.96                [status(thm)],
% 1.79/0.96                [c_608,c_21]) ).
% 1.79/0.96  
% 1.79/0.96  cnf(c_611,plain,
% 1.79/0.96      ( m1_connsp_2(sK4,sK2,sK3)
% 1.79/0.96      | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.79/0.96      | r1_tarski(k6_domain_1(u1_struct_0(sK2),sK3),k1_tops_1(sK2,sK4)) ),
% 1.79/0.96      inference(renaming,[status(thm)],[c_610]) ).
% 1.79/0.96  
% 1.79/0.96  cnf(c_15,plain,
% 1.79/0.96      ( ~ m1_connsp_2(X0,X1,X2)
% 1.79/0.96      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.79/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.79/0.96      | r2_hidden(X2,k1_tops_1(X1,X0))
% 1.79/0.96      | ~ v2_pre_topc(X1)
% 1.79/0.96      | v2_struct_0(X1)
% 1.79/0.96      | ~ l1_pre_topc(X1) ),
% 1.79/0.96      inference(cnf_transformation,[],[f64]) ).
% 1.79/0.96  
% 1.79/0.96  cnf(c_18,plain,
% 1.79/0.96      ( ~ m1_connsp_2(X0,X1,X2)
% 1.79/0.96      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.79/0.96      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.79/0.96      | ~ v2_pre_topc(X1)
% 1.79/0.96      | v2_struct_0(X1)
% 1.79/0.96      | ~ l1_pre_topc(X1) ),
% 1.79/0.96      inference(cnf_transformation,[],[f68]) ).
% 1.79/0.96  
% 1.79/0.96  cnf(c_151,plain,
% 1.79/0.96      ( ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.79/0.96      | ~ m1_connsp_2(X0,X1,X2)
% 1.79/0.96      | r2_hidden(X2,k1_tops_1(X1,X0))
% 1.79/0.96      | ~ v2_pre_topc(X1)
% 1.79/0.96      | v2_struct_0(X1)
% 1.79/0.96      | ~ l1_pre_topc(X1) ),
% 1.79/0.96      inference(global_propositional_subsumption,
% 1.79/0.96                [status(thm)],
% 1.79/0.96                [c_15,c_18]) ).
% 1.79/0.96  
% 1.79/0.96  cnf(c_152,plain,
% 1.79/0.96      ( ~ m1_connsp_2(X0,X1,X2)
% 1.79/0.96      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.79/0.96      | r2_hidden(X2,k1_tops_1(X1,X0))
% 1.79/0.96      | ~ v2_pre_topc(X1)
% 1.79/0.96      | v2_struct_0(X1)
% 1.79/0.96      | ~ l1_pre_topc(X1) ),
% 1.79/0.96      inference(renaming,[status(thm)],[c_151]) ).
% 1.79/0.96  
% 1.79/0.96  cnf(c_436,plain,
% 1.79/0.96      ( ~ m1_connsp_2(X0,X1,X2)
% 1.79/0.96      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.79/0.96      | r2_hidden(X2,k1_tops_1(X1,X0))
% 1.79/0.96      | ~ v2_pre_topc(X1)
% 1.79/0.96      | ~ l1_pre_topc(X1)
% 1.79/0.96      | sK2 != X1 ),
% 1.79/0.96      inference(resolution_lifted,[status(thm)],[c_152,c_25]) ).
% 1.79/0.96  
% 1.79/0.96  cnf(c_437,plain,
% 1.79/0.96      ( ~ m1_connsp_2(X0,sK2,X1)
% 1.79/0.96      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.79/0.96      | r2_hidden(X1,k1_tops_1(sK2,X0))
% 1.79/0.96      | ~ v2_pre_topc(sK2)
% 1.79/0.96      | ~ l1_pre_topc(sK2) ),
% 1.79/0.96      inference(unflattening,[status(thm)],[c_436]) ).
% 1.79/0.96  
% 1.79/0.96  cnf(c_441,plain,
% 1.79/0.96      ( ~ m1_connsp_2(X0,sK2,X1)
% 1.79/0.96      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.79/0.96      | r2_hidden(X1,k1_tops_1(sK2,X0)) ),
% 1.79/0.96      inference(global_propositional_subsumption,
% 1.79/0.96                [status(thm)],
% 1.79/0.96                [c_437,c_24,c_23]) ).
% 1.79/0.96  
% 1.79/0.96  cnf(c_654,plain,
% 1.79/0.96      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.79/0.96      | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.79/0.96      | r2_hidden(X0,k1_tops_1(sK2,X1))
% 1.79/0.96      | r1_tarski(k6_domain_1(u1_struct_0(sK2),sK3),k1_tops_1(sK2,sK4))
% 1.79/0.96      | sK3 != X0
% 1.79/0.96      | sK2 != sK2
% 1.79/0.96      | sK4 != X1 ),
% 1.79/0.96      inference(resolution_lifted,[status(thm)],[c_611,c_441]) ).
% 1.79/0.96  
% 1.79/0.96  cnf(c_655,plain,
% 1.79/0.96      ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.79/0.96      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 1.79/0.96      | r2_hidden(sK3,k1_tops_1(sK2,sK4))
% 1.79/0.96      | r1_tarski(k6_domain_1(u1_struct_0(sK2),sK3),k1_tops_1(sK2,sK4)) ),
% 1.79/0.96      inference(unflattening,[status(thm)],[c_654]) ).
% 1.79/0.96  
% 1.79/0.96  cnf(c_657,plain,
% 1.79/0.96      ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.79/0.96      | r2_hidden(sK3,k1_tops_1(sK2,sK4))
% 1.79/0.96      | r1_tarski(k6_domain_1(u1_struct_0(sK2),sK3),k1_tops_1(sK2,sK4)) ),
% 1.79/0.96      inference(global_propositional_subsumption,
% 1.79/0.96                [status(thm)],
% 1.79/0.96                [c_655,c_22]) ).
% 1.79/0.96  
% 1.79/0.96  cnf(c_1560,plain,
% 1.79/0.96      ( m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.79/0.96      | r2_hidden(sK3,k1_tops_1(sK2,sK4)) = iProver_top
% 1.79/0.96      | r1_tarski(k6_domain_1(u1_struct_0(sK2),sK3),k1_tops_1(sK2,sK4)) = iProver_top ),
% 1.79/0.96      inference(predicate_to_equality,[status(thm)],[c_657]) ).
% 1.79/0.96  
% 1.79/0.96  cnf(c_656,plain,
% 1.79/0.96      ( m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.79/0.96      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 1.79/0.96      | r2_hidden(sK3,k1_tops_1(sK2,sK4)) = iProver_top
% 1.79/0.96      | r1_tarski(k6_domain_1(u1_struct_0(sK2),sK3),k1_tops_1(sK2,sK4)) = iProver_top ),
% 1.79/0.96      inference(predicate_to_equality,[status(thm)],[c_655]) ).
% 1.79/0.96  
% 1.79/0.96  cnf(c_1898,plain,
% 1.79/0.96      ( r2_hidden(sK3,k1_tops_1(sK2,sK4)) = iProver_top
% 1.79/0.96      | r1_tarski(k6_domain_1(u1_struct_0(sK2),sK3),k1_tops_1(sK2,sK4)) = iProver_top ),
% 1.79/0.96      inference(global_propositional_subsumption,
% 1.79/0.96                [status(thm)],
% 1.79/0.96                [c_1560,c_29,c_656,c_1679]) ).
% 1.79/0.96  
% 1.79/0.96  cnf(c_1902,plain,
% 1.79/0.96      ( r2_hidden(sK3,k1_tops_1(sK2,sK4)) = iProver_top
% 1.79/0.96      | r1_tarski(k2_tarski(sK3,sK3),k1_tops_1(sK2,sK4)) = iProver_top ),
% 1.79/0.96      inference(light_normalisation,[status(thm)],[c_1898,c_1715]) ).
% 1.79/0.96  
% 1.79/0.96  cnf(c_5,plain,
% 1.79/0.96      ( r2_hidden(X0,k2_tarski(X0,X0)) ),
% 1.79/0.96      inference(cnf_transformation,[],[f83]) ).
% 1.79/0.96  
% 1.79/0.96  cnf(c_1873,plain,
% 1.79/0.96      ( r2_hidden(sK3,k2_tarski(sK3,sK3)) ),
% 1.79/0.96      inference(instantiation,[status(thm)],[c_5]) ).
% 1.79/0.96  
% 1.79/0.96  cnf(c_1874,plain,
% 1.79/0.96      ( r2_hidden(sK3,k2_tarski(sK3,sK3)) = iProver_top ),
% 1.79/0.96      inference(predicate_to_equality,[status(thm)],[c_1873]) ).
% 1.79/0.96  
% 1.79/0.96  cnf(contradiction,plain,
% 1.79/0.96      ( $false ),
% 1.79/0.96      inference(minisat,[status(thm)],[c_2773,c_1963,c_1902,c_1874]) ).
% 1.79/0.96  
% 1.79/0.96  
% 1.79/0.96  % SZS output end CNFRefutation for theBenchmark.p
% 1.79/0.96  
% 1.79/0.96  ------                               Statistics
% 1.79/0.96  
% 1.79/0.96  ------ General
% 1.79/0.96  
% 1.79/0.96  abstr_ref_over_cycles:                  0
% 1.79/0.96  abstr_ref_under_cycles:                 0
% 1.79/0.96  gc_basic_clause_elim:                   0
% 1.79/0.96  forced_gc_time:                         0
% 1.79/0.96  parsing_time:                           0.013
% 1.79/0.96  unif_index_cands_time:                  0.
% 1.79/0.96  unif_index_add_time:                    0.
% 1.79/0.96  orderings_time:                         0.
% 1.79/0.96  out_proof_time:                         0.013
% 1.79/0.96  total_time:                             0.109
% 1.79/0.96  num_of_symbols:                         51
% 1.79/0.96  num_of_terms:                           2131
% 1.79/0.96  
% 1.79/0.96  ------ Preprocessing
% 1.79/0.96  
% 1.79/0.96  num_of_splits:                          0
% 1.79/0.96  num_of_split_atoms:                     0
% 1.79/0.96  num_of_reused_defs:                     0
% 1.79/0.96  num_eq_ax_congr_red:                    22
% 1.79/0.96  num_of_sem_filtered_clauses:            1
% 1.79/0.96  num_of_subtypes:                        0
% 1.79/0.96  monotx_restored_types:                  0
% 1.79/0.96  sat_num_of_epr_types:                   0
% 1.79/0.96  sat_num_of_non_cyclic_types:            0
% 1.79/0.96  sat_guarded_non_collapsed_types:        0
% 1.79/0.96  num_pure_diseq_elim:                    0
% 1.79/0.96  simp_replaced_by:                       0
% 1.79/0.96  res_preprocessed:                       93
% 1.79/0.96  prep_upred:                             0
% 1.79/0.96  prep_unflattend:                        52
% 1.79/0.96  smt_new_axioms:                         0
% 1.79/0.96  pred_elim_cands:                        3
% 1.79/0.96  pred_elim:                              7
% 1.79/0.96  pred_elim_cl:                           10
% 1.79/0.96  pred_elim_cycles:                       10
% 1.79/0.96  merged_defs:                            10
% 1.79/0.96  merged_defs_ncl:                        0
% 1.79/0.96  bin_hyper_res:                          10
% 1.79/0.96  prep_cycles:                            4
% 1.79/0.96  pred_elim_time:                         0.011
% 1.79/0.96  splitting_time:                         0.
% 1.79/0.96  sem_filter_time:                        0.
% 1.79/0.96  monotx_time:                            0.
% 1.79/0.96  subtype_inf_time:                       0.
% 1.79/0.96  
% 1.79/0.96  ------ Problem properties
% 1.79/0.96  
% 1.79/0.96  clauses:                                16
% 1.79/0.96  conjectures:                            2
% 1.79/0.96  epr:                                    1
% 1.79/0.96  horn:                                   13
% 1.79/0.96  ground:                                 4
% 1.79/0.96  unary:                                  3
% 1.79/0.96  binary:                                 8
% 1.79/0.96  lits:                                   34
% 1.79/0.96  lits_eq:                                6
% 1.79/0.96  fd_pure:                                0
% 1.79/0.96  fd_pseudo:                              0
% 1.79/0.96  fd_cond:                                0
% 1.79/0.96  fd_pseudo_cond:                         2
% 1.79/0.96  ac_symbols:                             0
% 1.79/0.96  
% 1.79/0.96  ------ Propositional Solver
% 1.79/0.96  
% 1.79/0.96  prop_solver_calls:                      26
% 1.79/0.96  prop_fast_solver_calls:                 665
% 1.79/0.96  smt_solver_calls:                       0
% 1.79/0.96  smt_fast_solver_calls:                  0
% 1.79/0.96  prop_num_of_clauses:                    859
% 1.79/0.96  prop_preprocess_simplified:             3519
% 1.79/0.96  prop_fo_subsumed:                       18
% 1.79/0.96  prop_solver_time:                       0.
% 1.79/0.96  smt_solver_time:                        0.
% 1.79/0.96  smt_fast_solver_time:                   0.
% 1.79/0.96  prop_fast_solver_time:                  0.
% 1.79/0.96  prop_unsat_core_time:                   0.
% 1.79/0.96  
% 1.79/0.96  ------ QBF
% 1.79/0.96  
% 1.79/0.96  qbf_q_res:                              0
% 1.79/0.96  qbf_num_tautologies:                    0
% 1.79/0.96  qbf_prep_cycles:                        0
% 1.79/0.96  
% 1.79/0.96  ------ BMC1
% 1.79/0.96  
% 1.79/0.96  bmc1_current_bound:                     -1
% 1.79/0.96  bmc1_last_solved_bound:                 -1
% 1.79/0.96  bmc1_unsat_core_size:                   -1
% 1.79/0.96  bmc1_unsat_core_parents_size:           -1
% 1.79/0.96  bmc1_merge_next_fun:                    0
% 1.79/0.96  bmc1_unsat_core_clauses_time:           0.
% 1.79/0.96  
% 1.79/0.96  ------ Instantiation
% 1.79/0.96  
% 1.79/0.96  inst_num_of_clauses:                    214
% 1.79/0.96  inst_num_in_passive:                    14
% 1.79/0.96  inst_num_in_active:                     102
% 1.79/0.96  inst_num_in_unprocessed:                98
% 1.79/0.96  inst_num_of_loops:                      120
% 1.79/0.96  inst_num_of_learning_restarts:          0
% 1.79/0.96  inst_num_moves_active_passive:          16
% 1.79/0.96  inst_lit_activity:                      0
% 1.79/0.96  inst_lit_activity_moves:                0
% 1.79/0.96  inst_num_tautologies:                   0
% 1.79/0.96  inst_num_prop_implied:                  0
% 1.79/0.96  inst_num_existing_simplified:           0
% 1.79/0.96  inst_num_eq_res_simplified:             0
% 1.79/0.96  inst_num_child_elim:                    0
% 1.79/0.96  inst_num_of_dismatching_blockings:      43
% 1.79/0.96  inst_num_of_non_proper_insts:           196
% 1.79/0.96  inst_num_of_duplicates:                 0
% 1.79/0.96  inst_inst_num_from_inst_to_res:         0
% 1.79/0.96  inst_dismatching_checking_time:         0.
% 1.79/0.96  
% 1.79/0.96  ------ Resolution
% 1.79/0.96  
% 1.79/0.96  res_num_of_clauses:                     0
% 1.79/0.96  res_num_in_passive:                     0
% 1.79/0.96  res_num_in_active:                      0
% 1.79/0.96  res_num_of_loops:                       97
% 1.79/0.96  res_forward_subset_subsumed:            21
% 1.79/0.96  res_backward_subset_subsumed:           0
% 1.79/0.96  res_forward_subsumed:                   0
% 1.79/0.96  res_backward_subsumed:                  0
% 1.79/0.96  res_forward_subsumption_resolution:     0
% 1.79/0.96  res_backward_subsumption_resolution:    0
% 1.79/0.96  res_clause_to_clause_subsumption:       99
% 1.79/0.96  res_orphan_elimination:                 0
% 1.79/0.96  res_tautology_del:                      44
% 1.79/0.96  res_num_eq_res_simplified:              0
% 1.79/0.96  res_num_sel_changes:                    0
% 1.79/0.96  res_moves_from_active_to_pass:          0
% 1.79/0.96  
% 1.79/0.96  ------ Superposition
% 1.79/0.96  
% 1.79/0.96  sup_time_total:                         0.
% 1.79/0.96  sup_time_generating:                    0.
% 1.79/0.96  sup_time_sim_full:                      0.
% 1.79/0.96  sup_time_sim_immed:                     0.
% 1.79/0.96  
% 1.79/0.96  sup_num_of_clauses:                     30
% 1.79/0.96  sup_num_in_active:                      22
% 1.79/0.96  sup_num_in_passive:                     8
% 1.79/0.96  sup_num_of_loops:                       22
% 1.79/0.96  sup_fw_superposition:                   11
% 1.79/0.96  sup_bw_superposition:                   6
% 1.79/0.96  sup_immediate_simplified:               1
% 1.79/0.96  sup_given_eliminated:                   0
% 1.79/0.96  comparisons_done:                       0
% 1.79/0.96  comparisons_avoided:                    2
% 1.79/0.96  
% 1.79/0.96  ------ Simplifications
% 1.79/0.96  
% 1.79/0.96  
% 1.79/0.96  sim_fw_subset_subsumed:                 1
% 1.79/0.96  sim_bw_subset_subsumed:                 2
% 1.79/0.96  sim_fw_subsumed:                        0
% 1.79/0.96  sim_bw_subsumed:                        0
% 1.79/0.96  sim_fw_subsumption_res:                 0
% 1.79/0.96  sim_bw_subsumption_res:                 0
% 1.79/0.96  sim_tautology_del:                      2
% 1.79/0.96  sim_eq_tautology_del:                   1
% 1.79/0.96  sim_eq_res_simp:                        0
% 1.79/0.96  sim_fw_demodulated:                     0
% 1.79/0.96  sim_bw_demodulated:                     0
% 1.79/0.96  sim_light_normalised:                   2
% 1.79/0.96  sim_joinable_taut:                      0
% 1.79/0.96  sim_joinable_simp:                      0
% 1.79/0.96  sim_ac_normalised:                      0
% 1.79/0.96  sim_smt_subsumption:                    0
% 1.79/0.96  
%------------------------------------------------------------------------------
