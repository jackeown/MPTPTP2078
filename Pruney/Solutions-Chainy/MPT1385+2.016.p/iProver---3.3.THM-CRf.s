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
% DateTime   : Thu Dec  3 12:18:30 EST 2020

% Result     : Theorem 1.15s
% Output     : CNFRefutation 1.15s
% Verified   : 
% Statistics : Number of formulae       :  154 (1869 expanded)
%              Number of clauses        :  106 ( 481 expanded)
%              Number of leaves         :   15 ( 487 expanded)
%              Depth                    :   25
%              Number of atoms          :  584 (12234 expanded)
%              Number of equality atoms :  116 ( 309 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m2_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
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
    inference(negated_conjecture,[],[f8])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ m1_connsp_2(X2,X0,X1)
            | ~ m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) )
          & ( m1_connsp_2(X2,X0,X1)
            | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ~ m1_connsp_2(sK2,X0,X1)
          | ~ m2_connsp_2(sK2,X0,k6_domain_1(u1_struct_0(X0),X1)) )
        & ( m1_connsp_2(sK2,X0,X1)
          | m2_connsp_2(sK2,X0,k6_domain_1(u1_struct_0(X0),X1)) )
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
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
            ( ( ~ m1_connsp_2(X2,X0,sK1)
              | ~ m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),sK1)) )
            & ( m1_connsp_2(X2,X0,sK1)
              | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),sK1)) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK1,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
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
              ( ( ~ m1_connsp_2(X2,sK0,X1)
                | ~ m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),X1)) )
              & ( m1_connsp_2(X2,sK0,X1)
                | m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),X1)) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ( ~ m1_connsp_2(sK2,sK0,sK1)
      | ~ m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )
    & ( m1_connsp_2(sK2,sK0,sK1)
      | m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f30,f29,f28])).

fof(f44,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f43,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f48,plain,
    ( ~ m1_connsp_2(sK2,sK0,sK1)
    | ~ m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) ),
    inference(cnf_transformation,[],[f31])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f42,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f45,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f31])).

fof(f46,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f31])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f34,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f12,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( m2_connsp_2(X2,X0,X1)
      | ~ r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f47,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) ),
    inference(cnf_transformation,[],[f31])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_1,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_127,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(k1_tarski(X0),X1) ),
    inference(prop_impl,[status(thm)],[c_1])).

cnf(c_9,plain,
    ( ~ m2_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_14,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_404,plain,
    ( ~ m2_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_14])).

cnf(c_405,plain,
    ( ~ m2_connsp_2(X0,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X1,k1_tops_1(sK0,X0))
    | ~ v2_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_404])).

cnf(c_15,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_409,plain,
    ( r1_tarski(X1,k1_tops_1(sK0,X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m2_connsp_2(X0,sK0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_405,c_15])).

cnf(c_410,plain,
    ( ~ m2_connsp_2(X0,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X1,k1_tops_1(sK0,X0)) ),
    inference(renaming,[status(thm)],[c_409])).

cnf(c_482,plain,
    ( ~ m2_connsp_2(X0,sK0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(X2,X3)
    | k1_tops_1(sK0,X0) != X3
    | k1_tarski(X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_127,c_410])).

cnf(c_483,plain,
    ( ~ m2_connsp_2(X0,sK0,k1_tarski(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tarski(X1),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(X1,k1_tops_1(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_482])).

cnf(c_10,negated_conjecture,
    ( ~ m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))
    | ~ m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_131,plain,
    ( ~ m1_connsp_2(sK2,sK0,sK1)
    | ~ m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) ),
    inference(prop_impl,[status(thm)],[c_10])).

cnf(c_132,plain,
    ( ~ m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))
    | ~ m1_connsp_2(sK2,sK0,sK1) ),
    inference(renaming,[status(thm)],[c_131])).

cnf(c_6,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_16,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_338,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_16])).

cnf(c_339,plain,
    ( m1_connsp_2(X0,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ r2_hidden(X1,k1_tops_1(sK0,X0))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_338])).

cnf(c_343,plain,
    ( m1_connsp_2(X0,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ r2_hidden(X1,k1_tops_1(sK0,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_339,c_15,c_14])).

cnf(c_526,plain,
    ( ~ m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ r2_hidden(X1,k1_tops_1(sK0,X0))
    | sK1 != X1
    | sK0 != sK0
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_132,c_343])).

cnf(c_527,plain,
    ( ~ m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(unflattening,[status(thm)],[c_526])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_529,plain,
    ( ~ m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_527,c_13,c_12])).

cnf(c_548,plain,
    ( ~ m2_connsp_2(X0,sK0,k1_tarski(X1))
    | ~ m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tarski(X1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) != k1_tops_1(sK0,sK2)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_483,c_529])).

cnf(c_549,plain,
    ( ~ m2_connsp_2(X0,sK0,k1_tarski(sK1))
    | ~ m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) != k1_tops_1(sK0,sK2) ),
    inference(unflattening,[status(thm)],[c_548])).

cnf(c_651,plain,
    ( ~ m2_connsp_2(X0_46,sK0,k1_tarski(sK1))
    | ~ m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0_46) != k1_tops_1(sK0,sK2) ),
    inference(subtyping,[status(esa)],[c_549])).

cnf(c_656,plain,
    ( ~ m2_connsp_2(X0_46,sK0,k1_tarski(sK1))
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0_46) != k1_tops_1(sK0,sK2)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_651])).

cnf(c_833,plain,
    ( k1_tops_1(sK0,X0_46) != k1_tops_1(sK0,sK2)
    | m2_connsp_2(X0_46,sK0,k1_tarski(sK1)) != iProver_top
    | m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_656])).

cnf(c_20,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_21,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_665,plain,
    ( X0_46 != X1_46
    | k1_tarski(X0_46) = k1_tarski(X1_46) ),
    theory(equality)).

cnf(c_670,plain,
    ( k1_tarski(sK1) = k1_tarski(sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_665])).

cnf(c_661,plain,
    ( X0_46 = X0_46 ),
    theory(equality)).

cnf(c_676,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_661])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_2,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_3,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_241,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_2,c_3])).

cnf(c_303,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_pre_topc(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_241,c_16])).

cnf(c_304,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_303])).

cnf(c_43,plain,
    ( v2_struct_0(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ l1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_46,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_306,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_304,c_16,c_14,c_43,c_46])).

cnf(c_374,plain,
    ( ~ m1_subset_1(X0,X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0)
    | u1_struct_0(sK0) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_306])).

cnf(c_375,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | k6_domain_1(u1_struct_0(sK0),X0) = k1_tarski(X0) ),
    inference(unflattening,[status(thm)],[c_374])).

cnf(c_653,plain,
    ( ~ m1_subset_1(X0_46,u1_struct_0(sK0))
    | k6_domain_1(u1_struct_0(sK0),X0_46) = k1_tarski(X0_46) ),
    inference(subtyping,[status(esa)],[c_375])).

cnf(c_681,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) ),
    inference(instantiation,[status(thm)],[c_653])).

cnf(c_687,plain,
    ( k1_tops_1(sK0,X0_46) != k1_tops_1(sK0,sK2)
    | m2_connsp_2(X0_46,sK0,k1_tarski(sK1)) != iProver_top
    | m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_656])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_129,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k1_tarski(X0),X1) ),
    inference(prop_impl,[status(thm)],[c_0])).

cnf(c_8,plain,
    ( m2_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_428,plain,
    ( m2_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_14])).

cnf(c_429,plain,
    ( m2_connsp_2(X0,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X1,k1_tops_1(sK0,X0))
    | ~ v2_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_428])).

cnf(c_433,plain,
    ( ~ r1_tarski(X1,k1_tops_1(sK0,X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m2_connsp_2(X0,sK0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_429,c_15])).

cnf(c_434,plain,
    ( m2_connsp_2(X0,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X1,k1_tops_1(sK0,X0)) ),
    inference(renaming,[status(thm)],[c_433])).

cnf(c_464,plain,
    ( m2_connsp_2(X0,sK0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(X2,X3)
    | k1_tops_1(sK0,X0) != X3
    | k1_tarski(X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_129,c_434])).

cnf(c_465,plain,
    ( m2_connsp_2(X0,sK0,k1_tarski(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tarski(X1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(X1,k1_tops_1(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_464])).

cnf(c_11,negated_conjecture,
    ( m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_133,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) ),
    inference(prop_impl,[status(thm)],[c_11])).

cnf(c_134,plain,
    ( m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(renaming,[status(thm)],[c_133])).

cnf(c_7,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_314,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_16])).

cnf(c_315,plain,
    ( ~ m1_connsp_2(X0,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | r2_hidden(X1,k1_tops_1(sK0,X0))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_314])).

cnf(c_319,plain,
    ( ~ m1_connsp_2(X0,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | r2_hidden(X1,k1_tops_1(sK0,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_315,c_15,c_14])).

cnf(c_512,plain,
    ( m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | r2_hidden(X1,k1_tops_1(sK0,X0))
    | sK1 != X1
    | sK0 != sK0
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_134,c_319])).

cnf(c_513,plain,
    ( m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(unflattening,[status(thm)],[c_512])).

cnf(c_515,plain,
    ( m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_513,c_13,c_12])).

cnf(c_569,plain,
    ( m2_connsp_2(X0,sK0,k1_tarski(X1))
    | m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tarski(X1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) != k1_tops_1(sK0,sK2)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_465,c_515])).

cnf(c_570,plain,
    ( m2_connsp_2(X0,sK0,k1_tarski(sK1))
    | m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) != k1_tops_1(sK0,sK2) ),
    inference(unflattening,[status(thm)],[c_569])).

cnf(c_650,plain,
    ( m2_connsp_2(X0_46,sK0,k1_tarski(sK1))
    | m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0_46) != k1_tops_1(sK0,sK2) ),
    inference(subtyping,[status(esa)],[c_570])).

cnf(c_659,plain,
    ( m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_650])).

cnf(c_690,plain,
    ( m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) = iProver_top
    | m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | sP1_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_659])).

cnf(c_936,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_661])).

cnf(c_654,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_829,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_654])).

cnf(c_830,plain,
    ( k6_domain_1(u1_struct_0(sK0),X0_46) = k1_tarski(X0_46)
    | m1_subset_1(X0_46,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_653])).

cnf(c_925,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) ),
    inference(superposition,[status(thm)],[c_829,c_830])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_386,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | u1_struct_0(sK0) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_306])).

cnf(c_387,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | m1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_386])).

cnf(c_652,plain,
    ( ~ m1_subset_1(X0_46,u1_struct_0(sK0))
    | m1_subset_1(k6_domain_1(u1_struct_0(sK0),X0_46),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_387])).

cnf(c_831,plain,
    ( m1_subset_1(X0_46,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k6_domain_1(u1_struct_0(sK0),X0_46),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_652])).

cnf(c_968,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_925,c_831])).

cnf(c_663,plain,
    ( X0_46 != X1_46
    | X2_46 != X1_46
    | X2_46 = X0_46 ),
    theory(equality)).

cnf(c_928,plain,
    ( X0_46 != X1_46
    | X0_46 = k6_domain_1(u1_struct_0(sK0),X2_46)
    | k6_domain_1(u1_struct_0(sK0),X2_46) != X1_46 ),
    inference(instantiation,[status(thm)],[c_663])).

cnf(c_947,plain,
    ( X0_46 = k6_domain_1(u1_struct_0(sK0),X1_46)
    | X0_46 != k1_tarski(X1_46)
    | k6_domain_1(u1_struct_0(sK0),X1_46) != k1_tarski(X1_46) ),
    inference(instantiation,[status(thm)],[c_928])).

cnf(c_983,plain,
    ( k6_domain_1(u1_struct_0(sK0),X0_46) != k1_tarski(X0_46)
    | k1_tarski(X0_46) = k6_domain_1(u1_struct_0(sK0),X0_46)
    | k1_tarski(X0_46) != k1_tarski(X0_46) ),
    inference(instantiation,[status(thm)],[c_947])).

cnf(c_985,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) != k1_tarski(sK1)
    | k1_tarski(sK1) = k6_domain_1(u1_struct_0(sK0),sK1)
    | k1_tarski(sK1) != k1_tarski(sK1) ),
    inference(instantiation,[status(thm)],[c_983])).

cnf(c_669,plain,
    ( ~ m2_connsp_2(X0_46,X0_47,X1_46)
    | m2_connsp_2(X2_46,X0_47,X3_46)
    | X2_46 != X0_46
    | X3_46 != X1_46 ),
    theory(equality)).

cnf(c_911,plain,
    ( m2_connsp_2(X0_46,sK0,X1_46)
    | ~ m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))
    | X1_46 != k6_domain_1(u1_struct_0(sK0),sK1)
    | X0_46 != sK2 ),
    inference(instantiation,[status(thm)],[c_669])).

cnf(c_935,plain,
    ( m2_connsp_2(sK2,sK0,X0_46)
    | ~ m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))
    | X0_46 != k6_domain_1(u1_struct_0(sK0),sK1)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_911])).

cnf(c_1001,plain,
    ( ~ m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))
    | m2_connsp_2(sK2,sK0,k1_tarski(sK1))
    | k1_tarski(sK1) != k6_domain_1(u1_struct_0(sK0),sK1)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_935])).

cnf(c_1002,plain,
    ( k1_tarski(sK1) != k6_domain_1(u1_struct_0(sK0),sK1)
    | sK2 != sK2
    | m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != iProver_top
    | m2_connsp_2(sK2,sK0,k1_tarski(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1001])).

cnf(c_657,plain,
    ( ~ m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_651])).

cnf(c_832,plain,
    ( m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != iProver_top
    | m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_657])).

cnf(c_686,plain,
    ( m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != iProver_top
    | m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_657])).

cnf(c_1023,plain,
    ( m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_832,c_20,c_686,c_968])).

cnf(c_1027,plain,
    ( m2_connsp_2(sK2,sK0,k1_tarski(sK1)) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1023,c_925])).

cnf(c_658,plain,
    ( m2_connsp_2(X0_46,sK0,k1_tarski(sK1))
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0_46) != k1_tops_1(sK0,sK2)
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_650])).

cnf(c_835,plain,
    ( k1_tops_1(sK0,X0_46) != k1_tops_1(sK0,sK2)
    | m2_connsp_2(X0_46,sK0,k1_tarski(sK1)) = iProver_top
    | m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_658])).

cnf(c_1036,plain,
    ( m2_connsp_2(sK2,sK0,k1_tarski(sK1)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_835])).

cnf(c_1078,plain,
    ( m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m2_connsp_2(X0_46,sK0,k1_tarski(sK1)) != iProver_top
    | k1_tops_1(sK0,X0_46) != k1_tops_1(sK0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_833,c_13,c_20,c_21,c_670,c_676,c_681,c_687,c_690,c_936,c_968,c_985,c_1002,c_1027,c_1036])).

cnf(c_1079,plain,
    ( k1_tops_1(sK0,X0_46) != k1_tops_1(sK0,sK2)
    | m2_connsp_2(X0_46,sK0,k1_tarski(sK1)) != iProver_top
    | m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1078])).

cnf(c_1087,plain,
    ( m2_connsp_2(sK2,sK0,k1_tarski(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1079])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1087,c_1036,c_1002,c_985,c_968,c_936,c_690,c_681,c_676,c_670,c_21,c_20,c_13])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:40:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.03/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.03/1.00  
% 1.03/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.03/1.00  
% 1.03/1.00  ------  iProver source info
% 1.03/1.00  
% 1.03/1.00  git: date: 2020-06-30 10:37:57 +0100
% 1.03/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.03/1.00  git: non_committed_changes: false
% 1.03/1.00  git: last_make_outside_of_git: false
% 1.03/1.00  
% 1.03/1.00  ------ 
% 1.03/1.00  
% 1.03/1.00  ------ Input Options
% 1.03/1.00  
% 1.03/1.00  --out_options                           all
% 1.03/1.00  --tptp_safe_out                         true
% 1.03/1.00  --problem_path                          ""
% 1.03/1.00  --include_path                          ""
% 1.03/1.00  --clausifier                            res/vclausify_rel
% 1.03/1.00  --clausifier_options                    --mode clausify
% 1.03/1.00  --stdin                                 false
% 1.03/1.00  --stats_out                             all
% 1.03/1.00  
% 1.03/1.00  ------ General Options
% 1.03/1.00  
% 1.03/1.00  --fof                                   false
% 1.03/1.00  --time_out_real                         305.
% 1.03/1.00  --time_out_virtual                      -1.
% 1.03/1.00  --symbol_type_check                     false
% 1.03/1.00  --clausify_out                          false
% 1.03/1.00  --sig_cnt_out                           false
% 1.03/1.00  --trig_cnt_out                          false
% 1.03/1.00  --trig_cnt_out_tolerance                1.
% 1.03/1.00  --trig_cnt_out_sk_spl                   false
% 1.03/1.00  --abstr_cl_out                          false
% 1.03/1.00  
% 1.03/1.00  ------ Global Options
% 1.03/1.00  
% 1.03/1.00  --schedule                              default
% 1.03/1.00  --add_important_lit                     false
% 1.03/1.00  --prop_solver_per_cl                    1000
% 1.03/1.00  --min_unsat_core                        false
% 1.03/1.00  --soft_assumptions                      false
% 1.03/1.00  --soft_lemma_size                       3
% 1.03/1.00  --prop_impl_unit_size                   0
% 1.03/1.00  --prop_impl_unit                        []
% 1.03/1.00  --share_sel_clauses                     true
% 1.03/1.00  --reset_solvers                         false
% 1.03/1.00  --bc_imp_inh                            [conj_cone]
% 1.03/1.00  --conj_cone_tolerance                   3.
% 1.03/1.00  --extra_neg_conj                        none
% 1.03/1.00  --large_theory_mode                     true
% 1.03/1.00  --prolific_symb_bound                   200
% 1.03/1.00  --lt_threshold                          2000
% 1.03/1.00  --clause_weak_htbl                      true
% 1.03/1.00  --gc_record_bc_elim                     false
% 1.03/1.00  
% 1.03/1.00  ------ Preprocessing Options
% 1.03/1.00  
% 1.03/1.00  --preprocessing_flag                    true
% 1.03/1.00  --time_out_prep_mult                    0.1
% 1.03/1.00  --splitting_mode                        input
% 1.03/1.00  --splitting_grd                         true
% 1.03/1.00  --splitting_cvd                         false
% 1.03/1.00  --splitting_cvd_svl                     false
% 1.03/1.00  --splitting_nvd                         32
% 1.03/1.00  --sub_typing                            true
% 1.03/1.00  --prep_gs_sim                           true
% 1.03/1.00  --prep_unflatten                        true
% 1.03/1.00  --prep_res_sim                          true
% 1.03/1.00  --prep_upred                            true
% 1.03/1.00  --prep_sem_filter                       exhaustive
% 1.03/1.00  --prep_sem_filter_out                   false
% 1.03/1.00  --pred_elim                             true
% 1.03/1.00  --res_sim_input                         true
% 1.03/1.00  --eq_ax_congr_red                       true
% 1.03/1.00  --pure_diseq_elim                       true
% 1.03/1.00  --brand_transform                       false
% 1.03/1.00  --non_eq_to_eq                          false
% 1.03/1.00  --prep_def_merge                        true
% 1.03/1.00  --prep_def_merge_prop_impl              false
% 1.03/1.00  --prep_def_merge_mbd                    true
% 1.03/1.00  --prep_def_merge_tr_red                 false
% 1.03/1.00  --prep_def_merge_tr_cl                  false
% 1.03/1.00  --smt_preprocessing                     true
% 1.03/1.00  --smt_ac_axioms                         fast
% 1.03/1.00  --preprocessed_out                      false
% 1.03/1.00  --preprocessed_stats                    false
% 1.03/1.00  
% 1.03/1.00  ------ Abstraction refinement Options
% 1.03/1.00  
% 1.03/1.00  --abstr_ref                             []
% 1.03/1.00  --abstr_ref_prep                        false
% 1.03/1.00  --abstr_ref_until_sat                   false
% 1.03/1.00  --abstr_ref_sig_restrict                funpre
% 1.03/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.03/1.00  --abstr_ref_under                       []
% 1.03/1.00  
% 1.03/1.00  ------ SAT Options
% 1.03/1.00  
% 1.03/1.00  --sat_mode                              false
% 1.03/1.00  --sat_fm_restart_options                ""
% 1.03/1.00  --sat_gr_def                            false
% 1.03/1.00  --sat_epr_types                         true
% 1.03/1.00  --sat_non_cyclic_types                  false
% 1.03/1.00  --sat_finite_models                     false
% 1.03/1.00  --sat_fm_lemmas                         false
% 1.03/1.00  --sat_fm_prep                           false
% 1.03/1.00  --sat_fm_uc_incr                        true
% 1.03/1.00  --sat_out_model                         small
% 1.03/1.00  --sat_out_clauses                       false
% 1.03/1.00  
% 1.03/1.00  ------ QBF Options
% 1.03/1.00  
% 1.03/1.00  --qbf_mode                              false
% 1.03/1.00  --qbf_elim_univ                         false
% 1.03/1.00  --qbf_dom_inst                          none
% 1.03/1.00  --qbf_dom_pre_inst                      false
% 1.03/1.00  --qbf_sk_in                             false
% 1.03/1.00  --qbf_pred_elim                         true
% 1.03/1.00  --qbf_split                             512
% 1.03/1.00  
% 1.03/1.00  ------ BMC1 Options
% 1.03/1.00  
% 1.03/1.00  --bmc1_incremental                      false
% 1.03/1.00  --bmc1_axioms                           reachable_all
% 1.03/1.00  --bmc1_min_bound                        0
% 1.03/1.00  --bmc1_max_bound                        -1
% 1.03/1.00  --bmc1_max_bound_default                -1
% 1.03/1.00  --bmc1_symbol_reachability              true
% 1.03/1.00  --bmc1_property_lemmas                  false
% 1.03/1.00  --bmc1_k_induction                      false
% 1.03/1.00  --bmc1_non_equiv_states                 false
% 1.03/1.00  --bmc1_deadlock                         false
% 1.03/1.00  --bmc1_ucm                              false
% 1.03/1.00  --bmc1_add_unsat_core                   none
% 1.03/1.00  --bmc1_unsat_core_children              false
% 1.03/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.03/1.00  --bmc1_out_stat                         full
% 1.03/1.00  --bmc1_ground_init                      false
% 1.03/1.00  --bmc1_pre_inst_next_state              false
% 1.03/1.00  --bmc1_pre_inst_state                   false
% 1.03/1.00  --bmc1_pre_inst_reach_state             false
% 1.03/1.00  --bmc1_out_unsat_core                   false
% 1.03/1.00  --bmc1_aig_witness_out                  false
% 1.03/1.00  --bmc1_verbose                          false
% 1.03/1.00  --bmc1_dump_clauses_tptp                false
% 1.03/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.03/1.00  --bmc1_dump_file                        -
% 1.03/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.03/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.03/1.00  --bmc1_ucm_extend_mode                  1
% 1.03/1.00  --bmc1_ucm_init_mode                    2
% 1.03/1.00  --bmc1_ucm_cone_mode                    none
% 1.03/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.03/1.00  --bmc1_ucm_relax_model                  4
% 1.03/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.03/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.03/1.00  --bmc1_ucm_layered_model                none
% 1.03/1.00  --bmc1_ucm_max_lemma_size               10
% 1.03/1.00  
% 1.03/1.00  ------ AIG Options
% 1.03/1.00  
% 1.03/1.00  --aig_mode                              false
% 1.03/1.00  
% 1.03/1.00  ------ Instantiation Options
% 1.03/1.00  
% 1.03/1.00  --instantiation_flag                    true
% 1.03/1.00  --inst_sos_flag                         false
% 1.03/1.00  --inst_sos_phase                        true
% 1.03/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.03/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.03/1.00  --inst_lit_sel_side                     num_symb
% 1.03/1.00  --inst_solver_per_active                1400
% 1.03/1.00  --inst_solver_calls_frac                1.
% 1.03/1.00  --inst_passive_queue_type               priority_queues
% 1.03/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.03/1.00  --inst_passive_queues_freq              [25;2]
% 1.03/1.00  --inst_dismatching                      true
% 1.03/1.00  --inst_eager_unprocessed_to_passive     true
% 1.03/1.00  --inst_prop_sim_given                   true
% 1.03/1.00  --inst_prop_sim_new                     false
% 1.03/1.00  --inst_subs_new                         false
% 1.03/1.00  --inst_eq_res_simp                      false
% 1.03/1.00  --inst_subs_given                       false
% 1.03/1.00  --inst_orphan_elimination               true
% 1.03/1.00  --inst_learning_loop_flag               true
% 1.03/1.00  --inst_learning_start                   3000
% 1.03/1.00  --inst_learning_factor                  2
% 1.03/1.00  --inst_start_prop_sim_after_learn       3
% 1.03/1.00  --inst_sel_renew                        solver
% 1.03/1.00  --inst_lit_activity_flag                true
% 1.03/1.00  --inst_restr_to_given                   false
% 1.03/1.00  --inst_activity_threshold               500
% 1.03/1.00  --inst_out_proof                        true
% 1.03/1.00  
% 1.03/1.00  ------ Resolution Options
% 1.03/1.00  
% 1.03/1.00  --resolution_flag                       true
% 1.03/1.00  --res_lit_sel                           adaptive
% 1.03/1.00  --res_lit_sel_side                      none
% 1.03/1.00  --res_ordering                          kbo
% 1.03/1.00  --res_to_prop_solver                    active
% 1.03/1.00  --res_prop_simpl_new                    false
% 1.03/1.00  --res_prop_simpl_given                  true
% 1.03/1.00  --res_passive_queue_type                priority_queues
% 1.03/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.03/1.00  --res_passive_queues_freq               [15;5]
% 1.03/1.00  --res_forward_subs                      full
% 1.03/1.00  --res_backward_subs                     full
% 1.03/1.00  --res_forward_subs_resolution           true
% 1.03/1.00  --res_backward_subs_resolution          true
% 1.03/1.00  --res_orphan_elimination                true
% 1.03/1.00  --res_time_limit                        2.
% 1.03/1.00  --res_out_proof                         true
% 1.03/1.00  
% 1.03/1.00  ------ Superposition Options
% 1.03/1.00  
% 1.03/1.00  --superposition_flag                    true
% 1.03/1.00  --sup_passive_queue_type                priority_queues
% 1.03/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.03/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.03/1.00  --demod_completeness_check              fast
% 1.03/1.00  --demod_use_ground                      true
% 1.03/1.00  --sup_to_prop_solver                    passive
% 1.03/1.00  --sup_prop_simpl_new                    true
% 1.03/1.00  --sup_prop_simpl_given                  true
% 1.03/1.00  --sup_fun_splitting                     false
% 1.03/1.00  --sup_smt_interval                      50000
% 1.03/1.00  
% 1.03/1.00  ------ Superposition Simplification Setup
% 1.03/1.00  
% 1.03/1.00  --sup_indices_passive                   []
% 1.03/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.03/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.03/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.03/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.03/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.03/1.00  --sup_full_bw                           [BwDemod]
% 1.03/1.00  --sup_immed_triv                        [TrivRules]
% 1.03/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.03/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.03/1.00  --sup_immed_bw_main                     []
% 1.03/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.03/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.03/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.03/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.03/1.00  
% 1.03/1.00  ------ Combination Options
% 1.03/1.00  
% 1.03/1.00  --comb_res_mult                         3
% 1.03/1.00  --comb_sup_mult                         2
% 1.03/1.00  --comb_inst_mult                        10
% 1.03/1.00  
% 1.03/1.00  ------ Debug Options
% 1.03/1.00  
% 1.03/1.00  --dbg_backtrace                         false
% 1.03/1.00  --dbg_dump_prop_clauses                 false
% 1.03/1.00  --dbg_dump_prop_clauses_file            -
% 1.03/1.00  --dbg_out_stat                          false
% 1.03/1.00  ------ Parsing...
% 1.03/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.03/1.00  
% 1.03/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe_e 
% 1.03/1.00  
% 1.03/1.00  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.03/1.00  
% 1.03/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.03/1.00  ------ Proving...
% 1.03/1.00  ------ Problem Properties 
% 1.03/1.00  
% 1.03/1.00  
% 1.03/1.00  clauses                                 8
% 1.03/1.00  conjectures                             2
% 1.03/1.00  EPR                                     0
% 1.03/1.00  Horn                                    7
% 1.03/1.00  unary                                   2
% 1.03/1.00  binary                                  2
% 1.03/1.00  lits                                    20
% 1.03/1.00  lits eq                                 3
% 1.03/1.00  fd_pure                                 0
% 1.03/1.00  fd_pseudo                               0
% 1.03/1.00  fd_cond                                 0
% 1.03/1.00  fd_pseudo_cond                          0
% 1.03/1.00  AC symbols                              0
% 1.03/1.00  
% 1.03/1.00  ------ Schedule dynamic 5 is on 
% 1.03/1.00  
% 1.03/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.03/1.00  
% 1.03/1.00  
% 1.03/1.00  ------ 
% 1.03/1.00  Current options:
% 1.03/1.00  ------ 
% 1.03/1.00  
% 1.03/1.00  ------ Input Options
% 1.03/1.00  
% 1.03/1.00  --out_options                           all
% 1.03/1.00  --tptp_safe_out                         true
% 1.03/1.00  --problem_path                          ""
% 1.03/1.00  --include_path                          ""
% 1.03/1.00  --clausifier                            res/vclausify_rel
% 1.03/1.00  --clausifier_options                    --mode clausify
% 1.03/1.00  --stdin                                 false
% 1.03/1.00  --stats_out                             all
% 1.03/1.00  
% 1.03/1.00  ------ General Options
% 1.03/1.00  
% 1.03/1.00  --fof                                   false
% 1.03/1.00  --time_out_real                         305.
% 1.03/1.00  --time_out_virtual                      -1.
% 1.03/1.00  --symbol_type_check                     false
% 1.03/1.00  --clausify_out                          false
% 1.03/1.00  --sig_cnt_out                           false
% 1.03/1.00  --trig_cnt_out                          false
% 1.03/1.00  --trig_cnt_out_tolerance                1.
% 1.03/1.00  --trig_cnt_out_sk_spl                   false
% 1.03/1.00  --abstr_cl_out                          false
% 1.03/1.00  
% 1.03/1.00  ------ Global Options
% 1.03/1.00  
% 1.03/1.00  --schedule                              default
% 1.03/1.00  --add_important_lit                     false
% 1.03/1.00  --prop_solver_per_cl                    1000
% 1.03/1.00  --min_unsat_core                        false
% 1.03/1.00  --soft_assumptions                      false
% 1.03/1.00  --soft_lemma_size                       3
% 1.03/1.00  --prop_impl_unit_size                   0
% 1.03/1.00  --prop_impl_unit                        []
% 1.03/1.00  --share_sel_clauses                     true
% 1.03/1.00  --reset_solvers                         false
% 1.03/1.00  --bc_imp_inh                            [conj_cone]
% 1.03/1.00  --conj_cone_tolerance                   3.
% 1.03/1.00  --extra_neg_conj                        none
% 1.03/1.00  --large_theory_mode                     true
% 1.03/1.00  --prolific_symb_bound                   200
% 1.03/1.00  --lt_threshold                          2000
% 1.03/1.00  --clause_weak_htbl                      true
% 1.03/1.00  --gc_record_bc_elim                     false
% 1.03/1.00  
% 1.03/1.00  ------ Preprocessing Options
% 1.03/1.00  
% 1.03/1.00  --preprocessing_flag                    true
% 1.03/1.00  --time_out_prep_mult                    0.1
% 1.03/1.00  --splitting_mode                        input
% 1.03/1.00  --splitting_grd                         true
% 1.03/1.00  --splitting_cvd                         false
% 1.03/1.00  --splitting_cvd_svl                     false
% 1.03/1.00  --splitting_nvd                         32
% 1.03/1.00  --sub_typing                            true
% 1.03/1.00  --prep_gs_sim                           true
% 1.03/1.00  --prep_unflatten                        true
% 1.03/1.00  --prep_res_sim                          true
% 1.03/1.00  --prep_upred                            true
% 1.03/1.00  --prep_sem_filter                       exhaustive
% 1.03/1.00  --prep_sem_filter_out                   false
% 1.03/1.00  --pred_elim                             true
% 1.03/1.00  --res_sim_input                         true
% 1.03/1.00  --eq_ax_congr_red                       true
% 1.03/1.00  --pure_diseq_elim                       true
% 1.03/1.00  --brand_transform                       false
% 1.03/1.00  --non_eq_to_eq                          false
% 1.03/1.00  --prep_def_merge                        true
% 1.03/1.00  --prep_def_merge_prop_impl              false
% 1.03/1.00  --prep_def_merge_mbd                    true
% 1.03/1.00  --prep_def_merge_tr_red                 false
% 1.03/1.00  --prep_def_merge_tr_cl                  false
% 1.03/1.00  --smt_preprocessing                     true
% 1.03/1.00  --smt_ac_axioms                         fast
% 1.03/1.00  --preprocessed_out                      false
% 1.03/1.00  --preprocessed_stats                    false
% 1.03/1.00  
% 1.03/1.00  ------ Abstraction refinement Options
% 1.03/1.00  
% 1.03/1.00  --abstr_ref                             []
% 1.03/1.00  --abstr_ref_prep                        false
% 1.03/1.00  --abstr_ref_until_sat                   false
% 1.03/1.00  --abstr_ref_sig_restrict                funpre
% 1.03/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.03/1.00  --abstr_ref_under                       []
% 1.03/1.00  
% 1.03/1.00  ------ SAT Options
% 1.03/1.00  
% 1.03/1.00  --sat_mode                              false
% 1.03/1.00  --sat_fm_restart_options                ""
% 1.03/1.00  --sat_gr_def                            false
% 1.03/1.00  --sat_epr_types                         true
% 1.03/1.00  --sat_non_cyclic_types                  false
% 1.03/1.00  --sat_finite_models                     false
% 1.03/1.00  --sat_fm_lemmas                         false
% 1.03/1.00  --sat_fm_prep                           false
% 1.03/1.00  --sat_fm_uc_incr                        true
% 1.03/1.00  --sat_out_model                         small
% 1.03/1.00  --sat_out_clauses                       false
% 1.03/1.00  
% 1.03/1.00  ------ QBF Options
% 1.03/1.00  
% 1.03/1.00  --qbf_mode                              false
% 1.03/1.00  --qbf_elim_univ                         false
% 1.03/1.00  --qbf_dom_inst                          none
% 1.03/1.00  --qbf_dom_pre_inst                      false
% 1.03/1.00  --qbf_sk_in                             false
% 1.03/1.00  --qbf_pred_elim                         true
% 1.03/1.00  --qbf_split                             512
% 1.03/1.00  
% 1.03/1.00  ------ BMC1 Options
% 1.03/1.00  
% 1.03/1.00  --bmc1_incremental                      false
% 1.03/1.00  --bmc1_axioms                           reachable_all
% 1.03/1.00  --bmc1_min_bound                        0
% 1.03/1.00  --bmc1_max_bound                        -1
% 1.03/1.00  --bmc1_max_bound_default                -1
% 1.03/1.00  --bmc1_symbol_reachability              true
% 1.03/1.00  --bmc1_property_lemmas                  false
% 1.03/1.00  --bmc1_k_induction                      false
% 1.03/1.00  --bmc1_non_equiv_states                 false
% 1.03/1.00  --bmc1_deadlock                         false
% 1.03/1.00  --bmc1_ucm                              false
% 1.03/1.00  --bmc1_add_unsat_core                   none
% 1.03/1.00  --bmc1_unsat_core_children              false
% 1.03/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.03/1.00  --bmc1_out_stat                         full
% 1.03/1.00  --bmc1_ground_init                      false
% 1.03/1.00  --bmc1_pre_inst_next_state              false
% 1.03/1.00  --bmc1_pre_inst_state                   false
% 1.03/1.00  --bmc1_pre_inst_reach_state             false
% 1.03/1.00  --bmc1_out_unsat_core                   false
% 1.03/1.00  --bmc1_aig_witness_out                  false
% 1.03/1.00  --bmc1_verbose                          false
% 1.03/1.00  --bmc1_dump_clauses_tptp                false
% 1.03/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.03/1.00  --bmc1_dump_file                        -
% 1.03/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.03/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.03/1.00  --bmc1_ucm_extend_mode                  1
% 1.15/1.00  --bmc1_ucm_init_mode                    2
% 1.15/1.00  --bmc1_ucm_cone_mode                    none
% 1.15/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.15/1.00  --bmc1_ucm_relax_model                  4
% 1.15/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.15/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.15/1.00  --bmc1_ucm_layered_model                none
% 1.15/1.00  --bmc1_ucm_max_lemma_size               10
% 1.15/1.00  
% 1.15/1.00  ------ AIG Options
% 1.15/1.00  
% 1.15/1.00  --aig_mode                              false
% 1.15/1.00  
% 1.15/1.00  ------ Instantiation Options
% 1.15/1.00  
% 1.15/1.00  --instantiation_flag                    true
% 1.15/1.00  --inst_sos_flag                         false
% 1.15/1.00  --inst_sos_phase                        true
% 1.15/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.15/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.15/1.00  --inst_lit_sel_side                     none
% 1.15/1.00  --inst_solver_per_active                1400
% 1.15/1.00  --inst_solver_calls_frac                1.
% 1.15/1.00  --inst_passive_queue_type               priority_queues
% 1.15/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.15/1.00  --inst_passive_queues_freq              [25;2]
% 1.15/1.00  --inst_dismatching                      true
% 1.15/1.00  --inst_eager_unprocessed_to_passive     true
% 1.15/1.00  --inst_prop_sim_given                   true
% 1.15/1.00  --inst_prop_sim_new                     false
% 1.15/1.00  --inst_subs_new                         false
% 1.15/1.00  --inst_eq_res_simp                      false
% 1.15/1.00  --inst_subs_given                       false
% 1.15/1.00  --inst_orphan_elimination               true
% 1.15/1.00  --inst_learning_loop_flag               true
% 1.15/1.00  --inst_learning_start                   3000
% 1.15/1.00  --inst_learning_factor                  2
% 1.15/1.00  --inst_start_prop_sim_after_learn       3
% 1.15/1.00  --inst_sel_renew                        solver
% 1.15/1.00  --inst_lit_activity_flag                true
% 1.15/1.00  --inst_restr_to_given                   false
% 1.15/1.00  --inst_activity_threshold               500
% 1.15/1.00  --inst_out_proof                        true
% 1.15/1.00  
% 1.15/1.00  ------ Resolution Options
% 1.15/1.00  
% 1.15/1.00  --resolution_flag                       false
% 1.15/1.00  --res_lit_sel                           adaptive
% 1.15/1.00  --res_lit_sel_side                      none
% 1.15/1.00  --res_ordering                          kbo
% 1.15/1.00  --res_to_prop_solver                    active
% 1.15/1.00  --res_prop_simpl_new                    false
% 1.15/1.00  --res_prop_simpl_given                  true
% 1.15/1.00  --res_passive_queue_type                priority_queues
% 1.15/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.15/1.00  --res_passive_queues_freq               [15;5]
% 1.15/1.00  --res_forward_subs                      full
% 1.15/1.00  --res_backward_subs                     full
% 1.15/1.00  --res_forward_subs_resolution           true
% 1.15/1.00  --res_backward_subs_resolution          true
% 1.15/1.00  --res_orphan_elimination                true
% 1.15/1.00  --res_time_limit                        2.
% 1.15/1.00  --res_out_proof                         true
% 1.15/1.00  
% 1.15/1.00  ------ Superposition Options
% 1.15/1.00  
% 1.15/1.00  --superposition_flag                    true
% 1.15/1.00  --sup_passive_queue_type                priority_queues
% 1.15/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.15/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.15/1.00  --demod_completeness_check              fast
% 1.15/1.00  --demod_use_ground                      true
% 1.15/1.00  --sup_to_prop_solver                    passive
% 1.15/1.00  --sup_prop_simpl_new                    true
% 1.15/1.00  --sup_prop_simpl_given                  true
% 1.15/1.00  --sup_fun_splitting                     false
% 1.15/1.00  --sup_smt_interval                      50000
% 1.15/1.00  
% 1.15/1.00  ------ Superposition Simplification Setup
% 1.15/1.00  
% 1.15/1.00  --sup_indices_passive                   []
% 1.15/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.15/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.15/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.15/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.15/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.15/1.00  --sup_full_bw                           [BwDemod]
% 1.15/1.00  --sup_immed_triv                        [TrivRules]
% 1.15/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.15/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.15/1.00  --sup_immed_bw_main                     []
% 1.15/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.15/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.15/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.15/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.15/1.00  
% 1.15/1.00  ------ Combination Options
% 1.15/1.00  
% 1.15/1.00  --comb_res_mult                         3
% 1.15/1.00  --comb_sup_mult                         2
% 1.15/1.00  --comb_inst_mult                        10
% 1.15/1.00  
% 1.15/1.00  ------ Debug Options
% 1.15/1.00  
% 1.15/1.00  --dbg_backtrace                         false
% 1.15/1.00  --dbg_dump_prop_clauses                 false
% 1.15/1.00  --dbg_dump_prop_clauses_file            -
% 1.15/1.00  --dbg_out_stat                          false
% 1.15/1.00  
% 1.15/1.00  
% 1.15/1.00  
% 1.15/1.00  
% 1.15/1.00  ------ Proving...
% 1.15/1.00  
% 1.15/1.00  
% 1.15/1.00  % SZS status Theorem for theBenchmark.p
% 1.15/1.00  
% 1.15/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 1.15/1.00  
% 1.15/1.00  fof(f1,axiom,(
% 1.15/1.00    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.15/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.15/1.00  
% 1.15/1.00  fof(f23,plain,(
% 1.15/1.00    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 1.15/1.00    inference(nnf_transformation,[],[f1])).
% 1.15/1.00  
% 1.15/1.00  fof(f32,plain,(
% 1.15/1.00    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 1.15/1.00    inference(cnf_transformation,[],[f23])).
% 1.15/1.00  
% 1.15/1.00  fof(f7,axiom,(
% 1.15/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 1.15/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.15/1.00  
% 1.15/1.00  fof(f19,plain,(
% 1.15/1.00    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.15/1.00    inference(ennf_transformation,[],[f7])).
% 1.15/1.00  
% 1.15/1.00  fof(f20,plain,(
% 1.15/1.00    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.15/1.00    inference(flattening,[],[f19])).
% 1.15/1.00  
% 1.15/1.00  fof(f25,plain,(
% 1.15/1.00    ! [X0] : (! [X1] : (! [X2] : (((m2_connsp_2(X2,X0,X1) | ~r1_tarski(X1,k1_tops_1(X0,X2))) & (r1_tarski(X1,k1_tops_1(X0,X2)) | ~m2_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.15/1.00    inference(nnf_transformation,[],[f20])).
% 1.15/1.00  
% 1.15/1.00  fof(f40,plain,(
% 1.15/1.00    ( ! [X2,X0,X1] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~m2_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.15/1.00    inference(cnf_transformation,[],[f25])).
% 1.15/1.00  
% 1.15/1.00  fof(f8,conjecture,(
% 1.15/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) <=> m1_connsp_2(X2,X0,X1)))))),
% 1.15/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.15/1.00  
% 1.15/1.00  fof(f9,negated_conjecture,(
% 1.15/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) <=> m1_connsp_2(X2,X0,X1)))))),
% 1.15/1.00    inference(negated_conjecture,[],[f8])).
% 1.15/1.00  
% 1.15/1.00  fof(f21,plain,(
% 1.15/1.00    ? [X0] : (? [X1] : (? [X2] : ((m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) <~> m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.15/1.00    inference(ennf_transformation,[],[f9])).
% 1.15/1.00  
% 1.15/1.00  fof(f22,plain,(
% 1.15/1.00    ? [X0] : (? [X1] : (? [X2] : ((m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) <~> m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.15/1.00    inference(flattening,[],[f21])).
% 1.15/1.00  
% 1.15/1.00  fof(f26,plain,(
% 1.15/1.00    ? [X0] : (? [X1] : (? [X2] : (((~m1_connsp_2(X2,X0,X1) | ~m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & (m1_connsp_2(X2,X0,X1) | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.15/1.00    inference(nnf_transformation,[],[f22])).
% 1.15/1.00  
% 1.15/1.00  fof(f27,plain,(
% 1.15/1.00    ? [X0] : (? [X1] : (? [X2] : ((~m1_connsp_2(X2,X0,X1) | ~m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & (m1_connsp_2(X2,X0,X1) | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.15/1.00    inference(flattening,[],[f26])).
% 1.15/1.00  
% 1.15/1.00  fof(f30,plain,(
% 1.15/1.00    ( ! [X0,X1] : (? [X2] : ((~m1_connsp_2(X2,X0,X1) | ~m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & (m1_connsp_2(X2,X0,X1) | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => ((~m1_connsp_2(sK2,X0,X1) | ~m2_connsp_2(sK2,X0,k6_domain_1(u1_struct_0(X0),X1))) & (m1_connsp_2(sK2,X0,X1) | m2_connsp_2(sK2,X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 1.15/1.00    introduced(choice_axiom,[])).
% 1.15/1.00  
% 1.15/1.00  fof(f29,plain,(
% 1.15/1.00    ( ! [X0] : (? [X1] : (? [X2] : ((~m1_connsp_2(X2,X0,X1) | ~m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & (m1_connsp_2(X2,X0,X1) | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : ((~m1_connsp_2(X2,X0,sK1) | ~m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),sK1))) & (m1_connsp_2(X2,X0,sK1) | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),sK1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK1,u1_struct_0(X0)))) )),
% 1.15/1.00    introduced(choice_axiom,[])).
% 1.15/1.00  
% 1.15/1.00  fof(f28,plain,(
% 1.15/1.00    ? [X0] : (? [X1] : (? [X2] : ((~m1_connsp_2(X2,X0,X1) | ~m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & (m1_connsp_2(X2,X0,X1) | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~m1_connsp_2(X2,sK0,X1) | ~m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),X1))) & (m1_connsp_2(X2,sK0,X1) | m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.15/1.00    introduced(choice_axiom,[])).
% 1.15/1.00  
% 1.15/1.00  fof(f31,plain,(
% 1.15/1.00    (((~m1_connsp_2(sK2,sK0,sK1) | ~m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))) & (m1_connsp_2(sK2,sK0,sK1) | m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.15/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f30,f29,f28])).
% 1.15/1.00  
% 1.15/1.00  fof(f44,plain,(
% 1.15/1.00    l1_pre_topc(sK0)),
% 1.15/1.00    inference(cnf_transformation,[],[f31])).
% 1.15/1.00  
% 1.15/1.00  fof(f43,plain,(
% 1.15/1.00    v2_pre_topc(sK0)),
% 1.15/1.00    inference(cnf_transformation,[],[f31])).
% 1.15/1.00  
% 1.15/1.00  fof(f48,plain,(
% 1.15/1.00    ~m1_connsp_2(sK2,sK0,sK1) | ~m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))),
% 1.15/1.00    inference(cnf_transformation,[],[f31])).
% 1.15/1.00  
% 1.15/1.00  fof(f6,axiom,(
% 1.15/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 1.15/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.15/1.00  
% 1.15/1.00  fof(f17,plain,(
% 1.15/1.00    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.15/1.00    inference(ennf_transformation,[],[f6])).
% 1.15/1.00  
% 1.15/1.00  fof(f18,plain,(
% 1.15/1.00    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.15/1.00    inference(flattening,[],[f17])).
% 1.15/1.00  
% 1.15/1.00  fof(f24,plain,(
% 1.15/1.00    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.15/1.00    inference(nnf_transformation,[],[f18])).
% 1.15/1.00  
% 1.15/1.00  fof(f39,plain,(
% 1.15/1.00    ( ! [X2,X0,X1] : (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.15/1.00    inference(cnf_transformation,[],[f24])).
% 1.15/1.00  
% 1.15/1.00  fof(f42,plain,(
% 1.15/1.00    ~v2_struct_0(sK0)),
% 1.15/1.00    inference(cnf_transformation,[],[f31])).
% 1.15/1.00  
% 1.15/1.00  fof(f45,plain,(
% 1.15/1.00    m1_subset_1(sK1,u1_struct_0(sK0))),
% 1.15/1.00    inference(cnf_transformation,[],[f31])).
% 1.15/1.00  
% 1.15/1.00  fof(f46,plain,(
% 1.15/1.00    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.15/1.00    inference(cnf_transformation,[],[f31])).
% 1.15/1.00  
% 1.15/1.00  fof(f5,axiom,(
% 1.15/1.00    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 1.15/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.15/1.00  
% 1.15/1.00  fof(f15,plain,(
% 1.15/1.00    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.15/1.00    inference(ennf_transformation,[],[f5])).
% 1.15/1.00  
% 1.15/1.00  fof(f16,plain,(
% 1.15/1.00    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.15/1.00    inference(flattening,[],[f15])).
% 1.15/1.00  
% 1.15/1.00  fof(f37,plain,(
% 1.15/1.00    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.15/1.00    inference(cnf_transformation,[],[f16])).
% 1.15/1.00  
% 1.15/1.00  fof(f2,axiom,(
% 1.15/1.00    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.15/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.15/1.00  
% 1.15/1.00  fof(f10,plain,(
% 1.15/1.00    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.15/1.00    inference(ennf_transformation,[],[f2])).
% 1.15/1.00  
% 1.15/1.00  fof(f34,plain,(
% 1.15/1.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.15/1.00    inference(cnf_transformation,[],[f10])).
% 1.15/1.00  
% 1.15/1.00  fof(f3,axiom,(
% 1.15/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.15/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.15/1.00  
% 1.15/1.00  fof(f11,plain,(
% 1.15/1.00    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.15/1.00    inference(ennf_transformation,[],[f3])).
% 1.15/1.00  
% 1.15/1.00  fof(f12,plain,(
% 1.15/1.00    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.15/1.00    inference(flattening,[],[f11])).
% 1.15/1.00  
% 1.15/1.00  fof(f35,plain,(
% 1.15/1.00    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.15/1.00    inference(cnf_transformation,[],[f12])).
% 1.15/1.00  
% 1.15/1.00  fof(f33,plain,(
% 1.15/1.00    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.15/1.00    inference(cnf_transformation,[],[f23])).
% 1.15/1.00  
% 1.15/1.00  fof(f41,plain,(
% 1.15/1.00    ( ! [X2,X0,X1] : (m2_connsp_2(X2,X0,X1) | ~r1_tarski(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.15/1.00    inference(cnf_transformation,[],[f25])).
% 1.15/1.00  
% 1.15/1.00  fof(f47,plain,(
% 1.15/1.00    m1_connsp_2(sK2,sK0,sK1) | m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))),
% 1.15/1.00    inference(cnf_transformation,[],[f31])).
% 1.15/1.00  
% 1.15/1.00  fof(f38,plain,(
% 1.15/1.00    ( ! [X2,X0,X1] : (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.15/1.00    inference(cnf_transformation,[],[f24])).
% 1.15/1.00  
% 1.15/1.00  fof(f4,axiom,(
% 1.15/1.00    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.15/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.15/1.00  
% 1.15/1.00  fof(f13,plain,(
% 1.15/1.00    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.15/1.00    inference(ennf_transformation,[],[f4])).
% 1.15/1.00  
% 1.15/1.00  fof(f14,plain,(
% 1.15/1.00    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.15/1.00    inference(flattening,[],[f13])).
% 1.15/1.00  
% 1.15/1.00  fof(f36,plain,(
% 1.15/1.00    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.15/1.00    inference(cnf_transformation,[],[f14])).
% 1.15/1.00  
% 1.15/1.00  cnf(c_1,plain,
% 1.15/1.00      ( r2_hidden(X0,X1) | ~ r1_tarski(k1_tarski(X0),X1) ),
% 1.15/1.00      inference(cnf_transformation,[],[f32]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_127,plain,
% 1.15/1.00      ( r2_hidden(X0,X1) | ~ r1_tarski(k1_tarski(X0),X1) ),
% 1.15/1.00      inference(prop_impl,[status(thm)],[c_1]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_9,plain,
% 1.15/1.00      ( ~ m2_connsp_2(X0,X1,X2)
% 1.15/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.15/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.15/1.00      | r1_tarski(X2,k1_tops_1(X1,X0))
% 1.15/1.00      | ~ v2_pre_topc(X1)
% 1.15/1.00      | ~ l1_pre_topc(X1) ),
% 1.15/1.00      inference(cnf_transformation,[],[f40]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_14,negated_conjecture,
% 1.15/1.00      ( l1_pre_topc(sK0) ),
% 1.15/1.00      inference(cnf_transformation,[],[f44]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_404,plain,
% 1.15/1.00      ( ~ m2_connsp_2(X0,X1,X2)
% 1.15/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.15/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.15/1.00      | r1_tarski(X2,k1_tops_1(X1,X0))
% 1.15/1.00      | ~ v2_pre_topc(X1)
% 1.15/1.00      | sK0 != X1 ),
% 1.15/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_14]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_405,plain,
% 1.15/1.00      ( ~ m2_connsp_2(X0,sK0,X1)
% 1.15/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.15/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.15/1.00      | r1_tarski(X1,k1_tops_1(sK0,X0))
% 1.15/1.00      | ~ v2_pre_topc(sK0) ),
% 1.15/1.00      inference(unflattening,[status(thm)],[c_404]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_15,negated_conjecture,
% 1.15/1.00      ( v2_pre_topc(sK0) ),
% 1.15/1.00      inference(cnf_transformation,[],[f43]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_409,plain,
% 1.15/1.00      ( r1_tarski(X1,k1_tops_1(sK0,X0))
% 1.15/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.15/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.15/1.00      | ~ m2_connsp_2(X0,sK0,X1) ),
% 1.15/1.00      inference(global_propositional_subsumption,
% 1.15/1.00                [status(thm)],
% 1.15/1.00                [c_405,c_15]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_410,plain,
% 1.15/1.00      ( ~ m2_connsp_2(X0,sK0,X1)
% 1.15/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.15/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.15/1.00      | r1_tarski(X1,k1_tops_1(sK0,X0)) ),
% 1.15/1.00      inference(renaming,[status(thm)],[c_409]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_482,plain,
% 1.15/1.00      ( ~ m2_connsp_2(X0,sK0,X1)
% 1.15/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.15/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.15/1.00      | r2_hidden(X2,X3)
% 1.15/1.00      | k1_tops_1(sK0,X0) != X3
% 1.15/1.00      | k1_tarski(X2) != X1 ),
% 1.15/1.00      inference(resolution_lifted,[status(thm)],[c_127,c_410]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_483,plain,
% 1.15/1.00      ( ~ m2_connsp_2(X0,sK0,k1_tarski(X1))
% 1.15/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.15/1.00      | ~ m1_subset_1(k1_tarski(X1),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.15/1.00      | r2_hidden(X1,k1_tops_1(sK0,X0)) ),
% 1.15/1.00      inference(unflattening,[status(thm)],[c_482]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_10,negated_conjecture,
% 1.15/1.00      ( ~ m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))
% 1.15/1.00      | ~ m1_connsp_2(sK2,sK0,sK1) ),
% 1.15/1.00      inference(cnf_transformation,[],[f48]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_131,plain,
% 1.15/1.00      ( ~ m1_connsp_2(sK2,sK0,sK1)
% 1.15/1.00      | ~ m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) ),
% 1.15/1.00      inference(prop_impl,[status(thm)],[c_10]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_132,plain,
% 1.15/1.00      ( ~ m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))
% 1.15/1.00      | ~ m1_connsp_2(sK2,sK0,sK1) ),
% 1.15/1.00      inference(renaming,[status(thm)],[c_131]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_6,plain,
% 1.15/1.00      ( m1_connsp_2(X0,X1,X2)
% 1.15/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.15/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.15/1.00      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 1.15/1.00      | ~ v2_pre_topc(X1)
% 1.15/1.00      | v2_struct_0(X1)
% 1.15/1.00      | ~ l1_pre_topc(X1) ),
% 1.15/1.00      inference(cnf_transformation,[],[f39]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_16,negated_conjecture,
% 1.15/1.00      ( ~ v2_struct_0(sK0) ),
% 1.15/1.00      inference(cnf_transformation,[],[f42]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_338,plain,
% 1.15/1.00      ( m1_connsp_2(X0,X1,X2)
% 1.15/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.15/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.15/1.00      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 1.15/1.00      | ~ v2_pre_topc(X1)
% 1.15/1.00      | ~ l1_pre_topc(X1)
% 1.15/1.00      | sK0 != X1 ),
% 1.15/1.00      inference(resolution_lifted,[status(thm)],[c_6,c_16]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_339,plain,
% 1.15/1.00      ( m1_connsp_2(X0,sK0,X1)
% 1.15/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.15/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 1.15/1.00      | ~ r2_hidden(X1,k1_tops_1(sK0,X0))
% 1.15/1.00      | ~ v2_pre_topc(sK0)
% 1.15/1.00      | ~ l1_pre_topc(sK0) ),
% 1.15/1.00      inference(unflattening,[status(thm)],[c_338]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_343,plain,
% 1.15/1.00      ( m1_connsp_2(X0,sK0,X1)
% 1.15/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.15/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 1.15/1.00      | ~ r2_hidden(X1,k1_tops_1(sK0,X0)) ),
% 1.15/1.00      inference(global_propositional_subsumption,
% 1.15/1.00                [status(thm)],
% 1.15/1.00                [c_339,c_15,c_14]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_526,plain,
% 1.15/1.00      ( ~ m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))
% 1.15/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.15/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 1.15/1.00      | ~ r2_hidden(X1,k1_tops_1(sK0,X0))
% 1.15/1.00      | sK1 != X1
% 1.15/1.00      | sK0 != sK0
% 1.15/1.00      | sK2 != X0 ),
% 1.15/1.00      inference(resolution_lifted,[status(thm)],[c_132,c_343]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_527,plain,
% 1.15/1.00      ( ~ m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))
% 1.15/1.00      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
% 1.15/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.15/1.00      | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
% 1.15/1.00      inference(unflattening,[status(thm)],[c_526]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_13,negated_conjecture,
% 1.15/1.00      ( m1_subset_1(sK1,u1_struct_0(sK0)) ),
% 1.15/1.00      inference(cnf_transformation,[],[f45]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_12,negated_conjecture,
% 1.15/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.15/1.00      inference(cnf_transformation,[],[f46]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_529,plain,
% 1.15/1.00      ( ~ m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))
% 1.15/1.00      | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
% 1.15/1.00      inference(global_propositional_subsumption,
% 1.15/1.00                [status(thm)],
% 1.15/1.00                [c_527,c_13,c_12]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_548,plain,
% 1.15/1.00      ( ~ m2_connsp_2(X0,sK0,k1_tarski(X1))
% 1.15/1.00      | ~ m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))
% 1.15/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.15/1.00      | ~ m1_subset_1(k1_tarski(X1),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.15/1.00      | k1_tops_1(sK0,X0) != k1_tops_1(sK0,sK2)
% 1.15/1.00      | sK1 != X1 ),
% 1.15/1.00      inference(resolution_lifted,[status(thm)],[c_483,c_529]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_549,plain,
% 1.15/1.00      ( ~ m2_connsp_2(X0,sK0,k1_tarski(sK1))
% 1.15/1.00      | ~ m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))
% 1.15/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.15/1.00      | ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.15/1.00      | k1_tops_1(sK0,X0) != k1_tops_1(sK0,sK2) ),
% 1.15/1.00      inference(unflattening,[status(thm)],[c_548]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_651,plain,
% 1.15/1.00      ( ~ m2_connsp_2(X0_46,sK0,k1_tarski(sK1))
% 1.15/1.00      | ~ m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))
% 1.15/1.00      | ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.15/1.00      | ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.15/1.00      | k1_tops_1(sK0,X0_46) != k1_tops_1(sK0,sK2) ),
% 1.15/1.00      inference(subtyping,[status(esa)],[c_549]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_656,plain,
% 1.15/1.00      ( ~ m2_connsp_2(X0_46,sK0,k1_tarski(sK1))
% 1.15/1.00      | ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.15/1.00      | k1_tops_1(sK0,X0_46) != k1_tops_1(sK0,sK2)
% 1.15/1.00      | ~ sP0_iProver_split ),
% 1.15/1.00      inference(splitting,
% 1.15/1.00                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 1.15/1.00                [c_651]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_833,plain,
% 1.15/1.00      ( k1_tops_1(sK0,X0_46) != k1_tops_1(sK0,sK2)
% 1.15/1.00      | m2_connsp_2(X0_46,sK0,k1_tarski(sK1)) != iProver_top
% 1.15/1.00      | m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 1.15/1.00      | sP0_iProver_split != iProver_top ),
% 1.15/1.00      inference(predicate_to_equality,[status(thm)],[c_656]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_20,plain,
% 1.15/1.00      ( m1_subset_1(sK1,u1_struct_0(sK0)) = iProver_top ),
% 1.15/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_21,plain,
% 1.15/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 1.15/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_665,plain,
% 1.15/1.00      ( X0_46 != X1_46 | k1_tarski(X0_46) = k1_tarski(X1_46) ),
% 1.15/1.00      theory(equality) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_670,plain,
% 1.15/1.00      ( k1_tarski(sK1) = k1_tarski(sK1) | sK1 != sK1 ),
% 1.15/1.00      inference(instantiation,[status(thm)],[c_665]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_661,plain,( X0_46 = X0_46 ),theory(equality) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_676,plain,
% 1.15/1.00      ( sK1 = sK1 ),
% 1.15/1.00      inference(instantiation,[status(thm)],[c_661]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_5,plain,
% 1.15/1.00      ( ~ m1_subset_1(X0,X1)
% 1.15/1.00      | v1_xboole_0(X1)
% 1.15/1.00      | k6_domain_1(X1,X0) = k1_tarski(X0) ),
% 1.15/1.00      inference(cnf_transformation,[],[f37]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_2,plain,
% 1.15/1.00      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 1.15/1.00      inference(cnf_transformation,[],[f34]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_3,plain,
% 1.15/1.00      ( v2_struct_0(X0)
% 1.15/1.00      | ~ v1_xboole_0(u1_struct_0(X0))
% 1.15/1.00      | ~ l1_struct_0(X0) ),
% 1.15/1.00      inference(cnf_transformation,[],[f35]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_241,plain,
% 1.15/1.00      ( v2_struct_0(X0)
% 1.15/1.00      | ~ v1_xboole_0(u1_struct_0(X0))
% 1.15/1.00      | ~ l1_pre_topc(X0) ),
% 1.15/1.00      inference(resolution,[status(thm)],[c_2,c_3]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_303,plain,
% 1.15/1.00      ( ~ v1_xboole_0(u1_struct_0(X0)) | ~ l1_pre_topc(X0) | sK0 != X0 ),
% 1.15/1.00      inference(resolution_lifted,[status(thm)],[c_241,c_16]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_304,plain,
% 1.15/1.00      ( ~ v1_xboole_0(u1_struct_0(sK0)) | ~ l1_pre_topc(sK0) ),
% 1.15/1.00      inference(unflattening,[status(thm)],[c_303]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_43,plain,
% 1.15/1.00      ( v2_struct_0(sK0)
% 1.15/1.00      | ~ v1_xboole_0(u1_struct_0(sK0))
% 1.15/1.00      | ~ l1_struct_0(sK0) ),
% 1.15/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_46,plain,
% 1.15/1.00      ( ~ l1_pre_topc(sK0) | l1_struct_0(sK0) ),
% 1.15/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_306,plain,
% 1.15/1.00      ( ~ v1_xboole_0(u1_struct_0(sK0)) ),
% 1.15/1.00      inference(global_propositional_subsumption,
% 1.15/1.00                [status(thm)],
% 1.15/1.00                [c_304,c_16,c_14,c_43,c_46]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_374,plain,
% 1.15/1.00      ( ~ m1_subset_1(X0,X1)
% 1.15/1.00      | k6_domain_1(X1,X0) = k1_tarski(X0)
% 1.15/1.00      | u1_struct_0(sK0) != X1 ),
% 1.15/1.00      inference(resolution_lifted,[status(thm)],[c_5,c_306]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_375,plain,
% 1.15/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 1.15/1.00      | k6_domain_1(u1_struct_0(sK0),X0) = k1_tarski(X0) ),
% 1.15/1.00      inference(unflattening,[status(thm)],[c_374]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_653,plain,
% 1.15/1.00      ( ~ m1_subset_1(X0_46,u1_struct_0(sK0))
% 1.15/1.00      | k6_domain_1(u1_struct_0(sK0),X0_46) = k1_tarski(X0_46) ),
% 1.15/1.00      inference(subtyping,[status(esa)],[c_375]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_681,plain,
% 1.15/1.00      ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
% 1.15/1.00      | k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) ),
% 1.15/1.00      inference(instantiation,[status(thm)],[c_653]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_687,plain,
% 1.15/1.00      ( k1_tops_1(sK0,X0_46) != k1_tops_1(sK0,sK2)
% 1.15/1.00      | m2_connsp_2(X0_46,sK0,k1_tarski(sK1)) != iProver_top
% 1.15/1.00      | m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 1.15/1.00      | sP0_iProver_split != iProver_top ),
% 1.15/1.00      inference(predicate_to_equality,[status(thm)],[c_656]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_0,plain,
% 1.15/1.00      ( ~ r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1) ),
% 1.15/1.00      inference(cnf_transformation,[],[f33]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_129,plain,
% 1.15/1.00      ( ~ r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1) ),
% 1.15/1.00      inference(prop_impl,[status(thm)],[c_0]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_8,plain,
% 1.15/1.00      ( m2_connsp_2(X0,X1,X2)
% 1.15/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.15/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.15/1.00      | ~ r1_tarski(X2,k1_tops_1(X1,X0))
% 1.15/1.00      | ~ v2_pre_topc(X1)
% 1.15/1.00      | ~ l1_pre_topc(X1) ),
% 1.15/1.00      inference(cnf_transformation,[],[f41]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_428,plain,
% 1.15/1.00      ( m2_connsp_2(X0,X1,X2)
% 1.15/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.15/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.15/1.00      | ~ r1_tarski(X2,k1_tops_1(X1,X0))
% 1.15/1.00      | ~ v2_pre_topc(X1)
% 1.15/1.00      | sK0 != X1 ),
% 1.15/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_14]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_429,plain,
% 1.15/1.00      ( m2_connsp_2(X0,sK0,X1)
% 1.15/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.15/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.15/1.00      | ~ r1_tarski(X1,k1_tops_1(sK0,X0))
% 1.15/1.00      | ~ v2_pre_topc(sK0) ),
% 1.15/1.00      inference(unflattening,[status(thm)],[c_428]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_433,plain,
% 1.15/1.00      ( ~ r1_tarski(X1,k1_tops_1(sK0,X0))
% 1.15/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.15/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.15/1.00      | m2_connsp_2(X0,sK0,X1) ),
% 1.15/1.00      inference(global_propositional_subsumption,
% 1.15/1.00                [status(thm)],
% 1.15/1.00                [c_429,c_15]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_434,plain,
% 1.15/1.00      ( m2_connsp_2(X0,sK0,X1)
% 1.15/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.15/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.15/1.00      | ~ r1_tarski(X1,k1_tops_1(sK0,X0)) ),
% 1.15/1.00      inference(renaming,[status(thm)],[c_433]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_464,plain,
% 1.15/1.00      ( m2_connsp_2(X0,sK0,X1)
% 1.15/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.15/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.15/1.00      | ~ r2_hidden(X2,X3)
% 1.15/1.00      | k1_tops_1(sK0,X0) != X3
% 1.15/1.00      | k1_tarski(X2) != X1 ),
% 1.15/1.00      inference(resolution_lifted,[status(thm)],[c_129,c_434]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_465,plain,
% 1.15/1.00      ( m2_connsp_2(X0,sK0,k1_tarski(X1))
% 1.15/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.15/1.00      | ~ m1_subset_1(k1_tarski(X1),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.15/1.00      | ~ r2_hidden(X1,k1_tops_1(sK0,X0)) ),
% 1.15/1.00      inference(unflattening,[status(thm)],[c_464]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_11,negated_conjecture,
% 1.15/1.00      ( m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))
% 1.15/1.00      | m1_connsp_2(sK2,sK0,sK1) ),
% 1.15/1.00      inference(cnf_transformation,[],[f47]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_133,plain,
% 1.15/1.00      ( m1_connsp_2(sK2,sK0,sK1)
% 1.15/1.00      | m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) ),
% 1.15/1.00      inference(prop_impl,[status(thm)],[c_11]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_134,plain,
% 1.15/1.00      ( m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))
% 1.15/1.00      | m1_connsp_2(sK2,sK0,sK1) ),
% 1.15/1.00      inference(renaming,[status(thm)],[c_133]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_7,plain,
% 1.15/1.00      ( ~ m1_connsp_2(X0,X1,X2)
% 1.15/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.15/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.15/1.00      | r2_hidden(X2,k1_tops_1(X1,X0))
% 1.15/1.00      | ~ v2_pre_topc(X1)
% 1.15/1.00      | v2_struct_0(X1)
% 1.15/1.00      | ~ l1_pre_topc(X1) ),
% 1.15/1.00      inference(cnf_transformation,[],[f38]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_314,plain,
% 1.15/1.00      ( ~ m1_connsp_2(X0,X1,X2)
% 1.15/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.15/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.15/1.00      | r2_hidden(X2,k1_tops_1(X1,X0))
% 1.15/1.00      | ~ v2_pre_topc(X1)
% 1.15/1.00      | ~ l1_pre_topc(X1)
% 1.15/1.00      | sK0 != X1 ),
% 1.15/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_16]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_315,plain,
% 1.15/1.00      ( ~ m1_connsp_2(X0,sK0,X1)
% 1.15/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.15/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 1.15/1.00      | r2_hidden(X1,k1_tops_1(sK0,X0))
% 1.15/1.00      | ~ v2_pre_topc(sK0)
% 1.15/1.00      | ~ l1_pre_topc(sK0) ),
% 1.15/1.00      inference(unflattening,[status(thm)],[c_314]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_319,plain,
% 1.15/1.00      ( ~ m1_connsp_2(X0,sK0,X1)
% 1.15/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.15/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 1.15/1.00      | r2_hidden(X1,k1_tops_1(sK0,X0)) ),
% 1.15/1.00      inference(global_propositional_subsumption,
% 1.15/1.00                [status(thm)],
% 1.15/1.00                [c_315,c_15,c_14]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_512,plain,
% 1.15/1.00      ( m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))
% 1.15/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.15/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 1.15/1.00      | r2_hidden(X1,k1_tops_1(sK0,X0))
% 1.15/1.00      | sK1 != X1
% 1.15/1.00      | sK0 != sK0
% 1.15/1.00      | sK2 != X0 ),
% 1.15/1.00      inference(resolution_lifted,[status(thm)],[c_134,c_319]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_513,plain,
% 1.15/1.00      ( m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))
% 1.15/1.00      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
% 1.15/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.15/1.00      | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
% 1.15/1.00      inference(unflattening,[status(thm)],[c_512]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_515,plain,
% 1.15/1.00      ( m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))
% 1.15/1.00      | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
% 1.15/1.00      inference(global_propositional_subsumption,
% 1.15/1.00                [status(thm)],
% 1.15/1.00                [c_513,c_13,c_12]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_569,plain,
% 1.15/1.00      ( m2_connsp_2(X0,sK0,k1_tarski(X1))
% 1.15/1.00      | m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))
% 1.15/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.15/1.00      | ~ m1_subset_1(k1_tarski(X1),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.15/1.00      | k1_tops_1(sK0,X0) != k1_tops_1(sK0,sK2)
% 1.15/1.00      | sK1 != X1 ),
% 1.15/1.00      inference(resolution_lifted,[status(thm)],[c_465,c_515]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_570,plain,
% 1.15/1.00      ( m2_connsp_2(X0,sK0,k1_tarski(sK1))
% 1.15/1.00      | m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))
% 1.15/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.15/1.00      | ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.15/1.00      | k1_tops_1(sK0,X0) != k1_tops_1(sK0,sK2) ),
% 1.15/1.00      inference(unflattening,[status(thm)],[c_569]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_650,plain,
% 1.15/1.00      ( m2_connsp_2(X0_46,sK0,k1_tarski(sK1))
% 1.15/1.00      | m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))
% 1.15/1.00      | ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.15/1.00      | ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.15/1.00      | k1_tops_1(sK0,X0_46) != k1_tops_1(sK0,sK2) ),
% 1.15/1.00      inference(subtyping,[status(esa)],[c_570]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_659,plain,
% 1.15/1.00      ( m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))
% 1.15/1.00      | ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.15/1.00      | sP1_iProver_split ),
% 1.15/1.00      inference(splitting,
% 1.15/1.00                [splitting(split),new_symbols(definition,[])],
% 1.15/1.00                [c_650]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_690,plain,
% 1.15/1.00      ( m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) = iProver_top
% 1.15/1.00      | m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 1.15/1.00      | sP1_iProver_split = iProver_top ),
% 1.15/1.00      inference(predicate_to_equality,[status(thm)],[c_659]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_936,plain,
% 1.15/1.00      ( sK2 = sK2 ),
% 1.15/1.00      inference(instantiation,[status(thm)],[c_661]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_654,negated_conjecture,
% 1.15/1.00      ( m1_subset_1(sK1,u1_struct_0(sK0)) ),
% 1.15/1.00      inference(subtyping,[status(esa)],[c_13]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_829,plain,
% 1.15/1.00      ( m1_subset_1(sK1,u1_struct_0(sK0)) = iProver_top ),
% 1.15/1.00      inference(predicate_to_equality,[status(thm)],[c_654]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_830,plain,
% 1.15/1.00      ( k6_domain_1(u1_struct_0(sK0),X0_46) = k1_tarski(X0_46)
% 1.15/1.00      | m1_subset_1(X0_46,u1_struct_0(sK0)) != iProver_top ),
% 1.15/1.00      inference(predicate_to_equality,[status(thm)],[c_653]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_925,plain,
% 1.15/1.00      ( k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) ),
% 1.15/1.00      inference(superposition,[status(thm)],[c_829,c_830]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_4,plain,
% 1.15/1.00      ( ~ m1_subset_1(X0,X1)
% 1.15/1.00      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
% 1.15/1.00      | v1_xboole_0(X1) ),
% 1.15/1.00      inference(cnf_transformation,[],[f36]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_386,plain,
% 1.15/1.00      ( ~ m1_subset_1(X0,X1)
% 1.15/1.00      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
% 1.15/1.00      | u1_struct_0(sK0) != X1 ),
% 1.15/1.00      inference(resolution_lifted,[status(thm)],[c_4,c_306]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_387,plain,
% 1.15/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 1.15/1.00      | m1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.15/1.00      inference(unflattening,[status(thm)],[c_386]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_652,plain,
% 1.15/1.00      ( ~ m1_subset_1(X0_46,u1_struct_0(sK0))
% 1.15/1.00      | m1_subset_1(k6_domain_1(u1_struct_0(sK0),X0_46),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.15/1.00      inference(subtyping,[status(esa)],[c_387]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_831,plain,
% 1.15/1.00      ( m1_subset_1(X0_46,u1_struct_0(sK0)) != iProver_top
% 1.15/1.00      | m1_subset_1(k6_domain_1(u1_struct_0(sK0),X0_46),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 1.15/1.00      inference(predicate_to_equality,[status(thm)],[c_652]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_968,plain,
% 1.15/1.00      ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 1.15/1.00      | m1_subset_1(sK1,u1_struct_0(sK0)) != iProver_top ),
% 1.15/1.00      inference(superposition,[status(thm)],[c_925,c_831]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_663,plain,
% 1.15/1.00      ( X0_46 != X1_46 | X2_46 != X1_46 | X2_46 = X0_46 ),
% 1.15/1.00      theory(equality) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_928,plain,
% 1.15/1.00      ( X0_46 != X1_46
% 1.15/1.00      | X0_46 = k6_domain_1(u1_struct_0(sK0),X2_46)
% 1.15/1.00      | k6_domain_1(u1_struct_0(sK0),X2_46) != X1_46 ),
% 1.15/1.00      inference(instantiation,[status(thm)],[c_663]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_947,plain,
% 1.15/1.00      ( X0_46 = k6_domain_1(u1_struct_0(sK0),X1_46)
% 1.15/1.00      | X0_46 != k1_tarski(X1_46)
% 1.15/1.00      | k6_domain_1(u1_struct_0(sK0),X1_46) != k1_tarski(X1_46) ),
% 1.15/1.00      inference(instantiation,[status(thm)],[c_928]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_983,plain,
% 1.15/1.00      ( k6_domain_1(u1_struct_0(sK0),X0_46) != k1_tarski(X0_46)
% 1.15/1.00      | k1_tarski(X0_46) = k6_domain_1(u1_struct_0(sK0),X0_46)
% 1.15/1.00      | k1_tarski(X0_46) != k1_tarski(X0_46) ),
% 1.15/1.00      inference(instantiation,[status(thm)],[c_947]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_985,plain,
% 1.15/1.00      ( k6_domain_1(u1_struct_0(sK0),sK1) != k1_tarski(sK1)
% 1.15/1.00      | k1_tarski(sK1) = k6_domain_1(u1_struct_0(sK0),sK1)
% 1.15/1.00      | k1_tarski(sK1) != k1_tarski(sK1) ),
% 1.15/1.00      inference(instantiation,[status(thm)],[c_983]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_669,plain,
% 1.15/1.00      ( ~ m2_connsp_2(X0_46,X0_47,X1_46)
% 1.15/1.00      | m2_connsp_2(X2_46,X0_47,X3_46)
% 1.15/1.00      | X2_46 != X0_46
% 1.15/1.00      | X3_46 != X1_46 ),
% 1.15/1.00      theory(equality) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_911,plain,
% 1.15/1.00      ( m2_connsp_2(X0_46,sK0,X1_46)
% 1.15/1.00      | ~ m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))
% 1.15/1.00      | X1_46 != k6_domain_1(u1_struct_0(sK0),sK1)
% 1.15/1.00      | X0_46 != sK2 ),
% 1.15/1.00      inference(instantiation,[status(thm)],[c_669]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_935,plain,
% 1.15/1.00      ( m2_connsp_2(sK2,sK0,X0_46)
% 1.15/1.00      | ~ m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))
% 1.15/1.00      | X0_46 != k6_domain_1(u1_struct_0(sK0),sK1)
% 1.15/1.00      | sK2 != sK2 ),
% 1.15/1.00      inference(instantiation,[status(thm)],[c_911]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_1001,plain,
% 1.15/1.00      ( ~ m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))
% 1.15/1.00      | m2_connsp_2(sK2,sK0,k1_tarski(sK1))
% 1.15/1.00      | k1_tarski(sK1) != k6_domain_1(u1_struct_0(sK0),sK1)
% 1.15/1.00      | sK2 != sK2 ),
% 1.15/1.00      inference(instantiation,[status(thm)],[c_935]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_1002,plain,
% 1.15/1.00      ( k1_tarski(sK1) != k6_domain_1(u1_struct_0(sK0),sK1)
% 1.15/1.00      | sK2 != sK2
% 1.15/1.00      | m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != iProver_top
% 1.15/1.00      | m2_connsp_2(sK2,sK0,k1_tarski(sK1)) = iProver_top ),
% 1.15/1.00      inference(predicate_to_equality,[status(thm)],[c_1001]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_657,plain,
% 1.15/1.00      ( ~ m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))
% 1.15/1.00      | ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.15/1.00      | sP0_iProver_split ),
% 1.15/1.00      inference(splitting,
% 1.15/1.00                [splitting(split),new_symbols(definition,[])],
% 1.15/1.00                [c_651]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_832,plain,
% 1.15/1.00      ( m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != iProver_top
% 1.15/1.00      | m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 1.15/1.00      | sP0_iProver_split = iProver_top ),
% 1.15/1.00      inference(predicate_to_equality,[status(thm)],[c_657]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_686,plain,
% 1.15/1.00      ( m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != iProver_top
% 1.15/1.00      | m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 1.15/1.00      | sP0_iProver_split = iProver_top ),
% 1.15/1.00      inference(predicate_to_equality,[status(thm)],[c_657]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_1023,plain,
% 1.15/1.00      ( m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != iProver_top
% 1.15/1.00      | sP0_iProver_split = iProver_top ),
% 1.15/1.00      inference(global_propositional_subsumption,
% 1.15/1.00                [status(thm)],
% 1.15/1.00                [c_832,c_20,c_686,c_968]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_1027,plain,
% 1.15/1.00      ( m2_connsp_2(sK2,sK0,k1_tarski(sK1)) != iProver_top
% 1.15/1.00      | sP0_iProver_split = iProver_top ),
% 1.15/1.00      inference(light_normalisation,[status(thm)],[c_1023,c_925]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_658,plain,
% 1.15/1.00      ( m2_connsp_2(X0_46,sK0,k1_tarski(sK1))
% 1.15/1.00      | ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.15/1.00      | k1_tops_1(sK0,X0_46) != k1_tops_1(sK0,sK2)
% 1.15/1.00      | ~ sP1_iProver_split ),
% 1.15/1.00      inference(splitting,
% 1.15/1.00                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 1.15/1.00                [c_650]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_835,plain,
% 1.15/1.00      ( k1_tops_1(sK0,X0_46) != k1_tops_1(sK0,sK2)
% 1.15/1.00      | m2_connsp_2(X0_46,sK0,k1_tarski(sK1)) = iProver_top
% 1.15/1.00      | m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 1.15/1.00      | sP1_iProver_split != iProver_top ),
% 1.15/1.00      inference(predicate_to_equality,[status(thm)],[c_658]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_1036,plain,
% 1.15/1.00      ( m2_connsp_2(sK2,sK0,k1_tarski(sK1)) = iProver_top
% 1.15/1.00      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 1.15/1.00      | sP1_iProver_split != iProver_top ),
% 1.15/1.00      inference(equality_resolution,[status(thm)],[c_835]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_1078,plain,
% 1.15/1.00      ( m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 1.15/1.00      | m2_connsp_2(X0_46,sK0,k1_tarski(sK1)) != iProver_top
% 1.15/1.00      | k1_tops_1(sK0,X0_46) != k1_tops_1(sK0,sK2) ),
% 1.15/1.00      inference(global_propositional_subsumption,
% 1.15/1.00                [status(thm)],
% 1.15/1.00                [c_833,c_13,c_20,c_21,c_670,c_676,c_681,c_687,c_690,
% 1.15/1.00                 c_936,c_968,c_985,c_1002,c_1027,c_1036]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_1079,plain,
% 1.15/1.00      ( k1_tops_1(sK0,X0_46) != k1_tops_1(sK0,sK2)
% 1.15/1.00      | m2_connsp_2(X0_46,sK0,k1_tarski(sK1)) != iProver_top
% 1.15/1.00      | m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 1.15/1.00      inference(renaming,[status(thm)],[c_1078]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(c_1087,plain,
% 1.15/1.00      ( m2_connsp_2(sK2,sK0,k1_tarski(sK1)) != iProver_top
% 1.15/1.00      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 1.15/1.00      inference(equality_resolution,[status(thm)],[c_1079]) ).
% 1.15/1.00  
% 1.15/1.00  cnf(contradiction,plain,
% 1.15/1.00      ( $false ),
% 1.15/1.00      inference(minisat,
% 1.15/1.00                [status(thm)],
% 1.15/1.00                [c_1087,c_1036,c_1002,c_985,c_968,c_936,c_690,c_681,
% 1.15/1.00                 c_676,c_670,c_21,c_20,c_13]) ).
% 1.15/1.00  
% 1.15/1.00  
% 1.15/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 1.15/1.00  
% 1.15/1.00  ------                               Statistics
% 1.15/1.00  
% 1.15/1.00  ------ General
% 1.15/1.00  
% 1.15/1.00  abstr_ref_over_cycles:                  0
% 1.15/1.00  abstr_ref_under_cycles:                 0
% 1.15/1.00  gc_basic_clause_elim:                   0
% 1.15/1.00  forced_gc_time:                         0
% 1.15/1.00  parsing_time:                           0.01
% 1.15/1.00  unif_index_cands_time:                  0.
% 1.15/1.00  unif_index_add_time:                    0.
% 1.15/1.00  orderings_time:                         0.
% 1.15/1.00  out_proof_time:                         0.015
% 1.15/1.00  total_time:                             0.073
% 1.15/1.00  num_of_symbols:                         52
% 1.15/1.00  num_of_terms:                           873
% 1.15/1.00  
% 1.15/1.00  ------ Preprocessing
% 1.15/1.00  
% 1.15/1.00  num_of_splits:                          2
% 1.15/1.00  num_of_split_atoms:                     2
% 1.15/1.00  num_of_reused_defs:                     0
% 1.15/1.00  num_eq_ax_congr_red:                    11
% 1.15/1.00  num_of_sem_filtered_clauses:            1
% 1.15/1.00  num_of_subtypes:                        4
% 1.15/1.00  monotx_restored_types:                  0
% 1.15/1.00  sat_num_of_epr_types:                   0
% 1.15/1.00  sat_num_of_non_cyclic_types:            0
% 1.15/1.00  sat_guarded_non_collapsed_types:        0
% 1.15/1.00  num_pure_diseq_elim:                    0
% 1.15/1.00  simp_replaced_by:                       0
% 1.15/1.00  res_preprocessed:                       58
% 1.15/1.00  prep_upred:                             0
% 1.15/1.00  prep_unflattend:                        19
% 1.15/1.00  smt_new_axioms:                         0
% 1.15/1.00  pred_elim_cands:                        2
% 1.15/1.00  pred_elim:                              8
% 1.15/1.00  pred_elim_cl:                           11
% 1.15/1.00  pred_elim_cycles:                       11
% 1.15/1.00  merged_defs:                            4
% 1.15/1.00  merged_defs_ncl:                        0
% 1.15/1.00  bin_hyper_res:                          4
% 1.15/1.00  prep_cycles:                            4
% 1.15/1.00  pred_elim_time:                         0.006
% 1.15/1.00  splitting_time:                         0.
% 1.15/1.00  sem_filter_time:                        0.
% 1.15/1.00  monotx_time:                            0.
% 1.15/1.00  subtype_inf_time:                       0.
% 1.15/1.00  
% 1.15/1.00  ------ Problem properties
% 1.15/1.00  
% 1.15/1.00  clauses:                                8
% 1.15/1.00  conjectures:                            2
% 1.15/1.00  epr:                                    0
% 1.15/1.00  horn:                                   7
% 1.15/1.00  ground:                                 4
% 1.15/1.00  unary:                                  2
% 1.15/1.00  binary:                                 2
% 1.15/1.00  lits:                                   20
% 1.15/1.00  lits_eq:                                3
% 1.15/1.00  fd_pure:                                0
% 1.15/1.00  fd_pseudo:                              0
% 1.15/1.00  fd_cond:                                0
% 1.15/1.00  fd_pseudo_cond:                         0
% 1.15/1.00  ac_symbols:                             0
% 1.15/1.00  
% 1.15/1.00  ------ Propositional Solver
% 1.15/1.00  
% 1.15/1.00  prop_solver_calls:                      26
% 1.15/1.00  prop_fast_solver_calls:                 412
% 1.15/1.00  smt_solver_calls:                       0
% 1.15/1.00  smt_fast_solver_calls:                  0
% 1.15/1.00  prop_num_of_clauses:                    266
% 1.15/1.00  prop_preprocess_simplified:             1554
% 1.15/1.00  prop_fo_subsumed:                       14
% 1.15/1.00  prop_solver_time:                       0.
% 1.15/1.00  smt_solver_time:                        0.
% 1.15/1.00  smt_fast_solver_time:                   0.
% 1.15/1.00  prop_fast_solver_time:                  0.
% 1.15/1.00  prop_unsat_core_time:                   0.
% 1.15/1.00  
% 1.15/1.00  ------ QBF
% 1.15/1.00  
% 1.15/1.00  qbf_q_res:                              0
% 1.15/1.00  qbf_num_tautologies:                    0
% 1.15/1.00  qbf_prep_cycles:                        0
% 1.15/1.00  
% 1.15/1.00  ------ BMC1
% 1.15/1.00  
% 1.15/1.00  bmc1_current_bound:                     -1
% 1.15/1.00  bmc1_last_solved_bound:                 -1
% 1.15/1.00  bmc1_unsat_core_size:                   -1
% 1.15/1.00  bmc1_unsat_core_parents_size:           -1
% 1.15/1.00  bmc1_merge_next_fun:                    0
% 1.15/1.00  bmc1_unsat_core_clauses_time:           0.
% 1.15/1.00  
% 1.15/1.00  ------ Instantiation
% 1.15/1.00  
% 1.15/1.00  inst_num_of_clauses:                    59
% 1.15/1.00  inst_num_in_passive:                    14
% 1.15/1.00  inst_num_in_active:                     43
% 1.15/1.00  inst_num_in_unprocessed:                2
% 1.15/1.00  inst_num_of_loops:                      50
% 1.15/1.00  inst_num_of_learning_restarts:          0
% 1.15/1.01  inst_num_moves_active_passive:          2
% 1.15/1.01  inst_lit_activity:                      0
% 1.15/1.01  inst_lit_activity_moves:                0
% 1.15/1.01  inst_num_tautologies:                   0
% 1.15/1.01  inst_num_prop_implied:                  0
% 1.15/1.01  inst_num_existing_simplified:           0
% 1.15/1.01  inst_num_eq_res_simplified:             0
% 1.15/1.01  inst_num_child_elim:                    0
% 1.15/1.01  inst_num_of_dismatching_blockings:      9
% 1.15/1.01  inst_num_of_non_proper_insts:           51
% 1.15/1.01  inst_num_of_duplicates:                 0
% 1.15/1.01  inst_inst_num_from_inst_to_res:         0
% 1.15/1.01  inst_dismatching_checking_time:         0.
% 1.15/1.01  
% 1.15/1.01  ------ Resolution
% 1.15/1.01  
% 1.15/1.01  res_num_of_clauses:                     0
% 1.15/1.01  res_num_in_passive:                     0
% 1.15/1.01  res_num_in_active:                      0
% 1.15/1.01  res_num_of_loops:                       62
% 1.15/1.01  res_forward_subset_subsumed:            4
% 1.15/1.01  res_backward_subset_subsumed:           2
% 1.15/1.01  res_forward_subsumed:                   0
% 1.15/1.01  res_backward_subsumed:                  0
% 1.15/1.01  res_forward_subsumption_resolution:     0
% 1.15/1.01  res_backward_subsumption_resolution:    0
% 1.15/1.01  res_clause_to_clause_subsumption:       12
% 1.15/1.01  res_orphan_elimination:                 0
% 1.15/1.01  res_tautology_del:                      26
% 1.15/1.01  res_num_eq_res_simplified:              0
% 1.15/1.01  res_num_sel_changes:                    0
% 1.15/1.01  res_moves_from_active_to_pass:          0
% 1.15/1.01  
% 1.15/1.01  ------ Superposition
% 1.15/1.01  
% 1.15/1.01  sup_time_total:                         0.
% 1.15/1.01  sup_time_generating:                    0.
% 1.15/1.01  sup_time_sim_full:                      0.
% 1.15/1.01  sup_time_sim_immed:                     0.
% 1.15/1.01  
% 1.15/1.01  sup_num_of_clauses:                     12
% 1.15/1.01  sup_num_in_active:                      9
% 1.15/1.01  sup_num_in_passive:                     3
% 1.15/1.01  sup_num_of_loops:                       8
% 1.15/1.01  sup_fw_superposition:                   2
% 1.15/1.01  sup_bw_superposition:                   0
% 1.15/1.01  sup_immediate_simplified:               0
% 1.15/1.01  sup_given_eliminated:                   0
% 1.15/1.01  comparisons_done:                       0
% 1.15/1.01  comparisons_avoided:                    0
% 1.15/1.01  
% 1.15/1.01  ------ Simplifications
% 1.15/1.01  
% 1.15/1.01  
% 1.15/1.01  sim_fw_subset_subsumed:                 0
% 1.15/1.01  sim_bw_subset_subsumed:                 0
% 1.15/1.01  sim_fw_subsumed:                        0
% 1.15/1.01  sim_bw_subsumed:                        0
% 1.15/1.01  sim_fw_subsumption_res:                 0
% 1.15/1.01  sim_bw_subsumption_res:                 0
% 1.15/1.01  sim_tautology_del:                      0
% 1.15/1.01  sim_eq_tautology_del:                   0
% 1.15/1.01  sim_eq_res_simp:                        0
% 1.15/1.01  sim_fw_demodulated:                     0
% 1.15/1.01  sim_bw_demodulated:                     0
% 1.15/1.01  sim_light_normalised:                   1
% 1.15/1.01  sim_joinable_taut:                      0
% 1.15/1.01  sim_joinable_simp:                      0
% 1.15/1.01  sim_ac_normalised:                      0
% 1.15/1.01  sim_smt_subsumption:                    0
% 1.15/1.01  
%------------------------------------------------------------------------------
