%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:18:27 EST 2020

% Result     : Theorem 23.27s
% Output     : CNFRefutation 23.27s
% Verified   : 
% Statistics : Number of formulae       :  219 (1820 expanded)
%              Number of clauses        :  128 ( 452 expanded)
%              Number of leaves         :   26 ( 467 expanded)
%              Depth                    :   29
%              Number of atoms          :  806 (11139 expanded)
%              Number of equality atoms :  165 ( 538 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f43,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f42])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f43,f44])).

fof(f67,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f50,plain,(
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
    inference(rectify,[],[f49])).

fof(f51,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK2(X0,X1) != X0
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( sK2(X0,X1) = X0
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK2(X0,X1) != X0
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( sK2(X0,X1) = X0
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f50,f51])).

fof(f73,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f5,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f108,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f73,f76])).

fof(f112,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_tarski(X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f108])).

fof(f113,plain,(
    ! [X3] : r2_hidden(X3,k2_tarski(X3,X3)) ),
    inference(equality_resolution,[],[f112])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f85,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f110,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f85,f76])).

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

fof(f40,plain,(
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

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f61,plain,(
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
    inference(nnf_transformation,[],[f41])).

fof(f62,plain,(
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
    inference(flattening,[],[f61])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ m1_connsp_2(X2,X0,X1)
            | ~ m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) )
          & ( m1_connsp_2(X2,X0,X1)
            | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ~ m1_connsp_2(sK6,X0,X1)
          | ~ m2_connsp_2(sK6,X0,k6_domain_1(u1_struct_0(X0),X1)) )
        & ( m1_connsp_2(sK6,X0,X1)
          | m2_connsp_2(sK6,X0,k6_domain_1(u1_struct_0(X0),X1)) )
        & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
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
            ( ( ~ m1_connsp_2(X2,X0,sK5)
              | ~ m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),sK5)) )
            & ( m1_connsp_2(X2,X0,sK5)
              | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),sK5)) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK5,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,
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
              ( ( ~ m1_connsp_2(X2,sK4,X1)
                | ~ m2_connsp_2(X2,sK4,k6_domain_1(u1_struct_0(sK4),X1)) )
              & ( m1_connsp_2(X2,sK4,X1)
                | m2_connsp_2(X2,sK4,k6_domain_1(u1_struct_0(sK4),X1)) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4))) )
          & m1_subset_1(X1,u1_struct_0(sK4)) )
      & l1_pre_topc(sK4)
      & v2_pre_topc(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,
    ( ( ~ m1_connsp_2(sK6,sK4,sK5)
      | ~ m2_connsp_2(sK6,sK4,k6_domain_1(u1_struct_0(sK4),sK5)) )
    & ( m1_connsp_2(sK6,sK4,sK5)
      | m2_connsp_2(sK6,sK4,k6_domain_1(u1_struct_0(sK4),sK5)) )
    & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
    & m1_subset_1(sK5,u1_struct_0(sK4))
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f62,f65,f64,f63])).

fof(f102,plain,(
    m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f66])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f93,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f111,plain,(
    ! [X0,X1] :
      ( k2_tarski(X1,X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f93,f76])).

fof(f99,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f66])).

fof(f101,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f66])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f92,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f91,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f104,plain,
    ( m1_connsp_2(sK6,sK4,sK5)
    | m2_connsp_2(sK6,sK4,k6_domain_1(u1_struct_0(sK4),sK5)) ),
    inference(cnf_transformation,[],[f66])).

fof(f17,axiom,(
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

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f60,plain,(
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
    inference(nnf_transformation,[],[f37])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m2_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f100,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f66])).

fof(f103,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f66])).

fof(f16,axiom,(
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

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f59,plain,(
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
    inference(nnf_transformation,[],[f35])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f88,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f105,plain,
    ( ~ m1_connsp_2(sK6,sK4,sK5)
    | ~ m2_connsp_2(sK6,sK4,k6_domain_1(u1_struct_0(sK4),sK5)) ),
    inference(cnf_transformation,[],[f66])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( m2_connsp_2(X2,X0,X1)
      | ~ r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f83,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f46,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK1(X0,X1),X1)
          | ~ r2_hidden(sK1(X0,X1),X0) )
        & ( r2_hidden(sK1(X0,X1),X1)
          | r2_hidden(sK1(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK1(X0,X1),X1)
          | ~ r2_hidden(sK1(X0,X1),X0) )
        & ( r2_hidden(sK1(X0,X1),X1)
          | r2_hidden(sK1(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f46,f47])).

fof(f69,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK1(X0,X1),X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f12,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_14598,plain,
    ( ~ r2_hidden(sK1(sK5,X0),sK5)
    | ~ v1_xboole_0(sK5) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_74668,plain,
    ( ~ r2_hidden(sK1(sK5,k1_tops_1(sK4,sK6)),sK5)
    | ~ v1_xboole_0(sK5) ),
    inference(instantiation,[status(thm)],[c_14598])).

cnf(c_1669,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_5885,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k2_tarski(X2,X2))
    | X0 != X2
    | X1 != k2_tarski(X2,X2) ),
    inference(instantiation,[status(thm)],[c_1669])).

cnf(c_16885,plain,
    ( r2_hidden(X0,k6_domain_1(u1_struct_0(sK4),X1))
    | ~ r2_hidden(X1,k2_tarski(X1,X1))
    | X0 != X1
    | k6_domain_1(u1_struct_0(sK4),X1) != k2_tarski(X1,X1) ),
    inference(instantiation,[status(thm)],[c_5885])).

cnf(c_44950,plain,
    ( r2_hidden(k1_tops_1(sK4,sK6),k6_domain_1(u1_struct_0(sK4),sK5))
    | ~ r2_hidden(sK5,k2_tarski(sK5,sK5))
    | k1_tops_1(sK4,sK6) != sK5
    | k6_domain_1(u1_struct_0(sK4),sK5) != k2_tarski(sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_16885])).

cnf(c_7235,plain,
    ( ~ r2_hidden(sK1(sK5,X0),X0)
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_26397,plain,
    ( ~ r2_hidden(sK1(sK5,k1_tops_1(sK4,sK6)),k1_tops_1(sK4,sK6))
    | ~ v1_xboole_0(k1_tops_1(sK4,sK6)) ),
    inference(instantiation,[status(thm)],[c_7235])).

cnf(c_7,plain,
    ( r2_hidden(X0,k2_tarski(X0,X0)) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_20037,plain,
    ( r2_hidden(sK5,k2_tarski(sK5,sK5)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1672,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2370,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | k6_domain_1(u1_struct_0(sK4),sK5) != X0
    | k1_zfmisc_1(u1_struct_0(sK4)) != X1 ),
    inference(instantiation,[status(thm)],[c_1672])).

cnf(c_3010,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(k2_tarski(sK5,sK5),X0)
    | k6_domain_1(u1_struct_0(sK4),sK5) != k2_tarski(sK5,sK5)
    | k1_zfmisc_1(u1_struct_0(sK4)) != X0 ),
    inference(instantiation,[status(thm)],[c_2370])).

cnf(c_4927,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(X0))
    | k6_domain_1(u1_struct_0(sK4),sK5) != k2_tarski(sK5,sK5)
    | k1_zfmisc_1(u1_struct_0(sK4)) != k1_zfmisc_1(X0) ),
    inference(instantiation,[status(thm)],[c_3010])).

cnf(c_16081,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | k6_domain_1(u1_struct_0(sK4),sK5) != k2_tarski(sK5,sK5)
    | k1_zfmisc_1(u1_struct_0(sK4)) != k1_zfmisc_1(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_4927])).

cnf(c_17,plain,
    ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_3835,plain,
    ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X0,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_11089,plain,
    ( m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3835])).

cnf(c_2283,plain,
    ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1)) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_2276,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_2278,plain,
    ( k6_domain_1(X0,X1) = k2_tarski(X1,X1)
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2933,plain,
    ( k6_domain_1(u1_struct_0(sK4),sK5) = k2_tarski(sK5,sK5)
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2276,c_2278])).

cnf(c_37,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_35,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_24,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_64,plain,
    ( v2_struct_0(sK4)
    | ~ l1_struct_0(sK4)
    | ~ v1_xboole_0(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_23,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_67,plain,
    ( ~ l1_pre_topc(sK4)
    | l1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_2341,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | v1_xboole_0(u1_struct_0(sK4))
    | k6_domain_1(u1_struct_0(sK4),X0) = k2_tarski(X0,X0) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_2452,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | v1_xboole_0(u1_struct_0(sK4))
    | k6_domain_1(u1_struct_0(sK4),sK5) = k2_tarski(sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_2341])).

cnf(c_3252,plain,
    ( k6_domain_1(u1_struct_0(sK4),sK5) = k2_tarski(sK5,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2933,c_37,c_35,c_34,c_64,c_67,c_2452])).

cnf(c_32,negated_conjecture,
    ( m2_connsp_2(sK6,sK4,k6_domain_1(u1_struct_0(sK4),sK5))
    | m1_connsp_2(sK6,sK4,sK5) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_320,plain,
    ( m1_connsp_2(sK6,sK4,sK5)
    | m2_connsp_2(sK6,sK4,k6_domain_1(u1_struct_0(sK4),sK5)) ),
    inference(prop_impl,[status(thm)],[c_32])).

cnf(c_321,plain,
    ( m2_connsp_2(sK6,sK4,k6_domain_1(u1_struct_0(sK4),sK5))
    | m1_connsp_2(sK6,sK4,sK5) ),
    inference(renaming,[status(thm)],[c_320])).

cnf(c_29,plain,
    ( ~ m2_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_632,plain,
    ( ~ m2_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_35])).

cnf(c_633,plain,
    ( ~ m2_connsp_2(X0,sK4,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_tarski(X1,k1_tops_1(sK4,X0))
    | ~ v2_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_632])).

cnf(c_36,negated_conjecture,
    ( v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_637,plain,
    ( r1_tarski(X1,k1_tops_1(sK4,X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m2_connsp_2(X0,sK4,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_633,c_36])).

cnf(c_638,plain,
    ( ~ m2_connsp_2(X0,sK4,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_tarski(X1,k1_tops_1(sK4,X0)) ),
    inference(renaming,[status(thm)],[c_637])).

cnf(c_692,plain,
    ( m1_connsp_2(sK6,sK4,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_tarski(X1,k1_tops_1(sK4,X0))
    | k6_domain_1(u1_struct_0(sK4),sK5) != X1
    | sK4 != sK4
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_321,c_638])).

cnf(c_693,plain,
    ( m1_connsp_2(sK6,sK4,sK5)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_tarski(k6_domain_1(u1_struct_0(sK4),sK5),k1_tops_1(sK4,sK6)) ),
    inference(unflattening,[status(thm)],[c_692])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_695,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_connsp_2(sK6,sK4,sK5)
    | r1_tarski(k6_domain_1(u1_struct_0(sK4),sK5),k1_tops_1(sK4,sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_693,c_33])).

cnf(c_696,plain,
    ( m1_connsp_2(sK6,sK4,sK5)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_tarski(k6_domain_1(u1_struct_0(sK4),sK5),k1_tops_1(sK4,sK6)) ),
    inference(renaming,[status(thm)],[c_695])).

cnf(c_27,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_30,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_221,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X0,X1,X2)
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_27,c_30])).

cnf(c_222,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_221])).

cnf(c_551,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_222,c_37])).

cnf(c_552,plain,
    ( ~ m1_connsp_2(X0,sK4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | r2_hidden(X1,k1_tops_1(sK4,X0))
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_551])).

cnf(c_556,plain,
    ( ~ m1_connsp_2(X0,sK4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | r2_hidden(X1,k1_tops_1(sK4,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_552,c_36,c_35])).

cnf(c_739,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_tarski(k6_domain_1(u1_struct_0(sK4),sK5),k1_tops_1(sK4,sK6))
    | r2_hidden(X0,k1_tops_1(sK4,X1))
    | sK5 != X0
    | sK4 != sK4
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_696,c_556])).

cnf(c_740,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | r1_tarski(k6_domain_1(u1_struct_0(sK4),sK5),k1_tops_1(sK4,sK6))
    | r2_hidden(sK5,k1_tops_1(sK4,sK6)) ),
    inference(unflattening,[status(thm)],[c_739])).

cnf(c_742,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_tarski(k6_domain_1(u1_struct_0(sK4),sK5),k1_tops_1(sK4,sK6))
    | r2_hidden(sK5,k1_tops_1(sK4,sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_740,c_34])).

cnf(c_2273,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(k6_domain_1(u1_struct_0(sK4),sK5),k1_tops_1(sK4,sK6)) = iProver_top
    | r2_hidden(sK5,k1_tops_1(sK4,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_742])).

cnf(c_3254,plain,
    ( m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(k2_tarski(sK5,sK5),k1_tops_1(sK4,sK6)) = iProver_top
    | r2_hidden(sK5,k1_tops_1(sK4,sK6)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3252,c_2273])).

cnf(c_4242,plain,
    ( r1_tarski(k2_tarski(sK5,sK5),k1_tops_1(sK4,sK6)) = iProver_top
    | r2_hidden(sK5,k1_tops_1(sK4,sK6)) = iProver_top
    | r2_hidden(sK5,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2283,c_3254])).

cnf(c_38,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_40,plain,
    ( l1_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_41,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_63,plain,
    ( v2_struct_0(X0) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_65,plain,
    ( v2_struct_0(sK4) = iProver_top
    | l1_struct_0(sK4) != iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_63])).

cnf(c_66,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_68,plain,
    ( l1_pre_topc(sK4) != iProver_top
    | l1_struct_0(sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_66])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_2343,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r2_hidden(X0,u1_struct_0(sK4))
    | v1_xboole_0(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_2433,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | r2_hidden(sK5,u1_struct_0(sK4))
    | v1_xboole_0(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2343])).

cnf(c_2434,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK5,u1_struct_0(sK4)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2433])).

cnf(c_4994,plain,
    ( r2_hidden(sK5,k1_tops_1(sK4,sK6)) = iProver_top
    | r1_tarski(k2_tarski(sK5,sK5),k1_tops_1(sK4,sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4242,c_38,c_40,c_41,c_65,c_68,c_2434])).

cnf(c_4995,plain,
    ( r1_tarski(k2_tarski(sK5,sK5),k1_tops_1(sK4,sK6)) = iProver_top
    | r2_hidden(sK5,k1_tops_1(sK4,sK6)) = iProver_top ),
    inference(renaming,[status(thm)],[c_4994])).

cnf(c_2292,plain,
    ( r2_hidden(X0,k2_tarski(X0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_19,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_2282,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_21,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2280,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3652,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2282,c_2280])).

cnf(c_7686,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r1_tarski(k2_tarski(X0,X0),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2292,c_3652])).

cnf(c_9653,plain,
    ( m1_subset_1(sK5,k1_tops_1(sK4,sK6)) = iProver_top
    | r2_hidden(sK5,k1_tops_1(sK4,sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4995,c_7686])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2281,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4239,plain,
    ( r1_tarski(k2_tarski(X0,X0),X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2283,c_2281])).

cnf(c_31,negated_conjecture,
    ( ~ m2_connsp_2(sK6,sK4,k6_domain_1(u1_struct_0(sK4),sK5))
    | ~ m1_connsp_2(sK6,sK4,sK5) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_318,plain,
    ( ~ m1_connsp_2(sK6,sK4,sK5)
    | ~ m2_connsp_2(sK6,sK4,k6_domain_1(u1_struct_0(sK4),sK5)) ),
    inference(prop_impl,[status(thm)],[c_31])).

cnf(c_319,plain,
    ( ~ m2_connsp_2(sK6,sK4,k6_domain_1(u1_struct_0(sK4),sK5))
    | ~ m1_connsp_2(sK6,sK4,sK5) ),
    inference(renaming,[status(thm)],[c_318])).

cnf(c_28,plain,
    ( m2_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_656,plain,
    ( m2_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_35])).

cnf(c_657,plain,
    ( m2_connsp_2(X0,sK4,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(X1,k1_tops_1(sK4,X0))
    | ~ v2_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_656])).

cnf(c_661,plain,
    ( ~ r1_tarski(X1,k1_tops_1(sK4,X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m2_connsp_2(X0,sK4,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_657,c_36])).

cnf(c_662,plain,
    ( m2_connsp_2(X0,sK4,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(X1,k1_tops_1(sK4,X0)) ),
    inference(renaming,[status(thm)],[c_661])).

cnf(c_709,plain,
    ( ~ m1_connsp_2(sK6,sK4,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(X1,k1_tops_1(sK4,X0))
    | k6_domain_1(u1_struct_0(sK4),sK5) != X1
    | sK4 != sK4
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_319,c_662])).

cnf(c_710,plain,
    ( ~ m1_connsp_2(sK6,sK4,sK5)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(k6_domain_1(u1_struct_0(sK4),sK5),k1_tops_1(sK4,sK6)) ),
    inference(unflattening,[status(thm)],[c_709])).

cnf(c_712,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_connsp_2(sK6,sK4,sK5)
    | ~ r1_tarski(k6_domain_1(u1_struct_0(sK4),sK5),k1_tops_1(sK4,sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_710,c_33])).

cnf(c_713,plain,
    ( ~ m1_connsp_2(sK6,sK4,sK5)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(k6_domain_1(u1_struct_0(sK4),sK5),k1_tops_1(sK4,sK6)) ),
    inference(renaming,[status(thm)],[c_712])).

cnf(c_26,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_593,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_37])).

cnf(c_594,plain,
    ( m1_connsp_2(X0,sK4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X1,k1_tops_1(sK4,X0))
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_593])).

cnf(c_598,plain,
    ( m1_connsp_2(X0,sK4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X1,k1_tops_1(sK4,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_594,c_36,c_35])).

cnf(c_756,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(k6_domain_1(u1_struct_0(sK4),sK5),k1_tops_1(sK4,sK6))
    | ~ r2_hidden(X0,k1_tops_1(sK4,X1))
    | sK5 != X0
    | sK4 != sK4
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_713,c_598])).

cnf(c_757,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(k6_domain_1(u1_struct_0(sK4),sK5),k1_tops_1(sK4,sK6))
    | ~ r2_hidden(sK5,k1_tops_1(sK4,sK6)) ),
    inference(unflattening,[status(thm)],[c_756])).

cnf(c_759,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(k6_domain_1(u1_struct_0(sK4),sK5),k1_tops_1(sK4,sK6))
    | ~ r2_hidden(sK5,k1_tops_1(sK4,sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_757,c_34,c_33])).

cnf(c_2272,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(k6_domain_1(u1_struct_0(sK4),sK5),k1_tops_1(sK4,sK6)) != iProver_top
    | r2_hidden(sK5,k1_tops_1(sK4,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_759])).

cnf(c_3255,plain,
    ( m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(k2_tarski(sK5,sK5),k1_tops_1(sK4,sK6)) != iProver_top
    | r2_hidden(sK5,k1_tops_1(sK4,sK6)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3252,c_2272])).

cnf(c_4243,plain,
    ( r1_tarski(k2_tarski(sK5,sK5),k1_tops_1(sK4,sK6)) != iProver_top
    | r2_hidden(sK5,k1_tops_1(sK4,sK6)) != iProver_top
    | r2_hidden(sK5,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2283,c_3255])).

cnf(c_4987,plain,
    ( r2_hidden(sK5,k1_tops_1(sK4,sK6)) != iProver_top
    | r1_tarski(k2_tarski(sK5,sK5),k1_tops_1(sK4,sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4243,c_38,c_40,c_41,c_65,c_68,c_2434])).

cnf(c_4988,plain,
    ( r1_tarski(k2_tarski(sK5,sK5),k1_tops_1(sK4,sK6)) != iProver_top
    | r2_hidden(sK5,k1_tops_1(sK4,sK6)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4987])).

cnf(c_9440,plain,
    ( r2_hidden(sK5,k1_tops_1(sK4,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4239,c_4988])).

cnf(c_9867,plain,
    ( m1_subset_1(sK5,k1_tops_1(sK4,sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9653,c_9440])).

cnf(c_2284,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_9872,plain,
    ( r2_hidden(sK5,k1_tops_1(sK4,sK6)) = iProver_top
    | v1_xboole_0(k1_tops_1(sK4,sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_9867,c_2284])).

cnf(c_9875,plain,
    ( r2_hidden(sK5,k1_tops_1(sK4,sK6))
    | v1_xboole_0(k1_tops_1(sK4,sK6)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_9872])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2285,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_9871,plain,
    ( v1_xboole_0(k1_tops_1(sK4,sK6)) != iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_9867,c_2285])).

cnf(c_9874,plain,
    ( ~ v1_xboole_0(k1_tops_1(sK4,sK6))
    | v1_xboole_0(sK5) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_9871])).

cnf(c_9457,plain,
    ( ~ r2_hidden(sK5,k1_tops_1(sK4,sK6)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_9440])).

cnf(c_3,plain,
    ( r2_hidden(sK1(X0,X1),X1)
    | r2_hidden(sK1(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_3602,plain,
    ( r2_hidden(sK1(X0,k1_tops_1(sK4,sK6)),X0)
    | r2_hidden(sK1(X0,k1_tops_1(sK4,sK6)),k1_tops_1(sK4,sK6))
    | k1_tops_1(sK4,sK6) = X0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_6867,plain,
    ( r2_hidden(sK1(sK5,k1_tops_1(sK4,sK6)),k1_tops_1(sK4,sK6))
    | r2_hidden(sK1(sK5,k1_tops_1(sK4,sK6)),sK5)
    | k1_tops_1(sK4,sK6) = sK5 ),
    inference(instantiation,[status(thm)],[c_3602])).

cnf(c_1666,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2981,plain,
    ( k1_zfmisc_1(u1_struct_0(sK4)) = k1_zfmisc_1(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1666])).

cnf(c_22,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1020,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X0,X1)
    | r2_hidden(sK5,k1_tops_1(sK4,sK6))
    | k1_tops_1(sK4,sK6) != X0
    | k6_domain_1(u1_struct_0(sK4),sK5) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_742])).

cnf(c_1021,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(k1_tops_1(sK4,sK6),k6_domain_1(u1_struct_0(sK4),sK5))
    | r2_hidden(sK5,k1_tops_1(sK4,sK6)) ),
    inference(unflattening,[status(thm)],[c_1020])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_74668,c_44950,c_26397,c_20037,c_16081,c_11089,c_9875,c_9874,c_9457,c_6867,c_2981,c_2452,c_2433,c_1021,c_67,c_64,c_34,c_35,c_37])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:08:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 23.27/3.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.27/3.49  
% 23.27/3.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.27/3.49  
% 23.27/3.49  ------  iProver source info
% 23.27/3.49  
% 23.27/3.49  git: date: 2020-06-30 10:37:57 +0100
% 23.27/3.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.27/3.49  git: non_committed_changes: false
% 23.27/3.49  git: last_make_outside_of_git: false
% 23.27/3.49  
% 23.27/3.49  ------ 
% 23.27/3.49  
% 23.27/3.49  ------ Input Options
% 23.27/3.49  
% 23.27/3.49  --out_options                           all
% 23.27/3.49  --tptp_safe_out                         true
% 23.27/3.49  --problem_path                          ""
% 23.27/3.49  --include_path                          ""
% 23.27/3.49  --clausifier                            res/vclausify_rel
% 23.27/3.49  --clausifier_options                    ""
% 23.27/3.49  --stdin                                 false
% 23.27/3.49  --stats_out                             all
% 23.27/3.49  
% 23.27/3.49  ------ General Options
% 23.27/3.49  
% 23.27/3.49  --fof                                   false
% 23.27/3.49  --time_out_real                         305.
% 23.27/3.49  --time_out_virtual                      -1.
% 23.27/3.49  --symbol_type_check                     false
% 23.27/3.49  --clausify_out                          false
% 23.27/3.49  --sig_cnt_out                           false
% 23.27/3.49  --trig_cnt_out                          false
% 23.27/3.49  --trig_cnt_out_tolerance                1.
% 23.27/3.49  --trig_cnt_out_sk_spl                   false
% 23.27/3.49  --abstr_cl_out                          false
% 23.27/3.49  
% 23.27/3.49  ------ Global Options
% 23.27/3.49  
% 23.27/3.49  --schedule                              default
% 23.27/3.49  --add_important_lit                     false
% 23.27/3.49  --prop_solver_per_cl                    1000
% 23.27/3.49  --min_unsat_core                        false
% 23.27/3.49  --soft_assumptions                      false
% 23.27/3.49  --soft_lemma_size                       3
% 23.27/3.49  --prop_impl_unit_size                   0
% 23.27/3.49  --prop_impl_unit                        []
% 23.27/3.49  --share_sel_clauses                     true
% 23.27/3.49  --reset_solvers                         false
% 23.27/3.49  --bc_imp_inh                            [conj_cone]
% 23.27/3.49  --conj_cone_tolerance                   3.
% 23.27/3.49  --extra_neg_conj                        none
% 23.27/3.49  --large_theory_mode                     true
% 23.27/3.49  --prolific_symb_bound                   200
% 23.27/3.49  --lt_threshold                          2000
% 23.27/3.49  --clause_weak_htbl                      true
% 23.27/3.49  --gc_record_bc_elim                     false
% 23.27/3.49  
% 23.27/3.49  ------ Preprocessing Options
% 23.27/3.49  
% 23.27/3.49  --preprocessing_flag                    true
% 23.27/3.49  --time_out_prep_mult                    0.1
% 23.27/3.49  --splitting_mode                        input
% 23.27/3.49  --splitting_grd                         true
% 23.27/3.49  --splitting_cvd                         false
% 23.27/3.49  --splitting_cvd_svl                     false
% 23.27/3.49  --splitting_nvd                         32
% 23.27/3.49  --sub_typing                            true
% 23.27/3.49  --prep_gs_sim                           true
% 23.27/3.49  --prep_unflatten                        true
% 23.27/3.49  --prep_res_sim                          true
% 23.27/3.49  --prep_upred                            true
% 23.27/3.49  --prep_sem_filter                       exhaustive
% 23.27/3.49  --prep_sem_filter_out                   false
% 23.27/3.49  --pred_elim                             true
% 23.27/3.49  --res_sim_input                         true
% 23.27/3.49  --eq_ax_congr_red                       true
% 23.27/3.49  --pure_diseq_elim                       true
% 23.27/3.49  --brand_transform                       false
% 23.27/3.49  --non_eq_to_eq                          false
% 23.27/3.49  --prep_def_merge                        true
% 23.27/3.49  --prep_def_merge_prop_impl              false
% 23.27/3.49  --prep_def_merge_mbd                    true
% 23.27/3.49  --prep_def_merge_tr_red                 false
% 23.27/3.49  --prep_def_merge_tr_cl                  false
% 23.27/3.49  --smt_preprocessing                     true
% 23.27/3.49  --smt_ac_axioms                         fast
% 23.27/3.49  --preprocessed_out                      false
% 23.27/3.49  --preprocessed_stats                    false
% 23.27/3.49  
% 23.27/3.49  ------ Abstraction refinement Options
% 23.27/3.49  
% 23.27/3.49  --abstr_ref                             []
% 23.27/3.49  --abstr_ref_prep                        false
% 23.27/3.49  --abstr_ref_until_sat                   false
% 23.27/3.49  --abstr_ref_sig_restrict                funpre
% 23.27/3.49  --abstr_ref_af_restrict_to_split_sk     false
% 23.27/3.49  --abstr_ref_under                       []
% 23.27/3.49  
% 23.27/3.49  ------ SAT Options
% 23.27/3.49  
% 23.27/3.49  --sat_mode                              false
% 23.27/3.49  --sat_fm_restart_options                ""
% 23.27/3.49  --sat_gr_def                            false
% 23.27/3.49  --sat_epr_types                         true
% 23.27/3.49  --sat_non_cyclic_types                  false
% 23.27/3.49  --sat_finite_models                     false
% 23.27/3.49  --sat_fm_lemmas                         false
% 23.27/3.49  --sat_fm_prep                           false
% 23.27/3.49  --sat_fm_uc_incr                        true
% 23.27/3.49  --sat_out_model                         small
% 23.27/3.49  --sat_out_clauses                       false
% 23.27/3.49  
% 23.27/3.49  ------ QBF Options
% 23.27/3.49  
% 23.27/3.49  --qbf_mode                              false
% 23.27/3.49  --qbf_elim_univ                         false
% 23.27/3.49  --qbf_dom_inst                          none
% 23.27/3.49  --qbf_dom_pre_inst                      false
% 23.27/3.49  --qbf_sk_in                             false
% 23.27/3.49  --qbf_pred_elim                         true
% 23.27/3.49  --qbf_split                             512
% 23.27/3.49  
% 23.27/3.49  ------ BMC1 Options
% 23.27/3.49  
% 23.27/3.49  --bmc1_incremental                      false
% 23.27/3.49  --bmc1_axioms                           reachable_all
% 23.27/3.49  --bmc1_min_bound                        0
% 23.27/3.49  --bmc1_max_bound                        -1
% 23.27/3.49  --bmc1_max_bound_default                -1
% 23.27/3.49  --bmc1_symbol_reachability              true
% 23.27/3.49  --bmc1_property_lemmas                  false
% 23.27/3.49  --bmc1_k_induction                      false
% 23.27/3.49  --bmc1_non_equiv_states                 false
% 23.27/3.49  --bmc1_deadlock                         false
% 23.27/3.49  --bmc1_ucm                              false
% 23.27/3.49  --bmc1_add_unsat_core                   none
% 23.27/3.49  --bmc1_unsat_core_children              false
% 23.27/3.49  --bmc1_unsat_core_extrapolate_axioms    false
% 23.27/3.49  --bmc1_out_stat                         full
% 23.27/3.49  --bmc1_ground_init                      false
% 23.27/3.49  --bmc1_pre_inst_next_state              false
% 23.27/3.49  --bmc1_pre_inst_state                   false
% 23.27/3.49  --bmc1_pre_inst_reach_state             false
% 23.27/3.49  --bmc1_out_unsat_core                   false
% 23.27/3.49  --bmc1_aig_witness_out                  false
% 23.27/3.49  --bmc1_verbose                          false
% 23.27/3.49  --bmc1_dump_clauses_tptp                false
% 23.27/3.49  --bmc1_dump_unsat_core_tptp             false
% 23.27/3.49  --bmc1_dump_file                        -
% 23.27/3.49  --bmc1_ucm_expand_uc_limit              128
% 23.27/3.49  --bmc1_ucm_n_expand_iterations          6
% 23.27/3.49  --bmc1_ucm_extend_mode                  1
% 23.27/3.49  --bmc1_ucm_init_mode                    2
% 23.27/3.49  --bmc1_ucm_cone_mode                    none
% 23.27/3.49  --bmc1_ucm_reduced_relation_type        0
% 23.27/3.49  --bmc1_ucm_relax_model                  4
% 23.27/3.49  --bmc1_ucm_full_tr_after_sat            true
% 23.27/3.49  --bmc1_ucm_expand_neg_assumptions       false
% 23.27/3.49  --bmc1_ucm_layered_model                none
% 23.27/3.49  --bmc1_ucm_max_lemma_size               10
% 23.27/3.49  
% 23.27/3.49  ------ AIG Options
% 23.27/3.49  
% 23.27/3.49  --aig_mode                              false
% 23.27/3.49  
% 23.27/3.49  ------ Instantiation Options
% 23.27/3.49  
% 23.27/3.49  --instantiation_flag                    true
% 23.27/3.49  --inst_sos_flag                         true
% 23.27/3.49  --inst_sos_phase                        true
% 23.27/3.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.27/3.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.27/3.49  --inst_lit_sel_side                     num_symb
% 23.27/3.49  --inst_solver_per_active                1400
% 23.27/3.49  --inst_solver_calls_frac                1.
% 23.27/3.49  --inst_passive_queue_type               priority_queues
% 23.27/3.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.27/3.49  --inst_passive_queues_freq              [25;2]
% 23.27/3.49  --inst_dismatching                      true
% 23.27/3.49  --inst_eager_unprocessed_to_passive     true
% 23.27/3.49  --inst_prop_sim_given                   true
% 23.27/3.49  --inst_prop_sim_new                     false
% 23.27/3.49  --inst_subs_new                         false
% 23.27/3.49  --inst_eq_res_simp                      false
% 23.27/3.49  --inst_subs_given                       false
% 23.27/3.49  --inst_orphan_elimination               true
% 23.27/3.49  --inst_learning_loop_flag               true
% 23.27/3.49  --inst_learning_start                   3000
% 23.27/3.49  --inst_learning_factor                  2
% 23.27/3.49  --inst_start_prop_sim_after_learn       3
% 23.27/3.49  --inst_sel_renew                        solver
% 23.27/3.49  --inst_lit_activity_flag                true
% 23.27/3.49  --inst_restr_to_given                   false
% 23.27/3.49  --inst_activity_threshold               500
% 23.27/3.49  --inst_out_proof                        true
% 23.27/3.49  
% 23.27/3.49  ------ Resolution Options
% 23.27/3.49  
% 23.27/3.49  --resolution_flag                       true
% 23.27/3.49  --res_lit_sel                           adaptive
% 23.27/3.49  --res_lit_sel_side                      none
% 23.27/3.49  --res_ordering                          kbo
% 23.27/3.49  --res_to_prop_solver                    active
% 23.27/3.49  --res_prop_simpl_new                    false
% 23.27/3.49  --res_prop_simpl_given                  true
% 23.27/3.49  --res_passive_queue_type                priority_queues
% 23.27/3.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.27/3.49  --res_passive_queues_freq               [15;5]
% 23.27/3.49  --res_forward_subs                      full
% 23.27/3.49  --res_backward_subs                     full
% 23.27/3.49  --res_forward_subs_resolution           true
% 23.27/3.49  --res_backward_subs_resolution          true
% 23.27/3.49  --res_orphan_elimination                true
% 23.27/3.49  --res_time_limit                        2.
% 23.27/3.49  --res_out_proof                         true
% 23.27/3.49  
% 23.27/3.49  ------ Superposition Options
% 23.27/3.49  
% 23.27/3.49  --superposition_flag                    true
% 23.27/3.49  --sup_passive_queue_type                priority_queues
% 23.27/3.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.27/3.49  --sup_passive_queues_freq               [8;1;4]
% 23.27/3.49  --demod_completeness_check              fast
% 23.27/3.49  --demod_use_ground                      true
% 23.27/3.49  --sup_to_prop_solver                    passive
% 23.27/3.49  --sup_prop_simpl_new                    true
% 23.27/3.49  --sup_prop_simpl_given                  true
% 23.27/3.49  --sup_fun_splitting                     true
% 23.27/3.49  --sup_smt_interval                      50000
% 23.27/3.49  
% 23.27/3.49  ------ Superposition Simplification Setup
% 23.27/3.49  
% 23.27/3.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 23.27/3.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 23.27/3.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 23.27/3.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 23.27/3.49  --sup_full_triv                         [TrivRules;PropSubs]
% 23.27/3.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 23.27/3.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 23.27/3.49  --sup_immed_triv                        [TrivRules]
% 23.27/3.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.27/3.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.27/3.49  --sup_immed_bw_main                     []
% 23.27/3.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 23.27/3.49  --sup_input_triv                        [Unflattening;TrivRules]
% 23.27/3.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.27/3.49  --sup_input_bw                          []
% 23.27/3.49  
% 23.27/3.49  ------ Combination Options
% 23.27/3.49  
% 23.27/3.49  --comb_res_mult                         3
% 23.27/3.49  --comb_sup_mult                         2
% 23.27/3.49  --comb_inst_mult                        10
% 23.27/3.49  
% 23.27/3.49  ------ Debug Options
% 23.27/3.49  
% 23.27/3.49  --dbg_backtrace                         false
% 23.27/3.49  --dbg_dump_prop_clauses                 false
% 23.27/3.49  --dbg_dump_prop_clauses_file            -
% 23.27/3.49  --dbg_out_stat                          false
% 23.27/3.49  ------ Parsing...
% 23.27/3.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.27/3.49  
% 23.27/3.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 23.27/3.49  
% 23.27/3.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.27/3.49  
% 23.27/3.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.27/3.49  ------ Proving...
% 23.27/3.49  ------ Problem Properties 
% 23.27/3.49  
% 23.27/3.49  
% 23.27/3.49  clauses                                 28
% 23.27/3.49  conjectures                             2
% 23.27/3.49  EPR                                     7
% 23.27/3.49  Horn                                    21
% 23.27/3.49  unary                                   5
% 23.27/3.49  binary                                  10
% 23.27/3.49  lits                                    64
% 23.27/3.49  lits eq                                 10
% 23.27/3.49  fd_pure                                 0
% 23.27/3.49  fd_pseudo                               0
% 23.27/3.49  fd_cond                                 0
% 23.27/3.49  fd_pseudo_cond                          6
% 23.27/3.49  AC symbols                              0
% 23.27/3.49  
% 23.27/3.49  ------ Schedule dynamic 5 is on 
% 23.27/3.49  
% 23.27/3.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 23.27/3.49  
% 23.27/3.49  
% 23.27/3.49  ------ 
% 23.27/3.49  Current options:
% 23.27/3.49  ------ 
% 23.27/3.49  
% 23.27/3.49  ------ Input Options
% 23.27/3.49  
% 23.27/3.49  --out_options                           all
% 23.27/3.49  --tptp_safe_out                         true
% 23.27/3.49  --problem_path                          ""
% 23.27/3.49  --include_path                          ""
% 23.27/3.49  --clausifier                            res/vclausify_rel
% 23.27/3.49  --clausifier_options                    ""
% 23.27/3.49  --stdin                                 false
% 23.27/3.49  --stats_out                             all
% 23.27/3.49  
% 23.27/3.49  ------ General Options
% 23.27/3.49  
% 23.27/3.49  --fof                                   false
% 23.27/3.49  --time_out_real                         305.
% 23.27/3.49  --time_out_virtual                      -1.
% 23.27/3.49  --symbol_type_check                     false
% 23.27/3.49  --clausify_out                          false
% 23.27/3.49  --sig_cnt_out                           false
% 23.27/3.49  --trig_cnt_out                          false
% 23.27/3.49  --trig_cnt_out_tolerance                1.
% 23.27/3.49  --trig_cnt_out_sk_spl                   false
% 23.27/3.49  --abstr_cl_out                          false
% 23.27/3.49  
% 23.27/3.49  ------ Global Options
% 23.27/3.49  
% 23.27/3.49  --schedule                              default
% 23.27/3.49  --add_important_lit                     false
% 23.27/3.49  --prop_solver_per_cl                    1000
% 23.27/3.49  --min_unsat_core                        false
% 23.27/3.49  --soft_assumptions                      false
% 23.27/3.49  --soft_lemma_size                       3
% 23.27/3.49  --prop_impl_unit_size                   0
% 23.27/3.49  --prop_impl_unit                        []
% 23.27/3.49  --share_sel_clauses                     true
% 23.27/3.49  --reset_solvers                         false
% 23.27/3.49  --bc_imp_inh                            [conj_cone]
% 23.27/3.49  --conj_cone_tolerance                   3.
% 23.27/3.49  --extra_neg_conj                        none
% 23.27/3.49  --large_theory_mode                     true
% 23.27/3.49  --prolific_symb_bound                   200
% 23.27/3.49  --lt_threshold                          2000
% 23.27/3.49  --clause_weak_htbl                      true
% 23.27/3.49  --gc_record_bc_elim                     false
% 23.27/3.49  
% 23.27/3.49  ------ Preprocessing Options
% 23.27/3.49  
% 23.27/3.49  --preprocessing_flag                    true
% 23.27/3.49  --time_out_prep_mult                    0.1
% 23.27/3.49  --splitting_mode                        input
% 23.27/3.49  --splitting_grd                         true
% 23.27/3.49  --splitting_cvd                         false
% 23.27/3.49  --splitting_cvd_svl                     false
% 23.27/3.49  --splitting_nvd                         32
% 23.27/3.49  --sub_typing                            true
% 23.27/3.49  --prep_gs_sim                           true
% 23.27/3.49  --prep_unflatten                        true
% 23.27/3.49  --prep_res_sim                          true
% 23.27/3.49  --prep_upred                            true
% 23.27/3.49  --prep_sem_filter                       exhaustive
% 23.27/3.49  --prep_sem_filter_out                   false
% 23.27/3.49  --pred_elim                             true
% 23.27/3.49  --res_sim_input                         true
% 23.27/3.49  --eq_ax_congr_red                       true
% 23.27/3.49  --pure_diseq_elim                       true
% 23.27/3.49  --brand_transform                       false
% 23.27/3.49  --non_eq_to_eq                          false
% 23.27/3.49  --prep_def_merge                        true
% 23.27/3.49  --prep_def_merge_prop_impl              false
% 23.27/3.49  --prep_def_merge_mbd                    true
% 23.27/3.49  --prep_def_merge_tr_red                 false
% 23.27/3.49  --prep_def_merge_tr_cl                  false
% 23.27/3.49  --smt_preprocessing                     true
% 23.27/3.49  --smt_ac_axioms                         fast
% 23.27/3.49  --preprocessed_out                      false
% 23.27/3.49  --preprocessed_stats                    false
% 23.27/3.49  
% 23.27/3.49  ------ Abstraction refinement Options
% 23.27/3.49  
% 23.27/3.49  --abstr_ref                             []
% 23.27/3.49  --abstr_ref_prep                        false
% 23.27/3.49  --abstr_ref_until_sat                   false
% 23.27/3.49  --abstr_ref_sig_restrict                funpre
% 23.27/3.49  --abstr_ref_af_restrict_to_split_sk     false
% 23.27/3.49  --abstr_ref_under                       []
% 23.27/3.49  
% 23.27/3.49  ------ SAT Options
% 23.27/3.49  
% 23.27/3.49  --sat_mode                              false
% 23.27/3.49  --sat_fm_restart_options                ""
% 23.27/3.49  --sat_gr_def                            false
% 23.27/3.49  --sat_epr_types                         true
% 23.27/3.49  --sat_non_cyclic_types                  false
% 23.27/3.49  --sat_finite_models                     false
% 23.27/3.49  --sat_fm_lemmas                         false
% 23.27/3.49  --sat_fm_prep                           false
% 23.27/3.49  --sat_fm_uc_incr                        true
% 23.27/3.49  --sat_out_model                         small
% 23.27/3.49  --sat_out_clauses                       false
% 23.27/3.49  
% 23.27/3.49  ------ QBF Options
% 23.27/3.49  
% 23.27/3.49  --qbf_mode                              false
% 23.27/3.49  --qbf_elim_univ                         false
% 23.27/3.49  --qbf_dom_inst                          none
% 23.27/3.49  --qbf_dom_pre_inst                      false
% 23.27/3.49  --qbf_sk_in                             false
% 23.27/3.49  --qbf_pred_elim                         true
% 23.27/3.49  --qbf_split                             512
% 23.27/3.49  
% 23.27/3.49  ------ BMC1 Options
% 23.27/3.49  
% 23.27/3.49  --bmc1_incremental                      false
% 23.27/3.49  --bmc1_axioms                           reachable_all
% 23.27/3.49  --bmc1_min_bound                        0
% 23.27/3.49  --bmc1_max_bound                        -1
% 23.27/3.49  --bmc1_max_bound_default                -1
% 23.27/3.49  --bmc1_symbol_reachability              true
% 23.27/3.49  --bmc1_property_lemmas                  false
% 23.27/3.49  --bmc1_k_induction                      false
% 23.27/3.49  --bmc1_non_equiv_states                 false
% 23.27/3.49  --bmc1_deadlock                         false
% 23.27/3.49  --bmc1_ucm                              false
% 23.27/3.49  --bmc1_add_unsat_core                   none
% 23.27/3.49  --bmc1_unsat_core_children              false
% 23.27/3.49  --bmc1_unsat_core_extrapolate_axioms    false
% 23.27/3.49  --bmc1_out_stat                         full
% 23.27/3.49  --bmc1_ground_init                      false
% 23.27/3.49  --bmc1_pre_inst_next_state              false
% 23.27/3.49  --bmc1_pre_inst_state                   false
% 23.27/3.49  --bmc1_pre_inst_reach_state             false
% 23.27/3.49  --bmc1_out_unsat_core                   false
% 23.27/3.49  --bmc1_aig_witness_out                  false
% 23.27/3.49  --bmc1_verbose                          false
% 23.27/3.49  --bmc1_dump_clauses_tptp                false
% 23.27/3.49  --bmc1_dump_unsat_core_tptp             false
% 23.27/3.49  --bmc1_dump_file                        -
% 23.27/3.49  --bmc1_ucm_expand_uc_limit              128
% 23.27/3.49  --bmc1_ucm_n_expand_iterations          6
% 23.27/3.49  --bmc1_ucm_extend_mode                  1
% 23.27/3.49  --bmc1_ucm_init_mode                    2
% 23.27/3.49  --bmc1_ucm_cone_mode                    none
% 23.27/3.49  --bmc1_ucm_reduced_relation_type        0
% 23.27/3.49  --bmc1_ucm_relax_model                  4
% 23.27/3.49  --bmc1_ucm_full_tr_after_sat            true
% 23.27/3.49  --bmc1_ucm_expand_neg_assumptions       false
% 23.27/3.49  --bmc1_ucm_layered_model                none
% 23.27/3.49  --bmc1_ucm_max_lemma_size               10
% 23.27/3.49  
% 23.27/3.49  ------ AIG Options
% 23.27/3.49  
% 23.27/3.49  --aig_mode                              false
% 23.27/3.49  
% 23.27/3.49  ------ Instantiation Options
% 23.27/3.49  
% 23.27/3.49  --instantiation_flag                    true
% 23.27/3.49  --inst_sos_flag                         true
% 23.27/3.49  --inst_sos_phase                        true
% 23.27/3.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.27/3.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.27/3.49  --inst_lit_sel_side                     none
% 23.27/3.49  --inst_solver_per_active                1400
% 23.27/3.49  --inst_solver_calls_frac                1.
% 23.27/3.49  --inst_passive_queue_type               priority_queues
% 23.27/3.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.27/3.49  --inst_passive_queues_freq              [25;2]
% 23.27/3.49  --inst_dismatching                      true
% 23.27/3.49  --inst_eager_unprocessed_to_passive     true
% 23.27/3.49  --inst_prop_sim_given                   true
% 23.27/3.49  --inst_prop_sim_new                     false
% 23.27/3.49  --inst_subs_new                         false
% 23.27/3.49  --inst_eq_res_simp                      false
% 23.27/3.49  --inst_subs_given                       false
% 23.27/3.49  --inst_orphan_elimination               true
% 23.27/3.49  --inst_learning_loop_flag               true
% 23.27/3.49  --inst_learning_start                   3000
% 23.27/3.49  --inst_learning_factor                  2
% 23.27/3.49  --inst_start_prop_sim_after_learn       3
% 23.27/3.49  --inst_sel_renew                        solver
% 23.27/3.49  --inst_lit_activity_flag                true
% 23.27/3.49  --inst_restr_to_given                   false
% 23.27/3.49  --inst_activity_threshold               500
% 23.27/3.49  --inst_out_proof                        true
% 23.27/3.49  
% 23.27/3.49  ------ Resolution Options
% 23.27/3.49  
% 23.27/3.49  --resolution_flag                       false
% 23.27/3.49  --res_lit_sel                           adaptive
% 23.27/3.49  --res_lit_sel_side                      none
% 23.27/3.49  --res_ordering                          kbo
% 23.27/3.49  --res_to_prop_solver                    active
% 23.27/3.49  --res_prop_simpl_new                    false
% 23.27/3.49  --res_prop_simpl_given                  true
% 23.27/3.49  --res_passive_queue_type                priority_queues
% 23.27/3.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.27/3.49  --res_passive_queues_freq               [15;5]
% 23.27/3.49  --res_forward_subs                      full
% 23.27/3.49  --res_backward_subs                     full
% 23.27/3.49  --res_forward_subs_resolution           true
% 23.27/3.49  --res_backward_subs_resolution          true
% 23.27/3.49  --res_orphan_elimination                true
% 23.27/3.49  --res_time_limit                        2.
% 23.27/3.49  --res_out_proof                         true
% 23.27/3.49  
% 23.27/3.49  ------ Superposition Options
% 23.27/3.49  
% 23.27/3.49  --superposition_flag                    true
% 23.27/3.49  --sup_passive_queue_type                priority_queues
% 23.27/3.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.27/3.49  --sup_passive_queues_freq               [8;1;4]
% 23.27/3.49  --demod_completeness_check              fast
% 23.27/3.49  --demod_use_ground                      true
% 23.27/3.49  --sup_to_prop_solver                    passive
% 23.27/3.49  --sup_prop_simpl_new                    true
% 23.27/3.49  --sup_prop_simpl_given                  true
% 23.27/3.49  --sup_fun_splitting                     true
% 23.27/3.49  --sup_smt_interval                      50000
% 23.27/3.49  
% 23.27/3.49  ------ Superposition Simplification Setup
% 23.27/3.49  
% 23.27/3.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 23.27/3.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 23.27/3.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 23.27/3.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 23.27/3.49  --sup_full_triv                         [TrivRules;PropSubs]
% 23.27/3.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 23.27/3.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 23.27/3.49  --sup_immed_triv                        [TrivRules]
% 23.27/3.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.27/3.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.27/3.49  --sup_immed_bw_main                     []
% 23.27/3.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 23.27/3.49  --sup_input_triv                        [Unflattening;TrivRules]
% 23.27/3.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.27/3.49  --sup_input_bw                          []
% 23.27/3.49  
% 23.27/3.49  ------ Combination Options
% 23.27/3.49  
% 23.27/3.49  --comb_res_mult                         3
% 23.27/3.49  --comb_sup_mult                         2
% 23.27/3.49  --comb_inst_mult                        10
% 23.27/3.49  
% 23.27/3.49  ------ Debug Options
% 23.27/3.49  
% 23.27/3.49  --dbg_backtrace                         false
% 23.27/3.49  --dbg_dump_prop_clauses                 false
% 23.27/3.49  --dbg_dump_prop_clauses_file            -
% 23.27/3.49  --dbg_out_stat                          false
% 23.27/3.49  
% 23.27/3.49  
% 23.27/3.49  
% 23.27/3.49  
% 23.27/3.49  ------ Proving...
% 23.27/3.49  
% 23.27/3.49  
% 23.27/3.49  % SZS status Theorem for theBenchmark.p
% 23.27/3.49  
% 23.27/3.49  % SZS output start CNFRefutation for theBenchmark.p
% 23.27/3.49  
% 23.27/3.49  fof(f1,axiom,(
% 23.27/3.49    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 23.27/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.27/3.49  
% 23.27/3.49  fof(f42,plain,(
% 23.27/3.49    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 23.27/3.49    inference(nnf_transformation,[],[f1])).
% 23.27/3.49  
% 23.27/3.49  fof(f43,plain,(
% 23.27/3.49    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 23.27/3.49    inference(rectify,[],[f42])).
% 23.27/3.49  
% 23.27/3.49  fof(f44,plain,(
% 23.27/3.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 23.27/3.49    introduced(choice_axiom,[])).
% 23.27/3.49  
% 23.27/3.49  fof(f45,plain,(
% 23.27/3.49    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 23.27/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f43,f44])).
% 23.27/3.49  
% 23.27/3.49  fof(f67,plain,(
% 23.27/3.49    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 23.27/3.49    inference(cnf_transformation,[],[f45])).
% 23.27/3.49  
% 23.27/3.49  fof(f4,axiom,(
% 23.27/3.49    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 23.27/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.27/3.49  
% 23.27/3.49  fof(f49,plain,(
% 23.27/3.49    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 23.27/3.49    inference(nnf_transformation,[],[f4])).
% 23.27/3.49  
% 23.27/3.49  fof(f50,plain,(
% 23.27/3.49    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 23.27/3.49    inference(rectify,[],[f49])).
% 23.27/3.49  
% 23.27/3.49  fof(f51,plain,(
% 23.27/3.49    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 23.27/3.49    introduced(choice_axiom,[])).
% 23.27/3.49  
% 23.27/3.49  fof(f52,plain,(
% 23.27/3.49    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 23.27/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f50,f51])).
% 23.27/3.49  
% 23.27/3.49  fof(f73,plain,(
% 23.27/3.49    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 23.27/3.49    inference(cnf_transformation,[],[f52])).
% 23.27/3.49  
% 23.27/3.49  fof(f5,axiom,(
% 23.27/3.49    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 23.27/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.27/3.49  
% 23.27/3.49  fof(f76,plain,(
% 23.27/3.49    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 23.27/3.49    inference(cnf_transformation,[],[f5])).
% 23.27/3.49  
% 23.27/3.49  fof(f108,plain,(
% 23.27/3.49    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_tarski(X0,X0) != X1) )),
% 23.27/3.49    inference(definition_unfolding,[],[f73,f76])).
% 23.27/3.49  
% 23.27/3.49  fof(f112,plain,(
% 23.27/3.49    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_tarski(X3,X3) != X1) )),
% 23.27/3.49    inference(equality_resolution,[],[f108])).
% 23.27/3.49  
% 23.27/3.49  fof(f113,plain,(
% 23.27/3.49    ( ! [X3] : (r2_hidden(X3,k2_tarski(X3,X3))) )),
% 23.27/3.49    inference(equality_resolution,[],[f112])).
% 23.27/3.49  
% 23.27/3.49  fof(f8,axiom,(
% 23.27/3.49    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 23.27/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.27/3.49  
% 23.27/3.49  fof(f23,plain,(
% 23.27/3.49    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 23.27/3.49    inference(ennf_transformation,[],[f8])).
% 23.27/3.49  
% 23.27/3.49  fof(f85,plain,(
% 23.27/3.49    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 23.27/3.49    inference(cnf_transformation,[],[f23])).
% 23.27/3.49  
% 23.27/3.49  fof(f110,plain,(
% 23.27/3.49    ( ! [X0,X1] : (m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 23.27/3.49    inference(definition_unfolding,[],[f85,f76])).
% 23.27/3.49  
% 23.27/3.49  fof(f19,conjecture,(
% 23.27/3.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) <=> m1_connsp_2(X2,X0,X1)))))),
% 23.27/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.27/3.49  
% 23.27/3.49  fof(f20,negated_conjecture,(
% 23.27/3.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) <=> m1_connsp_2(X2,X0,X1)))))),
% 23.27/3.49    inference(negated_conjecture,[],[f19])).
% 23.27/3.49  
% 23.27/3.49  fof(f40,plain,(
% 23.27/3.49    ? [X0] : (? [X1] : (? [X2] : ((m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) <~> m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 23.27/3.49    inference(ennf_transformation,[],[f20])).
% 23.27/3.49  
% 23.27/3.49  fof(f41,plain,(
% 23.27/3.49    ? [X0] : (? [X1] : (? [X2] : ((m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) <~> m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 23.27/3.49    inference(flattening,[],[f40])).
% 23.27/3.49  
% 23.27/3.49  fof(f61,plain,(
% 23.27/3.49    ? [X0] : (? [X1] : (? [X2] : (((~m1_connsp_2(X2,X0,X1) | ~m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & (m1_connsp_2(X2,X0,X1) | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 23.27/3.49    inference(nnf_transformation,[],[f41])).
% 23.27/3.49  
% 23.27/3.49  fof(f62,plain,(
% 23.27/3.49    ? [X0] : (? [X1] : (? [X2] : ((~m1_connsp_2(X2,X0,X1) | ~m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & (m1_connsp_2(X2,X0,X1) | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 23.27/3.49    inference(flattening,[],[f61])).
% 23.27/3.49  
% 23.27/3.49  fof(f65,plain,(
% 23.27/3.49    ( ! [X0,X1] : (? [X2] : ((~m1_connsp_2(X2,X0,X1) | ~m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & (m1_connsp_2(X2,X0,X1) | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => ((~m1_connsp_2(sK6,X0,X1) | ~m2_connsp_2(sK6,X0,k6_domain_1(u1_struct_0(X0),X1))) & (m1_connsp_2(sK6,X0,X1) | m2_connsp_2(sK6,X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 23.27/3.49    introduced(choice_axiom,[])).
% 23.27/3.49  
% 23.27/3.49  fof(f64,plain,(
% 23.27/3.49    ( ! [X0] : (? [X1] : (? [X2] : ((~m1_connsp_2(X2,X0,X1) | ~m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & (m1_connsp_2(X2,X0,X1) | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : ((~m1_connsp_2(X2,X0,sK5) | ~m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),sK5))) & (m1_connsp_2(X2,X0,sK5) | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),sK5))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK5,u1_struct_0(X0)))) )),
% 23.27/3.49    introduced(choice_axiom,[])).
% 23.27/3.49  
% 23.27/3.49  fof(f63,plain,(
% 23.27/3.49    ? [X0] : (? [X1] : (? [X2] : ((~m1_connsp_2(X2,X0,X1) | ~m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & (m1_connsp_2(X2,X0,X1) | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~m1_connsp_2(X2,sK4,X1) | ~m2_connsp_2(X2,sK4,k6_domain_1(u1_struct_0(sK4),X1))) & (m1_connsp_2(X2,sK4,X1) | m2_connsp_2(X2,sK4,k6_domain_1(u1_struct_0(sK4),X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))) & m1_subset_1(X1,u1_struct_0(sK4))) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4))),
% 23.27/3.49    introduced(choice_axiom,[])).
% 23.27/3.49  
% 23.27/3.49  fof(f66,plain,(
% 23.27/3.49    (((~m1_connsp_2(sK6,sK4,sK5) | ~m2_connsp_2(sK6,sK4,k6_domain_1(u1_struct_0(sK4),sK5))) & (m1_connsp_2(sK6,sK4,sK5) | m2_connsp_2(sK6,sK4,k6_domain_1(u1_struct_0(sK4),sK5))) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))) & m1_subset_1(sK5,u1_struct_0(sK4))) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4)),
% 23.27/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f62,f65,f64,f63])).
% 23.27/3.49  
% 23.27/3.49  fof(f102,plain,(
% 23.27/3.49    m1_subset_1(sK5,u1_struct_0(sK4))),
% 23.27/3.49    inference(cnf_transformation,[],[f66])).
% 23.27/3.49  
% 23.27/3.49  fof(f15,axiom,(
% 23.27/3.49    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 23.27/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.27/3.49  
% 23.27/3.49  fof(f32,plain,(
% 23.27/3.49    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 23.27/3.49    inference(ennf_transformation,[],[f15])).
% 23.27/3.49  
% 23.27/3.49  fof(f33,plain,(
% 23.27/3.49    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 23.27/3.49    inference(flattening,[],[f32])).
% 23.27/3.49  
% 23.27/3.49  fof(f93,plain,(
% 23.27/3.49    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 23.27/3.49    inference(cnf_transformation,[],[f33])).
% 23.27/3.49  
% 23.27/3.49  fof(f111,plain,(
% 23.27/3.49    ( ! [X0,X1] : (k2_tarski(X1,X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 23.27/3.49    inference(definition_unfolding,[],[f93,f76])).
% 23.27/3.49  
% 23.27/3.49  fof(f99,plain,(
% 23.27/3.49    ~v2_struct_0(sK4)),
% 23.27/3.49    inference(cnf_transformation,[],[f66])).
% 23.27/3.49  
% 23.27/3.49  fof(f101,plain,(
% 23.27/3.49    l1_pre_topc(sK4)),
% 23.27/3.49    inference(cnf_transformation,[],[f66])).
% 23.27/3.49  
% 23.27/3.49  fof(f14,axiom,(
% 23.27/3.49    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 23.27/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.27/3.49  
% 23.27/3.49  fof(f30,plain,(
% 23.27/3.49    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 23.27/3.49    inference(ennf_transformation,[],[f14])).
% 23.27/3.49  
% 23.27/3.49  fof(f31,plain,(
% 23.27/3.49    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 23.27/3.49    inference(flattening,[],[f30])).
% 23.27/3.49  
% 23.27/3.49  fof(f92,plain,(
% 23.27/3.49    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 23.27/3.49    inference(cnf_transformation,[],[f31])).
% 23.27/3.49  
% 23.27/3.49  fof(f13,axiom,(
% 23.27/3.49    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 23.27/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.27/3.49  
% 23.27/3.49  fof(f29,plain,(
% 23.27/3.49    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 23.27/3.49    inference(ennf_transformation,[],[f13])).
% 23.27/3.49  
% 23.27/3.49  fof(f91,plain,(
% 23.27/3.49    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 23.27/3.49    inference(cnf_transformation,[],[f29])).
% 23.27/3.49  
% 23.27/3.49  fof(f104,plain,(
% 23.27/3.49    m1_connsp_2(sK6,sK4,sK5) | m2_connsp_2(sK6,sK4,k6_domain_1(u1_struct_0(sK4),sK5))),
% 23.27/3.49    inference(cnf_transformation,[],[f66])).
% 23.27/3.49  
% 23.27/3.49  fof(f17,axiom,(
% 23.27/3.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 23.27/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.27/3.49  
% 23.27/3.49  fof(f36,plain,(
% 23.27/3.49    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 23.27/3.49    inference(ennf_transformation,[],[f17])).
% 23.27/3.49  
% 23.27/3.49  fof(f37,plain,(
% 23.27/3.49    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 23.27/3.49    inference(flattening,[],[f36])).
% 23.27/3.49  
% 23.27/3.49  fof(f60,plain,(
% 23.27/3.49    ! [X0] : (! [X1] : (! [X2] : (((m2_connsp_2(X2,X0,X1) | ~r1_tarski(X1,k1_tops_1(X0,X2))) & (r1_tarski(X1,k1_tops_1(X0,X2)) | ~m2_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 23.27/3.49    inference(nnf_transformation,[],[f37])).
% 23.27/3.49  
% 23.27/3.49  fof(f96,plain,(
% 23.27/3.49    ( ! [X2,X0,X1] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~m2_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 23.27/3.49    inference(cnf_transformation,[],[f60])).
% 23.27/3.49  
% 23.27/3.49  fof(f100,plain,(
% 23.27/3.49    v2_pre_topc(sK4)),
% 23.27/3.49    inference(cnf_transformation,[],[f66])).
% 23.27/3.49  
% 23.27/3.49  fof(f103,plain,(
% 23.27/3.49    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))),
% 23.27/3.49    inference(cnf_transformation,[],[f66])).
% 23.27/3.49  
% 23.27/3.49  fof(f16,axiom,(
% 23.27/3.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 23.27/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.27/3.49  
% 23.27/3.49  fof(f34,plain,(
% 23.27/3.49    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 23.27/3.49    inference(ennf_transformation,[],[f16])).
% 23.27/3.49  
% 23.27/3.49  fof(f35,plain,(
% 23.27/3.49    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 23.27/3.49    inference(flattening,[],[f34])).
% 23.27/3.49  
% 23.27/3.49  fof(f59,plain,(
% 23.27/3.49    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 23.27/3.49    inference(nnf_transformation,[],[f35])).
% 23.27/3.49  
% 23.27/3.49  fof(f94,plain,(
% 23.27/3.49    ( ! [X2,X0,X1] : (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.27/3.49    inference(cnf_transformation,[],[f59])).
% 23.27/3.49  
% 23.27/3.49  fof(f18,axiom,(
% 23.27/3.49    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 23.27/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.27/3.49  
% 23.27/3.49  fof(f38,plain,(
% 23.27/3.49    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 23.27/3.49    inference(ennf_transformation,[],[f18])).
% 23.27/3.49  
% 23.27/3.49  fof(f39,plain,(
% 23.27/3.49    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 23.27/3.49    inference(flattening,[],[f38])).
% 23.27/3.49  
% 23.27/3.49  fof(f98,plain,(
% 23.27/3.49    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.27/3.49    inference(cnf_transformation,[],[f39])).
% 23.27/3.49  
% 23.27/3.49  fof(f9,axiom,(
% 23.27/3.49    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 23.27/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.27/3.49  
% 23.27/3.49  fof(f24,plain,(
% 23.27/3.49    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 23.27/3.49    inference(ennf_transformation,[],[f9])).
% 23.27/3.49  
% 23.27/3.49  fof(f25,plain,(
% 23.27/3.49    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 23.27/3.49    inference(flattening,[],[f24])).
% 23.27/3.49  
% 23.27/3.49  fof(f86,plain,(
% 23.27/3.49    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 23.27/3.49    inference(cnf_transformation,[],[f25])).
% 23.27/3.49  
% 23.27/3.49  fof(f10,axiom,(
% 23.27/3.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 23.27/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.27/3.49  
% 23.27/3.49  fof(f58,plain,(
% 23.27/3.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 23.27/3.49    inference(nnf_transformation,[],[f10])).
% 23.27/3.49  
% 23.27/3.49  fof(f88,plain,(
% 23.27/3.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 23.27/3.49    inference(cnf_transformation,[],[f58])).
% 23.27/3.49  
% 23.27/3.49  fof(f11,axiom,(
% 23.27/3.49    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 23.27/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.27/3.49  
% 23.27/3.49  fof(f26,plain,(
% 23.27/3.49    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 23.27/3.49    inference(ennf_transformation,[],[f11])).
% 23.27/3.49  
% 23.27/3.49  fof(f27,plain,(
% 23.27/3.49    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 23.27/3.49    inference(flattening,[],[f26])).
% 23.27/3.49  
% 23.27/3.49  fof(f89,plain,(
% 23.27/3.49    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 23.27/3.49    inference(cnf_transformation,[],[f27])).
% 23.27/3.49  
% 23.27/3.49  fof(f87,plain,(
% 23.27/3.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 23.27/3.49    inference(cnf_transformation,[],[f58])).
% 23.27/3.49  
% 23.27/3.49  fof(f105,plain,(
% 23.27/3.49    ~m1_connsp_2(sK6,sK4,sK5) | ~m2_connsp_2(sK6,sK4,k6_domain_1(u1_struct_0(sK4),sK5))),
% 23.27/3.49    inference(cnf_transformation,[],[f66])).
% 23.27/3.49  
% 23.27/3.49  fof(f97,plain,(
% 23.27/3.49    ( ! [X2,X0,X1] : (m2_connsp_2(X2,X0,X1) | ~r1_tarski(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 23.27/3.49    inference(cnf_transformation,[],[f60])).
% 23.27/3.49  
% 23.27/3.49  fof(f95,plain,(
% 23.27/3.49    ( ! [X2,X0,X1] : (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.27/3.49    inference(cnf_transformation,[],[f59])).
% 23.27/3.49  
% 23.27/3.49  fof(f7,axiom,(
% 23.27/3.49    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 23.27/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.27/3.49  
% 23.27/3.49  fof(f22,plain,(
% 23.27/3.49    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 23.27/3.49    inference(ennf_transformation,[],[f7])).
% 23.27/3.49  
% 23.27/3.49  fof(f57,plain,(
% 23.27/3.49    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 23.27/3.49    inference(nnf_transformation,[],[f22])).
% 23.27/3.49  
% 23.27/3.49  fof(f83,plain,(
% 23.27/3.49    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,X0) | ~v1_xboole_0(X0)) )),
% 23.27/3.49    inference(cnf_transformation,[],[f57])).
% 23.27/3.49  
% 23.27/3.49  fof(f2,axiom,(
% 23.27/3.49    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 23.27/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.27/3.49  
% 23.27/3.49  fof(f21,plain,(
% 23.27/3.49    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 23.27/3.49    inference(ennf_transformation,[],[f2])).
% 23.27/3.49  
% 23.27/3.49  fof(f46,plain,(
% 23.27/3.49    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 23.27/3.49    inference(nnf_transformation,[],[f21])).
% 23.27/3.49  
% 23.27/3.49  fof(f47,plain,(
% 23.27/3.49    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK1(X0,X1),X1) | ~r2_hidden(sK1(X0,X1),X0)) & (r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0))))),
% 23.27/3.49    introduced(choice_axiom,[])).
% 23.27/3.49  
% 23.27/3.49  fof(f48,plain,(
% 23.27/3.49    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK1(X0,X1),X1) | ~r2_hidden(sK1(X0,X1),X0)) & (r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0))))),
% 23.27/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f46,f47])).
% 23.27/3.49  
% 23.27/3.49  fof(f69,plain,(
% 23.27/3.49    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 23.27/3.49    inference(cnf_transformation,[],[f48])).
% 23.27/3.49  
% 23.27/3.49  fof(f12,axiom,(
% 23.27/3.49    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 23.27/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.27/3.49  
% 23.27/3.49  fof(f28,plain,(
% 23.27/3.49    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 23.27/3.49    inference(ennf_transformation,[],[f12])).
% 23.27/3.49  
% 23.27/3.49  fof(f90,plain,(
% 23.27/3.49    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 23.27/3.49    inference(cnf_transformation,[],[f28])).
% 23.27/3.49  
% 23.27/3.49  cnf(c_1,plain,
% 23.27/3.49      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 23.27/3.49      inference(cnf_transformation,[],[f67]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_14598,plain,
% 23.27/3.49      ( ~ r2_hidden(sK1(sK5,X0),sK5) | ~ v1_xboole_0(sK5) ),
% 23.27/3.49      inference(instantiation,[status(thm)],[c_1]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_74668,plain,
% 23.27/3.49      ( ~ r2_hidden(sK1(sK5,k1_tops_1(sK4,sK6)),sK5)
% 23.27/3.49      | ~ v1_xboole_0(sK5) ),
% 23.27/3.49      inference(instantiation,[status(thm)],[c_14598]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_1669,plain,
% 23.27/3.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 23.27/3.49      theory(equality) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_5885,plain,
% 23.27/3.49      ( r2_hidden(X0,X1)
% 23.27/3.49      | ~ r2_hidden(X2,k2_tarski(X2,X2))
% 23.27/3.49      | X0 != X2
% 23.27/3.49      | X1 != k2_tarski(X2,X2) ),
% 23.27/3.49      inference(instantiation,[status(thm)],[c_1669]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_16885,plain,
% 23.27/3.49      ( r2_hidden(X0,k6_domain_1(u1_struct_0(sK4),X1))
% 23.27/3.49      | ~ r2_hidden(X1,k2_tarski(X1,X1))
% 23.27/3.49      | X0 != X1
% 23.27/3.49      | k6_domain_1(u1_struct_0(sK4),X1) != k2_tarski(X1,X1) ),
% 23.27/3.49      inference(instantiation,[status(thm)],[c_5885]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_44950,plain,
% 23.27/3.49      ( r2_hidden(k1_tops_1(sK4,sK6),k6_domain_1(u1_struct_0(sK4),sK5))
% 23.27/3.49      | ~ r2_hidden(sK5,k2_tarski(sK5,sK5))
% 23.27/3.49      | k1_tops_1(sK4,sK6) != sK5
% 23.27/3.49      | k6_domain_1(u1_struct_0(sK4),sK5) != k2_tarski(sK5,sK5) ),
% 23.27/3.49      inference(instantiation,[status(thm)],[c_16885]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_7235,plain,
% 23.27/3.49      ( ~ r2_hidden(sK1(sK5,X0),X0) | ~ v1_xboole_0(X0) ),
% 23.27/3.49      inference(instantiation,[status(thm)],[c_1]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_26397,plain,
% 23.27/3.49      ( ~ r2_hidden(sK1(sK5,k1_tops_1(sK4,sK6)),k1_tops_1(sK4,sK6))
% 23.27/3.49      | ~ v1_xboole_0(k1_tops_1(sK4,sK6)) ),
% 23.27/3.49      inference(instantiation,[status(thm)],[c_7235]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_7,plain,
% 23.27/3.49      ( r2_hidden(X0,k2_tarski(X0,X0)) ),
% 23.27/3.49      inference(cnf_transformation,[],[f113]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_20037,plain,
% 23.27/3.49      ( r2_hidden(sK5,k2_tarski(sK5,sK5)) ),
% 23.27/3.49      inference(instantiation,[status(thm)],[c_7]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_1672,plain,
% 23.27/3.49      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 23.27/3.49      theory(equality) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_2370,plain,
% 23.27/3.49      ( ~ m1_subset_1(X0,X1)
% 23.27/3.49      | m1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),k1_zfmisc_1(u1_struct_0(sK4)))
% 23.27/3.49      | k6_domain_1(u1_struct_0(sK4),sK5) != X0
% 23.27/3.49      | k1_zfmisc_1(u1_struct_0(sK4)) != X1 ),
% 23.27/3.49      inference(instantiation,[status(thm)],[c_1672]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_3010,plain,
% 23.27/3.49      ( m1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),k1_zfmisc_1(u1_struct_0(sK4)))
% 23.27/3.49      | ~ m1_subset_1(k2_tarski(sK5,sK5),X0)
% 23.27/3.49      | k6_domain_1(u1_struct_0(sK4),sK5) != k2_tarski(sK5,sK5)
% 23.27/3.49      | k1_zfmisc_1(u1_struct_0(sK4)) != X0 ),
% 23.27/3.49      inference(instantiation,[status(thm)],[c_2370]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_4927,plain,
% 23.27/3.49      ( m1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),k1_zfmisc_1(u1_struct_0(sK4)))
% 23.27/3.49      | ~ m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(X0))
% 23.27/3.49      | k6_domain_1(u1_struct_0(sK4),sK5) != k2_tarski(sK5,sK5)
% 23.27/3.49      | k1_zfmisc_1(u1_struct_0(sK4)) != k1_zfmisc_1(X0) ),
% 23.27/3.49      inference(instantiation,[status(thm)],[c_3010]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_16081,plain,
% 23.27/3.49      ( m1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),k1_zfmisc_1(u1_struct_0(sK4)))
% 23.27/3.49      | ~ m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK4)))
% 23.27/3.49      | k6_domain_1(u1_struct_0(sK4),sK5) != k2_tarski(sK5,sK5)
% 23.27/3.49      | k1_zfmisc_1(u1_struct_0(sK4)) != k1_zfmisc_1(u1_struct_0(sK4)) ),
% 23.27/3.49      inference(instantiation,[status(thm)],[c_4927]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_17,plain,
% 23.27/3.49      ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1))
% 23.27/3.49      | ~ r2_hidden(X0,X1) ),
% 23.27/3.49      inference(cnf_transformation,[],[f110]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_3835,plain,
% 23.27/3.49      ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(u1_struct_0(sK4)))
% 23.27/3.49      | ~ r2_hidden(X0,u1_struct_0(sK4)) ),
% 23.27/3.49      inference(instantiation,[status(thm)],[c_17]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_11089,plain,
% 23.27/3.49      ( m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK4)))
% 23.27/3.49      | ~ r2_hidden(sK5,u1_struct_0(sK4)) ),
% 23.27/3.49      inference(instantiation,[status(thm)],[c_3835]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_2283,plain,
% 23.27/3.49      ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1)) = iProver_top
% 23.27/3.49      | r2_hidden(X0,X1) != iProver_top ),
% 23.27/3.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_34,negated_conjecture,
% 23.27/3.49      ( m1_subset_1(sK5,u1_struct_0(sK4)) ),
% 23.27/3.49      inference(cnf_transformation,[],[f102]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_2276,plain,
% 23.27/3.49      ( m1_subset_1(sK5,u1_struct_0(sK4)) = iProver_top ),
% 23.27/3.49      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_25,plain,
% 23.27/3.49      ( ~ m1_subset_1(X0,X1)
% 23.27/3.49      | v1_xboole_0(X1)
% 23.27/3.49      | k6_domain_1(X1,X0) = k2_tarski(X0,X0) ),
% 23.27/3.49      inference(cnf_transformation,[],[f111]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_2278,plain,
% 23.27/3.49      ( k6_domain_1(X0,X1) = k2_tarski(X1,X1)
% 23.27/3.49      | m1_subset_1(X1,X0) != iProver_top
% 23.27/3.49      | v1_xboole_0(X0) = iProver_top ),
% 23.27/3.49      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_2933,plain,
% 23.27/3.49      ( k6_domain_1(u1_struct_0(sK4),sK5) = k2_tarski(sK5,sK5)
% 23.27/3.49      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
% 23.27/3.49      inference(superposition,[status(thm)],[c_2276,c_2278]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_37,negated_conjecture,
% 23.27/3.49      ( ~ v2_struct_0(sK4) ),
% 23.27/3.49      inference(cnf_transformation,[],[f99]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_35,negated_conjecture,
% 23.27/3.49      ( l1_pre_topc(sK4) ),
% 23.27/3.49      inference(cnf_transformation,[],[f101]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_24,plain,
% 23.27/3.49      ( v2_struct_0(X0)
% 23.27/3.49      | ~ l1_struct_0(X0)
% 23.27/3.49      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 23.27/3.49      inference(cnf_transformation,[],[f92]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_64,plain,
% 23.27/3.49      ( v2_struct_0(sK4)
% 23.27/3.49      | ~ l1_struct_0(sK4)
% 23.27/3.49      | ~ v1_xboole_0(u1_struct_0(sK4)) ),
% 23.27/3.49      inference(instantiation,[status(thm)],[c_24]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_23,plain,
% 23.27/3.49      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 23.27/3.49      inference(cnf_transformation,[],[f91]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_67,plain,
% 23.27/3.49      ( ~ l1_pre_topc(sK4) | l1_struct_0(sK4) ),
% 23.27/3.49      inference(instantiation,[status(thm)],[c_23]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_2341,plain,
% 23.27/3.49      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 23.27/3.49      | v1_xboole_0(u1_struct_0(sK4))
% 23.27/3.49      | k6_domain_1(u1_struct_0(sK4),X0) = k2_tarski(X0,X0) ),
% 23.27/3.49      inference(instantiation,[status(thm)],[c_25]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_2452,plain,
% 23.27/3.49      ( ~ m1_subset_1(sK5,u1_struct_0(sK4))
% 23.27/3.49      | v1_xboole_0(u1_struct_0(sK4))
% 23.27/3.49      | k6_domain_1(u1_struct_0(sK4),sK5) = k2_tarski(sK5,sK5) ),
% 23.27/3.49      inference(instantiation,[status(thm)],[c_2341]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_3252,plain,
% 23.27/3.49      ( k6_domain_1(u1_struct_0(sK4),sK5) = k2_tarski(sK5,sK5) ),
% 23.27/3.49      inference(global_propositional_subsumption,
% 23.27/3.49                [status(thm)],
% 23.27/3.49                [c_2933,c_37,c_35,c_34,c_64,c_67,c_2452]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_32,negated_conjecture,
% 23.27/3.49      ( m2_connsp_2(sK6,sK4,k6_domain_1(u1_struct_0(sK4),sK5))
% 23.27/3.49      | m1_connsp_2(sK6,sK4,sK5) ),
% 23.27/3.49      inference(cnf_transformation,[],[f104]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_320,plain,
% 23.27/3.49      ( m1_connsp_2(sK6,sK4,sK5)
% 23.27/3.49      | m2_connsp_2(sK6,sK4,k6_domain_1(u1_struct_0(sK4),sK5)) ),
% 23.27/3.49      inference(prop_impl,[status(thm)],[c_32]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_321,plain,
% 23.27/3.49      ( m2_connsp_2(sK6,sK4,k6_domain_1(u1_struct_0(sK4),sK5))
% 23.27/3.49      | m1_connsp_2(sK6,sK4,sK5) ),
% 23.27/3.49      inference(renaming,[status(thm)],[c_320]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_29,plain,
% 23.27/3.49      ( ~ m2_connsp_2(X0,X1,X2)
% 23.27/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.27/3.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 23.27/3.49      | r1_tarski(X2,k1_tops_1(X1,X0))
% 23.27/3.49      | ~ v2_pre_topc(X1)
% 23.27/3.49      | ~ l1_pre_topc(X1) ),
% 23.27/3.49      inference(cnf_transformation,[],[f96]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_632,plain,
% 23.27/3.49      ( ~ m2_connsp_2(X0,X1,X2)
% 23.27/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.27/3.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 23.27/3.49      | r1_tarski(X2,k1_tops_1(X1,X0))
% 23.27/3.49      | ~ v2_pre_topc(X1)
% 23.27/3.49      | sK4 != X1 ),
% 23.27/3.49      inference(resolution_lifted,[status(thm)],[c_29,c_35]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_633,plain,
% 23.27/3.49      ( ~ m2_connsp_2(X0,sK4,X1)
% 23.27/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 23.27/3.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 23.27/3.49      | r1_tarski(X1,k1_tops_1(sK4,X0))
% 23.27/3.49      | ~ v2_pre_topc(sK4) ),
% 23.27/3.49      inference(unflattening,[status(thm)],[c_632]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_36,negated_conjecture,
% 23.27/3.49      ( v2_pre_topc(sK4) ),
% 23.27/3.49      inference(cnf_transformation,[],[f100]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_637,plain,
% 23.27/3.49      ( r1_tarski(X1,k1_tops_1(sK4,X0))
% 23.27/3.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 23.27/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 23.27/3.49      | ~ m2_connsp_2(X0,sK4,X1) ),
% 23.27/3.49      inference(global_propositional_subsumption,
% 23.27/3.49                [status(thm)],
% 23.27/3.49                [c_633,c_36]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_638,plain,
% 23.27/3.49      ( ~ m2_connsp_2(X0,sK4,X1)
% 23.27/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 23.27/3.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 23.27/3.49      | r1_tarski(X1,k1_tops_1(sK4,X0)) ),
% 23.27/3.49      inference(renaming,[status(thm)],[c_637]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_692,plain,
% 23.27/3.49      ( m1_connsp_2(sK6,sK4,sK5)
% 23.27/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 23.27/3.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 23.27/3.49      | r1_tarski(X1,k1_tops_1(sK4,X0))
% 23.27/3.49      | k6_domain_1(u1_struct_0(sK4),sK5) != X1
% 23.27/3.49      | sK4 != sK4
% 23.27/3.49      | sK6 != X0 ),
% 23.27/3.49      inference(resolution_lifted,[status(thm)],[c_321,c_638]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_693,plain,
% 23.27/3.49      ( m1_connsp_2(sK6,sK4,sK5)
% 23.27/3.49      | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),k1_zfmisc_1(u1_struct_0(sK4)))
% 23.27/3.49      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
% 23.27/3.49      | r1_tarski(k6_domain_1(u1_struct_0(sK4),sK5),k1_tops_1(sK4,sK6)) ),
% 23.27/3.49      inference(unflattening,[status(thm)],[c_692]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_33,negated_conjecture,
% 23.27/3.49      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 23.27/3.49      inference(cnf_transformation,[],[f103]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_695,plain,
% 23.27/3.49      ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),k1_zfmisc_1(u1_struct_0(sK4)))
% 23.27/3.49      | m1_connsp_2(sK6,sK4,sK5)
% 23.27/3.49      | r1_tarski(k6_domain_1(u1_struct_0(sK4),sK5),k1_tops_1(sK4,sK6)) ),
% 23.27/3.49      inference(global_propositional_subsumption,
% 23.27/3.49                [status(thm)],
% 23.27/3.49                [c_693,c_33]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_696,plain,
% 23.27/3.49      ( m1_connsp_2(sK6,sK4,sK5)
% 23.27/3.49      | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),k1_zfmisc_1(u1_struct_0(sK4)))
% 23.27/3.49      | r1_tarski(k6_domain_1(u1_struct_0(sK4),sK5),k1_tops_1(sK4,sK6)) ),
% 23.27/3.49      inference(renaming,[status(thm)],[c_695]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_27,plain,
% 23.27/3.49      ( ~ m1_connsp_2(X0,X1,X2)
% 23.27/3.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 23.27/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.27/3.49      | r2_hidden(X2,k1_tops_1(X1,X0))
% 23.27/3.49      | ~ v2_pre_topc(X1)
% 23.27/3.49      | v2_struct_0(X1)
% 23.27/3.49      | ~ l1_pre_topc(X1) ),
% 23.27/3.49      inference(cnf_transformation,[],[f94]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_30,plain,
% 23.27/3.49      ( ~ m1_connsp_2(X0,X1,X2)
% 23.27/3.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 23.27/3.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.27/3.49      | ~ v2_pre_topc(X1)
% 23.27/3.49      | v2_struct_0(X1)
% 23.27/3.49      | ~ l1_pre_topc(X1) ),
% 23.27/3.49      inference(cnf_transformation,[],[f98]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_221,plain,
% 23.27/3.49      ( ~ m1_subset_1(X2,u1_struct_0(X1))
% 23.27/3.49      | ~ m1_connsp_2(X0,X1,X2)
% 23.27/3.49      | r2_hidden(X2,k1_tops_1(X1,X0))
% 23.27/3.49      | ~ v2_pre_topc(X1)
% 23.27/3.49      | v2_struct_0(X1)
% 23.27/3.49      | ~ l1_pre_topc(X1) ),
% 23.27/3.49      inference(global_propositional_subsumption,
% 23.27/3.49                [status(thm)],
% 23.27/3.49                [c_27,c_30]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_222,plain,
% 23.27/3.49      ( ~ m1_connsp_2(X0,X1,X2)
% 23.27/3.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 23.27/3.49      | r2_hidden(X2,k1_tops_1(X1,X0))
% 23.27/3.49      | ~ v2_pre_topc(X1)
% 23.27/3.49      | v2_struct_0(X1)
% 23.27/3.49      | ~ l1_pre_topc(X1) ),
% 23.27/3.49      inference(renaming,[status(thm)],[c_221]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_551,plain,
% 23.27/3.49      ( ~ m1_connsp_2(X0,X1,X2)
% 23.27/3.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 23.27/3.49      | r2_hidden(X2,k1_tops_1(X1,X0))
% 23.27/3.49      | ~ v2_pre_topc(X1)
% 23.27/3.49      | ~ l1_pre_topc(X1)
% 23.27/3.49      | sK4 != X1 ),
% 23.27/3.49      inference(resolution_lifted,[status(thm)],[c_222,c_37]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_552,plain,
% 23.27/3.49      ( ~ m1_connsp_2(X0,sK4,X1)
% 23.27/3.49      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 23.27/3.49      | r2_hidden(X1,k1_tops_1(sK4,X0))
% 23.27/3.49      | ~ v2_pre_topc(sK4)
% 23.27/3.49      | ~ l1_pre_topc(sK4) ),
% 23.27/3.49      inference(unflattening,[status(thm)],[c_551]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_556,plain,
% 23.27/3.49      ( ~ m1_connsp_2(X0,sK4,X1)
% 23.27/3.49      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 23.27/3.49      | r2_hidden(X1,k1_tops_1(sK4,X0)) ),
% 23.27/3.49      inference(global_propositional_subsumption,
% 23.27/3.49                [status(thm)],
% 23.27/3.49                [c_552,c_36,c_35]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_739,plain,
% 23.27/3.49      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 23.27/3.49      | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),k1_zfmisc_1(u1_struct_0(sK4)))
% 23.27/3.49      | r1_tarski(k6_domain_1(u1_struct_0(sK4),sK5),k1_tops_1(sK4,sK6))
% 23.27/3.49      | r2_hidden(X0,k1_tops_1(sK4,X1))
% 23.27/3.49      | sK5 != X0
% 23.27/3.49      | sK4 != sK4
% 23.27/3.49      | sK6 != X1 ),
% 23.27/3.49      inference(resolution_lifted,[status(thm)],[c_696,c_556]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_740,plain,
% 23.27/3.49      ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),k1_zfmisc_1(u1_struct_0(sK4)))
% 23.27/3.49      | ~ m1_subset_1(sK5,u1_struct_0(sK4))
% 23.27/3.49      | r1_tarski(k6_domain_1(u1_struct_0(sK4),sK5),k1_tops_1(sK4,sK6))
% 23.27/3.49      | r2_hidden(sK5,k1_tops_1(sK4,sK6)) ),
% 23.27/3.49      inference(unflattening,[status(thm)],[c_739]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_742,plain,
% 23.27/3.49      ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),k1_zfmisc_1(u1_struct_0(sK4)))
% 23.27/3.49      | r1_tarski(k6_domain_1(u1_struct_0(sK4),sK5),k1_tops_1(sK4,sK6))
% 23.27/3.49      | r2_hidden(sK5,k1_tops_1(sK4,sK6)) ),
% 23.27/3.49      inference(global_propositional_subsumption,
% 23.27/3.49                [status(thm)],
% 23.27/3.49                [c_740,c_34]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_2273,plain,
% 23.27/3.49      ( m1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 23.27/3.49      | r1_tarski(k6_domain_1(u1_struct_0(sK4),sK5),k1_tops_1(sK4,sK6)) = iProver_top
% 23.27/3.49      | r2_hidden(sK5,k1_tops_1(sK4,sK6)) = iProver_top ),
% 23.27/3.49      inference(predicate_to_equality,[status(thm)],[c_742]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_3254,plain,
% 23.27/3.49      ( m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 23.27/3.49      | r1_tarski(k2_tarski(sK5,sK5),k1_tops_1(sK4,sK6)) = iProver_top
% 23.27/3.49      | r2_hidden(sK5,k1_tops_1(sK4,sK6)) = iProver_top ),
% 23.27/3.49      inference(demodulation,[status(thm)],[c_3252,c_2273]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_4242,plain,
% 23.27/3.49      ( r1_tarski(k2_tarski(sK5,sK5),k1_tops_1(sK4,sK6)) = iProver_top
% 23.27/3.49      | r2_hidden(sK5,k1_tops_1(sK4,sK6)) = iProver_top
% 23.27/3.49      | r2_hidden(sK5,u1_struct_0(sK4)) != iProver_top ),
% 23.27/3.49      inference(superposition,[status(thm)],[c_2283,c_3254]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_38,plain,
% 23.27/3.49      ( v2_struct_0(sK4) != iProver_top ),
% 23.27/3.49      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_40,plain,
% 23.27/3.49      ( l1_pre_topc(sK4) = iProver_top ),
% 23.27/3.49      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_41,plain,
% 23.27/3.49      ( m1_subset_1(sK5,u1_struct_0(sK4)) = iProver_top ),
% 23.27/3.49      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_63,plain,
% 23.27/3.49      ( v2_struct_0(X0) = iProver_top
% 23.27/3.49      | l1_struct_0(X0) != iProver_top
% 23.27/3.49      | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
% 23.27/3.49      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_65,plain,
% 23.27/3.49      ( v2_struct_0(sK4) = iProver_top
% 23.27/3.49      | l1_struct_0(sK4) != iProver_top
% 23.27/3.49      | v1_xboole_0(u1_struct_0(sK4)) != iProver_top ),
% 23.27/3.49      inference(instantiation,[status(thm)],[c_63]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_66,plain,
% 23.27/3.49      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 23.27/3.49      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_68,plain,
% 23.27/3.49      ( l1_pre_topc(sK4) != iProver_top
% 23.27/3.49      | l1_struct_0(sK4) = iProver_top ),
% 23.27/3.49      inference(instantiation,[status(thm)],[c_66]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_18,plain,
% 23.27/3.49      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 23.27/3.49      inference(cnf_transformation,[],[f86]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_2343,plain,
% 23.27/3.49      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 23.27/3.49      | r2_hidden(X0,u1_struct_0(sK4))
% 23.27/3.49      | v1_xboole_0(u1_struct_0(sK4)) ),
% 23.27/3.49      inference(instantiation,[status(thm)],[c_18]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_2433,plain,
% 23.27/3.49      ( ~ m1_subset_1(sK5,u1_struct_0(sK4))
% 23.27/3.49      | r2_hidden(sK5,u1_struct_0(sK4))
% 23.27/3.49      | v1_xboole_0(u1_struct_0(sK4)) ),
% 23.27/3.49      inference(instantiation,[status(thm)],[c_2343]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_2434,plain,
% 23.27/3.49      ( m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
% 23.27/3.49      | r2_hidden(sK5,u1_struct_0(sK4)) = iProver_top
% 23.27/3.49      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
% 23.27/3.49      inference(predicate_to_equality,[status(thm)],[c_2433]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_4994,plain,
% 23.27/3.49      ( r2_hidden(sK5,k1_tops_1(sK4,sK6)) = iProver_top
% 23.27/3.49      | r1_tarski(k2_tarski(sK5,sK5),k1_tops_1(sK4,sK6)) = iProver_top ),
% 23.27/3.49      inference(global_propositional_subsumption,
% 23.27/3.49                [status(thm)],
% 23.27/3.49                [c_4242,c_38,c_40,c_41,c_65,c_68,c_2434]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_4995,plain,
% 23.27/3.49      ( r1_tarski(k2_tarski(sK5,sK5),k1_tops_1(sK4,sK6)) = iProver_top
% 23.27/3.49      | r2_hidden(sK5,k1_tops_1(sK4,sK6)) = iProver_top ),
% 23.27/3.49      inference(renaming,[status(thm)],[c_4994]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_2292,plain,
% 23.27/3.49      ( r2_hidden(X0,k2_tarski(X0,X0)) = iProver_top ),
% 23.27/3.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_19,plain,
% 23.27/3.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 23.27/3.49      inference(cnf_transformation,[],[f88]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_2282,plain,
% 23.27/3.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 23.27/3.49      | r1_tarski(X0,X1) != iProver_top ),
% 23.27/3.49      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_21,plain,
% 23.27/3.49      ( m1_subset_1(X0,X1)
% 23.27/3.49      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 23.27/3.49      | ~ r2_hidden(X0,X2) ),
% 23.27/3.49      inference(cnf_transformation,[],[f89]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_2280,plain,
% 23.27/3.49      ( m1_subset_1(X0,X1) = iProver_top
% 23.27/3.49      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 23.27/3.49      | r2_hidden(X0,X2) != iProver_top ),
% 23.27/3.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_3652,plain,
% 23.27/3.49      ( m1_subset_1(X0,X1) = iProver_top
% 23.27/3.49      | r1_tarski(X2,X1) != iProver_top
% 23.27/3.49      | r2_hidden(X0,X2) != iProver_top ),
% 23.27/3.49      inference(superposition,[status(thm)],[c_2282,c_2280]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_7686,plain,
% 23.27/3.49      ( m1_subset_1(X0,X1) = iProver_top
% 23.27/3.49      | r1_tarski(k2_tarski(X0,X0),X1) != iProver_top ),
% 23.27/3.49      inference(superposition,[status(thm)],[c_2292,c_3652]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_9653,plain,
% 23.27/3.49      ( m1_subset_1(sK5,k1_tops_1(sK4,sK6)) = iProver_top
% 23.27/3.49      | r2_hidden(sK5,k1_tops_1(sK4,sK6)) = iProver_top ),
% 23.27/3.49      inference(superposition,[status(thm)],[c_4995,c_7686]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_20,plain,
% 23.27/3.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 23.27/3.49      inference(cnf_transformation,[],[f87]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_2281,plain,
% 23.27/3.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 23.27/3.49      | r1_tarski(X0,X1) = iProver_top ),
% 23.27/3.49      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_4239,plain,
% 23.27/3.49      ( r1_tarski(k2_tarski(X0,X0),X1) = iProver_top
% 23.27/3.49      | r2_hidden(X0,X1) != iProver_top ),
% 23.27/3.49      inference(superposition,[status(thm)],[c_2283,c_2281]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_31,negated_conjecture,
% 23.27/3.49      ( ~ m2_connsp_2(sK6,sK4,k6_domain_1(u1_struct_0(sK4),sK5))
% 23.27/3.49      | ~ m1_connsp_2(sK6,sK4,sK5) ),
% 23.27/3.49      inference(cnf_transformation,[],[f105]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_318,plain,
% 23.27/3.49      ( ~ m1_connsp_2(sK6,sK4,sK5)
% 23.27/3.49      | ~ m2_connsp_2(sK6,sK4,k6_domain_1(u1_struct_0(sK4),sK5)) ),
% 23.27/3.49      inference(prop_impl,[status(thm)],[c_31]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_319,plain,
% 23.27/3.49      ( ~ m2_connsp_2(sK6,sK4,k6_domain_1(u1_struct_0(sK4),sK5))
% 23.27/3.49      | ~ m1_connsp_2(sK6,sK4,sK5) ),
% 23.27/3.49      inference(renaming,[status(thm)],[c_318]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_28,plain,
% 23.27/3.49      ( m2_connsp_2(X0,X1,X2)
% 23.27/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.27/3.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 23.27/3.49      | ~ r1_tarski(X2,k1_tops_1(X1,X0))
% 23.27/3.49      | ~ v2_pre_topc(X1)
% 23.27/3.49      | ~ l1_pre_topc(X1) ),
% 23.27/3.49      inference(cnf_transformation,[],[f97]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_656,plain,
% 23.27/3.49      ( m2_connsp_2(X0,X1,X2)
% 23.27/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.27/3.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 23.27/3.49      | ~ r1_tarski(X2,k1_tops_1(X1,X0))
% 23.27/3.49      | ~ v2_pre_topc(X1)
% 23.27/3.49      | sK4 != X1 ),
% 23.27/3.49      inference(resolution_lifted,[status(thm)],[c_28,c_35]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_657,plain,
% 23.27/3.49      ( m2_connsp_2(X0,sK4,X1)
% 23.27/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 23.27/3.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 23.27/3.49      | ~ r1_tarski(X1,k1_tops_1(sK4,X0))
% 23.27/3.49      | ~ v2_pre_topc(sK4) ),
% 23.27/3.49      inference(unflattening,[status(thm)],[c_656]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_661,plain,
% 23.27/3.49      ( ~ r1_tarski(X1,k1_tops_1(sK4,X0))
% 23.27/3.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 23.27/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 23.27/3.49      | m2_connsp_2(X0,sK4,X1) ),
% 23.27/3.49      inference(global_propositional_subsumption,
% 23.27/3.49                [status(thm)],
% 23.27/3.49                [c_657,c_36]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_662,plain,
% 23.27/3.49      ( m2_connsp_2(X0,sK4,X1)
% 23.27/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 23.27/3.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 23.27/3.49      | ~ r1_tarski(X1,k1_tops_1(sK4,X0)) ),
% 23.27/3.49      inference(renaming,[status(thm)],[c_661]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_709,plain,
% 23.27/3.49      ( ~ m1_connsp_2(sK6,sK4,sK5)
% 23.27/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 23.27/3.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 23.27/3.49      | ~ r1_tarski(X1,k1_tops_1(sK4,X0))
% 23.27/3.49      | k6_domain_1(u1_struct_0(sK4),sK5) != X1
% 23.27/3.49      | sK4 != sK4
% 23.27/3.49      | sK6 != X0 ),
% 23.27/3.49      inference(resolution_lifted,[status(thm)],[c_319,c_662]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_710,plain,
% 23.27/3.49      ( ~ m1_connsp_2(sK6,sK4,sK5)
% 23.27/3.49      | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),k1_zfmisc_1(u1_struct_0(sK4)))
% 23.27/3.49      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
% 23.27/3.49      | ~ r1_tarski(k6_domain_1(u1_struct_0(sK4),sK5),k1_tops_1(sK4,sK6)) ),
% 23.27/3.49      inference(unflattening,[status(thm)],[c_709]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_712,plain,
% 23.27/3.49      ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),k1_zfmisc_1(u1_struct_0(sK4)))
% 23.27/3.49      | ~ m1_connsp_2(sK6,sK4,sK5)
% 23.27/3.49      | ~ r1_tarski(k6_domain_1(u1_struct_0(sK4),sK5),k1_tops_1(sK4,sK6)) ),
% 23.27/3.49      inference(global_propositional_subsumption,
% 23.27/3.49                [status(thm)],
% 23.27/3.49                [c_710,c_33]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_713,plain,
% 23.27/3.49      ( ~ m1_connsp_2(sK6,sK4,sK5)
% 23.27/3.49      | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),k1_zfmisc_1(u1_struct_0(sK4)))
% 23.27/3.49      | ~ r1_tarski(k6_domain_1(u1_struct_0(sK4),sK5),k1_tops_1(sK4,sK6)) ),
% 23.27/3.49      inference(renaming,[status(thm)],[c_712]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_26,plain,
% 23.27/3.49      ( m1_connsp_2(X0,X1,X2)
% 23.27/3.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 23.27/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.27/3.49      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 23.27/3.49      | ~ v2_pre_topc(X1)
% 23.27/3.49      | v2_struct_0(X1)
% 23.27/3.49      | ~ l1_pre_topc(X1) ),
% 23.27/3.49      inference(cnf_transformation,[],[f95]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_593,plain,
% 23.27/3.49      ( m1_connsp_2(X0,X1,X2)
% 23.27/3.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 23.27/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.27/3.49      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 23.27/3.49      | ~ v2_pre_topc(X1)
% 23.27/3.49      | ~ l1_pre_topc(X1)
% 23.27/3.49      | sK4 != X1 ),
% 23.27/3.49      inference(resolution_lifted,[status(thm)],[c_26,c_37]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_594,plain,
% 23.27/3.49      ( m1_connsp_2(X0,sK4,X1)
% 23.27/3.49      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 23.27/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 23.27/3.49      | ~ r2_hidden(X1,k1_tops_1(sK4,X0))
% 23.27/3.49      | ~ v2_pre_topc(sK4)
% 23.27/3.49      | ~ l1_pre_topc(sK4) ),
% 23.27/3.49      inference(unflattening,[status(thm)],[c_593]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_598,plain,
% 23.27/3.49      ( m1_connsp_2(X0,sK4,X1)
% 23.27/3.49      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 23.27/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 23.27/3.49      | ~ r2_hidden(X1,k1_tops_1(sK4,X0)) ),
% 23.27/3.49      inference(global_propositional_subsumption,
% 23.27/3.49                [status(thm)],
% 23.27/3.49                [c_594,c_36,c_35]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_756,plain,
% 23.27/3.49      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 23.27/3.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 23.27/3.49      | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),k1_zfmisc_1(u1_struct_0(sK4)))
% 23.27/3.49      | ~ r1_tarski(k6_domain_1(u1_struct_0(sK4),sK5),k1_tops_1(sK4,sK6))
% 23.27/3.49      | ~ r2_hidden(X0,k1_tops_1(sK4,X1))
% 23.27/3.49      | sK5 != X0
% 23.27/3.49      | sK4 != sK4
% 23.27/3.49      | sK6 != X1 ),
% 23.27/3.49      inference(resolution_lifted,[status(thm)],[c_713,c_598]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_757,plain,
% 23.27/3.49      ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),k1_zfmisc_1(u1_struct_0(sK4)))
% 23.27/3.49      | ~ m1_subset_1(sK5,u1_struct_0(sK4))
% 23.27/3.49      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
% 23.27/3.49      | ~ r1_tarski(k6_domain_1(u1_struct_0(sK4),sK5),k1_tops_1(sK4,sK6))
% 23.27/3.49      | ~ r2_hidden(sK5,k1_tops_1(sK4,sK6)) ),
% 23.27/3.49      inference(unflattening,[status(thm)],[c_756]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_759,plain,
% 23.27/3.49      ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),k1_zfmisc_1(u1_struct_0(sK4)))
% 23.27/3.49      | ~ r1_tarski(k6_domain_1(u1_struct_0(sK4),sK5),k1_tops_1(sK4,sK6))
% 23.27/3.49      | ~ r2_hidden(sK5,k1_tops_1(sK4,sK6)) ),
% 23.27/3.49      inference(global_propositional_subsumption,
% 23.27/3.49                [status(thm)],
% 23.27/3.49                [c_757,c_34,c_33]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_2272,plain,
% 23.27/3.49      ( m1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 23.27/3.49      | r1_tarski(k6_domain_1(u1_struct_0(sK4),sK5),k1_tops_1(sK4,sK6)) != iProver_top
% 23.27/3.49      | r2_hidden(sK5,k1_tops_1(sK4,sK6)) != iProver_top ),
% 23.27/3.49      inference(predicate_to_equality,[status(thm)],[c_759]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_3255,plain,
% 23.27/3.49      ( m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 23.27/3.49      | r1_tarski(k2_tarski(sK5,sK5),k1_tops_1(sK4,sK6)) != iProver_top
% 23.27/3.49      | r2_hidden(sK5,k1_tops_1(sK4,sK6)) != iProver_top ),
% 23.27/3.49      inference(demodulation,[status(thm)],[c_3252,c_2272]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_4243,plain,
% 23.27/3.49      ( r1_tarski(k2_tarski(sK5,sK5),k1_tops_1(sK4,sK6)) != iProver_top
% 23.27/3.49      | r2_hidden(sK5,k1_tops_1(sK4,sK6)) != iProver_top
% 23.27/3.49      | r2_hidden(sK5,u1_struct_0(sK4)) != iProver_top ),
% 23.27/3.49      inference(superposition,[status(thm)],[c_2283,c_3255]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_4987,plain,
% 23.27/3.49      ( r2_hidden(sK5,k1_tops_1(sK4,sK6)) != iProver_top
% 23.27/3.49      | r1_tarski(k2_tarski(sK5,sK5),k1_tops_1(sK4,sK6)) != iProver_top ),
% 23.27/3.49      inference(global_propositional_subsumption,
% 23.27/3.49                [status(thm)],
% 23.27/3.49                [c_4243,c_38,c_40,c_41,c_65,c_68,c_2434]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_4988,plain,
% 23.27/3.49      ( r1_tarski(k2_tarski(sK5,sK5),k1_tops_1(sK4,sK6)) != iProver_top
% 23.27/3.49      | r2_hidden(sK5,k1_tops_1(sK4,sK6)) != iProver_top ),
% 23.27/3.49      inference(renaming,[status(thm)],[c_4987]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_9440,plain,
% 23.27/3.49      ( r2_hidden(sK5,k1_tops_1(sK4,sK6)) != iProver_top ),
% 23.27/3.49      inference(superposition,[status(thm)],[c_4239,c_4988]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_9867,plain,
% 23.27/3.49      ( m1_subset_1(sK5,k1_tops_1(sK4,sK6)) = iProver_top ),
% 23.27/3.49      inference(global_propositional_subsumption,
% 23.27/3.49                [status(thm)],
% 23.27/3.49                [c_9653,c_9440]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_2284,plain,
% 23.27/3.49      ( m1_subset_1(X0,X1) != iProver_top
% 23.27/3.49      | r2_hidden(X0,X1) = iProver_top
% 23.27/3.49      | v1_xboole_0(X1) = iProver_top ),
% 23.27/3.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_9872,plain,
% 23.27/3.49      ( r2_hidden(sK5,k1_tops_1(sK4,sK6)) = iProver_top
% 23.27/3.49      | v1_xboole_0(k1_tops_1(sK4,sK6)) = iProver_top ),
% 23.27/3.49      inference(superposition,[status(thm)],[c_9867,c_2284]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_9875,plain,
% 23.27/3.49      ( r2_hidden(sK5,k1_tops_1(sK4,sK6))
% 23.27/3.49      | v1_xboole_0(k1_tops_1(sK4,sK6)) ),
% 23.27/3.49      inference(predicate_to_equality_rev,[status(thm)],[c_9872]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_14,plain,
% 23.27/3.49      ( ~ m1_subset_1(X0,X1) | ~ v1_xboole_0(X1) | v1_xboole_0(X0) ),
% 23.27/3.49      inference(cnf_transformation,[],[f83]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_2285,plain,
% 23.27/3.49      ( m1_subset_1(X0,X1) != iProver_top
% 23.27/3.49      | v1_xboole_0(X1) != iProver_top
% 23.27/3.49      | v1_xboole_0(X0) = iProver_top ),
% 23.27/3.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_9871,plain,
% 23.27/3.49      ( v1_xboole_0(k1_tops_1(sK4,sK6)) != iProver_top
% 23.27/3.49      | v1_xboole_0(sK5) = iProver_top ),
% 23.27/3.49      inference(superposition,[status(thm)],[c_9867,c_2285]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_9874,plain,
% 23.27/3.49      ( ~ v1_xboole_0(k1_tops_1(sK4,sK6)) | v1_xboole_0(sK5) ),
% 23.27/3.49      inference(predicate_to_equality_rev,[status(thm)],[c_9871]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_9457,plain,
% 23.27/3.49      ( ~ r2_hidden(sK5,k1_tops_1(sK4,sK6)) ),
% 23.27/3.49      inference(predicate_to_equality_rev,[status(thm)],[c_9440]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_3,plain,
% 23.27/3.49      ( r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0) | X1 = X0 ),
% 23.27/3.49      inference(cnf_transformation,[],[f69]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_3602,plain,
% 23.27/3.49      ( r2_hidden(sK1(X0,k1_tops_1(sK4,sK6)),X0)
% 23.27/3.49      | r2_hidden(sK1(X0,k1_tops_1(sK4,sK6)),k1_tops_1(sK4,sK6))
% 23.27/3.49      | k1_tops_1(sK4,sK6) = X0 ),
% 23.27/3.49      inference(instantiation,[status(thm)],[c_3]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_6867,plain,
% 23.27/3.49      ( r2_hidden(sK1(sK5,k1_tops_1(sK4,sK6)),k1_tops_1(sK4,sK6))
% 23.27/3.49      | r2_hidden(sK1(sK5,k1_tops_1(sK4,sK6)),sK5)
% 23.27/3.49      | k1_tops_1(sK4,sK6) = sK5 ),
% 23.27/3.49      inference(instantiation,[status(thm)],[c_3602]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_1666,plain,( X0 = X0 ),theory(equality) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_2981,plain,
% 23.27/3.49      ( k1_zfmisc_1(u1_struct_0(sK4)) = k1_zfmisc_1(u1_struct_0(sK4)) ),
% 23.27/3.49      inference(instantiation,[status(thm)],[c_1666]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_22,plain,
% 23.27/3.49      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 23.27/3.49      inference(cnf_transformation,[],[f90]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_1020,plain,
% 23.27/3.49      ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),k1_zfmisc_1(u1_struct_0(sK4)))
% 23.27/3.49      | ~ r2_hidden(X0,X1)
% 23.27/3.49      | r2_hidden(sK5,k1_tops_1(sK4,sK6))
% 23.27/3.49      | k1_tops_1(sK4,sK6) != X0
% 23.27/3.49      | k6_domain_1(u1_struct_0(sK4),sK5) != X1 ),
% 23.27/3.49      inference(resolution_lifted,[status(thm)],[c_22,c_742]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_1021,plain,
% 23.27/3.49      ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),k1_zfmisc_1(u1_struct_0(sK4)))
% 23.27/3.49      | ~ r2_hidden(k1_tops_1(sK4,sK6),k6_domain_1(u1_struct_0(sK4),sK5))
% 23.27/3.49      | r2_hidden(sK5,k1_tops_1(sK4,sK6)) ),
% 23.27/3.49      inference(unflattening,[status(thm)],[c_1020]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(contradiction,plain,
% 23.27/3.49      ( $false ),
% 23.27/3.49      inference(minisat,
% 23.27/3.49                [status(thm)],
% 23.27/3.49                [c_74668,c_44950,c_26397,c_20037,c_16081,c_11089,c_9875,
% 23.27/3.49                 c_9874,c_9457,c_6867,c_2981,c_2452,c_2433,c_1021,c_67,
% 23.27/3.49                 c_64,c_34,c_35,c_37]) ).
% 23.27/3.49  
% 23.27/3.49  
% 23.27/3.49  % SZS output end CNFRefutation for theBenchmark.p
% 23.27/3.49  
% 23.27/3.49  ------                               Statistics
% 23.27/3.49  
% 23.27/3.49  ------ General
% 23.27/3.49  
% 23.27/3.49  abstr_ref_over_cycles:                  0
% 23.27/3.49  abstr_ref_under_cycles:                 0
% 23.27/3.49  gc_basic_clause_elim:                   0
% 23.27/3.49  forced_gc_time:                         0
% 23.27/3.49  parsing_time:                           0.009
% 23.27/3.49  unif_index_cands_time:                  0.
% 23.27/3.49  unif_index_add_time:                    0.
% 23.27/3.49  orderings_time:                         0.
% 23.27/3.49  out_proof_time:                         0.016
% 23.27/3.49  total_time:                             2.651
% 23.27/3.49  num_of_symbols:                         54
% 23.27/3.49  num_of_terms:                           60423
% 23.27/3.49  
% 23.27/3.49  ------ Preprocessing
% 23.27/3.49  
% 23.27/3.49  num_of_splits:                          0
% 23.27/3.49  num_of_split_atoms:                     0
% 23.27/3.49  num_of_reused_defs:                     0
% 23.27/3.49  num_eq_ax_congr_red:                    30
% 23.27/3.49  num_of_sem_filtered_clauses:            1
% 23.27/3.49  num_of_subtypes:                        0
% 23.27/3.49  monotx_restored_types:                  0
% 23.27/3.49  sat_num_of_epr_types:                   0
% 23.27/3.49  sat_num_of_non_cyclic_types:            0
% 23.27/3.49  sat_guarded_non_collapsed_types:        0
% 23.27/3.49  num_pure_diseq_elim:                    0
% 23.27/3.49  simp_replaced_by:                       0
% 23.27/3.49  res_preprocessed:                       142
% 23.27/3.49  prep_upred:                             0
% 23.27/3.49  prep_unflattend:                        76
% 23.27/3.49  smt_new_axioms:                         0
% 23.27/3.49  pred_elim_cands:                        4
% 23.27/3.49  pred_elim:                              6
% 23.27/3.49  pred_elim_cl:                           9
% 23.27/3.49  pred_elim_cycles:                       8
% 23.27/3.49  merged_defs:                            18
% 23.27/3.49  merged_defs_ncl:                        0
% 23.27/3.49  bin_hyper_res:                          18
% 23.27/3.49  prep_cycles:                            4
% 23.27/3.49  pred_elim_time:                         0.017
% 23.27/3.49  splitting_time:                         0.
% 23.27/3.49  sem_filter_time:                        0.
% 23.27/3.49  monotx_time:                            0.001
% 23.27/3.49  subtype_inf_time:                       0.
% 23.27/3.49  
% 23.27/3.49  ------ Problem properties
% 23.27/3.49  
% 23.27/3.49  clauses:                                28
% 23.27/3.49  conjectures:                            2
% 23.27/3.49  epr:                                    7
% 23.27/3.49  horn:                                   21
% 23.27/3.49  ground:                                 5
% 23.27/3.49  unary:                                  5
% 23.27/3.49  binary:                                 10
% 23.27/3.49  lits:                                   64
% 23.27/3.49  lits_eq:                                10
% 23.27/3.49  fd_pure:                                0
% 23.27/3.49  fd_pseudo:                              0
% 23.27/3.49  fd_cond:                                0
% 23.27/3.49  fd_pseudo_cond:                         6
% 23.27/3.49  ac_symbols:                             0
% 23.27/3.49  
% 23.27/3.49  ------ Propositional Solver
% 23.27/3.49  
% 23.27/3.49  prop_solver_calls:                      36
% 23.27/3.49  prop_fast_solver_calls:                 3220
% 23.27/3.49  smt_solver_calls:                       0
% 23.27/3.49  smt_fast_solver_calls:                  0
% 23.27/3.49  prop_num_of_clauses:                    35117
% 23.27/3.49  prop_preprocess_simplified:             35543
% 23.27/3.49  prop_fo_subsumed:                       206
% 23.27/3.49  prop_solver_time:                       0.
% 23.27/3.49  smt_solver_time:                        0.
% 23.27/3.49  smt_fast_solver_time:                   0.
% 23.27/3.49  prop_fast_solver_time:                  0.
% 23.27/3.49  prop_unsat_core_time:                   0.002
% 23.27/3.49  
% 23.27/3.49  ------ QBF
% 23.27/3.49  
% 23.27/3.49  qbf_q_res:                              0
% 23.27/3.49  qbf_num_tautologies:                    0
% 23.27/3.49  qbf_prep_cycles:                        0
% 23.27/3.49  
% 23.27/3.49  ------ BMC1
% 23.27/3.49  
% 23.27/3.49  bmc1_current_bound:                     -1
% 23.27/3.49  bmc1_last_solved_bound:                 -1
% 23.27/3.49  bmc1_unsat_core_size:                   -1
% 23.27/3.49  bmc1_unsat_core_parents_size:           -1
% 23.27/3.49  bmc1_merge_next_fun:                    0
% 23.27/3.49  bmc1_unsat_core_clauses_time:           0.
% 23.27/3.49  
% 23.27/3.49  ------ Instantiation
% 23.27/3.49  
% 23.27/3.49  inst_num_of_clauses:                    5180
% 23.27/3.49  inst_num_in_passive:                    995
% 23.27/3.49  inst_num_in_active:                     1624
% 23.27/3.49  inst_num_in_unprocessed:                2560
% 23.27/3.49  inst_num_of_loops:                      2677
% 23.27/3.49  inst_num_of_learning_restarts:          0
% 23.27/3.49  inst_num_moves_active_passive:          1052
% 23.27/3.49  inst_lit_activity:                      0
% 23.27/3.49  inst_lit_activity_moves:                0
% 23.27/3.49  inst_num_tautologies:                   0
% 23.27/3.49  inst_num_prop_implied:                  0
% 23.27/3.49  inst_num_existing_simplified:           0
% 23.27/3.49  inst_num_eq_res_simplified:             0
% 23.27/3.49  inst_num_child_elim:                    0
% 23.27/3.49  inst_num_of_dismatching_blockings:      5872
% 23.27/3.49  inst_num_of_non_proper_insts:           7531
% 23.27/3.49  inst_num_of_duplicates:                 0
% 23.27/3.49  inst_inst_num_from_inst_to_res:         0
% 23.27/3.49  inst_dismatching_checking_time:         0.
% 23.27/3.49  
% 23.27/3.49  ------ Resolution
% 23.27/3.49  
% 23.27/3.49  res_num_of_clauses:                     0
% 23.27/3.49  res_num_in_passive:                     0
% 23.27/3.49  res_num_in_active:                      0
% 23.27/3.49  res_num_of_loops:                       146
% 23.27/3.49  res_forward_subset_subsumed:            684
% 23.27/3.49  res_backward_subset_subsumed:           0
% 23.27/3.49  res_forward_subsumed:                   2
% 23.27/3.49  res_backward_subsumed:                  0
% 23.27/3.49  res_forward_subsumption_resolution:     0
% 23.27/3.49  res_backward_subsumption_resolution:    0
% 23.27/3.49  res_clause_to_clause_subsumption:       63267
% 23.27/3.49  res_orphan_elimination:                 0
% 23.27/3.49  res_tautology_del:                      418
% 23.27/3.49  res_num_eq_res_simplified:              0
% 23.27/3.49  res_num_sel_changes:                    0
% 23.27/3.49  res_moves_from_active_to_pass:          0
% 23.27/3.49  
% 23.27/3.49  ------ Superposition
% 23.27/3.49  
% 23.27/3.49  sup_time_total:                         0.
% 23.27/3.49  sup_time_generating:                    0.
% 23.27/3.49  sup_time_sim_full:                      0.
% 23.27/3.49  sup_time_sim_immed:                     0.
% 23.27/3.49  
% 23.27/3.49  sup_num_of_clauses:                     6950
% 23.27/3.49  sup_num_in_active:                      497
% 23.27/3.49  sup_num_in_passive:                     6453
% 23.27/3.49  sup_num_of_loops:                       534
% 23.27/3.49  sup_fw_superposition:                   6003
% 23.27/3.49  sup_bw_superposition:                   5686
% 23.27/3.49  sup_immediate_simplified:               2764
% 23.27/3.49  sup_given_eliminated:                   3
% 23.27/3.49  comparisons_done:                       0
% 23.27/3.49  comparisons_avoided:                    567
% 23.27/3.49  
% 23.27/3.49  ------ Simplifications
% 23.27/3.49  
% 23.27/3.49  
% 23.27/3.49  sim_fw_subset_subsumed:                 1008
% 23.27/3.49  sim_bw_subset_subsumed:                 150
% 23.27/3.49  sim_fw_subsumed:                        999
% 23.27/3.49  sim_bw_subsumed:                        145
% 23.27/3.49  sim_fw_subsumption_res:                 0
% 23.27/3.49  sim_bw_subsumption_res:                 0
% 23.27/3.49  sim_tautology_del:                      46
% 23.27/3.49  sim_eq_tautology_del:                   233
% 23.27/3.49  sim_eq_res_simp:                        3
% 23.27/3.49  sim_fw_demodulated:                     357
% 23.27/3.49  sim_bw_demodulated:                     6
% 23.27/3.49  sim_light_normalised:                   505
% 23.27/3.49  sim_joinable_taut:                      0
% 23.27/3.49  sim_joinable_simp:                      0
% 23.27/3.49  sim_ac_normalised:                      0
% 23.27/3.49  sim_smt_subsumption:                    0
% 23.27/3.49  
%------------------------------------------------------------------------------
