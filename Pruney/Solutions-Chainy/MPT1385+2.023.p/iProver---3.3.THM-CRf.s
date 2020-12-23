%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:18:31 EST 2020

% Result     : Theorem 1.56s
% Output     : CNFRefutation 1.56s
% Verified   : 
% Statistics : Number of formulae       :  209 (2714 expanded)
%              Number of clauses        :  138 ( 722 expanded)
%              Number of leaves         :   19 ( 689 expanded)
%              Depth                    :   31
%              Number of atoms          :  797 (17693 expanded)
%              Number of equality atoms :  130 ( 469 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
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

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

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

fof(f33,plain,(
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

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f34])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f44,plain,(
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

fof(f43,plain,(
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

fof(f42,plain,
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

fof(f45,plain,
    ( ( ~ m1_connsp_2(sK3,sK1,sK2)
      | ~ m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2)) )
    & ( m1_connsp_2(sK3,sK1,sK2)
      | m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2)) )
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f41,f44,f43,f42])).

fof(f61,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f62,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f63,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tarski(X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f48,f46])).

fof(f67,plain,
    ( ~ m1_connsp_2(sK3,sK1,sK2)
    | ~ m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2)) ),
    inference(cnf_transformation,[],[f45])).

fof(f8,axiom,(
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

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( m2_connsp_2(X2,X0,X1)
      | ~ r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f65,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f45])).

fof(f64,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f45])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X2] : m1_connsp_2(X2,X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
     => m1_connsp_2(sK0(X0,X1),X0,X1) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_connsp_2(sK0(X0,X1),X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f38])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_connsp_2(sK0(X0,X1),X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f12,axiom,(
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

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ m1_connsp_2(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f49,f46])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k2_tarski(X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f47,f46])).

fof(f66,plain,
    ( m1_connsp_2(sK3,sK1,sK2)
    | m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2)) ),
    inference(cnf_transformation,[],[f45])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m2_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X2] :
          ( m2_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m2_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m2_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m2_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k2_tarski(X1,X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f52,f46])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1901,plain,
    ( ~ m1_subset_1(X0_46,X1_46)
    | m1_subset_1(X2_46,X3_46)
    | X2_46 != X0_46
    | X3_46 != X1_46 ),
    theory(equality)).

cnf(c_2590,plain,
    ( m1_subset_1(X0_46,X1_46)
    | ~ m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | X0_46 != k2_tarski(sK2,sK2)
    | X1_46 != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1901])).

cnf(c_3029,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),X0_46)
    | ~ m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | X0_46 != k1_zfmisc_1(u1_struct_0(sK1))
    | k6_domain_1(u1_struct_0(sK1),sK2) != k2_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_2590])).

cnf(c_3273,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | k6_domain_1(u1_struct_0(sK1),sK2) != k2_tarski(sK2,sK2)
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_3029])).

cnf(c_7,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_10,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_134,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X0,X1,X2)
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7,c_10])).

cnf(c_135,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_134])).

cnf(c_20,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_419,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_135,c_20])).

cnf(c_420,plain,
    ( ~ m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | r2_hidden(X1,k1_tops_1(sK1,X0))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_419])).

cnf(c_19,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_18,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_424,plain,
    ( ~ m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | r2_hidden(X1,k1_tops_1(sK1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_420,c_19,c_18])).

cnf(c_1884,plain,
    ( ~ m1_connsp_2(X0_46,sK1,X1_46)
    | ~ m1_subset_1(X1_46,u1_struct_0(sK1))
    | r2_hidden(X1_46,k1_tops_1(sK1,X0_46)) ),
    inference(subtyping,[status(esa)],[c_424])).

cnf(c_2195,plain,
    ( m1_connsp_2(X0_46,sK1,X1_46) != iProver_top
    | m1_subset_1(X1_46,u1_struct_0(sK1)) != iProver_top
    | r2_hidden(X1_46,k1_tops_1(sK1,X0_46)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1884])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k2_tarski(X0,X0),X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_175,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k2_tarski(X0,X0),X1) ),
    inference(prop_impl,[status(thm)],[c_0])).

cnf(c_14,negated_conjecture,
    ( ~ m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2))
    | ~ m1_connsp_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_177,plain,
    ( ~ m1_connsp_2(sK3,sK1,sK2)
    | ~ m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2)) ),
    inference(prop_impl,[status(thm)],[c_14])).

cnf(c_178,plain,
    ( ~ m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2))
    | ~ m1_connsp_2(sK3,sK1,sK2) ),
    inference(renaming,[status(thm)],[c_177])).

cnf(c_8,plain,
    ( m2_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_564,plain,
    ( m2_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_18])).

cnf(c_565,plain,
    ( m2_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X1,k1_tops_1(sK1,X0))
    | ~ v2_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_564])).

cnf(c_569,plain,
    ( ~ r1_tarski(X1,k1_tops_1(sK1,X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m2_connsp_2(X0,sK1,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_565,c_19])).

cnf(c_570,plain,
    ( m2_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X1,k1_tops_1(sK1,X0)) ),
    inference(renaming,[status(thm)],[c_569])).

cnf(c_661,plain,
    ( ~ m1_connsp_2(sK3,sK1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X1,k1_tops_1(sK1,X0))
    | k6_domain_1(u1_struct_0(sK1),sK2) != X1
    | sK1 != sK1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_178,c_570])).

cnf(c_662,plain,
    ( ~ m1_connsp_2(sK3,sK1,sK2)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(k6_domain_1(u1_struct_0(sK1),sK2),k1_tops_1(sK1,sK3)) ),
    inference(unflattening,[status(thm)],[c_661])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_664,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_connsp_2(sK3,sK1,sK2)
    | ~ r1_tarski(k6_domain_1(u1_struct_0(sK1),sK2),k1_tops_1(sK1,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_662,c_16])).

cnf(c_665,plain,
    ( ~ m1_connsp_2(sK3,sK1,sK2)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(k6_domain_1(u1_struct_0(sK1),sK2),k1_tops_1(sK1,sK3)) ),
    inference(renaming,[status(thm)],[c_664])).

cnf(c_688,plain,
    ( ~ m1_connsp_2(sK3,sK1,sK2)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X0,X1)
    | k1_tops_1(sK1,sK3) != X1
    | k6_domain_1(u1_struct_0(sK1),sK2) != k2_tarski(X0,X0) ),
    inference(resolution_lifted,[status(thm)],[c_175,c_665])).

cnf(c_689,plain,
    ( ~ m1_connsp_2(sK3,sK1,sK2)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X0,k1_tops_1(sK1,sK3))
    | k6_domain_1(u1_struct_0(sK1),sK2) != k2_tarski(X0,X0) ),
    inference(unflattening,[status(thm)],[c_688])).

cnf(c_1880,plain,
    ( ~ m1_connsp_2(sK3,sK1,sK2)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X0_46,k1_tops_1(sK1,sK3))
    | k6_domain_1(u1_struct_0(sK1),sK2) != k2_tarski(X0_46,X0_46) ),
    inference(subtyping,[status(esa)],[c_689])).

cnf(c_1892,plain,
    ( ~ r2_hidden(X0_46,k1_tops_1(sK1,sK3))
    | k6_domain_1(u1_struct_0(sK1),sK2) != k2_tarski(X0_46,X0_46)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_1880])).

cnf(c_2200,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK2) != k2_tarski(X0_46,X0_46)
    | r2_hidden(X0_46,k1_tops_1(sK1,sK3)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1892])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_24,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_12,plain,
    ( m1_connsp_2(sK0(X0,X1),X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_401,plain,
    ( m1_connsp_2(sK0(X0,X1),X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_20])).

cnf(c_402,plain,
    ( m1_connsp_2(sK0(sK1,X0),sK1,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_401])).

cnf(c_406,plain,
    ( m1_connsp_2(sK0(sK1,X0),sK1,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_402,c_19,c_18])).

cnf(c_1885,plain,
    ( m1_connsp_2(sK0(sK1,X0_46),sK1,X0_46)
    | ~ m1_subset_1(X0_46,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_406])).

cnf(c_1927,plain,
    ( m1_connsp_2(sK0(sK1,X0_46),sK1,X0_46) = iProver_top
    | m1_subset_1(X0_46,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1885])).

cnf(c_1929,plain,
    ( m1_connsp_2(sK0(sK1,sK2),sK1,sK2) = iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1927])).

cnf(c_1943,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK2) != k2_tarski(X0_46,X0_46)
    | r2_hidden(X0_46,k1_tops_1(sK1,sK3)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1892])).

cnf(c_461,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_20])).

cnf(c_462,plain,
    ( ~ m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_461])).

cnf(c_466,plain,
    ( ~ m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_462,c_19,c_18])).

cnf(c_1882,plain,
    ( ~ m1_connsp_2(X0_46,sK1,X1_46)
    | ~ m1_subset_1(X1_46,u1_struct_0(sK1))
    | m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_466])).

cnf(c_2316,plain,
    ( ~ m1_connsp_2(sK0(sK1,X0_46),sK1,X0_46)
    | ~ m1_subset_1(X0_46,u1_struct_0(sK1))
    | m1_subset_1(sK0(sK1,X0_46),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_1882])).

cnf(c_2317,plain,
    ( m1_connsp_2(sK0(sK1,X0_46),sK1,X0_46) != iProver_top
    | m1_subset_1(X0_46,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK0(sK1,X0_46),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2316])).

cnf(c_2319,plain,
    ( m1_connsp_2(sK0(sK1,sK2),sK1,sK2) != iProver_top
    | m1_subset_1(sK0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2317])).

cnf(c_13,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_118,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X0,X1,X2)
    | r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13,c_10])).

cnf(c_119,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_118])).

cnf(c_440,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_119,c_20])).

cnf(c_441,plain,
    ( ~ m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | r2_hidden(X1,X0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_440])).

cnf(c_445,plain,
    ( ~ m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | r2_hidden(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_441,c_19,c_18])).

cnf(c_1883,plain,
    ( ~ m1_connsp_2(X0_46,sK1,X1_46)
    | ~ m1_subset_1(X1_46,u1_struct_0(sK1))
    | r2_hidden(X1_46,X0_46) ),
    inference(subtyping,[status(esa)],[c_445])).

cnf(c_2321,plain,
    ( ~ m1_connsp_2(sK0(sK1,X0_46),sK1,X0_46)
    | ~ m1_subset_1(X0_46,u1_struct_0(sK1))
    | r2_hidden(X0_46,sK0(sK1,X0_46)) ),
    inference(instantiation,[status(thm)],[c_1883])).

cnf(c_2322,plain,
    ( m1_connsp_2(sK0(sK1,X0_46),sK1,X0_46) != iProver_top
    | m1_subset_1(X0_46,u1_struct_0(sK1)) != iProver_top
    | r2_hidden(X0_46,sK0(sK1,X0_46)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2321])).

cnf(c_2324,plain,
    ( m1_connsp_2(sK0(sK1,sK2),sK1,sK2) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | r2_hidden(sK2,sK0(sK1,sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2322])).

cnf(c_2,plain,
    ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1891,plain,
    ( m1_subset_1(k2_tarski(X0_46,X0_46),k1_zfmisc_1(X1_46))
    | ~ r2_hidden(X0_46,X1_46) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_2476,plain,
    ( m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK2,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1891])).

cnf(c_2477,plain,
    ( m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | r2_hidden(sK2,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2476])).

cnf(c_1886,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_2193,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1886])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1890,plain,
    ( ~ m1_subset_1(X0_46,X1_46)
    | r2_hidden(X0_46,X1_46)
    | v1_xboole_0(X1_46) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_2189,plain,
    ( m1_subset_1(X0_46,X1_46) != iProver_top
    | r2_hidden(X0_46,X1_46) = iProver_top
    | v1_xboole_0(X1_46) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1890])).

cnf(c_2562,plain,
    ( r2_hidden(sK2,u1_struct_0(sK1)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2193,c_2189])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1889,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(X1_46))
    | ~ r2_hidden(X2_46,X0_46)
    | ~ v1_xboole_0(X1_46) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_2383,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X1_46,X0_46)
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1889])).

cnf(c_2787,plain,
    ( ~ m1_subset_1(sK0(sK1,X0_46),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X1_46,sK0(sK1,X0_46))
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_2383])).

cnf(c_2788,plain,
    ( m1_subset_1(sK0(sK1,X0_46),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(X1_46,sK0(sK1,X0_46)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2787])).

cnf(c_2790,plain,
    ( m1_subset_1(sK0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(sK2,sK0(sK1,sK2)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2788])).

cnf(c_1893,plain,
    ( ~ m1_connsp_2(sK3,sK1,sK2)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_1880])).

cnf(c_2199,plain,
    ( m1_connsp_2(sK3,sK1,sK2) != iProver_top
    | m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1893])).

cnf(c_25,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1942,plain,
    ( m1_connsp_2(sK3,sK1,sK2) != iProver_top
    | m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1893])).

cnf(c_1,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(k2_tarski(X0,X0),X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_173,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(k2_tarski(X0,X0),X1) ),
    inference(prop_impl,[status(thm)],[c_1])).

cnf(c_15,negated_conjecture,
    ( m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2))
    | m1_connsp_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_179,plain,
    ( m1_connsp_2(sK3,sK1,sK2)
    | m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2)) ),
    inference(prop_impl,[status(thm)],[c_15])).

cnf(c_180,plain,
    ( m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2))
    | m1_connsp_2(sK3,sK1,sK2) ),
    inference(renaming,[status(thm)],[c_179])).

cnf(c_9,plain,
    ( ~ m2_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_11,plain,
    ( ~ m2_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_128,plain,
    ( ~ m2_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9,c_11])).

cnf(c_526,plain,
    ( ~ m2_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_128,c_18])).

cnf(c_527,plain,
    ( ~ m2_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(X1,k1_tops_1(sK1,X0))
    | ~ v2_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_526])).

cnf(c_531,plain,
    ( r1_tarski(X1,k1_tops_1(sK1,X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m2_connsp_2(X0,sK1,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_527,c_19])).

cnf(c_532,plain,
    ( ~ m2_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(X1,k1_tops_1(sK1,X0)) ),
    inference(renaming,[status(thm)],[c_531])).

cnf(c_648,plain,
    ( m1_connsp_2(sK3,sK1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(X0,k1_tops_1(sK1,X1))
    | k6_domain_1(u1_struct_0(sK1),sK2) != X0
    | sK1 != sK1
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_180,c_532])).

cnf(c_649,plain,
    ( m1_connsp_2(sK3,sK1,sK2)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(k6_domain_1(u1_struct_0(sK1),sK2),k1_tops_1(sK1,sK3)) ),
    inference(unflattening,[status(thm)],[c_648])).

cnf(c_706,plain,
    ( m1_connsp_2(sK3,sK1,sK2)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(X0,X1)
    | k1_tops_1(sK1,sK3) != X1
    | k6_domain_1(u1_struct_0(sK1),sK2) != k2_tarski(X0,X0) ),
    inference(resolution_lifted,[status(thm)],[c_173,c_649])).

cnf(c_707,plain,
    ( m1_connsp_2(sK3,sK1,sK2)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(X0,k1_tops_1(sK1,sK3))
    | k6_domain_1(u1_struct_0(sK1),sK2) != k2_tarski(X0,X0) ),
    inference(unflattening,[status(thm)],[c_706])).

cnf(c_1879,plain,
    ( m1_connsp_2(sK3,sK1,sK2)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(X0_46,k1_tops_1(sK1,sK3))
    | k6_domain_1(u1_struct_0(sK1),sK2) != k2_tarski(X0_46,X0_46) ),
    inference(subtyping,[status(esa)],[c_707])).

cnf(c_1895,plain,
    ( m1_connsp_2(sK3,sK1,sK2)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_1879])).

cnf(c_1946,plain,
    ( m1_connsp_2(sK3,sK1,sK2) = iProver_top
    | m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | sP1_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1895])).

cnf(c_1894,plain,
    ( r2_hidden(X0_46,k1_tops_1(sK1,sK3))
    | k6_domain_1(u1_struct_0(sK1),sK2) != k2_tarski(X0_46,X0_46)
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_1879])).

cnf(c_2202,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK2) != k2_tarski(X0_46,X0_46)
    | r2_hidden(X0_46,k1_tops_1(sK1,sK3)) = iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1894])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1888,plain,
    ( ~ m1_subset_1(X0_46,X1_46)
    | v1_xboole_0(X1_46)
    | k6_domain_1(X1_46,X0_46) = k2_tarski(X0_46,X0_46) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_2191,plain,
    ( k6_domain_1(X0_46,X1_46) = k2_tarski(X1_46,X1_46)
    | m1_subset_1(X1_46,X0_46) != iProver_top
    | v1_xboole_0(X0_46) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1888])).

cnf(c_2661,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK2) = k2_tarski(sK2,sK2)
    | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2193,c_2191])).

cnf(c_1928,plain,
    ( m1_connsp_2(sK0(sK1,sK2),sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1885])).

cnf(c_2318,plain,
    ( ~ m1_connsp_2(sK0(sK1,sK2),sK1,sK2)
    | m1_subset_1(sK0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_2316])).

cnf(c_2323,plain,
    ( ~ m1_connsp_2(sK0(sK1,sK2),sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | r2_hidden(sK2,sK0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_2321])).

cnf(c_2678,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | k6_domain_1(u1_struct_0(sK1),sK2) = k2_tarski(sK2,sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2661])).

cnf(c_2789,plain,
    ( ~ m1_subset_1(sK0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK2,sK0(sK1,sK2))
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_2787])).

cnf(c_2807,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK2) = k2_tarski(sK2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2661,c_17,c_1928,c_2318,c_2323,c_2678,c_2789])).

cnf(c_2919,plain,
    ( k2_tarski(X0_46,X0_46) != k2_tarski(sK2,sK2)
    | r2_hidden(X0_46,k1_tops_1(sK1,sK3)) = iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2202,c_2807])).

cnf(c_2926,plain,
    ( r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2919])).

cnf(c_6,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_482,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_20])).

cnf(c_483,plain,
    ( m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X1,k1_tops_1(sK1,X0))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_482])).

cnf(c_487,plain,
    ( m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X1,k1_tops_1(sK1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_483,c_19,c_18])).

cnf(c_1881,plain,
    ( m1_connsp_2(X0_46,sK1,X1_46)
    | ~ m1_subset_1(X1_46,u1_struct_0(sK1))
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X1_46,k1_tops_1(sK1,X0_46)) ),
    inference(subtyping,[status(esa)],[c_487])).

cnf(c_2198,plain,
    ( m1_connsp_2(X0_46,sK1,X1_46) = iProver_top
    | m1_subset_1(X1_46,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(X1_46,k1_tops_1(sK1,X0_46)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1881])).

cnf(c_2931,plain,
    ( m1_connsp_2(sK3,sK1,sK2) = iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_2926,c_2198])).

cnf(c_2992,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2199,c_24,c_25,c_1942,c_1946,c_2931])).

cnf(c_2996,plain,
    ( m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2992,c_2807])).

cnf(c_3197,plain,
    ( r2_hidden(X0_46,k1_tops_1(sK1,sK3)) != iProver_top
    | k6_domain_1(u1_struct_0(sK1),sK2) != k2_tarski(X0_46,X0_46) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2200,c_24,c_1929,c_1943,c_2319,c_2324,c_2477,c_2562,c_2790,c_2996])).

cnf(c_3198,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK2) != k2_tarski(X0_46,X0_46)
    | r2_hidden(X0_46,k1_tops_1(sK1,sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3197])).

cnf(c_3203,plain,
    ( k2_tarski(X0_46,X0_46) != k2_tarski(sK2,sK2)
    | r2_hidden(X0_46,k1_tops_1(sK1,sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3198,c_2807])).

cnf(c_3209,plain,
    ( r2_hidden(sK2,k1_tops_1(sK1,sK3)) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3203])).

cnf(c_3214,plain,
    ( m1_connsp_2(sK3,sK1,sK2) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2195,c_3209])).

cnf(c_3219,plain,
    ( ~ m1_connsp_2(sK3,sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3214])).

cnf(c_2999,plain,
    ( ~ m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | sP0_iProver_split ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2996])).

cnf(c_2579,plain,
    ( r2_hidden(sK2,u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2562])).

cnf(c_1897,plain,
    ( X0_46 = X0_46 ),
    theory(equality)).

cnf(c_2546,plain,
    ( k1_zfmisc_1(u1_struct_0(sK1)) = k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1897])).

cnf(c_1948,plain,
    ( r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | ~ sP1_iProver_split
    | k6_domain_1(u1_struct_0(sK1),sK2) != k2_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_1894])).

cnf(c_1944,plain,
    ( ~ r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | ~ sP0_iProver_split
    | k6_domain_1(u1_struct_0(sK1),sK2) != k2_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_1892])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3273,c_3219,c_2999,c_2789,c_2678,c_2579,c_2546,c_2476,c_2323,c_2318,c_1948,c_1895,c_1944,c_1928,c_17])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n001.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 20:26:45 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 1.56/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.56/0.98  
% 1.56/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.56/0.98  
% 1.56/0.98  ------  iProver source info
% 1.56/0.98  
% 1.56/0.98  git: date: 2020-06-30 10:37:57 +0100
% 1.56/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.56/0.98  git: non_committed_changes: false
% 1.56/0.98  git: last_make_outside_of_git: false
% 1.56/0.98  
% 1.56/0.98  ------ 
% 1.56/0.98  
% 1.56/0.98  ------ Input Options
% 1.56/0.98  
% 1.56/0.98  --out_options                           all
% 1.56/0.98  --tptp_safe_out                         true
% 1.56/0.98  --problem_path                          ""
% 1.56/0.98  --include_path                          ""
% 1.56/0.98  --clausifier                            res/vclausify_rel
% 1.56/0.98  --clausifier_options                    --mode clausify
% 1.56/0.98  --stdin                                 false
% 1.56/0.98  --stats_out                             all
% 1.56/0.98  
% 1.56/0.98  ------ General Options
% 1.56/0.98  
% 1.56/0.98  --fof                                   false
% 1.56/0.98  --time_out_real                         305.
% 1.56/0.98  --time_out_virtual                      -1.
% 1.56/0.98  --symbol_type_check                     false
% 1.56/0.98  --clausify_out                          false
% 1.56/0.98  --sig_cnt_out                           false
% 1.56/0.98  --trig_cnt_out                          false
% 1.56/0.98  --trig_cnt_out_tolerance                1.
% 1.56/0.98  --trig_cnt_out_sk_spl                   false
% 1.56/0.98  --abstr_cl_out                          false
% 1.56/0.98  
% 1.56/0.98  ------ Global Options
% 1.56/0.98  
% 1.56/0.98  --schedule                              default
% 1.56/0.98  --add_important_lit                     false
% 1.56/0.98  --prop_solver_per_cl                    1000
% 1.56/0.98  --min_unsat_core                        false
% 1.56/0.98  --soft_assumptions                      false
% 1.56/0.98  --soft_lemma_size                       3
% 1.56/0.98  --prop_impl_unit_size                   0
% 1.56/0.98  --prop_impl_unit                        []
% 1.56/0.98  --share_sel_clauses                     true
% 1.56/0.98  --reset_solvers                         false
% 1.56/0.98  --bc_imp_inh                            [conj_cone]
% 1.56/0.98  --conj_cone_tolerance                   3.
% 1.56/0.98  --extra_neg_conj                        none
% 1.56/0.98  --large_theory_mode                     true
% 1.56/0.98  --prolific_symb_bound                   200
% 1.56/0.98  --lt_threshold                          2000
% 1.56/0.98  --clause_weak_htbl                      true
% 1.56/0.98  --gc_record_bc_elim                     false
% 1.56/0.98  
% 1.56/0.98  ------ Preprocessing Options
% 1.56/0.98  
% 1.56/0.98  --preprocessing_flag                    true
% 1.56/0.98  --time_out_prep_mult                    0.1
% 1.56/0.98  --splitting_mode                        input
% 1.56/0.98  --splitting_grd                         true
% 1.56/0.98  --splitting_cvd                         false
% 1.56/0.98  --splitting_cvd_svl                     false
% 1.56/0.98  --splitting_nvd                         32
% 1.56/0.98  --sub_typing                            true
% 1.56/0.98  --prep_gs_sim                           true
% 1.56/0.98  --prep_unflatten                        true
% 1.56/0.98  --prep_res_sim                          true
% 1.56/0.98  --prep_upred                            true
% 1.56/0.98  --prep_sem_filter                       exhaustive
% 1.56/0.98  --prep_sem_filter_out                   false
% 1.56/0.98  --pred_elim                             true
% 1.56/0.98  --res_sim_input                         true
% 1.56/0.98  --eq_ax_congr_red                       true
% 1.56/0.98  --pure_diseq_elim                       true
% 1.56/0.98  --brand_transform                       false
% 1.56/0.98  --non_eq_to_eq                          false
% 1.56/0.98  --prep_def_merge                        true
% 1.56/0.98  --prep_def_merge_prop_impl              false
% 1.56/0.98  --prep_def_merge_mbd                    true
% 1.56/0.98  --prep_def_merge_tr_red                 false
% 1.56/0.98  --prep_def_merge_tr_cl                  false
% 1.56/0.98  --smt_preprocessing                     true
% 1.56/0.98  --smt_ac_axioms                         fast
% 1.56/0.98  --preprocessed_out                      false
% 1.56/0.98  --preprocessed_stats                    false
% 1.56/0.98  
% 1.56/0.98  ------ Abstraction refinement Options
% 1.56/0.98  
% 1.56/0.98  --abstr_ref                             []
% 1.56/0.98  --abstr_ref_prep                        false
% 1.56/0.98  --abstr_ref_until_sat                   false
% 1.56/0.98  --abstr_ref_sig_restrict                funpre
% 1.56/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.56/0.98  --abstr_ref_under                       []
% 1.56/0.98  
% 1.56/0.98  ------ SAT Options
% 1.56/0.98  
% 1.56/0.98  --sat_mode                              false
% 1.56/0.98  --sat_fm_restart_options                ""
% 1.56/0.98  --sat_gr_def                            false
% 1.56/0.98  --sat_epr_types                         true
% 1.56/0.98  --sat_non_cyclic_types                  false
% 1.56/0.98  --sat_finite_models                     false
% 1.56/0.98  --sat_fm_lemmas                         false
% 1.56/0.98  --sat_fm_prep                           false
% 1.56/0.98  --sat_fm_uc_incr                        true
% 1.56/0.98  --sat_out_model                         small
% 1.56/0.98  --sat_out_clauses                       false
% 1.56/0.98  
% 1.56/0.98  ------ QBF Options
% 1.56/0.98  
% 1.56/0.98  --qbf_mode                              false
% 1.56/0.98  --qbf_elim_univ                         false
% 1.56/0.98  --qbf_dom_inst                          none
% 1.56/0.98  --qbf_dom_pre_inst                      false
% 1.56/0.98  --qbf_sk_in                             false
% 1.56/0.98  --qbf_pred_elim                         true
% 1.56/0.98  --qbf_split                             512
% 1.56/0.98  
% 1.56/0.98  ------ BMC1 Options
% 1.56/0.98  
% 1.56/0.98  --bmc1_incremental                      false
% 1.56/0.98  --bmc1_axioms                           reachable_all
% 1.56/0.98  --bmc1_min_bound                        0
% 1.56/0.98  --bmc1_max_bound                        -1
% 1.56/0.98  --bmc1_max_bound_default                -1
% 1.56/0.98  --bmc1_symbol_reachability              true
% 1.56/0.98  --bmc1_property_lemmas                  false
% 1.56/0.98  --bmc1_k_induction                      false
% 1.56/0.98  --bmc1_non_equiv_states                 false
% 1.56/0.98  --bmc1_deadlock                         false
% 1.56/0.98  --bmc1_ucm                              false
% 1.56/0.98  --bmc1_add_unsat_core                   none
% 1.56/0.98  --bmc1_unsat_core_children              false
% 1.56/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.56/0.98  --bmc1_out_stat                         full
% 1.56/0.98  --bmc1_ground_init                      false
% 1.56/0.98  --bmc1_pre_inst_next_state              false
% 1.56/0.98  --bmc1_pre_inst_state                   false
% 1.56/0.98  --bmc1_pre_inst_reach_state             false
% 1.56/0.98  --bmc1_out_unsat_core                   false
% 1.56/0.98  --bmc1_aig_witness_out                  false
% 1.56/0.98  --bmc1_verbose                          false
% 1.56/0.98  --bmc1_dump_clauses_tptp                false
% 1.56/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.56/0.98  --bmc1_dump_file                        -
% 1.56/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.56/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.56/0.98  --bmc1_ucm_extend_mode                  1
% 1.56/0.98  --bmc1_ucm_init_mode                    2
% 1.56/0.98  --bmc1_ucm_cone_mode                    none
% 1.56/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.56/0.98  --bmc1_ucm_relax_model                  4
% 1.56/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.56/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.56/0.98  --bmc1_ucm_layered_model                none
% 1.56/0.98  --bmc1_ucm_max_lemma_size               10
% 1.56/0.98  
% 1.56/0.98  ------ AIG Options
% 1.56/0.98  
% 1.56/0.98  --aig_mode                              false
% 1.56/0.98  
% 1.56/0.98  ------ Instantiation Options
% 1.56/0.98  
% 1.56/0.98  --instantiation_flag                    true
% 1.56/0.98  --inst_sos_flag                         false
% 1.56/0.98  --inst_sos_phase                        true
% 1.56/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.56/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.56/0.98  --inst_lit_sel_side                     num_symb
% 1.56/0.98  --inst_solver_per_active                1400
% 1.56/0.98  --inst_solver_calls_frac                1.
% 1.56/0.98  --inst_passive_queue_type               priority_queues
% 1.56/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.56/0.98  --inst_passive_queues_freq              [25;2]
% 1.56/0.98  --inst_dismatching                      true
% 1.56/0.98  --inst_eager_unprocessed_to_passive     true
% 1.56/0.98  --inst_prop_sim_given                   true
% 1.56/0.98  --inst_prop_sim_new                     false
% 1.56/0.98  --inst_subs_new                         false
% 1.56/0.98  --inst_eq_res_simp                      false
% 1.56/0.98  --inst_subs_given                       false
% 1.56/0.98  --inst_orphan_elimination               true
% 1.56/0.98  --inst_learning_loop_flag               true
% 1.56/0.98  --inst_learning_start                   3000
% 1.56/0.98  --inst_learning_factor                  2
% 1.56/0.98  --inst_start_prop_sim_after_learn       3
% 1.56/0.98  --inst_sel_renew                        solver
% 1.56/0.98  --inst_lit_activity_flag                true
% 1.56/0.98  --inst_restr_to_given                   false
% 1.56/0.98  --inst_activity_threshold               500
% 1.56/0.98  --inst_out_proof                        true
% 1.56/0.98  
% 1.56/0.98  ------ Resolution Options
% 1.56/0.98  
% 1.56/0.98  --resolution_flag                       true
% 1.56/0.98  --res_lit_sel                           adaptive
% 1.56/0.98  --res_lit_sel_side                      none
% 1.56/0.98  --res_ordering                          kbo
% 1.56/0.98  --res_to_prop_solver                    active
% 1.56/0.98  --res_prop_simpl_new                    false
% 1.56/0.98  --res_prop_simpl_given                  true
% 1.56/0.98  --res_passive_queue_type                priority_queues
% 1.56/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.56/0.98  --res_passive_queues_freq               [15;5]
% 1.56/0.98  --res_forward_subs                      full
% 1.56/0.98  --res_backward_subs                     full
% 1.56/0.98  --res_forward_subs_resolution           true
% 1.56/0.98  --res_backward_subs_resolution          true
% 1.56/0.98  --res_orphan_elimination                true
% 1.56/0.98  --res_time_limit                        2.
% 1.56/0.98  --res_out_proof                         true
% 1.56/0.98  
% 1.56/0.98  ------ Superposition Options
% 1.56/0.98  
% 1.56/0.98  --superposition_flag                    true
% 1.56/0.98  --sup_passive_queue_type                priority_queues
% 1.56/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.56/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.56/0.98  --demod_completeness_check              fast
% 1.56/0.98  --demod_use_ground                      true
% 1.56/0.98  --sup_to_prop_solver                    passive
% 1.56/0.98  --sup_prop_simpl_new                    true
% 1.56/0.98  --sup_prop_simpl_given                  true
% 1.56/0.98  --sup_fun_splitting                     false
% 1.56/0.98  --sup_smt_interval                      50000
% 1.56/0.98  
% 1.56/0.98  ------ Superposition Simplification Setup
% 1.56/0.98  
% 1.56/0.98  --sup_indices_passive                   []
% 1.56/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.56/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.56/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.56/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.56/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.56/0.98  --sup_full_bw                           [BwDemod]
% 1.56/0.98  --sup_immed_triv                        [TrivRules]
% 1.56/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.56/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.56/0.98  --sup_immed_bw_main                     []
% 1.56/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.56/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.56/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.56/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.56/0.98  
% 1.56/0.98  ------ Combination Options
% 1.56/0.98  
% 1.56/0.98  --comb_res_mult                         3
% 1.56/0.98  --comb_sup_mult                         2
% 1.56/0.98  --comb_inst_mult                        10
% 1.56/0.98  
% 1.56/0.98  ------ Debug Options
% 1.56/0.98  
% 1.56/0.98  --dbg_backtrace                         false
% 1.56/0.98  --dbg_dump_prop_clauses                 false
% 1.56/0.98  --dbg_dump_prop_clauses_file            -
% 1.56/0.98  --dbg_out_stat                          false
% 1.56/0.98  ------ Parsing...
% 1.56/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.56/0.98  
% 1.56/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 1.56/0.98  
% 1.56/0.98  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.56/0.98  
% 1.56/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.56/0.98  ------ Proving...
% 1.56/0.98  ------ Problem Properties 
% 1.56/0.98  
% 1.56/0.98  
% 1.56/0.98  clauses                                 15
% 1.56/0.98  conjectures                             2
% 1.56/0.98  EPR                                     1
% 1.56/0.98  Horn                                    12
% 1.56/0.98  unary                                   2
% 1.56/0.98  binary                                  2
% 1.56/0.98  lits                                    40
% 1.56/0.98  lits eq                                 3
% 1.56/0.98  fd_pure                                 0
% 1.56/0.98  fd_pseudo                               0
% 1.56/0.98  fd_cond                                 0
% 1.56/0.98  fd_pseudo_cond                          0
% 1.56/0.98  AC symbols                              0
% 1.56/0.98  
% 1.56/0.98  ------ Schedule dynamic 5 is on 
% 1.56/0.98  
% 1.56/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.56/0.98  
% 1.56/0.98  
% 1.56/0.98  ------ 
% 1.56/0.98  Current options:
% 1.56/0.98  ------ 
% 1.56/0.98  
% 1.56/0.98  ------ Input Options
% 1.56/0.98  
% 1.56/0.98  --out_options                           all
% 1.56/0.98  --tptp_safe_out                         true
% 1.56/0.98  --problem_path                          ""
% 1.56/0.98  --include_path                          ""
% 1.56/0.98  --clausifier                            res/vclausify_rel
% 1.56/0.98  --clausifier_options                    --mode clausify
% 1.56/0.98  --stdin                                 false
% 1.56/0.98  --stats_out                             all
% 1.56/0.98  
% 1.56/0.98  ------ General Options
% 1.56/0.98  
% 1.56/0.98  --fof                                   false
% 1.56/0.98  --time_out_real                         305.
% 1.56/0.98  --time_out_virtual                      -1.
% 1.56/0.98  --symbol_type_check                     false
% 1.56/0.98  --clausify_out                          false
% 1.56/0.98  --sig_cnt_out                           false
% 1.56/0.98  --trig_cnt_out                          false
% 1.56/0.98  --trig_cnt_out_tolerance                1.
% 1.56/0.98  --trig_cnt_out_sk_spl                   false
% 1.56/0.98  --abstr_cl_out                          false
% 1.56/0.98  
% 1.56/0.98  ------ Global Options
% 1.56/0.98  
% 1.56/0.98  --schedule                              default
% 1.56/0.98  --add_important_lit                     false
% 1.56/0.98  --prop_solver_per_cl                    1000
% 1.56/0.98  --min_unsat_core                        false
% 1.56/0.98  --soft_assumptions                      false
% 1.56/0.98  --soft_lemma_size                       3
% 1.56/0.98  --prop_impl_unit_size                   0
% 1.56/0.98  --prop_impl_unit                        []
% 1.56/0.98  --share_sel_clauses                     true
% 1.56/0.98  --reset_solvers                         false
% 1.56/0.98  --bc_imp_inh                            [conj_cone]
% 1.56/0.98  --conj_cone_tolerance                   3.
% 1.56/0.98  --extra_neg_conj                        none
% 1.56/0.98  --large_theory_mode                     true
% 1.56/0.98  --prolific_symb_bound                   200
% 1.56/0.98  --lt_threshold                          2000
% 1.56/0.98  --clause_weak_htbl                      true
% 1.56/0.98  --gc_record_bc_elim                     false
% 1.56/0.98  
% 1.56/0.98  ------ Preprocessing Options
% 1.56/0.98  
% 1.56/0.98  --preprocessing_flag                    true
% 1.56/0.98  --time_out_prep_mult                    0.1
% 1.56/0.98  --splitting_mode                        input
% 1.56/0.98  --splitting_grd                         true
% 1.56/0.98  --splitting_cvd                         false
% 1.56/0.98  --splitting_cvd_svl                     false
% 1.56/0.98  --splitting_nvd                         32
% 1.56/0.98  --sub_typing                            true
% 1.56/0.98  --prep_gs_sim                           true
% 1.56/0.98  --prep_unflatten                        true
% 1.56/0.98  --prep_res_sim                          true
% 1.56/0.98  --prep_upred                            true
% 1.56/0.98  --prep_sem_filter                       exhaustive
% 1.56/0.98  --prep_sem_filter_out                   false
% 1.56/0.98  --pred_elim                             true
% 1.56/0.98  --res_sim_input                         true
% 1.56/0.98  --eq_ax_congr_red                       true
% 1.56/0.98  --pure_diseq_elim                       true
% 1.56/0.98  --brand_transform                       false
% 1.56/0.98  --non_eq_to_eq                          false
% 1.56/0.98  --prep_def_merge                        true
% 1.56/0.98  --prep_def_merge_prop_impl              false
% 1.56/0.98  --prep_def_merge_mbd                    true
% 1.56/0.98  --prep_def_merge_tr_red                 false
% 1.56/0.98  --prep_def_merge_tr_cl                  false
% 1.56/0.98  --smt_preprocessing                     true
% 1.56/0.98  --smt_ac_axioms                         fast
% 1.56/0.98  --preprocessed_out                      false
% 1.56/0.98  --preprocessed_stats                    false
% 1.56/0.98  
% 1.56/0.98  ------ Abstraction refinement Options
% 1.56/0.98  
% 1.56/0.98  --abstr_ref                             []
% 1.56/0.98  --abstr_ref_prep                        false
% 1.56/0.98  --abstr_ref_until_sat                   false
% 1.56/0.98  --abstr_ref_sig_restrict                funpre
% 1.56/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.56/0.98  --abstr_ref_under                       []
% 1.56/0.98  
% 1.56/0.98  ------ SAT Options
% 1.56/0.98  
% 1.56/0.98  --sat_mode                              false
% 1.56/0.98  --sat_fm_restart_options                ""
% 1.56/0.98  --sat_gr_def                            false
% 1.56/0.98  --sat_epr_types                         true
% 1.56/0.98  --sat_non_cyclic_types                  false
% 1.56/0.98  --sat_finite_models                     false
% 1.56/0.98  --sat_fm_lemmas                         false
% 1.56/0.98  --sat_fm_prep                           false
% 1.56/0.98  --sat_fm_uc_incr                        true
% 1.56/0.98  --sat_out_model                         small
% 1.56/0.98  --sat_out_clauses                       false
% 1.56/0.98  
% 1.56/0.98  ------ QBF Options
% 1.56/0.98  
% 1.56/0.98  --qbf_mode                              false
% 1.56/0.98  --qbf_elim_univ                         false
% 1.56/0.98  --qbf_dom_inst                          none
% 1.56/0.98  --qbf_dom_pre_inst                      false
% 1.56/0.98  --qbf_sk_in                             false
% 1.56/0.98  --qbf_pred_elim                         true
% 1.56/0.98  --qbf_split                             512
% 1.56/0.98  
% 1.56/0.98  ------ BMC1 Options
% 1.56/0.98  
% 1.56/0.98  --bmc1_incremental                      false
% 1.56/0.98  --bmc1_axioms                           reachable_all
% 1.56/0.98  --bmc1_min_bound                        0
% 1.56/0.98  --bmc1_max_bound                        -1
% 1.56/0.98  --bmc1_max_bound_default                -1
% 1.56/0.98  --bmc1_symbol_reachability              true
% 1.56/0.98  --bmc1_property_lemmas                  false
% 1.56/0.98  --bmc1_k_induction                      false
% 1.56/0.98  --bmc1_non_equiv_states                 false
% 1.56/0.98  --bmc1_deadlock                         false
% 1.56/0.98  --bmc1_ucm                              false
% 1.56/0.98  --bmc1_add_unsat_core                   none
% 1.56/0.98  --bmc1_unsat_core_children              false
% 1.56/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.56/0.98  --bmc1_out_stat                         full
% 1.56/0.98  --bmc1_ground_init                      false
% 1.56/0.98  --bmc1_pre_inst_next_state              false
% 1.56/0.98  --bmc1_pre_inst_state                   false
% 1.56/0.98  --bmc1_pre_inst_reach_state             false
% 1.56/0.98  --bmc1_out_unsat_core                   false
% 1.56/0.98  --bmc1_aig_witness_out                  false
% 1.56/0.98  --bmc1_verbose                          false
% 1.56/0.98  --bmc1_dump_clauses_tptp                false
% 1.56/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.56/0.98  --bmc1_dump_file                        -
% 1.56/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.56/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.56/0.98  --bmc1_ucm_extend_mode                  1
% 1.56/0.98  --bmc1_ucm_init_mode                    2
% 1.56/0.98  --bmc1_ucm_cone_mode                    none
% 1.56/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.56/0.98  --bmc1_ucm_relax_model                  4
% 1.56/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.56/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.56/0.98  --bmc1_ucm_layered_model                none
% 1.56/0.98  --bmc1_ucm_max_lemma_size               10
% 1.56/0.98  
% 1.56/0.98  ------ AIG Options
% 1.56/0.98  
% 1.56/0.98  --aig_mode                              false
% 1.56/0.98  
% 1.56/0.98  ------ Instantiation Options
% 1.56/0.98  
% 1.56/0.98  --instantiation_flag                    true
% 1.56/0.98  --inst_sos_flag                         false
% 1.56/0.98  --inst_sos_phase                        true
% 1.56/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.56/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.56/0.98  --inst_lit_sel_side                     none
% 1.56/0.98  --inst_solver_per_active                1400
% 1.56/0.98  --inst_solver_calls_frac                1.
% 1.56/0.98  --inst_passive_queue_type               priority_queues
% 1.56/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.56/0.98  --inst_passive_queues_freq              [25;2]
% 1.56/0.98  --inst_dismatching                      true
% 1.56/0.98  --inst_eager_unprocessed_to_passive     true
% 1.56/0.98  --inst_prop_sim_given                   true
% 1.56/0.98  --inst_prop_sim_new                     false
% 1.56/0.98  --inst_subs_new                         false
% 1.56/0.98  --inst_eq_res_simp                      false
% 1.56/0.98  --inst_subs_given                       false
% 1.56/0.98  --inst_orphan_elimination               true
% 1.56/0.98  --inst_learning_loop_flag               true
% 1.56/0.98  --inst_learning_start                   3000
% 1.56/0.98  --inst_learning_factor                  2
% 1.56/0.98  --inst_start_prop_sim_after_learn       3
% 1.56/0.98  --inst_sel_renew                        solver
% 1.56/0.98  --inst_lit_activity_flag                true
% 1.56/0.98  --inst_restr_to_given                   false
% 1.56/0.98  --inst_activity_threshold               500
% 1.56/0.98  --inst_out_proof                        true
% 1.56/0.98  
% 1.56/0.98  ------ Resolution Options
% 1.56/0.98  
% 1.56/0.98  --resolution_flag                       false
% 1.56/0.98  --res_lit_sel                           adaptive
% 1.56/0.98  --res_lit_sel_side                      none
% 1.56/0.98  --res_ordering                          kbo
% 1.56/0.98  --res_to_prop_solver                    active
% 1.56/0.98  --res_prop_simpl_new                    false
% 1.56/0.98  --res_prop_simpl_given                  true
% 1.56/0.98  --res_passive_queue_type                priority_queues
% 1.56/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.56/0.98  --res_passive_queues_freq               [15;5]
% 1.56/0.98  --res_forward_subs                      full
% 1.56/0.98  --res_backward_subs                     full
% 1.56/0.98  --res_forward_subs_resolution           true
% 1.56/0.98  --res_backward_subs_resolution          true
% 1.56/0.98  --res_orphan_elimination                true
% 1.56/0.98  --res_time_limit                        2.
% 1.56/0.98  --res_out_proof                         true
% 1.56/0.98  
% 1.56/0.98  ------ Superposition Options
% 1.56/0.98  
% 1.56/0.98  --superposition_flag                    true
% 1.56/0.98  --sup_passive_queue_type                priority_queues
% 1.56/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.56/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.56/0.98  --demod_completeness_check              fast
% 1.56/0.98  --demod_use_ground                      true
% 1.56/0.98  --sup_to_prop_solver                    passive
% 1.56/0.98  --sup_prop_simpl_new                    true
% 1.56/0.98  --sup_prop_simpl_given                  true
% 1.56/0.98  --sup_fun_splitting                     false
% 1.56/0.98  --sup_smt_interval                      50000
% 1.56/0.98  
% 1.56/0.98  ------ Superposition Simplification Setup
% 1.56/0.98  
% 1.56/0.98  --sup_indices_passive                   []
% 1.56/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.56/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.56/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.56/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.56/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.56/0.98  --sup_full_bw                           [BwDemod]
% 1.56/0.98  --sup_immed_triv                        [TrivRules]
% 1.56/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.56/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.56/0.98  --sup_immed_bw_main                     []
% 1.56/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.56/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.56/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.56/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.56/0.98  
% 1.56/0.98  ------ Combination Options
% 1.56/0.98  
% 1.56/0.98  --comb_res_mult                         3
% 1.56/0.98  --comb_sup_mult                         2
% 1.56/0.98  --comb_inst_mult                        10
% 1.56/0.98  
% 1.56/0.98  ------ Debug Options
% 1.56/0.98  
% 1.56/0.98  --dbg_backtrace                         false
% 1.56/0.98  --dbg_dump_prop_clauses                 false
% 1.56/0.98  --dbg_dump_prop_clauses_file            -
% 1.56/0.98  --dbg_out_stat                          false
% 1.56/0.98  
% 1.56/0.98  
% 1.56/0.98  
% 1.56/0.98  
% 1.56/0.98  ------ Proving...
% 1.56/0.98  
% 1.56/0.98  
% 1.56/0.98  % SZS status Theorem for theBenchmark.p
% 1.56/0.98  
% 1.56/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 1.56/0.98  
% 1.56/0.98  fof(f7,axiom,(
% 1.56/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 1.56/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.56/0.98  
% 1.56/0.98  fof(f21,plain,(
% 1.56/0.98    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.56/0.98    inference(ennf_transformation,[],[f7])).
% 1.56/0.98  
% 1.56/0.98  fof(f22,plain,(
% 1.56/0.98    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.56/0.98    inference(flattening,[],[f21])).
% 1.56/0.98  
% 1.56/0.98  fof(f36,plain,(
% 1.56/0.98    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.56/0.98    inference(nnf_transformation,[],[f22])).
% 1.56/0.98  
% 1.56/0.98  fof(f53,plain,(
% 1.56/0.98    ( ! [X2,X0,X1] : (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.56/0.98    inference(cnf_transformation,[],[f36])).
% 1.56/0.98  
% 1.56/0.98  fof(f9,axiom,(
% 1.56/0.98    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.56/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.56/0.98  
% 1.56/0.98  fof(f25,plain,(
% 1.56/0.98    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.56/0.98    inference(ennf_transformation,[],[f9])).
% 1.56/0.98  
% 1.56/0.98  fof(f26,plain,(
% 1.56/0.98    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.56/0.98    inference(flattening,[],[f25])).
% 1.56/0.98  
% 1.56/0.98  fof(f57,plain,(
% 1.56/0.98    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.56/0.98    inference(cnf_transformation,[],[f26])).
% 1.56/0.98  
% 1.56/0.98  fof(f13,conjecture,(
% 1.56/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) <=> m1_connsp_2(X2,X0,X1)))))),
% 1.56/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.56/0.98  
% 1.56/0.98  fof(f14,negated_conjecture,(
% 1.56/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) <=> m1_connsp_2(X2,X0,X1)))))),
% 1.56/0.98    inference(negated_conjecture,[],[f13])).
% 1.56/0.98  
% 1.56/0.98  fof(f33,plain,(
% 1.56/0.98    ? [X0] : (? [X1] : (? [X2] : ((m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) <~> m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.56/0.98    inference(ennf_transformation,[],[f14])).
% 1.56/0.98  
% 1.56/0.98  fof(f34,plain,(
% 1.56/0.98    ? [X0] : (? [X1] : (? [X2] : ((m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) <~> m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.56/0.98    inference(flattening,[],[f33])).
% 1.56/0.98  
% 1.56/0.98  fof(f40,plain,(
% 1.56/0.98    ? [X0] : (? [X1] : (? [X2] : (((~m1_connsp_2(X2,X0,X1) | ~m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & (m1_connsp_2(X2,X0,X1) | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.56/0.98    inference(nnf_transformation,[],[f34])).
% 1.56/0.98  
% 1.56/0.98  fof(f41,plain,(
% 1.56/0.98    ? [X0] : (? [X1] : (? [X2] : ((~m1_connsp_2(X2,X0,X1) | ~m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & (m1_connsp_2(X2,X0,X1) | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.56/0.98    inference(flattening,[],[f40])).
% 1.56/0.98  
% 1.56/0.98  fof(f44,plain,(
% 1.56/0.98    ( ! [X0,X1] : (? [X2] : ((~m1_connsp_2(X2,X0,X1) | ~m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & (m1_connsp_2(X2,X0,X1) | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => ((~m1_connsp_2(sK3,X0,X1) | ~m2_connsp_2(sK3,X0,k6_domain_1(u1_struct_0(X0),X1))) & (m1_connsp_2(sK3,X0,X1) | m2_connsp_2(sK3,X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 1.56/0.98    introduced(choice_axiom,[])).
% 1.56/0.98  
% 1.56/0.98  fof(f43,plain,(
% 1.56/0.98    ( ! [X0] : (? [X1] : (? [X2] : ((~m1_connsp_2(X2,X0,X1) | ~m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & (m1_connsp_2(X2,X0,X1) | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : ((~m1_connsp_2(X2,X0,sK2) | ~m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),sK2))) & (m1_connsp_2(X2,X0,sK2) | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),sK2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK2,u1_struct_0(X0)))) )),
% 1.56/0.98    introduced(choice_axiom,[])).
% 1.56/0.98  
% 1.56/0.98  fof(f42,plain,(
% 1.56/0.98    ? [X0] : (? [X1] : (? [X2] : ((~m1_connsp_2(X2,X0,X1) | ~m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & (m1_connsp_2(X2,X0,X1) | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~m1_connsp_2(X2,sK1,X1) | ~m2_connsp_2(X2,sK1,k6_domain_1(u1_struct_0(sK1),X1))) & (m1_connsp_2(X2,sK1,X1) | m2_connsp_2(X2,sK1,k6_domain_1(u1_struct_0(sK1),X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X1,u1_struct_0(sK1))) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 1.56/0.98    introduced(choice_axiom,[])).
% 1.56/0.98  
% 1.56/0.98  fof(f45,plain,(
% 1.56/0.98    (((~m1_connsp_2(sK3,sK1,sK2) | ~m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2))) & (m1_connsp_2(sK3,sK1,sK2) | m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK2,u1_struct_0(sK1))) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 1.56/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f41,f44,f43,f42])).
% 1.56/0.98  
% 1.56/0.98  fof(f61,plain,(
% 1.56/0.98    ~v2_struct_0(sK1)),
% 1.56/0.98    inference(cnf_transformation,[],[f45])).
% 1.56/0.98  
% 1.56/0.98  fof(f62,plain,(
% 1.56/0.98    v2_pre_topc(sK1)),
% 1.56/0.98    inference(cnf_transformation,[],[f45])).
% 1.56/0.98  
% 1.56/0.98  fof(f63,plain,(
% 1.56/0.98    l1_pre_topc(sK1)),
% 1.56/0.98    inference(cnf_transformation,[],[f45])).
% 1.56/0.98  
% 1.56/0.98  fof(f2,axiom,(
% 1.56/0.98    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.56/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.56/0.98  
% 1.56/0.98  fof(f35,plain,(
% 1.56/0.98    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 1.56/0.98    inference(nnf_transformation,[],[f2])).
% 1.56/0.98  
% 1.56/0.98  fof(f48,plain,(
% 1.56/0.98    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.56/0.98    inference(cnf_transformation,[],[f35])).
% 1.56/0.98  
% 1.56/0.98  fof(f1,axiom,(
% 1.56/0.98    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.56/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.56/0.98  
% 1.56/0.98  fof(f46,plain,(
% 1.56/0.98    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.56/0.98    inference(cnf_transformation,[],[f1])).
% 1.56/0.98  
% 1.56/0.98  fof(f68,plain,(
% 1.56/0.98    ( ! [X0,X1] : (r1_tarski(k2_tarski(X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.56/0.98    inference(definition_unfolding,[],[f48,f46])).
% 1.56/0.98  
% 1.56/0.98  fof(f67,plain,(
% 1.56/0.98    ~m1_connsp_2(sK3,sK1,sK2) | ~m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2))),
% 1.56/0.98    inference(cnf_transformation,[],[f45])).
% 1.56/0.98  
% 1.56/0.98  fof(f8,axiom,(
% 1.56/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 1.56/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.56/0.98  
% 1.56/0.98  fof(f23,plain,(
% 1.56/0.98    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.56/0.98    inference(ennf_transformation,[],[f8])).
% 1.56/0.98  
% 1.56/0.98  fof(f24,plain,(
% 1.56/0.98    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.56/0.98    inference(flattening,[],[f23])).
% 1.56/0.98  
% 1.56/0.98  fof(f37,plain,(
% 1.56/0.98    ! [X0] : (! [X1] : (! [X2] : (((m2_connsp_2(X2,X0,X1) | ~r1_tarski(X1,k1_tops_1(X0,X2))) & (r1_tarski(X1,k1_tops_1(X0,X2)) | ~m2_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.56/0.98    inference(nnf_transformation,[],[f24])).
% 1.56/0.98  
% 1.56/0.98  fof(f56,plain,(
% 1.56/0.98    ( ! [X2,X0,X1] : (m2_connsp_2(X2,X0,X1) | ~r1_tarski(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.56/0.98    inference(cnf_transformation,[],[f37])).
% 1.56/0.98  
% 1.56/0.98  fof(f65,plain,(
% 1.56/0.98    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 1.56/0.98    inference(cnf_transformation,[],[f45])).
% 1.56/0.98  
% 1.56/0.98  fof(f64,plain,(
% 1.56/0.98    m1_subset_1(sK2,u1_struct_0(sK1))),
% 1.56/0.98    inference(cnf_transformation,[],[f45])).
% 1.56/0.98  
% 1.56/0.98  fof(f11,axiom,(
% 1.56/0.98    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X2] : m1_connsp_2(X2,X0,X1))),
% 1.56/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.56/0.98  
% 1.56/0.98  fof(f29,plain,(
% 1.56/0.98    ! [X0,X1] : (? [X2] : m1_connsp_2(X2,X0,X1) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.56/0.98    inference(ennf_transformation,[],[f11])).
% 1.56/0.98  
% 1.56/0.98  fof(f30,plain,(
% 1.56/0.98    ! [X0,X1] : (? [X2] : m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.56/0.98    inference(flattening,[],[f29])).
% 1.56/0.98  
% 1.56/0.98  fof(f38,plain,(
% 1.56/0.98    ! [X1,X0] : (? [X2] : m1_connsp_2(X2,X0,X1) => m1_connsp_2(sK0(X0,X1),X0,X1))),
% 1.56/0.98    introduced(choice_axiom,[])).
% 1.56/0.98  
% 1.56/0.98  fof(f39,plain,(
% 1.56/0.98    ! [X0,X1] : (m1_connsp_2(sK0(X0,X1),X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.56/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f38])).
% 1.56/0.98  
% 1.56/0.98  fof(f59,plain,(
% 1.56/0.98    ( ! [X0,X1] : (m1_connsp_2(sK0(X0,X1),X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.56/0.98    inference(cnf_transformation,[],[f39])).
% 1.56/0.98  
% 1.56/0.98  fof(f12,axiom,(
% 1.56/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (m1_connsp_2(X1,X0,X2) => r2_hidden(X2,X1)))))),
% 1.56/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.56/0.98  
% 1.56/0.98  fof(f31,plain,(
% 1.56/0.98    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.56/0.98    inference(ennf_transformation,[],[f12])).
% 1.56/0.98  
% 1.56/0.98  fof(f32,plain,(
% 1.56/0.98    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.56/0.98    inference(flattening,[],[f31])).
% 1.56/0.98  
% 1.56/0.98  fof(f60,plain,(
% 1.56/0.98    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.56/0.98    inference(cnf_transformation,[],[f32])).
% 1.56/0.98  
% 1.56/0.98  fof(f3,axiom,(
% 1.56/0.98    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 1.56/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.56/0.98  
% 1.56/0.98  fof(f15,plain,(
% 1.56/0.98    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 1.56/0.98    inference(ennf_transformation,[],[f3])).
% 1.56/0.98  
% 1.56/0.98  fof(f49,plain,(
% 1.56/0.98    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 1.56/0.98    inference(cnf_transformation,[],[f15])).
% 1.56/0.98  
% 1.56/0.98  fof(f70,plain,(
% 1.56/0.98    ( ! [X0,X1] : (m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 1.56/0.98    inference(definition_unfolding,[],[f49,f46])).
% 1.56/0.98  
% 1.56/0.98  fof(f4,axiom,(
% 1.56/0.98    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.56/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.56/0.98  
% 1.56/0.98  fof(f16,plain,(
% 1.56/0.98    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.56/0.98    inference(ennf_transformation,[],[f4])).
% 1.56/0.98  
% 1.56/0.98  fof(f17,plain,(
% 1.56/0.98    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.56/0.98    inference(flattening,[],[f16])).
% 1.56/0.98  
% 1.56/0.98  fof(f50,plain,(
% 1.56/0.98    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 1.56/0.98    inference(cnf_transformation,[],[f17])).
% 1.56/0.98  
% 1.56/0.98  fof(f5,axiom,(
% 1.56/0.98    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.56/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.56/0.98  
% 1.56/0.98  fof(f18,plain,(
% 1.56/0.98    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.56/0.98    inference(ennf_transformation,[],[f5])).
% 1.56/0.98  
% 1.56/0.98  fof(f51,plain,(
% 1.56/0.98    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.56/0.98    inference(cnf_transformation,[],[f18])).
% 1.56/0.98  
% 1.56/0.98  fof(f47,plain,(
% 1.56/0.98    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 1.56/0.98    inference(cnf_transformation,[],[f35])).
% 1.56/0.98  
% 1.56/0.98  fof(f69,plain,(
% 1.56/0.98    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k2_tarski(X0,X0),X1)) )),
% 1.56/0.98    inference(definition_unfolding,[],[f47,f46])).
% 1.56/0.98  
% 1.56/0.98  fof(f66,plain,(
% 1.56/0.98    m1_connsp_2(sK3,sK1,sK2) | m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2))),
% 1.56/0.98    inference(cnf_transformation,[],[f45])).
% 1.56/0.98  
% 1.56/0.98  fof(f55,plain,(
% 1.56/0.98    ( ! [X2,X0,X1] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~m2_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.56/0.98    inference(cnf_transformation,[],[f37])).
% 1.56/0.98  
% 1.56/0.98  fof(f10,axiom,(
% 1.56/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X2] : (m2_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.56/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.56/0.98  
% 1.56/0.98  fof(f27,plain,(
% 1.56/0.98    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.56/0.98    inference(ennf_transformation,[],[f10])).
% 1.56/0.98  
% 1.56/0.98  fof(f28,plain,(
% 1.56/0.98    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.56/0.98    inference(flattening,[],[f27])).
% 1.56/0.98  
% 1.56/0.98  fof(f58,plain,(
% 1.56/0.98    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.56/0.98    inference(cnf_transformation,[],[f28])).
% 1.56/0.98  
% 1.56/0.98  fof(f6,axiom,(
% 1.56/0.98    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 1.56/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.56/0.98  
% 1.56/0.98  fof(f19,plain,(
% 1.56/0.98    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.56/0.98    inference(ennf_transformation,[],[f6])).
% 1.56/0.98  
% 1.56/0.98  fof(f20,plain,(
% 1.56/0.98    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.56/0.98    inference(flattening,[],[f19])).
% 1.56/0.98  
% 1.56/0.98  fof(f52,plain,(
% 1.56/0.98    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.56/0.98    inference(cnf_transformation,[],[f20])).
% 1.56/0.98  
% 1.56/0.98  fof(f71,plain,(
% 1.56/0.98    ( ! [X0,X1] : (k2_tarski(X1,X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.56/0.98    inference(definition_unfolding,[],[f52,f46])).
% 1.56/0.98  
% 1.56/0.98  fof(f54,plain,(
% 1.56/0.98    ( ! [X2,X0,X1] : (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.56/0.98    inference(cnf_transformation,[],[f36])).
% 1.56/0.98  
% 1.56/0.98  cnf(c_1901,plain,
% 1.56/0.98      ( ~ m1_subset_1(X0_46,X1_46)
% 1.56/0.98      | m1_subset_1(X2_46,X3_46)
% 1.56/0.98      | X2_46 != X0_46
% 1.56/0.98      | X3_46 != X1_46 ),
% 1.56/0.98      theory(equality) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_2590,plain,
% 1.56/0.98      ( m1_subset_1(X0_46,X1_46)
% 1.56/0.98      | ~ m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.56/0.98      | X0_46 != k2_tarski(sK2,sK2)
% 1.56/0.98      | X1_46 != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 1.56/0.98      inference(instantiation,[status(thm)],[c_1901]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_3029,plain,
% 1.56/0.98      ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),X0_46)
% 1.56/0.98      | ~ m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.56/0.98      | X0_46 != k1_zfmisc_1(u1_struct_0(sK1))
% 1.56/0.98      | k6_domain_1(u1_struct_0(sK1),sK2) != k2_tarski(sK2,sK2) ),
% 1.56/0.98      inference(instantiation,[status(thm)],[c_2590]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_3273,plain,
% 1.56/0.98      ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.56/0.98      | ~ m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.56/0.98      | k6_domain_1(u1_struct_0(sK1),sK2) != k2_tarski(sK2,sK2)
% 1.56/0.98      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 1.56/0.98      inference(instantiation,[status(thm)],[c_3029]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_7,plain,
% 1.56/0.98      ( ~ m1_connsp_2(X0,X1,X2)
% 1.56/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.56/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.56/0.98      | r2_hidden(X2,k1_tops_1(X1,X0))
% 1.56/0.98      | v2_struct_0(X1)
% 1.56/0.98      | ~ v2_pre_topc(X1)
% 1.56/0.98      | ~ l1_pre_topc(X1) ),
% 1.56/0.98      inference(cnf_transformation,[],[f53]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_10,plain,
% 1.56/0.98      ( ~ m1_connsp_2(X0,X1,X2)
% 1.56/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.56/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.56/0.98      | v2_struct_0(X1)
% 1.56/0.98      | ~ v2_pre_topc(X1)
% 1.56/0.98      | ~ l1_pre_topc(X1) ),
% 1.56/0.98      inference(cnf_transformation,[],[f57]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_134,plain,
% 1.56/0.98      ( ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.56/0.98      | ~ m1_connsp_2(X0,X1,X2)
% 1.56/0.98      | r2_hidden(X2,k1_tops_1(X1,X0))
% 1.56/0.98      | v2_struct_0(X1)
% 1.56/0.98      | ~ v2_pre_topc(X1)
% 1.56/0.98      | ~ l1_pre_topc(X1) ),
% 1.56/0.98      inference(global_propositional_subsumption,
% 1.56/0.98                [status(thm)],
% 1.56/0.98                [c_7,c_10]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_135,plain,
% 1.56/0.98      ( ~ m1_connsp_2(X0,X1,X2)
% 1.56/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.56/0.98      | r2_hidden(X2,k1_tops_1(X1,X0))
% 1.56/0.98      | v2_struct_0(X1)
% 1.56/0.98      | ~ v2_pre_topc(X1)
% 1.56/0.98      | ~ l1_pre_topc(X1) ),
% 1.56/0.98      inference(renaming,[status(thm)],[c_134]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_20,negated_conjecture,
% 1.56/0.98      ( ~ v2_struct_0(sK1) ),
% 1.56/0.98      inference(cnf_transformation,[],[f61]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_419,plain,
% 1.56/0.98      ( ~ m1_connsp_2(X0,X1,X2)
% 1.56/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.56/0.98      | r2_hidden(X2,k1_tops_1(X1,X0))
% 1.56/0.98      | ~ v2_pre_topc(X1)
% 1.56/0.98      | ~ l1_pre_topc(X1)
% 1.56/0.98      | sK1 != X1 ),
% 1.56/0.98      inference(resolution_lifted,[status(thm)],[c_135,c_20]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_420,plain,
% 1.56/0.98      ( ~ m1_connsp_2(X0,sK1,X1)
% 1.56/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.56/0.98      | r2_hidden(X1,k1_tops_1(sK1,X0))
% 1.56/0.98      | ~ v2_pre_topc(sK1)
% 1.56/0.98      | ~ l1_pre_topc(sK1) ),
% 1.56/0.98      inference(unflattening,[status(thm)],[c_419]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_19,negated_conjecture,
% 1.56/0.98      ( v2_pre_topc(sK1) ),
% 1.56/0.98      inference(cnf_transformation,[],[f62]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_18,negated_conjecture,
% 1.56/0.98      ( l1_pre_topc(sK1) ),
% 1.56/0.98      inference(cnf_transformation,[],[f63]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_424,plain,
% 1.56/0.98      ( ~ m1_connsp_2(X0,sK1,X1)
% 1.56/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.56/0.98      | r2_hidden(X1,k1_tops_1(sK1,X0)) ),
% 1.56/0.98      inference(global_propositional_subsumption,
% 1.56/0.98                [status(thm)],
% 1.56/0.98                [c_420,c_19,c_18]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_1884,plain,
% 1.56/0.98      ( ~ m1_connsp_2(X0_46,sK1,X1_46)
% 1.56/0.98      | ~ m1_subset_1(X1_46,u1_struct_0(sK1))
% 1.56/0.98      | r2_hidden(X1_46,k1_tops_1(sK1,X0_46)) ),
% 1.56/0.98      inference(subtyping,[status(esa)],[c_424]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_2195,plain,
% 1.56/0.98      ( m1_connsp_2(X0_46,sK1,X1_46) != iProver_top
% 1.56/0.98      | m1_subset_1(X1_46,u1_struct_0(sK1)) != iProver_top
% 1.56/0.98      | r2_hidden(X1_46,k1_tops_1(sK1,X0_46)) = iProver_top ),
% 1.56/0.98      inference(predicate_to_equality,[status(thm)],[c_1884]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_0,plain,
% 1.56/0.98      ( ~ r2_hidden(X0,X1) | r1_tarski(k2_tarski(X0,X0),X1) ),
% 1.56/0.98      inference(cnf_transformation,[],[f68]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_175,plain,
% 1.56/0.98      ( ~ r2_hidden(X0,X1) | r1_tarski(k2_tarski(X0,X0),X1) ),
% 1.56/0.98      inference(prop_impl,[status(thm)],[c_0]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_14,negated_conjecture,
% 1.56/0.98      ( ~ m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2))
% 1.56/0.98      | ~ m1_connsp_2(sK3,sK1,sK2) ),
% 1.56/0.98      inference(cnf_transformation,[],[f67]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_177,plain,
% 1.56/0.98      ( ~ m1_connsp_2(sK3,sK1,sK2)
% 1.56/0.98      | ~ m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2)) ),
% 1.56/0.98      inference(prop_impl,[status(thm)],[c_14]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_178,plain,
% 1.56/0.98      ( ~ m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2))
% 1.56/0.98      | ~ m1_connsp_2(sK3,sK1,sK2) ),
% 1.56/0.98      inference(renaming,[status(thm)],[c_177]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_8,plain,
% 1.56/0.98      ( m2_connsp_2(X0,X1,X2)
% 1.56/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.56/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.56/0.98      | ~ r1_tarski(X2,k1_tops_1(X1,X0))
% 1.56/0.98      | ~ v2_pre_topc(X1)
% 1.56/0.98      | ~ l1_pre_topc(X1) ),
% 1.56/0.98      inference(cnf_transformation,[],[f56]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_564,plain,
% 1.56/0.98      ( m2_connsp_2(X0,X1,X2)
% 1.56/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.56/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.56/0.98      | ~ r1_tarski(X2,k1_tops_1(X1,X0))
% 1.56/0.98      | ~ v2_pre_topc(X1)
% 1.56/0.98      | sK1 != X1 ),
% 1.56/0.98      inference(resolution_lifted,[status(thm)],[c_8,c_18]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_565,plain,
% 1.56/0.98      ( m2_connsp_2(X0,sK1,X1)
% 1.56/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.56/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.56/0.98      | ~ r1_tarski(X1,k1_tops_1(sK1,X0))
% 1.56/0.98      | ~ v2_pre_topc(sK1) ),
% 1.56/0.98      inference(unflattening,[status(thm)],[c_564]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_569,plain,
% 1.56/0.98      ( ~ r1_tarski(X1,k1_tops_1(sK1,X0))
% 1.56/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.56/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.56/0.98      | m2_connsp_2(X0,sK1,X1) ),
% 1.56/0.98      inference(global_propositional_subsumption,
% 1.56/0.98                [status(thm)],
% 1.56/0.98                [c_565,c_19]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_570,plain,
% 1.56/0.98      ( m2_connsp_2(X0,sK1,X1)
% 1.56/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.56/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.56/0.98      | ~ r1_tarski(X1,k1_tops_1(sK1,X0)) ),
% 1.56/0.98      inference(renaming,[status(thm)],[c_569]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_661,plain,
% 1.56/0.98      ( ~ m1_connsp_2(sK3,sK1,sK2)
% 1.56/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.56/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.56/0.98      | ~ r1_tarski(X1,k1_tops_1(sK1,X0))
% 1.56/0.98      | k6_domain_1(u1_struct_0(sK1),sK2) != X1
% 1.56/0.98      | sK1 != sK1
% 1.56/0.98      | sK3 != X0 ),
% 1.56/0.98      inference(resolution_lifted,[status(thm)],[c_178,c_570]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_662,plain,
% 1.56/0.98      ( ~ m1_connsp_2(sK3,sK1,sK2)
% 1.56/0.98      | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.56/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.56/0.98      | ~ r1_tarski(k6_domain_1(u1_struct_0(sK1),sK2),k1_tops_1(sK1,sK3)) ),
% 1.56/0.98      inference(unflattening,[status(thm)],[c_661]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_16,negated_conjecture,
% 1.56/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.56/0.98      inference(cnf_transformation,[],[f65]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_664,plain,
% 1.56/0.98      ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.56/0.98      | ~ m1_connsp_2(sK3,sK1,sK2)
% 1.56/0.98      | ~ r1_tarski(k6_domain_1(u1_struct_0(sK1),sK2),k1_tops_1(sK1,sK3)) ),
% 1.56/0.98      inference(global_propositional_subsumption,
% 1.56/0.98                [status(thm)],
% 1.56/0.98                [c_662,c_16]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_665,plain,
% 1.56/0.98      ( ~ m1_connsp_2(sK3,sK1,sK2)
% 1.56/0.98      | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.56/0.98      | ~ r1_tarski(k6_domain_1(u1_struct_0(sK1),sK2),k1_tops_1(sK1,sK3)) ),
% 1.56/0.98      inference(renaming,[status(thm)],[c_664]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_688,plain,
% 1.56/0.98      ( ~ m1_connsp_2(sK3,sK1,sK2)
% 1.56/0.98      | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.56/0.98      | ~ r2_hidden(X0,X1)
% 1.56/0.98      | k1_tops_1(sK1,sK3) != X1
% 1.56/0.98      | k6_domain_1(u1_struct_0(sK1),sK2) != k2_tarski(X0,X0) ),
% 1.56/0.98      inference(resolution_lifted,[status(thm)],[c_175,c_665]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_689,plain,
% 1.56/0.98      ( ~ m1_connsp_2(sK3,sK1,sK2)
% 1.56/0.98      | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.56/0.98      | ~ r2_hidden(X0,k1_tops_1(sK1,sK3))
% 1.56/0.98      | k6_domain_1(u1_struct_0(sK1),sK2) != k2_tarski(X0,X0) ),
% 1.56/0.98      inference(unflattening,[status(thm)],[c_688]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_1880,plain,
% 1.56/0.98      ( ~ m1_connsp_2(sK3,sK1,sK2)
% 1.56/0.98      | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.56/0.98      | ~ r2_hidden(X0_46,k1_tops_1(sK1,sK3))
% 1.56/0.98      | k6_domain_1(u1_struct_0(sK1),sK2) != k2_tarski(X0_46,X0_46) ),
% 1.56/0.98      inference(subtyping,[status(esa)],[c_689]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_1892,plain,
% 1.56/0.98      ( ~ r2_hidden(X0_46,k1_tops_1(sK1,sK3))
% 1.56/0.98      | k6_domain_1(u1_struct_0(sK1),sK2) != k2_tarski(X0_46,X0_46)
% 1.56/0.98      | ~ sP0_iProver_split ),
% 1.56/0.98      inference(splitting,
% 1.56/0.98                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 1.56/0.98                [c_1880]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_2200,plain,
% 1.56/0.98      ( k6_domain_1(u1_struct_0(sK1),sK2) != k2_tarski(X0_46,X0_46)
% 1.56/0.98      | r2_hidden(X0_46,k1_tops_1(sK1,sK3)) != iProver_top
% 1.56/0.98      | sP0_iProver_split != iProver_top ),
% 1.56/0.98      inference(predicate_to_equality,[status(thm)],[c_1892]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_17,negated_conjecture,
% 1.56/0.98      ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 1.56/0.98      inference(cnf_transformation,[],[f64]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_24,plain,
% 1.56/0.98      ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
% 1.56/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_12,plain,
% 1.56/0.98      ( m1_connsp_2(sK0(X0,X1),X0,X1)
% 1.56/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.56/0.98      | v2_struct_0(X0)
% 1.56/0.98      | ~ v2_pre_topc(X0)
% 1.56/0.98      | ~ l1_pre_topc(X0) ),
% 1.56/0.98      inference(cnf_transformation,[],[f59]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_401,plain,
% 1.56/0.98      ( m1_connsp_2(sK0(X0,X1),X0,X1)
% 1.56/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.56/0.98      | ~ v2_pre_topc(X0)
% 1.56/0.98      | ~ l1_pre_topc(X0)
% 1.56/0.98      | sK1 != X0 ),
% 1.56/0.98      inference(resolution_lifted,[status(thm)],[c_12,c_20]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_402,plain,
% 1.56/0.98      ( m1_connsp_2(sK0(sK1,X0),sK1,X0)
% 1.56/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.56/0.98      | ~ v2_pre_topc(sK1)
% 1.56/0.98      | ~ l1_pre_topc(sK1) ),
% 1.56/0.98      inference(unflattening,[status(thm)],[c_401]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_406,plain,
% 1.56/0.98      ( m1_connsp_2(sK0(sK1,X0),sK1,X0)
% 1.56/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
% 1.56/0.98      inference(global_propositional_subsumption,
% 1.56/0.98                [status(thm)],
% 1.56/0.98                [c_402,c_19,c_18]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_1885,plain,
% 1.56/0.98      ( m1_connsp_2(sK0(sK1,X0_46),sK1,X0_46)
% 1.56/0.98      | ~ m1_subset_1(X0_46,u1_struct_0(sK1)) ),
% 1.56/0.98      inference(subtyping,[status(esa)],[c_406]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_1927,plain,
% 1.56/0.98      ( m1_connsp_2(sK0(sK1,X0_46),sK1,X0_46) = iProver_top
% 1.56/0.98      | m1_subset_1(X0_46,u1_struct_0(sK1)) != iProver_top ),
% 1.56/0.98      inference(predicate_to_equality,[status(thm)],[c_1885]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_1929,plain,
% 1.56/0.98      ( m1_connsp_2(sK0(sK1,sK2),sK1,sK2) = iProver_top
% 1.56/0.98      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
% 1.56/0.98      inference(instantiation,[status(thm)],[c_1927]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_1943,plain,
% 1.56/0.98      ( k6_domain_1(u1_struct_0(sK1),sK2) != k2_tarski(X0_46,X0_46)
% 1.56/0.98      | r2_hidden(X0_46,k1_tops_1(sK1,sK3)) != iProver_top
% 1.56/0.98      | sP0_iProver_split != iProver_top ),
% 1.56/0.98      inference(predicate_to_equality,[status(thm)],[c_1892]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_461,plain,
% 1.56/0.98      ( ~ m1_connsp_2(X0,X1,X2)
% 1.56/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.56/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.56/0.98      | ~ v2_pre_topc(X1)
% 1.56/0.98      | ~ l1_pre_topc(X1)
% 1.56/0.98      | sK1 != X1 ),
% 1.56/0.98      inference(resolution_lifted,[status(thm)],[c_10,c_20]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_462,plain,
% 1.56/0.98      ( ~ m1_connsp_2(X0,sK1,X1)
% 1.56/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.56/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.56/0.98      | ~ v2_pre_topc(sK1)
% 1.56/0.98      | ~ l1_pre_topc(sK1) ),
% 1.56/0.98      inference(unflattening,[status(thm)],[c_461]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_466,plain,
% 1.56/0.98      ( ~ m1_connsp_2(X0,sK1,X1)
% 1.56/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.56/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.56/0.98      inference(global_propositional_subsumption,
% 1.56/0.98                [status(thm)],
% 1.56/0.98                [c_462,c_19,c_18]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_1882,plain,
% 1.56/0.98      ( ~ m1_connsp_2(X0_46,sK1,X1_46)
% 1.56/0.98      | ~ m1_subset_1(X1_46,u1_struct_0(sK1))
% 1.56/0.98      | m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.56/0.98      inference(subtyping,[status(esa)],[c_466]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_2316,plain,
% 1.56/0.98      ( ~ m1_connsp_2(sK0(sK1,X0_46),sK1,X0_46)
% 1.56/0.98      | ~ m1_subset_1(X0_46,u1_struct_0(sK1))
% 1.56/0.98      | m1_subset_1(sK0(sK1,X0_46),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.56/0.98      inference(instantiation,[status(thm)],[c_1882]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_2317,plain,
% 1.56/0.98      ( m1_connsp_2(sK0(sK1,X0_46),sK1,X0_46) != iProver_top
% 1.56/0.98      | m1_subset_1(X0_46,u1_struct_0(sK1)) != iProver_top
% 1.56/0.98      | m1_subset_1(sK0(sK1,X0_46),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 1.56/0.98      inference(predicate_to_equality,[status(thm)],[c_2316]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_2319,plain,
% 1.56/0.98      ( m1_connsp_2(sK0(sK1,sK2),sK1,sK2) != iProver_top
% 1.56/0.98      | m1_subset_1(sK0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 1.56/0.98      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
% 1.56/0.98      inference(instantiation,[status(thm)],[c_2317]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_13,plain,
% 1.56/0.98      ( ~ m1_connsp_2(X0,X1,X2)
% 1.56/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.56/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.56/0.98      | r2_hidden(X2,X0)
% 1.56/0.98      | v2_struct_0(X1)
% 1.56/0.98      | ~ v2_pre_topc(X1)
% 1.56/0.98      | ~ l1_pre_topc(X1) ),
% 1.56/0.98      inference(cnf_transformation,[],[f60]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_118,plain,
% 1.56/0.98      ( ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.56/0.98      | ~ m1_connsp_2(X0,X1,X2)
% 1.56/0.98      | r2_hidden(X2,X0)
% 1.56/0.98      | v2_struct_0(X1)
% 1.56/0.98      | ~ v2_pre_topc(X1)
% 1.56/0.98      | ~ l1_pre_topc(X1) ),
% 1.56/0.98      inference(global_propositional_subsumption,
% 1.56/0.98                [status(thm)],
% 1.56/0.98                [c_13,c_10]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_119,plain,
% 1.56/0.98      ( ~ m1_connsp_2(X0,X1,X2)
% 1.56/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.56/0.98      | r2_hidden(X2,X0)
% 1.56/0.98      | v2_struct_0(X1)
% 1.56/0.98      | ~ v2_pre_topc(X1)
% 1.56/0.98      | ~ l1_pre_topc(X1) ),
% 1.56/0.98      inference(renaming,[status(thm)],[c_118]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_440,plain,
% 1.56/0.98      ( ~ m1_connsp_2(X0,X1,X2)
% 1.56/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.56/0.98      | r2_hidden(X2,X0)
% 1.56/0.98      | ~ v2_pre_topc(X1)
% 1.56/0.98      | ~ l1_pre_topc(X1)
% 1.56/0.98      | sK1 != X1 ),
% 1.56/0.98      inference(resolution_lifted,[status(thm)],[c_119,c_20]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_441,plain,
% 1.56/0.98      ( ~ m1_connsp_2(X0,sK1,X1)
% 1.56/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.56/0.98      | r2_hidden(X1,X0)
% 1.56/0.98      | ~ v2_pre_topc(sK1)
% 1.56/0.98      | ~ l1_pre_topc(sK1) ),
% 1.56/0.98      inference(unflattening,[status(thm)],[c_440]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_445,plain,
% 1.56/0.98      ( ~ m1_connsp_2(X0,sK1,X1)
% 1.56/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.56/0.98      | r2_hidden(X1,X0) ),
% 1.56/0.98      inference(global_propositional_subsumption,
% 1.56/0.98                [status(thm)],
% 1.56/0.98                [c_441,c_19,c_18]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_1883,plain,
% 1.56/0.98      ( ~ m1_connsp_2(X0_46,sK1,X1_46)
% 1.56/0.98      | ~ m1_subset_1(X1_46,u1_struct_0(sK1))
% 1.56/0.98      | r2_hidden(X1_46,X0_46) ),
% 1.56/0.98      inference(subtyping,[status(esa)],[c_445]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_2321,plain,
% 1.56/0.98      ( ~ m1_connsp_2(sK0(sK1,X0_46),sK1,X0_46)
% 1.56/0.98      | ~ m1_subset_1(X0_46,u1_struct_0(sK1))
% 1.56/0.98      | r2_hidden(X0_46,sK0(sK1,X0_46)) ),
% 1.56/0.98      inference(instantiation,[status(thm)],[c_1883]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_2322,plain,
% 1.56/0.98      ( m1_connsp_2(sK0(sK1,X0_46),sK1,X0_46) != iProver_top
% 1.56/0.98      | m1_subset_1(X0_46,u1_struct_0(sK1)) != iProver_top
% 1.56/0.98      | r2_hidden(X0_46,sK0(sK1,X0_46)) = iProver_top ),
% 1.56/0.98      inference(predicate_to_equality,[status(thm)],[c_2321]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_2324,plain,
% 1.56/0.98      ( m1_connsp_2(sK0(sK1,sK2),sK1,sK2) != iProver_top
% 1.56/0.98      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 1.56/0.98      | r2_hidden(sK2,sK0(sK1,sK2)) = iProver_top ),
% 1.56/0.98      inference(instantiation,[status(thm)],[c_2322]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_2,plain,
% 1.56/0.98      ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1))
% 1.56/0.98      | ~ r2_hidden(X0,X1) ),
% 1.56/0.98      inference(cnf_transformation,[],[f70]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_1891,plain,
% 1.56/0.98      ( m1_subset_1(k2_tarski(X0_46,X0_46),k1_zfmisc_1(X1_46))
% 1.56/0.98      | ~ r2_hidden(X0_46,X1_46) ),
% 1.56/0.98      inference(subtyping,[status(esa)],[c_2]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_2476,plain,
% 1.56/0.98      ( m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.56/0.98      | ~ r2_hidden(sK2,u1_struct_0(sK1)) ),
% 1.56/0.98      inference(instantiation,[status(thm)],[c_1891]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_2477,plain,
% 1.56/0.98      ( m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 1.56/0.98      | r2_hidden(sK2,u1_struct_0(sK1)) != iProver_top ),
% 1.56/0.98      inference(predicate_to_equality,[status(thm)],[c_2476]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_1886,negated_conjecture,
% 1.56/0.98      ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 1.56/0.98      inference(subtyping,[status(esa)],[c_17]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_2193,plain,
% 1.56/0.98      ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
% 1.56/0.98      inference(predicate_to_equality,[status(thm)],[c_1886]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_3,plain,
% 1.56/0.98      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 1.56/0.98      inference(cnf_transformation,[],[f50]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_1890,plain,
% 1.56/0.98      ( ~ m1_subset_1(X0_46,X1_46)
% 1.56/0.98      | r2_hidden(X0_46,X1_46)
% 1.56/0.98      | v1_xboole_0(X1_46) ),
% 1.56/0.98      inference(subtyping,[status(esa)],[c_3]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_2189,plain,
% 1.56/0.98      ( m1_subset_1(X0_46,X1_46) != iProver_top
% 1.56/0.98      | r2_hidden(X0_46,X1_46) = iProver_top
% 1.56/0.98      | v1_xboole_0(X1_46) = iProver_top ),
% 1.56/0.98      inference(predicate_to_equality,[status(thm)],[c_1890]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_2562,plain,
% 1.56/0.98      ( r2_hidden(sK2,u1_struct_0(sK1)) = iProver_top
% 1.56/0.98      | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
% 1.56/0.98      inference(superposition,[status(thm)],[c_2193,c_2189]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_4,plain,
% 1.56/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.56/0.98      | ~ r2_hidden(X2,X0)
% 1.56/0.98      | ~ v1_xboole_0(X1) ),
% 1.56/0.98      inference(cnf_transformation,[],[f51]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_1889,plain,
% 1.56/0.98      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(X1_46))
% 1.56/0.98      | ~ r2_hidden(X2_46,X0_46)
% 1.56/0.98      | ~ v1_xboole_0(X1_46) ),
% 1.56/0.98      inference(subtyping,[status(esa)],[c_4]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_2383,plain,
% 1.56/0.98      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.56/0.98      | ~ r2_hidden(X1_46,X0_46)
% 1.56/0.98      | ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 1.56/0.98      inference(instantiation,[status(thm)],[c_1889]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_2787,plain,
% 1.56/0.98      ( ~ m1_subset_1(sK0(sK1,X0_46),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.56/0.98      | ~ r2_hidden(X1_46,sK0(sK1,X0_46))
% 1.56/0.98      | ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 1.56/0.98      inference(instantiation,[status(thm)],[c_2383]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_2788,plain,
% 1.56/0.98      ( m1_subset_1(sK0(sK1,X0_46),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.56/0.98      | r2_hidden(X1_46,sK0(sK1,X0_46)) != iProver_top
% 1.56/0.98      | v1_xboole_0(u1_struct_0(sK1)) != iProver_top ),
% 1.56/0.98      inference(predicate_to_equality,[status(thm)],[c_2787]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_2790,plain,
% 1.56/0.98      ( m1_subset_1(sK0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.56/0.98      | r2_hidden(sK2,sK0(sK1,sK2)) != iProver_top
% 1.56/0.98      | v1_xboole_0(u1_struct_0(sK1)) != iProver_top ),
% 1.56/0.98      inference(instantiation,[status(thm)],[c_2788]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_1893,plain,
% 1.56/0.98      ( ~ m1_connsp_2(sK3,sK1,sK2)
% 1.56/0.98      | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.56/0.98      | sP0_iProver_split ),
% 1.56/0.98      inference(splitting,
% 1.56/0.98                [splitting(split),new_symbols(definition,[])],
% 1.56/0.98                [c_1880]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_2199,plain,
% 1.56/0.98      ( m1_connsp_2(sK3,sK1,sK2) != iProver_top
% 1.56/0.98      | m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.56/0.98      | sP0_iProver_split = iProver_top ),
% 1.56/0.98      inference(predicate_to_equality,[status(thm)],[c_1893]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_25,plain,
% 1.56/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 1.56/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_1942,plain,
% 1.56/0.98      ( m1_connsp_2(sK3,sK1,sK2) != iProver_top
% 1.56/0.98      | m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.56/0.98      | sP0_iProver_split = iProver_top ),
% 1.56/0.98      inference(predicate_to_equality,[status(thm)],[c_1893]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_1,plain,
% 1.56/0.98      ( r2_hidden(X0,X1) | ~ r1_tarski(k2_tarski(X0,X0),X1) ),
% 1.56/0.98      inference(cnf_transformation,[],[f69]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_173,plain,
% 1.56/0.98      ( r2_hidden(X0,X1) | ~ r1_tarski(k2_tarski(X0,X0),X1) ),
% 1.56/0.98      inference(prop_impl,[status(thm)],[c_1]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_15,negated_conjecture,
% 1.56/0.98      ( m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2))
% 1.56/0.98      | m1_connsp_2(sK3,sK1,sK2) ),
% 1.56/0.98      inference(cnf_transformation,[],[f66]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_179,plain,
% 1.56/0.98      ( m1_connsp_2(sK3,sK1,sK2)
% 1.56/0.98      | m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2)) ),
% 1.56/0.98      inference(prop_impl,[status(thm)],[c_15]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_180,plain,
% 1.56/0.98      ( m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2))
% 1.56/0.98      | m1_connsp_2(sK3,sK1,sK2) ),
% 1.56/0.98      inference(renaming,[status(thm)],[c_179]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_9,plain,
% 1.56/0.98      ( ~ m2_connsp_2(X0,X1,X2)
% 1.56/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.56/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.56/0.98      | r1_tarski(X2,k1_tops_1(X1,X0))
% 1.56/0.98      | ~ v2_pre_topc(X1)
% 1.56/0.98      | ~ l1_pre_topc(X1) ),
% 1.56/0.98      inference(cnf_transformation,[],[f55]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_11,plain,
% 1.56/0.98      ( ~ m2_connsp_2(X0,X1,X2)
% 1.56/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.56/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.56/0.98      | ~ v2_pre_topc(X1)
% 1.56/0.98      | ~ l1_pre_topc(X1) ),
% 1.56/0.98      inference(cnf_transformation,[],[f58]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_128,plain,
% 1.56/0.98      ( ~ m2_connsp_2(X0,X1,X2)
% 1.56/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.56/0.98      | r1_tarski(X2,k1_tops_1(X1,X0))
% 1.56/0.98      | ~ v2_pre_topc(X1)
% 1.56/0.98      | ~ l1_pre_topc(X1) ),
% 1.56/0.98      inference(global_propositional_subsumption,
% 1.56/0.98                [status(thm)],
% 1.56/0.98                [c_9,c_11]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_526,plain,
% 1.56/0.98      ( ~ m2_connsp_2(X0,X1,X2)
% 1.56/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.56/0.98      | r1_tarski(X2,k1_tops_1(X1,X0))
% 1.56/0.98      | ~ v2_pre_topc(X1)
% 1.56/0.98      | sK1 != X1 ),
% 1.56/0.98      inference(resolution_lifted,[status(thm)],[c_128,c_18]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_527,plain,
% 1.56/0.98      ( ~ m2_connsp_2(X0,sK1,X1)
% 1.56/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.56/0.98      | r1_tarski(X1,k1_tops_1(sK1,X0))
% 1.56/0.98      | ~ v2_pre_topc(sK1) ),
% 1.56/0.98      inference(unflattening,[status(thm)],[c_526]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_531,plain,
% 1.56/0.98      ( r1_tarski(X1,k1_tops_1(sK1,X0))
% 1.56/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.56/0.98      | ~ m2_connsp_2(X0,sK1,X1) ),
% 1.56/0.98      inference(global_propositional_subsumption,
% 1.56/0.98                [status(thm)],
% 1.56/0.98                [c_527,c_19]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_532,plain,
% 1.56/0.98      ( ~ m2_connsp_2(X0,sK1,X1)
% 1.56/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.56/0.98      | r1_tarski(X1,k1_tops_1(sK1,X0)) ),
% 1.56/0.98      inference(renaming,[status(thm)],[c_531]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_648,plain,
% 1.56/0.98      ( m1_connsp_2(sK3,sK1,sK2)
% 1.56/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.56/0.98      | r1_tarski(X0,k1_tops_1(sK1,X1))
% 1.56/0.98      | k6_domain_1(u1_struct_0(sK1),sK2) != X0
% 1.56/0.98      | sK1 != sK1
% 1.56/0.98      | sK3 != X1 ),
% 1.56/0.98      inference(resolution_lifted,[status(thm)],[c_180,c_532]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_649,plain,
% 1.56/0.98      ( m1_connsp_2(sK3,sK1,sK2)
% 1.56/0.98      | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.56/0.98      | r1_tarski(k6_domain_1(u1_struct_0(sK1),sK2),k1_tops_1(sK1,sK3)) ),
% 1.56/0.98      inference(unflattening,[status(thm)],[c_648]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_706,plain,
% 1.56/0.98      ( m1_connsp_2(sK3,sK1,sK2)
% 1.56/0.98      | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.56/0.98      | r2_hidden(X0,X1)
% 1.56/0.98      | k1_tops_1(sK1,sK3) != X1
% 1.56/0.98      | k6_domain_1(u1_struct_0(sK1),sK2) != k2_tarski(X0,X0) ),
% 1.56/0.98      inference(resolution_lifted,[status(thm)],[c_173,c_649]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_707,plain,
% 1.56/0.98      ( m1_connsp_2(sK3,sK1,sK2)
% 1.56/0.98      | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.56/0.98      | r2_hidden(X0,k1_tops_1(sK1,sK3))
% 1.56/0.98      | k6_domain_1(u1_struct_0(sK1),sK2) != k2_tarski(X0,X0) ),
% 1.56/0.98      inference(unflattening,[status(thm)],[c_706]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_1879,plain,
% 1.56/0.98      ( m1_connsp_2(sK3,sK1,sK2)
% 1.56/0.98      | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.56/0.98      | r2_hidden(X0_46,k1_tops_1(sK1,sK3))
% 1.56/0.98      | k6_domain_1(u1_struct_0(sK1),sK2) != k2_tarski(X0_46,X0_46) ),
% 1.56/0.98      inference(subtyping,[status(esa)],[c_707]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_1895,plain,
% 1.56/0.98      ( m1_connsp_2(sK3,sK1,sK2)
% 1.56/0.98      | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.56/0.98      | sP1_iProver_split ),
% 1.56/0.98      inference(splitting,
% 1.56/0.98                [splitting(split),new_symbols(definition,[])],
% 1.56/0.98                [c_1879]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_1946,plain,
% 1.56/0.98      ( m1_connsp_2(sK3,sK1,sK2) = iProver_top
% 1.56/0.98      | m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.56/0.98      | sP1_iProver_split = iProver_top ),
% 1.56/0.98      inference(predicate_to_equality,[status(thm)],[c_1895]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_1894,plain,
% 1.56/0.98      ( r2_hidden(X0_46,k1_tops_1(sK1,sK3))
% 1.56/0.98      | k6_domain_1(u1_struct_0(sK1),sK2) != k2_tarski(X0_46,X0_46)
% 1.56/0.98      | ~ sP1_iProver_split ),
% 1.56/0.98      inference(splitting,
% 1.56/0.98                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 1.56/0.98                [c_1879]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_2202,plain,
% 1.56/0.98      ( k6_domain_1(u1_struct_0(sK1),sK2) != k2_tarski(X0_46,X0_46)
% 1.56/0.98      | r2_hidden(X0_46,k1_tops_1(sK1,sK3)) = iProver_top
% 1.56/0.98      | sP1_iProver_split != iProver_top ),
% 1.56/0.98      inference(predicate_to_equality,[status(thm)],[c_1894]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_5,plain,
% 1.56/0.98      ( ~ m1_subset_1(X0,X1)
% 1.56/0.98      | v1_xboole_0(X1)
% 1.56/0.98      | k6_domain_1(X1,X0) = k2_tarski(X0,X0) ),
% 1.56/0.98      inference(cnf_transformation,[],[f71]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_1888,plain,
% 1.56/0.98      ( ~ m1_subset_1(X0_46,X1_46)
% 1.56/0.98      | v1_xboole_0(X1_46)
% 1.56/0.98      | k6_domain_1(X1_46,X0_46) = k2_tarski(X0_46,X0_46) ),
% 1.56/0.98      inference(subtyping,[status(esa)],[c_5]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_2191,plain,
% 1.56/0.98      ( k6_domain_1(X0_46,X1_46) = k2_tarski(X1_46,X1_46)
% 1.56/0.98      | m1_subset_1(X1_46,X0_46) != iProver_top
% 1.56/0.98      | v1_xboole_0(X0_46) = iProver_top ),
% 1.56/0.98      inference(predicate_to_equality,[status(thm)],[c_1888]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_2661,plain,
% 1.56/0.98      ( k6_domain_1(u1_struct_0(sK1),sK2) = k2_tarski(sK2,sK2)
% 1.56/0.98      | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
% 1.56/0.98      inference(superposition,[status(thm)],[c_2193,c_2191]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_1928,plain,
% 1.56/0.98      ( m1_connsp_2(sK0(sK1,sK2),sK1,sK2)
% 1.56/0.98      | ~ m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 1.56/0.98      inference(instantiation,[status(thm)],[c_1885]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_2318,plain,
% 1.56/0.98      ( ~ m1_connsp_2(sK0(sK1,sK2),sK1,sK2)
% 1.56/0.98      | m1_subset_1(sK0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.56/0.98      | ~ m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 1.56/0.98      inference(instantiation,[status(thm)],[c_2316]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_2323,plain,
% 1.56/0.98      ( ~ m1_connsp_2(sK0(sK1,sK2),sK1,sK2)
% 1.56/0.98      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 1.56/0.98      | r2_hidden(sK2,sK0(sK1,sK2)) ),
% 1.56/0.98      inference(instantiation,[status(thm)],[c_2321]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_2678,plain,
% 1.56/0.98      ( v1_xboole_0(u1_struct_0(sK1))
% 1.56/0.98      | k6_domain_1(u1_struct_0(sK1),sK2) = k2_tarski(sK2,sK2) ),
% 1.56/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_2661]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_2789,plain,
% 1.56/0.98      ( ~ m1_subset_1(sK0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.56/0.98      | ~ r2_hidden(sK2,sK0(sK1,sK2))
% 1.56/0.98      | ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 1.56/0.98      inference(instantiation,[status(thm)],[c_2787]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_2807,plain,
% 1.56/0.98      ( k6_domain_1(u1_struct_0(sK1),sK2) = k2_tarski(sK2,sK2) ),
% 1.56/0.98      inference(global_propositional_subsumption,
% 1.56/0.98                [status(thm)],
% 1.56/0.98                [c_2661,c_17,c_1928,c_2318,c_2323,c_2678,c_2789]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_2919,plain,
% 1.56/0.98      ( k2_tarski(X0_46,X0_46) != k2_tarski(sK2,sK2)
% 1.56/0.98      | r2_hidden(X0_46,k1_tops_1(sK1,sK3)) = iProver_top
% 1.56/0.98      | sP1_iProver_split != iProver_top ),
% 1.56/0.98      inference(light_normalisation,[status(thm)],[c_2202,c_2807]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_2926,plain,
% 1.56/0.98      ( r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top
% 1.56/0.98      | sP1_iProver_split != iProver_top ),
% 1.56/0.98      inference(equality_resolution,[status(thm)],[c_2919]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_6,plain,
% 1.56/0.98      ( m1_connsp_2(X0,X1,X2)
% 1.56/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.56/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.56/0.98      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 1.56/0.98      | v2_struct_0(X1)
% 1.56/0.98      | ~ v2_pre_topc(X1)
% 1.56/0.98      | ~ l1_pre_topc(X1) ),
% 1.56/0.98      inference(cnf_transformation,[],[f54]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_482,plain,
% 1.56/0.98      ( m1_connsp_2(X0,X1,X2)
% 1.56/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.56/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.56/0.98      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 1.56/0.98      | ~ v2_pre_topc(X1)
% 1.56/0.98      | ~ l1_pre_topc(X1)
% 1.56/0.98      | sK1 != X1 ),
% 1.56/0.98      inference(resolution_lifted,[status(thm)],[c_6,c_20]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_483,plain,
% 1.56/0.98      ( m1_connsp_2(X0,sK1,X1)
% 1.56/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.56/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.56/0.98      | ~ r2_hidden(X1,k1_tops_1(sK1,X0))
% 1.56/0.98      | ~ v2_pre_topc(sK1)
% 1.56/0.98      | ~ l1_pre_topc(sK1) ),
% 1.56/0.98      inference(unflattening,[status(thm)],[c_482]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_487,plain,
% 1.56/0.98      ( m1_connsp_2(X0,sK1,X1)
% 1.56/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.56/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.56/0.98      | ~ r2_hidden(X1,k1_tops_1(sK1,X0)) ),
% 1.56/0.98      inference(global_propositional_subsumption,
% 1.56/0.98                [status(thm)],
% 1.56/0.98                [c_483,c_19,c_18]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_1881,plain,
% 1.56/0.98      ( m1_connsp_2(X0_46,sK1,X1_46)
% 1.56/0.98      | ~ m1_subset_1(X1_46,u1_struct_0(sK1))
% 1.56/0.98      | ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.56/0.98      | ~ r2_hidden(X1_46,k1_tops_1(sK1,X0_46)) ),
% 1.56/0.98      inference(subtyping,[status(esa)],[c_487]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_2198,plain,
% 1.56/0.98      ( m1_connsp_2(X0_46,sK1,X1_46) = iProver_top
% 1.56/0.98      | m1_subset_1(X1_46,u1_struct_0(sK1)) != iProver_top
% 1.56/0.98      | m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.56/0.98      | r2_hidden(X1_46,k1_tops_1(sK1,X0_46)) != iProver_top ),
% 1.56/0.98      inference(predicate_to_equality,[status(thm)],[c_1881]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_2931,plain,
% 1.56/0.98      ( m1_connsp_2(sK3,sK1,sK2) = iProver_top
% 1.56/0.98      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 1.56/0.98      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.56/0.98      | sP1_iProver_split != iProver_top ),
% 1.56/0.98      inference(superposition,[status(thm)],[c_2926,c_2198]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_2992,plain,
% 1.56/0.98      ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.56/0.98      | sP0_iProver_split = iProver_top ),
% 1.56/0.98      inference(global_propositional_subsumption,
% 1.56/0.98                [status(thm)],
% 1.56/0.98                [c_2199,c_24,c_25,c_1942,c_1946,c_2931]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_2996,plain,
% 1.56/0.98      ( m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.56/0.98      | sP0_iProver_split = iProver_top ),
% 1.56/0.98      inference(light_normalisation,[status(thm)],[c_2992,c_2807]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_3197,plain,
% 1.56/0.98      ( r2_hidden(X0_46,k1_tops_1(sK1,sK3)) != iProver_top
% 1.56/0.98      | k6_domain_1(u1_struct_0(sK1),sK2) != k2_tarski(X0_46,X0_46) ),
% 1.56/0.98      inference(global_propositional_subsumption,
% 1.56/0.98                [status(thm)],
% 1.56/0.98                [c_2200,c_24,c_1929,c_1943,c_2319,c_2324,c_2477,c_2562,
% 1.56/0.98                 c_2790,c_2996]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_3198,plain,
% 1.56/0.98      ( k6_domain_1(u1_struct_0(sK1),sK2) != k2_tarski(X0_46,X0_46)
% 1.56/0.98      | r2_hidden(X0_46,k1_tops_1(sK1,sK3)) != iProver_top ),
% 1.56/0.98      inference(renaming,[status(thm)],[c_3197]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_3203,plain,
% 1.56/0.98      ( k2_tarski(X0_46,X0_46) != k2_tarski(sK2,sK2)
% 1.56/0.98      | r2_hidden(X0_46,k1_tops_1(sK1,sK3)) != iProver_top ),
% 1.56/0.98      inference(light_normalisation,[status(thm)],[c_3198,c_2807]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_3209,plain,
% 1.56/0.98      ( r2_hidden(sK2,k1_tops_1(sK1,sK3)) != iProver_top ),
% 1.56/0.98      inference(equality_resolution,[status(thm)],[c_3203]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_3214,plain,
% 1.56/0.98      ( m1_connsp_2(sK3,sK1,sK2) != iProver_top
% 1.56/0.98      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
% 1.56/0.98      inference(superposition,[status(thm)],[c_2195,c_3209]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_3219,plain,
% 1.56/0.98      ( ~ m1_connsp_2(sK3,sK1,sK2)
% 1.56/0.98      | ~ m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 1.56/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_3214]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_2999,plain,
% 1.56/0.98      ( ~ m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.56/0.98      | sP0_iProver_split ),
% 1.56/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_2996]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_2579,plain,
% 1.56/0.98      ( r2_hidden(sK2,u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK1)) ),
% 1.56/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_2562]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_1897,plain,( X0_46 = X0_46 ),theory(equality) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_2546,plain,
% 1.56/0.98      ( k1_zfmisc_1(u1_struct_0(sK1)) = k1_zfmisc_1(u1_struct_0(sK1)) ),
% 1.56/0.98      inference(instantiation,[status(thm)],[c_1897]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_1948,plain,
% 1.56/0.98      ( r2_hidden(sK2,k1_tops_1(sK1,sK3))
% 1.56/0.98      | ~ sP1_iProver_split
% 1.56/0.98      | k6_domain_1(u1_struct_0(sK1),sK2) != k2_tarski(sK2,sK2) ),
% 1.56/0.98      inference(instantiation,[status(thm)],[c_1894]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(c_1944,plain,
% 1.56/0.98      ( ~ r2_hidden(sK2,k1_tops_1(sK1,sK3))
% 1.56/0.98      | ~ sP0_iProver_split
% 1.56/0.98      | k6_domain_1(u1_struct_0(sK1),sK2) != k2_tarski(sK2,sK2) ),
% 1.56/0.98      inference(instantiation,[status(thm)],[c_1892]) ).
% 1.56/0.98  
% 1.56/0.98  cnf(contradiction,plain,
% 1.56/0.98      ( $false ),
% 1.56/0.98      inference(minisat,
% 1.56/0.98                [status(thm)],
% 1.56/0.98                [c_3273,c_3219,c_2999,c_2789,c_2678,c_2579,c_2546,c_2476,
% 1.56/0.98                 c_2323,c_2318,c_1948,c_1895,c_1944,c_1928,c_17]) ).
% 1.56/0.98  
% 1.56/0.98  
% 1.56/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 1.56/0.98  
% 1.56/0.98  ------                               Statistics
% 1.56/0.98  
% 1.56/0.98  ------ General
% 1.56/0.98  
% 1.56/0.98  abstr_ref_over_cycles:                  0
% 1.56/0.98  abstr_ref_under_cycles:                 0
% 1.56/0.98  gc_basic_clause_elim:                   0
% 1.56/0.98  forced_gc_time:                         0
% 1.56/0.98  parsing_time:                           0.01
% 1.56/0.98  unif_index_cands_time:                  0.
% 1.56/0.98  unif_index_add_time:                    0.
% 1.56/0.98  orderings_time:                         0.
% 1.56/0.98  out_proof_time:                         0.015
% 1.56/0.98  total_time:                             0.12
% 1.56/0.98  num_of_symbols:                         53
% 1.56/0.98  num_of_terms:                           2109
% 1.56/0.98  
% 1.56/0.98  ------ Preprocessing
% 1.56/0.98  
% 1.56/0.98  num_of_splits:                          2
% 1.56/0.98  num_of_split_atoms:                     2
% 1.56/0.98  num_of_reused_defs:                     0
% 1.56/0.98  num_eq_ax_congr_red:                    22
% 1.56/0.98  num_of_sem_filtered_clauses:            1
% 1.56/0.98  num_of_subtypes:                        2
% 1.56/0.98  monotx_restored_types:                  0
% 1.56/0.98  sat_num_of_epr_types:                   0
% 1.56/0.98  sat_num_of_non_cyclic_types:            0
% 1.56/0.98  sat_guarded_non_collapsed_types:        0
% 1.56/0.98  num_pure_diseq_elim:                    0
% 1.56/0.98  simp_replaced_by:                       0
% 1.56/0.98  res_preprocessed:                       81
% 1.56/0.98  prep_upred:                             0
% 1.56/0.98  prep_unflattend:                        102
% 1.56/0.98  smt_new_axioms:                         0
% 1.56/0.98  pred_elim_cands:                        4
% 1.56/0.98  pred_elim:                              5
% 1.56/0.98  pred_elim_cl:                           8
% 1.56/0.98  pred_elim_cycles:                       13
% 1.56/0.98  merged_defs:                            4
% 1.56/0.98  merged_defs_ncl:                        0
% 1.56/0.98  bin_hyper_res:                          4
% 1.56/0.98  prep_cycles:                            4
% 1.56/0.98  pred_elim_time:                         0.027
% 1.56/0.98  splitting_time:                         0.
% 1.56/0.98  sem_filter_time:                        0.
% 1.56/0.98  monotx_time:                            0.
% 1.56/0.98  subtype_inf_time:                       0.
% 1.56/0.98  
% 1.56/0.98  ------ Problem properties
% 1.56/0.98  
% 1.56/0.98  clauses:                                15
% 1.56/0.98  conjectures:                            2
% 1.56/0.98  epr:                                    1
% 1.56/0.98  horn:                                   12
% 1.56/0.98  ground:                                 4
% 1.56/0.98  unary:                                  2
% 1.56/0.98  binary:                                 2
% 1.56/0.98  lits:                                   40
% 1.56/0.98  lits_eq:                                3
% 1.56/0.98  fd_pure:                                0
% 1.56/0.98  fd_pseudo:                              0
% 1.56/0.98  fd_cond:                                0
% 1.56/0.98  fd_pseudo_cond:                         0
% 1.56/0.98  ac_symbols:                             0
% 1.56/0.98  
% 1.56/0.98  ------ Propositional Solver
% 1.56/0.98  
% 1.56/0.98  prop_solver_calls:                      27
% 1.56/0.98  prop_fast_solver_calls:                 910
% 1.56/0.98  smt_solver_calls:                       0
% 1.56/0.98  smt_fast_solver_calls:                  0
% 1.56/0.98  prop_num_of_clauses:                    812
% 1.56/0.98  prop_preprocess_simplified:             3272
% 1.56/0.98  prop_fo_subsumed:                       36
% 1.56/0.98  prop_solver_time:                       0.
% 1.56/0.98  smt_solver_time:                        0.
% 1.56/0.98  smt_fast_solver_time:                   0.
% 1.56/0.98  prop_fast_solver_time:                  0.
% 1.56/0.98  prop_unsat_core_time:                   0.
% 1.56/0.98  
% 1.56/0.98  ------ QBF
% 1.56/0.98  
% 1.56/0.98  qbf_q_res:                              0
% 1.56/0.98  qbf_num_tautologies:                    0
% 1.56/0.98  qbf_prep_cycles:                        0
% 1.56/0.98  
% 1.56/0.98  ------ BMC1
% 1.56/0.98  
% 1.56/0.98  bmc1_current_bound:                     -1
% 1.56/0.98  bmc1_last_solved_bound:                 -1
% 1.56/0.98  bmc1_unsat_core_size:                   -1
% 1.56/0.98  bmc1_unsat_core_parents_size:           -1
% 1.56/0.98  bmc1_merge_next_fun:                    0
% 1.56/0.98  bmc1_unsat_core_clauses_time:           0.
% 1.56/0.98  
% 1.56/0.98  ------ Instantiation
% 1.56/0.98  
% 1.56/0.98  inst_num_of_clauses:                    176
% 1.56/0.98  inst_num_in_passive:                    40
% 1.56/0.98  inst_num_in_active:                     129
% 1.56/0.98  inst_num_in_unprocessed:                6
% 1.56/0.98  inst_num_of_loops:                      149
% 1.56/0.98  inst_num_of_learning_restarts:          0
% 1.56/0.98  inst_num_moves_active_passive:          15
% 1.56/0.98  inst_lit_activity:                      0
% 1.56/0.98  inst_lit_activity_moves:                0
% 1.56/0.98  inst_num_tautologies:                   0
% 1.56/0.98  inst_num_prop_implied:                  0
% 1.56/0.98  inst_num_existing_simplified:           0
% 1.56/0.98  inst_num_eq_res_simplified:             0
% 1.56/0.98  inst_num_child_elim:                    0
% 1.56/0.98  inst_num_of_dismatching_blockings:      9
% 1.56/0.98  inst_num_of_non_proper_insts:           164
% 1.56/0.98  inst_num_of_duplicates:                 0
% 1.56/0.98  inst_inst_num_from_inst_to_res:         0
% 1.56/0.98  inst_dismatching_checking_time:         0.
% 1.56/0.98  
% 1.56/0.98  ------ Resolution
% 1.56/0.98  
% 1.56/0.98  res_num_of_clauses:                     0
% 1.56/0.98  res_num_in_passive:                     0
% 1.56/0.98  res_num_in_active:                      0
% 1.56/0.98  res_num_of_loops:                       85
% 1.56/0.98  res_forward_subset_subsumed:            22
% 1.56/0.98  res_backward_subset_subsumed:           0
% 1.56/0.98  res_forward_subsumed:                   0
% 1.56/0.98  res_backward_subsumed:                  0
% 1.56/0.98  res_forward_subsumption_resolution:     0
% 1.56/0.98  res_backward_subsumption_resolution:    0
% 1.56/0.98  res_clause_to_clause_subsumption:       85
% 1.56/0.98  res_orphan_elimination:                 0
% 1.56/0.98  res_tautology_del:                      59
% 1.56/0.98  res_num_eq_res_simplified:              0
% 1.56/0.98  res_num_sel_changes:                    0
% 1.56/0.98  res_moves_from_active_to_pass:          0
% 1.56/0.98  
% 1.56/0.98  ------ Superposition
% 1.56/0.98  
% 1.56/0.98  sup_time_total:                         0.
% 1.56/0.98  sup_time_generating:                    0.
% 1.56/0.98  sup_time_sim_full:                      0.
% 1.56/0.98  sup_time_sim_immed:                     0.
% 1.56/0.98  
% 1.56/0.98  sup_num_of_clauses:                     33
% 1.56/0.98  sup_num_in_active:                      28
% 1.56/0.98  sup_num_in_passive:                     5
% 1.56/0.98  sup_num_of_loops:                       28
% 1.56/0.98  sup_fw_superposition:                   13
% 1.56/0.98  sup_bw_superposition:                   4
% 1.56/0.98  sup_immediate_simplified:               0
% 1.56/0.98  sup_given_eliminated:                   0
% 1.56/0.98  comparisons_done:                       0
% 1.56/0.98  comparisons_avoided:                    0
% 1.56/0.98  
% 1.56/0.98  ------ Simplifications
% 1.56/0.98  
% 1.56/0.98  
% 1.56/0.98  sim_fw_subset_subsumed:                 0
% 1.56/0.98  sim_bw_subset_subsumed:                 0
% 1.56/0.98  sim_fw_subsumed:                        0
% 1.56/0.98  sim_bw_subsumed:                        0
% 1.56/0.98  sim_fw_subsumption_res:                 0
% 1.56/0.98  sim_bw_subsumption_res:                 0
% 1.56/0.98  sim_tautology_del:                      1
% 1.56/0.98  sim_eq_tautology_del:                   0
% 1.56/0.98  sim_eq_res_simp:                        0
% 1.56/0.98  sim_fw_demodulated:                     0
% 1.56/0.98  sim_bw_demodulated:                     0
% 1.56/0.98  sim_light_normalised:                   3
% 1.56/0.98  sim_joinable_taut:                      0
% 1.56/0.98  sim_joinable_simp:                      0
% 1.56/0.98  sim_ac_normalised:                      0
% 1.56/0.98  sim_smt_subsumption:                    0
% 1.56/0.98  
%------------------------------------------------------------------------------
