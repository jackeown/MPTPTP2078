%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:18:26 EST 2020

% Result     : Theorem 1.78s
% Output     : CNFRefutation 1.78s
% Verified   : 
% Statistics : Number of formulae       :  222 (2470 expanded)
%              Number of clauses        :  145 ( 692 expanded)
%              Number of leaves         :   22 ( 622 expanded)
%              Depth                    :   28
%              Number of atoms          :  832 (15830 expanded)
%              Number of equality atoms :  140 ( 444 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

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
    inference(nnf_transformation,[],[f23])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f14,conjecture,(
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

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

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
    inference(ennf_transformation,[],[f15])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f35])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f49,plain,(
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

fof(f48,plain,(
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

fof(f47,plain,
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

fof(f50,plain,
    ( ( ~ m1_connsp_2(sK4,sK2,sK3)
      | ~ m2_connsp_2(sK4,sK2,k6_domain_1(u1_struct_0(sK2),sK3)) )
    & ( m1_connsp_2(sK4,sK2,sK3)
      | m2_connsp_2(sK4,sK2,k6_domain_1(u1_struct_0(sK2),sK3)) )
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f46,f49,f48,f47])).

fof(f68,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f69,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f70,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tarski(X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f55,f53])).

fof(f74,plain,
    ( ~ m1_connsp_2(sK4,sK2,sK3)
    | ~ m2_connsp_2(sK4,sK2,k6_domain_1(u1_struct_0(sK2),sK3)) ),
    inference(cnf_transformation,[],[f50])).

fof(f9,axiom,(
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
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

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
    inference(nnf_transformation,[],[f25])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( m2_connsp_2(X2,X0,X1)
      | ~ r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f72,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f50])).

fof(f71,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f50])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X2] : m1_connsp_2(X2,X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
     => m1_connsp_2(sK1(X0,X1),X0,X1) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_connsp_2(sK1(X0,X1),X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f43])).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_connsp_2(sK1(X0,X1),X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k2_tarski(X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f54,f53])).

fof(f73,plain,
    ( m1_connsp_2(sK4,sK2,sK3)
    | m2_connsp_2(sK4,sK2,k6_domain_1(u1_struct_0(sK2),sK3)) ),
    inference(cnf_transformation,[],[f50])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m2_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X2] :
          ( m2_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m2_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m2_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m2_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f13,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f13])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ m1_connsp_2(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k2_tarski(X1,X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f59,f53])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f77,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f56,f53])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f36])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).

fof(f51,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_9,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_12,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f64])).

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

cnf(c_22,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_402,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_145,c_22])).

cnf(c_403,plain,
    ( ~ m1_connsp_2(X0,sK2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r2_hidden(X1,k1_tops_1(sK2,X0))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_402])).

cnf(c_21,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_20,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_407,plain,
    ( ~ m1_connsp_2(X0,sK2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r2_hidden(X1,k1_tops_1(sK2,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_403,c_21,c_20])).

cnf(c_1893,plain,
    ( ~ m1_connsp_2(X0_47,sK2,X1_47)
    | ~ m1_subset_1(X1_47,u1_struct_0(sK2))
    | r2_hidden(X1_47,k1_tops_1(sK2,X0_47)) ),
    inference(subtyping,[status(esa)],[c_407])).

cnf(c_2242,plain,
    ( m1_connsp_2(X0_47,sK2,X1_47) != iProver_top
    | m1_subset_1(X1_47,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X1_47,k1_tops_1(sK2,X0_47)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1893])).

cnf(c_2,plain,
    ( r1_tarski(k2_tarski(X0,X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_191,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k2_tarski(X0,X0),X1) ),
    inference(prop_impl,[status(thm)],[c_2])).

cnf(c_192,plain,
    ( r1_tarski(k2_tarski(X0,X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(renaming,[status(thm)],[c_191])).

cnf(c_16,negated_conjecture,
    ( ~ m2_connsp_2(sK4,sK2,k6_domain_1(u1_struct_0(sK2),sK3))
    | ~ m1_connsp_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_193,plain,
    ( ~ m1_connsp_2(sK4,sK2,sK3)
    | ~ m2_connsp_2(sK4,sK2,k6_domain_1(u1_struct_0(sK2),sK3)) ),
    inference(prop_impl,[status(thm)],[c_16])).

cnf(c_194,plain,
    ( ~ m2_connsp_2(sK4,sK2,k6_domain_1(u1_struct_0(sK2),sK3))
    | ~ m1_connsp_2(sK4,sK2,sK3) ),
    inference(renaming,[status(thm)],[c_193])).

cnf(c_10,plain,
    ( m2_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_547,plain,
    ( m2_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_20])).

cnf(c_548,plain,
    ( m2_connsp_2(X0,sK2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X1,k1_tops_1(sK2,X0))
    | ~ v2_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_547])).

cnf(c_552,plain,
    ( ~ r1_tarski(X1,k1_tops_1(sK2,X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m2_connsp_2(X0,sK2,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_548,c_21])).

cnf(c_553,plain,
    ( m2_connsp_2(X0,sK2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X1,k1_tops_1(sK2,X0)) ),
    inference(renaming,[status(thm)],[c_552])).

cnf(c_644,plain,
    ( ~ m1_connsp_2(sK4,sK2,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X1,k1_tops_1(sK2,X0))
    | k6_domain_1(u1_struct_0(sK2),sK3) != X1
    | sK2 != sK2
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_194,c_553])).

cnf(c_645,plain,
    ( ~ m1_connsp_2(sK4,sK2,sK3)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(k6_domain_1(u1_struct_0(sK2),sK3),k1_tops_1(sK2,sK4)) ),
    inference(unflattening,[status(thm)],[c_644])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_647,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_connsp_2(sK4,sK2,sK3)
    | ~ r1_tarski(k6_domain_1(u1_struct_0(sK2),sK3),k1_tops_1(sK2,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_645,c_18])).

cnf(c_648,plain,
    ( ~ m1_connsp_2(sK4,sK2,sK3)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(k6_domain_1(u1_struct_0(sK2),sK3),k1_tops_1(sK2,sK4)) ),
    inference(renaming,[status(thm)],[c_647])).

cnf(c_671,plain,
    ( ~ m1_connsp_2(sK4,sK2,sK3)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X0,X1)
    | k1_tops_1(sK2,sK4) != X1
    | k6_domain_1(u1_struct_0(sK2),sK3) != k2_tarski(X0,X0) ),
    inference(resolution_lifted,[status(thm)],[c_192,c_648])).

cnf(c_672,plain,
    ( ~ m1_connsp_2(sK4,sK2,sK3)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X0,k1_tops_1(sK2,sK4))
    | k6_domain_1(u1_struct_0(sK2),sK3) != k2_tarski(X0,X0) ),
    inference(unflattening,[status(thm)],[c_671])).

cnf(c_1889,plain,
    ( ~ m1_connsp_2(sK4,sK2,sK3)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X0_47,k1_tops_1(sK2,sK4))
    | k6_domain_1(u1_struct_0(sK2),sK3) != k2_tarski(X0_47,X0_47) ),
    inference(subtyping,[status(esa)],[c_672])).

cnf(c_1903,plain,
    ( ~ r2_hidden(X0_47,k1_tops_1(sK2,sK4))
    | k6_domain_1(u1_struct_0(sK2),sK3) != k2_tarski(X0_47,X0_47)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_1889])).

cnf(c_2247,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK3) != k2_tarski(X0_47,X0_47)
    | r2_hidden(X0_47,k1_tops_1(sK2,sK4)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1903])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_26,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_14,plain,
    ( m1_connsp_2(sK1(X0,X1),X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_384,plain,
    ( m1_connsp_2(sK1(X0,X1),X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_22])).

cnf(c_385,plain,
    ( m1_connsp_2(sK1(sK2,X0),sK2,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_384])).

cnf(c_389,plain,
    ( m1_connsp_2(sK1(sK2,X0),sK2,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_385,c_21,c_20])).

cnf(c_1894,plain,
    ( m1_connsp_2(sK1(sK2,X0_47),sK2,X0_47)
    | ~ m1_subset_1(X0_47,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_389])).

cnf(c_1943,plain,
    ( m1_connsp_2(sK1(sK2,sK3),sK2,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1894])).

cnf(c_1942,plain,
    ( m1_connsp_2(sK1(sK2,X0_47),sK2,X0_47) = iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1894])).

cnf(c_1944,plain,
    ( m1_connsp_2(sK1(sK2,sK3),sK2,sK3) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1942])).

cnf(c_1904,plain,
    ( ~ m1_connsp_2(sK4,sK2,sK3)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_1889])).

cnf(c_1957,plain,
    ( m1_connsp_2(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1904])).

cnf(c_1958,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK3) != k2_tarski(X0_47,X0_47)
    | r2_hidden(X0_47,k1_tops_1(sK2,sK4)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1903])).

cnf(c_3,plain,
    ( ~ r1_tarski(k2_tarski(X0,X0),X1)
    | r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_189,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(k2_tarski(X0,X0),X1) ),
    inference(prop_impl,[status(thm)],[c_3])).

cnf(c_190,plain,
    ( ~ r1_tarski(k2_tarski(X0,X0),X1)
    | r2_hidden(X0,X1) ),
    inference(renaming,[status(thm)],[c_189])).

cnf(c_17,negated_conjecture,
    ( m2_connsp_2(sK4,sK2,k6_domain_1(u1_struct_0(sK2),sK3))
    | m1_connsp_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_195,plain,
    ( m1_connsp_2(sK4,sK2,sK3)
    | m2_connsp_2(sK4,sK2,k6_domain_1(u1_struct_0(sK2),sK3)) ),
    inference(prop_impl,[status(thm)],[c_17])).

cnf(c_196,plain,
    ( m2_connsp_2(sK4,sK2,k6_domain_1(u1_struct_0(sK2),sK3))
    | m1_connsp_2(sK4,sK2,sK3) ),
    inference(renaming,[status(thm)],[c_195])).

cnf(c_11,plain,
    ( ~ m2_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_13,plain,
    ( ~ m2_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_138,plain,
    ( ~ m2_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11,c_13])).

cnf(c_509,plain,
    ( ~ m2_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_138,c_20])).

cnf(c_510,plain,
    ( ~ m2_connsp_2(X0,sK2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(X1,k1_tops_1(sK2,X0))
    | ~ v2_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_509])).

cnf(c_514,plain,
    ( r1_tarski(X1,k1_tops_1(sK2,X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m2_connsp_2(X0,sK2,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_510,c_21])).

cnf(c_515,plain,
    ( ~ m2_connsp_2(X0,sK2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(X1,k1_tops_1(sK2,X0)) ),
    inference(renaming,[status(thm)],[c_514])).

cnf(c_631,plain,
    ( m1_connsp_2(sK4,sK2,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(X0,k1_tops_1(sK2,X1))
    | k6_domain_1(u1_struct_0(sK2),sK3) != X0
    | sK2 != sK2
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_196,c_515])).

cnf(c_632,plain,
    ( m1_connsp_2(sK4,sK2,sK3)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(k6_domain_1(u1_struct_0(sK2),sK3),k1_tops_1(sK2,sK4)) ),
    inference(unflattening,[status(thm)],[c_631])).

cnf(c_689,plain,
    ( m1_connsp_2(sK4,sK2,sK3)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(X0,X1)
    | k1_tops_1(sK2,sK4) != X1
    | k6_domain_1(u1_struct_0(sK2),sK3) != k2_tarski(X0,X0) ),
    inference(resolution_lifted,[status(thm)],[c_190,c_632])).

cnf(c_690,plain,
    ( m1_connsp_2(sK4,sK2,sK3)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(X0,k1_tops_1(sK2,sK4))
    | k6_domain_1(u1_struct_0(sK2),sK3) != k2_tarski(X0,X0) ),
    inference(unflattening,[status(thm)],[c_689])).

cnf(c_1888,plain,
    ( m1_connsp_2(sK4,sK2,sK3)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(X0_47,k1_tops_1(sK2,sK4))
    | k6_domain_1(u1_struct_0(sK2),sK3) != k2_tarski(X0_47,X0_47) ),
    inference(subtyping,[status(esa)],[c_690])).

cnf(c_1906,plain,
    ( m1_connsp_2(sK4,sK2,sK3)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_1888])).

cnf(c_1961,plain,
    ( m1_connsp_2(sK4,sK2,sK3) = iProver_top
    | m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | sP1_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1906])).

cnf(c_444,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_22])).

cnf(c_445,plain,
    ( ~ m1_connsp_2(X0,sK2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_444])).

cnf(c_449,plain,
    ( ~ m1_connsp_2(X0,sK2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_445,c_21,c_20])).

cnf(c_1891,plain,
    ( ~ m1_connsp_2(X0_47,sK2,X1_47)
    | ~ m1_subset_1(X1_47,u1_struct_0(sK2))
    | m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subtyping,[status(esa)],[c_449])).

cnf(c_2375,plain,
    ( ~ m1_connsp_2(sK1(sK2,X0_47),sK2,X0_47)
    | ~ m1_subset_1(X0_47,u1_struct_0(sK2))
    | m1_subset_1(sK1(sK2,X0_47),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_1891])).

cnf(c_2377,plain,
    ( ~ m1_connsp_2(sK1(sK2,sK3),sK2,sK3)
    | m1_subset_1(sK1(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2375])).

cnf(c_2376,plain,
    ( m1_connsp_2(sK1(sK2,X0_47),sK2,X0_47) != iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK1(sK2,X0_47),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2375])).

cnf(c_2378,plain,
    ( m1_connsp_2(sK1(sK2,sK3),sK2,sK3) != iProver_top
    | m1_subset_1(sK1(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2376])).

cnf(c_15,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f67])).

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

cnf(c_423,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_129,c_22])).

cnf(c_424,plain,
    ( ~ m1_connsp_2(X0,sK2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r2_hidden(X1,X0)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_423])).

cnf(c_428,plain,
    ( ~ m1_connsp_2(X0,sK2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r2_hidden(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_424,c_21,c_20])).

cnf(c_1892,plain,
    ( ~ m1_connsp_2(X0_47,sK2,X1_47)
    | ~ m1_subset_1(X1_47,u1_struct_0(sK2))
    | r2_hidden(X1_47,X0_47) ),
    inference(subtyping,[status(esa)],[c_428])).

cnf(c_2380,plain,
    ( ~ m1_connsp_2(sK1(sK2,X0_47),sK2,X0_47)
    | ~ m1_subset_1(X0_47,u1_struct_0(sK2))
    | r2_hidden(X0_47,sK1(sK2,X0_47)) ),
    inference(instantiation,[status(thm)],[c_1892])).

cnf(c_2382,plain,
    ( ~ m1_connsp_2(sK1(sK2,sK3),sK2,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | r2_hidden(sK3,sK1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_2380])).

cnf(c_2381,plain,
    ( m1_connsp_2(sK1(sK2,X0_47),sK2,X0_47) != iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X0_47,sK1(sK2,X0_47)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2380])).

cnf(c_2383,plain,
    ( m1_connsp_2(sK1(sK2,sK3),sK2,sK3) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK3,sK1(sK2,sK3)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2381])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1897,plain,
    ( ~ m1_subset_1(X0_47,X1_47)
    | v1_xboole_0(X1_47)
    | k6_domain_1(X1_47,X0_47) = k2_tarski(X0_47,X0_47) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_2408,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2))
    | k6_domain_1(u1_struct_0(sK2),sK3) = k2_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_1897])).

cnf(c_1908,plain,
    ( X0_47 = X0_47 ),
    theory(equality)).

cnf(c_2533,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1908])).

cnf(c_4,plain,
    ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1900,plain,
    ( m1_subset_1(k2_tarski(X0_47,X0_47),k1_zfmisc_1(X1_47))
    | ~ r2_hidden(X0_47,X1_47) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_2540,plain,
    ( m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK3,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1900])).

cnf(c_2541,plain,
    ( m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | r2_hidden(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2540])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1901,plain,
    ( ~ r2_hidden(X0_47,X1_47)
    | ~ v1_xboole_0(X1_47) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_2637,plain,
    ( ~ r2_hidden(X0_47,sK1(sK2,X0_47))
    | ~ v1_xboole_0(sK1(sK2,X0_47)) ),
    inference(instantiation,[status(thm)],[c_1901])).

cnf(c_2639,plain,
    ( ~ r2_hidden(sK3,sK1(sK2,sK3))
    | ~ v1_xboole_0(sK1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_2637])).

cnf(c_2638,plain,
    ( r2_hidden(X0_47,sK1(sK2,X0_47)) != iProver_top
    | v1_xboole_0(sK1(sK2,X0_47)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2637])).

cnf(c_2640,plain,
    ( r2_hidden(sK3,sK1(sK2,sK3)) != iProver_top
    | v1_xboole_0(sK1(sK2,sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2638])).

cnf(c_1895,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_2240,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1895])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1898,plain,
    ( ~ m1_subset_1(X0_47,X1_47)
    | r2_hidden(X0_47,X1_47)
    | v1_xboole_0(X1_47) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_2237,plain,
    ( m1_subset_1(X0_47,X1_47) != iProver_top
    | r2_hidden(X0_47,X1_47) = iProver_top
    | v1_xboole_0(X1_47) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1898])).

cnf(c_2687,plain,
    ( r2_hidden(sK3,u1_struct_0(sK2)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2240,c_2237])).

cnf(c_1911,plain,
    ( X0_47 != X1_47
    | k1_zfmisc_1(X0_47) = k1_zfmisc_1(X1_47) ),
    theory(equality)).

cnf(c_2565,plain,
    ( X0_47 != u1_struct_0(sK2)
    | k1_zfmisc_1(X0_47) = k1_zfmisc_1(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1911])).

cnf(c_2772,plain,
    ( u1_struct_0(sK2) != u1_struct_0(sK2)
    | k1_zfmisc_1(u1_struct_0(sK2)) = k1_zfmisc_1(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2565])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1899,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(X1_47))
    | ~ v1_xboole_0(X1_47)
    | v1_xboole_0(X0_47) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_2448,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(X0_47)
    | ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1899])).

cnf(c_2777,plain,
    ( ~ m1_subset_1(sK1(sK2,X0_47),k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(sK1(sK2,X0_47))
    | ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2448])).

cnf(c_2779,plain,
    ( ~ m1_subset_1(sK1(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(sK1(sK2,sK3))
    | ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2777])).

cnf(c_2778,plain,
    ( m1_subset_1(sK1(sK2,X0_47),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_xboole_0(sK1(sK2,X0_47)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2777])).

cnf(c_2780,plain,
    ( m1_subset_1(sK1(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_xboole_0(sK1(sK2,sK3)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2778])).

cnf(c_1912,plain,
    ( ~ m1_subset_1(X0_47,X1_47)
    | m1_subset_1(X2_47,X3_47)
    | X2_47 != X0_47
    | X3_47 != X1_47 ),
    theory(equality)).

cnf(c_2714,plain,
    ( m1_subset_1(X0_47,X1_47)
    | ~ m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | X0_47 != k2_tarski(sK3,sK3)
    | X1_47 != k1_zfmisc_1(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1912])).

cnf(c_2998,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),X0_47)
    | ~ m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | X0_47 != k1_zfmisc_1(u1_struct_0(sK2))
    | k6_domain_1(u1_struct_0(sK2),sK3) != k2_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_2714])).

cnf(c_3186,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | k6_domain_1(u1_struct_0(sK2),sK3) != k2_tarski(sK3,sK3)
    | k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2998])).

cnf(c_3187,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK3) != k2_tarski(sK3,sK3)
    | k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(u1_struct_0(sK2))
    | m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3186])).

cnf(c_1905,plain,
    ( r2_hidden(X0_47,k1_tops_1(sK2,sK4))
    | k6_domain_1(u1_struct_0(sK2),sK3) != k2_tarski(X0_47,X0_47)
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_1888])).

cnf(c_2249,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK3) != k2_tarski(X0_47,X0_47)
    | r2_hidden(X0_47,k1_tops_1(sK2,sK4)) = iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1905])).

cnf(c_27,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1960,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK3) != k2_tarski(sK3,sK3)
    | r2_hidden(sK3,k1_tops_1(sK2,sK4)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(instantiation,[status(thm)],[c_1958])).

cnf(c_1962,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK3) != k2_tarski(X0_47,X0_47)
    | r2_hidden(X0_47,k1_tops_1(sK2,sK4)) = iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1905])).

cnf(c_1964,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK3) != k2_tarski(sK3,sK3)
    | r2_hidden(sK3,k1_tops_1(sK2,sK4)) = iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(instantiation,[status(thm)],[c_1962])).

cnf(c_8,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_465,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_22])).

cnf(c_466,plain,
    ( m1_connsp_2(X0,sK2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1,k1_tops_1(sK2,X0))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_465])).

cnf(c_470,plain,
    ( m1_connsp_2(X0,sK2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1,k1_tops_1(sK2,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_466,c_21,c_20])).

cnf(c_1890,plain,
    ( m1_connsp_2(X0_47,sK2,X1_47)
    | ~ m1_subset_1(X1_47,u1_struct_0(sK2))
    | ~ m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1_47,k1_tops_1(sK2,X0_47)) ),
    inference(subtyping,[status(esa)],[c_470])).

cnf(c_2390,plain,
    ( m1_connsp_2(sK4,sK2,X0_47)
    | ~ m1_subset_1(X0_47,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X0_47,k1_tops_1(sK2,sK4)) ),
    inference(instantiation,[status(thm)],[c_1890])).

cnf(c_2391,plain,
    ( m1_connsp_2(sK4,sK2,X0_47) = iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(X0_47,k1_tops_1(sK2,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2390])).

cnf(c_2393,plain,
    ( m1_connsp_2(sK4,sK2,sK3) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(sK3,k1_tops_1(sK2,sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2391])).

cnf(c_3288,plain,
    ( sP1_iProver_split != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2249,c_19,c_26,c_27,c_1943,c_1944,c_1957,c_1960,c_1964,c_2377,c_2378,c_2382,c_2383,c_2393,c_2408,c_2533,c_2541,c_2639,c_2640,c_2687,c_2772,c_2779,c_2780,c_3187])).

cnf(c_3393,plain,
    ( r2_hidden(X0_47,k1_tops_1(sK2,sK4)) != iProver_top
    | k6_domain_1(u1_struct_0(sK2),sK3) != k2_tarski(X0_47,X0_47) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2247,c_19,c_26,c_27,c_1943,c_1944,c_1957,c_1958,c_1960,c_1961,c_1964,c_2377,c_2378,c_2382,c_2383,c_2393,c_2408,c_2533,c_2541,c_2639,c_2640,c_2687,c_2772,c_2779,c_2780,c_3187])).

cnf(c_3394,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK3) != k2_tarski(X0_47,X0_47)
    | r2_hidden(X0_47,k1_tops_1(sK2,sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3393])).

cnf(c_2238,plain,
    ( k6_domain_1(X0_47,X1_47) = k2_tarski(X1_47,X1_47)
    | m1_subset_1(X1_47,X0_47) != iProver_top
    | v1_xboole_0(X0_47) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1897])).

cnf(c_3066,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK3) = k2_tarski(sK3,sK3)
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2240,c_2238])).

cnf(c_3098,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK3) = k2_tarski(sK3,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3066,c_19,c_1943,c_2377,c_2382,c_2408,c_2639,c_2779])).

cnf(c_3399,plain,
    ( k2_tarski(X0_47,X0_47) != k2_tarski(sK3,sK3)
    | r2_hidden(X0_47,k1_tops_1(sK2,sK4)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3394,c_3098])).

cnf(c_3405,plain,
    ( r2_hidden(sK3,k1_tops_1(sK2,sK4)) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3399])).

cnf(c_3409,plain,
    ( m1_connsp_2(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2242,c_3405])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3409,c_3288,c_3187,c_2780,c_2779,c_2772,c_2687,c_2640,c_2639,c_2541,c_2533,c_2408,c_2383,c_2382,c_2378,c_2377,c_1961,c_1944,c_1943,c_26,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:17:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.78/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.78/0.98  
% 1.78/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.78/0.98  
% 1.78/0.98  ------  iProver source info
% 1.78/0.98  
% 1.78/0.98  git: date: 2020-06-30 10:37:57 +0100
% 1.78/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.78/0.98  git: non_committed_changes: false
% 1.78/0.98  git: last_make_outside_of_git: false
% 1.78/0.98  
% 1.78/0.98  ------ 
% 1.78/0.98  
% 1.78/0.98  ------ Input Options
% 1.78/0.98  
% 1.78/0.98  --out_options                           all
% 1.78/0.98  --tptp_safe_out                         true
% 1.78/0.98  --problem_path                          ""
% 1.78/0.98  --include_path                          ""
% 1.78/0.98  --clausifier                            res/vclausify_rel
% 1.78/0.98  --clausifier_options                    --mode clausify
% 1.78/0.98  --stdin                                 false
% 1.78/0.98  --stats_out                             all
% 1.78/0.98  
% 1.78/0.98  ------ General Options
% 1.78/0.98  
% 1.78/0.98  --fof                                   false
% 1.78/0.98  --time_out_real                         305.
% 1.78/0.98  --time_out_virtual                      -1.
% 1.78/0.98  --symbol_type_check                     false
% 1.78/0.98  --clausify_out                          false
% 1.78/0.98  --sig_cnt_out                           false
% 1.78/0.98  --trig_cnt_out                          false
% 1.78/0.98  --trig_cnt_out_tolerance                1.
% 1.78/0.98  --trig_cnt_out_sk_spl                   false
% 1.78/0.98  --abstr_cl_out                          false
% 1.78/0.98  
% 1.78/0.98  ------ Global Options
% 1.78/0.98  
% 1.78/0.98  --schedule                              default
% 1.78/0.98  --add_important_lit                     false
% 1.78/0.98  --prop_solver_per_cl                    1000
% 1.78/0.98  --min_unsat_core                        false
% 1.78/0.98  --soft_assumptions                      false
% 1.78/0.98  --soft_lemma_size                       3
% 1.78/0.98  --prop_impl_unit_size                   0
% 1.78/0.98  --prop_impl_unit                        []
% 1.78/0.98  --share_sel_clauses                     true
% 1.78/0.98  --reset_solvers                         false
% 1.78/0.98  --bc_imp_inh                            [conj_cone]
% 1.78/0.98  --conj_cone_tolerance                   3.
% 1.78/0.98  --extra_neg_conj                        none
% 1.78/0.98  --large_theory_mode                     true
% 1.78/0.98  --prolific_symb_bound                   200
% 1.78/0.98  --lt_threshold                          2000
% 1.78/0.98  --clause_weak_htbl                      true
% 1.78/0.98  --gc_record_bc_elim                     false
% 1.78/0.98  
% 1.78/0.98  ------ Preprocessing Options
% 1.78/0.98  
% 1.78/0.98  --preprocessing_flag                    true
% 1.78/0.98  --time_out_prep_mult                    0.1
% 1.78/0.98  --splitting_mode                        input
% 1.78/0.98  --splitting_grd                         true
% 1.78/0.98  --splitting_cvd                         false
% 1.78/0.98  --splitting_cvd_svl                     false
% 1.78/0.98  --splitting_nvd                         32
% 1.78/0.98  --sub_typing                            true
% 1.78/0.98  --prep_gs_sim                           true
% 1.78/0.98  --prep_unflatten                        true
% 1.78/0.98  --prep_res_sim                          true
% 1.78/0.98  --prep_upred                            true
% 1.78/0.98  --prep_sem_filter                       exhaustive
% 1.78/0.98  --prep_sem_filter_out                   false
% 1.78/0.98  --pred_elim                             true
% 1.78/0.98  --res_sim_input                         true
% 1.78/0.98  --eq_ax_congr_red                       true
% 1.78/0.98  --pure_diseq_elim                       true
% 1.78/0.98  --brand_transform                       false
% 1.78/0.98  --non_eq_to_eq                          false
% 1.78/0.98  --prep_def_merge                        true
% 1.78/0.98  --prep_def_merge_prop_impl              false
% 1.78/0.98  --prep_def_merge_mbd                    true
% 1.78/0.98  --prep_def_merge_tr_red                 false
% 1.78/0.98  --prep_def_merge_tr_cl                  false
% 1.78/0.98  --smt_preprocessing                     true
% 1.78/0.98  --smt_ac_axioms                         fast
% 1.78/0.98  --preprocessed_out                      false
% 1.78/0.98  --preprocessed_stats                    false
% 1.78/0.98  
% 1.78/0.98  ------ Abstraction refinement Options
% 1.78/0.98  
% 1.78/0.98  --abstr_ref                             []
% 1.78/0.98  --abstr_ref_prep                        false
% 1.78/0.98  --abstr_ref_until_sat                   false
% 1.78/0.98  --abstr_ref_sig_restrict                funpre
% 1.78/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.78/0.98  --abstr_ref_under                       []
% 1.78/0.98  
% 1.78/0.98  ------ SAT Options
% 1.78/0.98  
% 1.78/0.98  --sat_mode                              false
% 1.78/0.98  --sat_fm_restart_options                ""
% 1.78/0.98  --sat_gr_def                            false
% 1.78/0.98  --sat_epr_types                         true
% 1.78/0.98  --sat_non_cyclic_types                  false
% 1.78/0.98  --sat_finite_models                     false
% 1.78/0.98  --sat_fm_lemmas                         false
% 1.78/0.98  --sat_fm_prep                           false
% 1.78/0.98  --sat_fm_uc_incr                        true
% 1.78/0.98  --sat_out_model                         small
% 1.78/0.98  --sat_out_clauses                       false
% 1.78/0.98  
% 1.78/0.98  ------ QBF Options
% 1.78/0.98  
% 1.78/0.98  --qbf_mode                              false
% 1.78/0.98  --qbf_elim_univ                         false
% 1.78/0.98  --qbf_dom_inst                          none
% 1.78/0.98  --qbf_dom_pre_inst                      false
% 1.78/0.98  --qbf_sk_in                             false
% 1.78/0.98  --qbf_pred_elim                         true
% 1.78/0.98  --qbf_split                             512
% 1.78/0.98  
% 1.78/0.98  ------ BMC1 Options
% 1.78/0.98  
% 1.78/0.98  --bmc1_incremental                      false
% 1.78/0.98  --bmc1_axioms                           reachable_all
% 1.78/0.98  --bmc1_min_bound                        0
% 1.78/0.98  --bmc1_max_bound                        -1
% 1.78/0.98  --bmc1_max_bound_default                -1
% 1.78/0.98  --bmc1_symbol_reachability              true
% 1.78/0.98  --bmc1_property_lemmas                  false
% 1.78/0.98  --bmc1_k_induction                      false
% 1.78/0.98  --bmc1_non_equiv_states                 false
% 1.78/0.98  --bmc1_deadlock                         false
% 1.78/0.98  --bmc1_ucm                              false
% 1.78/0.98  --bmc1_add_unsat_core                   none
% 1.78/0.98  --bmc1_unsat_core_children              false
% 1.78/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.78/0.98  --bmc1_out_stat                         full
% 1.78/0.98  --bmc1_ground_init                      false
% 1.78/0.98  --bmc1_pre_inst_next_state              false
% 1.78/0.98  --bmc1_pre_inst_state                   false
% 1.78/0.98  --bmc1_pre_inst_reach_state             false
% 1.78/0.98  --bmc1_out_unsat_core                   false
% 1.78/0.98  --bmc1_aig_witness_out                  false
% 1.78/0.98  --bmc1_verbose                          false
% 1.78/0.98  --bmc1_dump_clauses_tptp                false
% 1.78/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.78/0.98  --bmc1_dump_file                        -
% 1.78/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.78/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.78/0.98  --bmc1_ucm_extend_mode                  1
% 1.78/0.98  --bmc1_ucm_init_mode                    2
% 1.78/0.98  --bmc1_ucm_cone_mode                    none
% 1.78/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.78/0.98  --bmc1_ucm_relax_model                  4
% 1.78/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.78/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.78/0.98  --bmc1_ucm_layered_model                none
% 1.78/0.98  --bmc1_ucm_max_lemma_size               10
% 1.78/0.98  
% 1.78/0.98  ------ AIG Options
% 1.78/0.98  
% 1.78/0.98  --aig_mode                              false
% 1.78/0.98  
% 1.78/0.98  ------ Instantiation Options
% 1.78/0.98  
% 1.78/0.98  --instantiation_flag                    true
% 1.78/0.98  --inst_sos_flag                         false
% 1.78/0.98  --inst_sos_phase                        true
% 1.78/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.78/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.78/0.98  --inst_lit_sel_side                     num_symb
% 1.78/0.98  --inst_solver_per_active                1400
% 1.78/0.98  --inst_solver_calls_frac                1.
% 1.78/0.98  --inst_passive_queue_type               priority_queues
% 1.78/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.78/0.98  --inst_passive_queues_freq              [25;2]
% 1.78/0.98  --inst_dismatching                      true
% 1.78/0.98  --inst_eager_unprocessed_to_passive     true
% 1.78/0.98  --inst_prop_sim_given                   true
% 1.78/0.98  --inst_prop_sim_new                     false
% 1.78/0.98  --inst_subs_new                         false
% 1.78/0.98  --inst_eq_res_simp                      false
% 1.78/0.98  --inst_subs_given                       false
% 1.78/0.98  --inst_orphan_elimination               true
% 1.78/0.98  --inst_learning_loop_flag               true
% 1.78/0.98  --inst_learning_start                   3000
% 1.78/0.98  --inst_learning_factor                  2
% 1.78/0.98  --inst_start_prop_sim_after_learn       3
% 1.78/0.98  --inst_sel_renew                        solver
% 1.78/0.98  --inst_lit_activity_flag                true
% 1.78/0.98  --inst_restr_to_given                   false
% 1.78/0.98  --inst_activity_threshold               500
% 1.78/0.98  --inst_out_proof                        true
% 1.78/0.98  
% 1.78/0.98  ------ Resolution Options
% 1.78/0.98  
% 1.78/0.98  --resolution_flag                       true
% 1.78/0.98  --res_lit_sel                           adaptive
% 1.78/0.98  --res_lit_sel_side                      none
% 1.78/0.98  --res_ordering                          kbo
% 1.78/0.98  --res_to_prop_solver                    active
% 1.78/0.98  --res_prop_simpl_new                    false
% 1.78/0.98  --res_prop_simpl_given                  true
% 1.78/0.98  --res_passive_queue_type                priority_queues
% 1.78/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.78/0.98  --res_passive_queues_freq               [15;5]
% 1.78/0.98  --res_forward_subs                      full
% 1.78/0.98  --res_backward_subs                     full
% 1.78/0.98  --res_forward_subs_resolution           true
% 1.78/0.98  --res_backward_subs_resolution          true
% 1.78/0.98  --res_orphan_elimination                true
% 1.78/0.98  --res_time_limit                        2.
% 1.78/0.98  --res_out_proof                         true
% 1.78/0.98  
% 1.78/0.98  ------ Superposition Options
% 1.78/0.98  
% 1.78/0.98  --superposition_flag                    true
% 1.78/0.98  --sup_passive_queue_type                priority_queues
% 1.78/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.78/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.78/0.98  --demod_completeness_check              fast
% 1.78/0.98  --demod_use_ground                      true
% 1.78/0.98  --sup_to_prop_solver                    passive
% 1.78/0.98  --sup_prop_simpl_new                    true
% 1.78/0.98  --sup_prop_simpl_given                  true
% 1.78/0.98  --sup_fun_splitting                     false
% 1.78/0.98  --sup_smt_interval                      50000
% 1.78/0.98  
% 1.78/0.98  ------ Superposition Simplification Setup
% 1.78/0.98  
% 1.78/0.98  --sup_indices_passive                   []
% 1.78/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.78/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.78/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.78/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.78/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.78/0.98  --sup_full_bw                           [BwDemod]
% 1.78/0.98  --sup_immed_triv                        [TrivRules]
% 1.78/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.78/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.78/0.98  --sup_immed_bw_main                     []
% 1.78/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.78/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.78/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.78/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.78/0.98  
% 1.78/0.98  ------ Combination Options
% 1.78/0.98  
% 1.78/0.98  --comb_res_mult                         3
% 1.78/0.98  --comb_sup_mult                         2
% 1.78/0.98  --comb_inst_mult                        10
% 1.78/0.98  
% 1.78/0.98  ------ Debug Options
% 1.78/0.98  
% 1.78/0.98  --dbg_backtrace                         false
% 1.78/0.98  --dbg_dump_prop_clauses                 false
% 1.78/0.98  --dbg_dump_prop_clauses_file            -
% 1.78/0.98  --dbg_out_stat                          false
% 1.78/0.98  ------ Parsing...
% 1.78/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.78/0.98  
% 1.78/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 1.78/0.98  
% 1.78/0.98  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.78/0.98  
% 1.78/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.78/0.98  ------ Proving...
% 1.78/0.98  ------ Problem Properties 
% 1.78/0.98  
% 1.78/0.98  
% 1.78/0.98  clauses                                 17
% 1.78/0.98  conjectures                             2
% 1.78/0.98  EPR                                     2
% 1.78/0.98  Horn                                    13
% 1.78/0.98  unary                                   2
% 1.78/0.98  binary                                  4
% 1.78/0.98  lits                                    44
% 1.78/0.98  lits eq                                 3
% 1.78/0.98  fd_pure                                 0
% 1.78/0.98  fd_pseudo                               0
% 1.78/0.98  fd_cond                                 0
% 1.78/0.98  fd_pseudo_cond                          0
% 1.78/0.98  AC symbols                              0
% 1.78/0.98  
% 1.78/0.98  ------ Schedule dynamic 5 is on 
% 1.78/0.98  
% 1.78/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.78/0.98  
% 1.78/0.98  
% 1.78/0.98  ------ 
% 1.78/0.98  Current options:
% 1.78/0.98  ------ 
% 1.78/0.98  
% 1.78/0.98  ------ Input Options
% 1.78/0.98  
% 1.78/0.98  --out_options                           all
% 1.78/0.98  --tptp_safe_out                         true
% 1.78/0.98  --problem_path                          ""
% 1.78/0.98  --include_path                          ""
% 1.78/0.98  --clausifier                            res/vclausify_rel
% 1.78/0.98  --clausifier_options                    --mode clausify
% 1.78/0.98  --stdin                                 false
% 1.78/0.98  --stats_out                             all
% 1.78/0.98  
% 1.78/0.98  ------ General Options
% 1.78/0.98  
% 1.78/0.98  --fof                                   false
% 1.78/0.98  --time_out_real                         305.
% 1.78/0.98  --time_out_virtual                      -1.
% 1.78/0.98  --symbol_type_check                     false
% 1.78/0.98  --clausify_out                          false
% 1.78/0.98  --sig_cnt_out                           false
% 1.78/0.98  --trig_cnt_out                          false
% 1.78/0.98  --trig_cnt_out_tolerance                1.
% 1.78/0.98  --trig_cnt_out_sk_spl                   false
% 1.78/0.98  --abstr_cl_out                          false
% 1.78/0.98  
% 1.78/0.98  ------ Global Options
% 1.78/0.98  
% 1.78/0.98  --schedule                              default
% 1.78/0.98  --add_important_lit                     false
% 1.78/0.98  --prop_solver_per_cl                    1000
% 1.78/0.98  --min_unsat_core                        false
% 1.78/0.98  --soft_assumptions                      false
% 1.78/0.98  --soft_lemma_size                       3
% 1.78/0.98  --prop_impl_unit_size                   0
% 1.78/0.98  --prop_impl_unit                        []
% 1.78/0.98  --share_sel_clauses                     true
% 1.78/0.98  --reset_solvers                         false
% 1.78/0.98  --bc_imp_inh                            [conj_cone]
% 1.78/0.98  --conj_cone_tolerance                   3.
% 1.78/0.98  --extra_neg_conj                        none
% 1.78/0.98  --large_theory_mode                     true
% 1.78/0.98  --prolific_symb_bound                   200
% 1.78/0.98  --lt_threshold                          2000
% 1.78/0.98  --clause_weak_htbl                      true
% 1.78/0.98  --gc_record_bc_elim                     false
% 1.78/0.98  
% 1.78/0.98  ------ Preprocessing Options
% 1.78/0.98  
% 1.78/0.98  --preprocessing_flag                    true
% 1.78/0.98  --time_out_prep_mult                    0.1
% 1.78/0.98  --splitting_mode                        input
% 1.78/0.98  --splitting_grd                         true
% 1.78/0.98  --splitting_cvd                         false
% 1.78/0.98  --splitting_cvd_svl                     false
% 1.78/0.98  --splitting_nvd                         32
% 1.78/0.98  --sub_typing                            true
% 1.78/0.98  --prep_gs_sim                           true
% 1.78/0.98  --prep_unflatten                        true
% 1.78/0.98  --prep_res_sim                          true
% 1.78/0.98  --prep_upred                            true
% 1.78/0.98  --prep_sem_filter                       exhaustive
% 1.78/0.98  --prep_sem_filter_out                   false
% 1.78/0.98  --pred_elim                             true
% 1.78/0.98  --res_sim_input                         true
% 1.78/0.98  --eq_ax_congr_red                       true
% 1.78/0.98  --pure_diseq_elim                       true
% 1.78/0.98  --brand_transform                       false
% 1.78/0.98  --non_eq_to_eq                          false
% 1.78/0.98  --prep_def_merge                        true
% 1.78/0.98  --prep_def_merge_prop_impl              false
% 1.78/0.98  --prep_def_merge_mbd                    true
% 1.78/0.98  --prep_def_merge_tr_red                 false
% 1.78/0.98  --prep_def_merge_tr_cl                  false
% 1.78/0.98  --smt_preprocessing                     true
% 1.78/0.98  --smt_ac_axioms                         fast
% 1.78/0.98  --preprocessed_out                      false
% 1.78/0.98  --preprocessed_stats                    false
% 1.78/0.98  
% 1.78/0.98  ------ Abstraction refinement Options
% 1.78/0.98  
% 1.78/0.98  --abstr_ref                             []
% 1.78/0.98  --abstr_ref_prep                        false
% 1.78/0.98  --abstr_ref_until_sat                   false
% 1.78/0.98  --abstr_ref_sig_restrict                funpre
% 1.78/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.78/0.98  --abstr_ref_under                       []
% 1.78/0.98  
% 1.78/0.98  ------ SAT Options
% 1.78/0.98  
% 1.78/0.98  --sat_mode                              false
% 1.78/0.98  --sat_fm_restart_options                ""
% 1.78/0.98  --sat_gr_def                            false
% 1.78/0.98  --sat_epr_types                         true
% 1.78/0.98  --sat_non_cyclic_types                  false
% 1.78/0.98  --sat_finite_models                     false
% 1.78/0.98  --sat_fm_lemmas                         false
% 1.78/0.98  --sat_fm_prep                           false
% 1.78/0.98  --sat_fm_uc_incr                        true
% 1.78/0.98  --sat_out_model                         small
% 1.78/0.98  --sat_out_clauses                       false
% 1.78/0.98  
% 1.78/0.98  ------ QBF Options
% 1.78/0.98  
% 1.78/0.98  --qbf_mode                              false
% 1.78/0.98  --qbf_elim_univ                         false
% 1.78/0.98  --qbf_dom_inst                          none
% 1.78/0.98  --qbf_dom_pre_inst                      false
% 1.78/0.98  --qbf_sk_in                             false
% 1.78/0.98  --qbf_pred_elim                         true
% 1.78/0.98  --qbf_split                             512
% 1.78/0.98  
% 1.78/0.98  ------ BMC1 Options
% 1.78/0.98  
% 1.78/0.98  --bmc1_incremental                      false
% 1.78/0.98  --bmc1_axioms                           reachable_all
% 1.78/0.98  --bmc1_min_bound                        0
% 1.78/0.98  --bmc1_max_bound                        -1
% 1.78/0.98  --bmc1_max_bound_default                -1
% 1.78/0.98  --bmc1_symbol_reachability              true
% 1.78/0.98  --bmc1_property_lemmas                  false
% 1.78/0.98  --bmc1_k_induction                      false
% 1.78/0.98  --bmc1_non_equiv_states                 false
% 1.78/0.98  --bmc1_deadlock                         false
% 1.78/0.98  --bmc1_ucm                              false
% 1.78/0.98  --bmc1_add_unsat_core                   none
% 1.78/0.98  --bmc1_unsat_core_children              false
% 1.78/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.78/0.98  --bmc1_out_stat                         full
% 1.78/0.98  --bmc1_ground_init                      false
% 1.78/0.98  --bmc1_pre_inst_next_state              false
% 1.78/0.98  --bmc1_pre_inst_state                   false
% 1.78/0.98  --bmc1_pre_inst_reach_state             false
% 1.78/0.98  --bmc1_out_unsat_core                   false
% 1.78/0.98  --bmc1_aig_witness_out                  false
% 1.78/0.98  --bmc1_verbose                          false
% 1.78/0.98  --bmc1_dump_clauses_tptp                false
% 1.78/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.78/0.98  --bmc1_dump_file                        -
% 1.78/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.78/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.78/0.98  --bmc1_ucm_extend_mode                  1
% 1.78/0.98  --bmc1_ucm_init_mode                    2
% 1.78/0.98  --bmc1_ucm_cone_mode                    none
% 1.78/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.78/0.98  --bmc1_ucm_relax_model                  4
% 1.78/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.78/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.78/0.98  --bmc1_ucm_layered_model                none
% 1.78/0.98  --bmc1_ucm_max_lemma_size               10
% 1.78/0.98  
% 1.78/0.98  ------ AIG Options
% 1.78/0.98  
% 1.78/0.98  --aig_mode                              false
% 1.78/0.98  
% 1.78/0.98  ------ Instantiation Options
% 1.78/0.98  
% 1.78/0.98  --instantiation_flag                    true
% 1.78/0.98  --inst_sos_flag                         false
% 1.78/0.98  --inst_sos_phase                        true
% 1.78/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.78/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.78/0.98  --inst_lit_sel_side                     none
% 1.78/0.98  --inst_solver_per_active                1400
% 1.78/0.98  --inst_solver_calls_frac                1.
% 1.78/0.98  --inst_passive_queue_type               priority_queues
% 1.78/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.78/0.98  --inst_passive_queues_freq              [25;2]
% 1.78/0.98  --inst_dismatching                      true
% 1.78/0.98  --inst_eager_unprocessed_to_passive     true
% 1.78/0.98  --inst_prop_sim_given                   true
% 1.78/0.98  --inst_prop_sim_new                     false
% 1.78/0.98  --inst_subs_new                         false
% 1.78/0.98  --inst_eq_res_simp                      false
% 1.78/0.98  --inst_subs_given                       false
% 1.78/0.98  --inst_orphan_elimination               true
% 1.78/0.98  --inst_learning_loop_flag               true
% 1.78/0.98  --inst_learning_start                   3000
% 1.78/0.98  --inst_learning_factor                  2
% 1.78/0.98  --inst_start_prop_sim_after_learn       3
% 1.78/0.98  --inst_sel_renew                        solver
% 1.78/0.98  --inst_lit_activity_flag                true
% 1.78/0.98  --inst_restr_to_given                   false
% 1.78/0.98  --inst_activity_threshold               500
% 1.78/0.98  --inst_out_proof                        true
% 1.78/0.98  
% 1.78/0.98  ------ Resolution Options
% 1.78/0.98  
% 1.78/0.98  --resolution_flag                       false
% 1.78/0.98  --res_lit_sel                           adaptive
% 1.78/0.98  --res_lit_sel_side                      none
% 1.78/0.98  --res_ordering                          kbo
% 1.78/0.98  --res_to_prop_solver                    active
% 1.78/0.98  --res_prop_simpl_new                    false
% 1.78/0.98  --res_prop_simpl_given                  true
% 1.78/0.98  --res_passive_queue_type                priority_queues
% 1.78/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.78/0.98  --res_passive_queues_freq               [15;5]
% 1.78/0.98  --res_forward_subs                      full
% 1.78/0.98  --res_backward_subs                     full
% 1.78/0.98  --res_forward_subs_resolution           true
% 1.78/0.98  --res_backward_subs_resolution          true
% 1.78/0.98  --res_orphan_elimination                true
% 1.78/0.98  --res_time_limit                        2.
% 1.78/0.98  --res_out_proof                         true
% 1.78/0.98  
% 1.78/0.98  ------ Superposition Options
% 1.78/0.98  
% 1.78/0.98  --superposition_flag                    true
% 1.78/0.98  --sup_passive_queue_type                priority_queues
% 1.78/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.78/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.78/0.98  --demod_completeness_check              fast
% 1.78/0.98  --demod_use_ground                      true
% 1.78/0.98  --sup_to_prop_solver                    passive
% 1.78/0.98  --sup_prop_simpl_new                    true
% 1.78/0.98  --sup_prop_simpl_given                  true
% 1.78/0.98  --sup_fun_splitting                     false
% 1.78/0.98  --sup_smt_interval                      50000
% 1.78/0.98  
% 1.78/0.98  ------ Superposition Simplification Setup
% 1.78/0.98  
% 1.78/0.98  --sup_indices_passive                   []
% 1.78/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.78/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.78/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.78/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.78/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.78/0.98  --sup_full_bw                           [BwDemod]
% 1.78/0.98  --sup_immed_triv                        [TrivRules]
% 1.78/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.78/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.78/0.98  --sup_immed_bw_main                     []
% 1.78/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.78/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.78/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.78/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.78/0.98  
% 1.78/0.98  ------ Combination Options
% 1.78/0.98  
% 1.78/0.98  --comb_res_mult                         3
% 1.78/0.98  --comb_sup_mult                         2
% 1.78/0.98  --comb_inst_mult                        10
% 1.78/0.98  
% 1.78/0.98  ------ Debug Options
% 1.78/0.98  
% 1.78/0.98  --dbg_backtrace                         false
% 1.78/0.98  --dbg_dump_prop_clauses                 false
% 1.78/0.98  --dbg_dump_prop_clauses_file            -
% 1.78/0.98  --dbg_out_stat                          false
% 1.78/0.98  
% 1.78/0.98  
% 1.78/0.98  
% 1.78/0.98  
% 1.78/0.98  ------ Proving...
% 1.78/0.98  
% 1.78/0.98  
% 1.78/0.98  % SZS status Theorem for theBenchmark.p
% 1.78/0.98  
% 1.78/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 1.78/0.98  
% 1.78/0.98  fof(f8,axiom,(
% 1.78/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 1.78/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.78/0.98  
% 1.78/0.98  fof(f22,plain,(
% 1.78/0.98    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.78/0.98    inference(ennf_transformation,[],[f8])).
% 1.78/0.98  
% 1.78/0.98  fof(f23,plain,(
% 1.78/0.98    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.78/0.98    inference(flattening,[],[f22])).
% 1.78/0.98  
% 1.78/0.98  fof(f41,plain,(
% 1.78/0.98    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.78/0.98    inference(nnf_transformation,[],[f23])).
% 1.78/0.98  
% 1.78/0.98  fof(f60,plain,(
% 1.78/0.98    ( ! [X2,X0,X1] : (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.78/0.98    inference(cnf_transformation,[],[f41])).
% 1.78/0.98  
% 1.78/0.98  fof(f10,axiom,(
% 1.78/0.98    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.78/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.78/0.98  
% 1.78/0.98  fof(f26,plain,(
% 1.78/0.98    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.78/0.98    inference(ennf_transformation,[],[f10])).
% 1.78/0.98  
% 1.78/0.98  fof(f27,plain,(
% 1.78/0.98    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.78/0.98    inference(flattening,[],[f26])).
% 1.78/0.98  
% 1.78/0.98  fof(f64,plain,(
% 1.78/0.98    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.78/0.98    inference(cnf_transformation,[],[f27])).
% 1.78/0.98  
% 1.78/0.98  fof(f14,conjecture,(
% 1.78/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) <=> m1_connsp_2(X2,X0,X1)))))),
% 1.78/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.78/0.98  
% 1.78/0.98  fof(f15,negated_conjecture,(
% 1.78/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) <=> m1_connsp_2(X2,X0,X1)))))),
% 1.78/0.98    inference(negated_conjecture,[],[f14])).
% 1.78/0.98  
% 1.78/0.98  fof(f34,plain,(
% 1.78/0.98    ? [X0] : (? [X1] : (? [X2] : ((m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) <~> m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.78/0.98    inference(ennf_transformation,[],[f15])).
% 1.78/0.98  
% 1.78/0.98  fof(f35,plain,(
% 1.78/0.98    ? [X0] : (? [X1] : (? [X2] : ((m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) <~> m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.78/0.98    inference(flattening,[],[f34])).
% 1.78/0.98  
% 1.78/0.98  fof(f45,plain,(
% 1.78/0.98    ? [X0] : (? [X1] : (? [X2] : (((~m1_connsp_2(X2,X0,X1) | ~m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & (m1_connsp_2(X2,X0,X1) | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.78/0.98    inference(nnf_transformation,[],[f35])).
% 1.78/0.98  
% 1.78/0.98  fof(f46,plain,(
% 1.78/0.98    ? [X0] : (? [X1] : (? [X2] : ((~m1_connsp_2(X2,X0,X1) | ~m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & (m1_connsp_2(X2,X0,X1) | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.78/0.98    inference(flattening,[],[f45])).
% 1.78/0.98  
% 1.78/0.98  fof(f49,plain,(
% 1.78/0.98    ( ! [X0,X1] : (? [X2] : ((~m1_connsp_2(X2,X0,X1) | ~m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & (m1_connsp_2(X2,X0,X1) | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => ((~m1_connsp_2(sK4,X0,X1) | ~m2_connsp_2(sK4,X0,k6_domain_1(u1_struct_0(X0),X1))) & (m1_connsp_2(sK4,X0,X1) | m2_connsp_2(sK4,X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 1.78/0.98    introduced(choice_axiom,[])).
% 1.78/0.98  
% 1.78/0.98  fof(f48,plain,(
% 1.78/0.98    ( ! [X0] : (? [X1] : (? [X2] : ((~m1_connsp_2(X2,X0,X1) | ~m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & (m1_connsp_2(X2,X0,X1) | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : ((~m1_connsp_2(X2,X0,sK3) | ~m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),sK3))) & (m1_connsp_2(X2,X0,sK3) | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),sK3))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK3,u1_struct_0(X0)))) )),
% 1.78/0.98    introduced(choice_axiom,[])).
% 1.78/0.98  
% 1.78/0.98  fof(f47,plain,(
% 1.78/0.98    ? [X0] : (? [X1] : (? [X2] : ((~m1_connsp_2(X2,X0,X1) | ~m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & (m1_connsp_2(X2,X0,X1) | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~m1_connsp_2(X2,sK2,X1) | ~m2_connsp_2(X2,sK2,k6_domain_1(u1_struct_0(sK2),X1))) & (m1_connsp_2(X2,sK2,X1) | m2_connsp_2(X2,sK2,k6_domain_1(u1_struct_0(sK2),X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(X1,u1_struct_0(sK2))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 1.78/0.98    introduced(choice_axiom,[])).
% 1.78/0.98  
% 1.78/0.98  fof(f50,plain,(
% 1.78/0.98    (((~m1_connsp_2(sK4,sK2,sK3) | ~m2_connsp_2(sK4,sK2,k6_domain_1(u1_struct_0(sK2),sK3))) & (m1_connsp_2(sK4,sK2,sK3) | m2_connsp_2(sK4,sK2,k6_domain_1(u1_struct_0(sK2),sK3))) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(sK3,u1_struct_0(sK2))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 1.78/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f46,f49,f48,f47])).
% 1.78/0.98  
% 1.78/0.98  fof(f68,plain,(
% 1.78/0.98    ~v2_struct_0(sK2)),
% 1.78/0.98    inference(cnf_transformation,[],[f50])).
% 1.78/0.98  
% 1.78/0.98  fof(f69,plain,(
% 1.78/0.98    v2_pre_topc(sK2)),
% 1.78/0.98    inference(cnf_transformation,[],[f50])).
% 1.78/0.98  
% 1.78/0.98  fof(f70,plain,(
% 1.78/0.98    l1_pre_topc(sK2)),
% 1.78/0.98    inference(cnf_transformation,[],[f50])).
% 1.78/0.98  
% 1.78/0.98  fof(f3,axiom,(
% 1.78/0.98    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.78/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.78/0.98  
% 1.78/0.98  fof(f40,plain,(
% 1.78/0.98    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 1.78/0.98    inference(nnf_transformation,[],[f3])).
% 1.78/0.98  
% 1.78/0.98  fof(f55,plain,(
% 1.78/0.98    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.78/0.98    inference(cnf_transformation,[],[f40])).
% 1.78/0.98  
% 1.78/0.98  fof(f2,axiom,(
% 1.78/0.98    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.78/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.78/0.98  
% 1.78/0.98  fof(f53,plain,(
% 1.78/0.98    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.78/0.98    inference(cnf_transformation,[],[f2])).
% 1.78/0.98  
% 1.78/0.98  fof(f75,plain,(
% 1.78/0.98    ( ! [X0,X1] : (r1_tarski(k2_tarski(X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.78/0.98    inference(definition_unfolding,[],[f55,f53])).
% 1.78/0.98  
% 1.78/0.98  fof(f74,plain,(
% 1.78/0.98    ~m1_connsp_2(sK4,sK2,sK3) | ~m2_connsp_2(sK4,sK2,k6_domain_1(u1_struct_0(sK2),sK3))),
% 1.78/0.98    inference(cnf_transformation,[],[f50])).
% 1.78/0.98  
% 1.78/0.98  fof(f9,axiom,(
% 1.78/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 1.78/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.78/0.98  
% 1.78/0.98  fof(f24,plain,(
% 1.78/0.98    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.78/0.98    inference(ennf_transformation,[],[f9])).
% 1.78/0.98  
% 1.78/0.98  fof(f25,plain,(
% 1.78/0.98    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.78/0.98    inference(flattening,[],[f24])).
% 1.78/0.98  
% 1.78/0.98  fof(f42,plain,(
% 1.78/0.98    ! [X0] : (! [X1] : (! [X2] : (((m2_connsp_2(X2,X0,X1) | ~r1_tarski(X1,k1_tops_1(X0,X2))) & (r1_tarski(X1,k1_tops_1(X0,X2)) | ~m2_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.78/0.98    inference(nnf_transformation,[],[f25])).
% 1.78/0.98  
% 1.78/0.98  fof(f63,plain,(
% 1.78/0.98    ( ! [X2,X0,X1] : (m2_connsp_2(X2,X0,X1) | ~r1_tarski(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.78/0.98    inference(cnf_transformation,[],[f42])).
% 1.78/0.98  
% 1.78/0.98  fof(f72,plain,(
% 1.78/0.98    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.78/0.98    inference(cnf_transformation,[],[f50])).
% 1.78/0.98  
% 1.78/0.98  fof(f71,plain,(
% 1.78/0.98    m1_subset_1(sK3,u1_struct_0(sK2))),
% 1.78/0.98    inference(cnf_transformation,[],[f50])).
% 1.78/0.98  
% 1.78/0.98  fof(f12,axiom,(
% 1.78/0.98    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X2] : m1_connsp_2(X2,X0,X1))),
% 1.78/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.78/0.98  
% 1.78/0.98  fof(f30,plain,(
% 1.78/0.98    ! [X0,X1] : (? [X2] : m1_connsp_2(X2,X0,X1) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.78/0.98    inference(ennf_transformation,[],[f12])).
% 1.78/0.98  
% 1.78/0.98  fof(f31,plain,(
% 1.78/0.98    ! [X0,X1] : (? [X2] : m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.78/0.98    inference(flattening,[],[f30])).
% 1.78/0.98  
% 1.78/0.98  fof(f43,plain,(
% 1.78/0.98    ! [X1,X0] : (? [X2] : m1_connsp_2(X2,X0,X1) => m1_connsp_2(sK1(X0,X1),X0,X1))),
% 1.78/0.98    introduced(choice_axiom,[])).
% 1.78/0.98  
% 1.78/0.98  fof(f44,plain,(
% 1.78/0.98    ! [X0,X1] : (m1_connsp_2(sK1(X0,X1),X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.78/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f43])).
% 1.78/0.98  
% 1.78/0.98  fof(f66,plain,(
% 1.78/0.98    ( ! [X0,X1] : (m1_connsp_2(sK1(X0,X1),X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.78/0.98    inference(cnf_transformation,[],[f44])).
% 1.78/0.98  
% 1.78/0.98  fof(f54,plain,(
% 1.78/0.98    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 1.78/0.98    inference(cnf_transformation,[],[f40])).
% 1.78/0.98  
% 1.78/0.98  fof(f76,plain,(
% 1.78/0.98    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k2_tarski(X0,X0),X1)) )),
% 1.78/0.98    inference(definition_unfolding,[],[f54,f53])).
% 1.78/0.98  
% 1.78/0.98  fof(f73,plain,(
% 1.78/0.98    m1_connsp_2(sK4,sK2,sK3) | m2_connsp_2(sK4,sK2,k6_domain_1(u1_struct_0(sK2),sK3))),
% 1.78/0.98    inference(cnf_transformation,[],[f50])).
% 1.78/0.98  
% 1.78/0.98  fof(f62,plain,(
% 1.78/0.98    ( ! [X2,X0,X1] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~m2_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.78/0.98    inference(cnf_transformation,[],[f42])).
% 1.78/0.98  
% 1.78/0.98  fof(f11,axiom,(
% 1.78/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X2] : (m2_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.78/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.78/0.98  
% 1.78/0.98  fof(f28,plain,(
% 1.78/0.98    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.78/0.98    inference(ennf_transformation,[],[f11])).
% 1.78/0.98  
% 1.78/0.98  fof(f29,plain,(
% 1.78/0.98    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.78/0.98    inference(flattening,[],[f28])).
% 1.78/0.98  
% 1.78/0.98  fof(f65,plain,(
% 1.78/0.98    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.78/0.98    inference(cnf_transformation,[],[f29])).
% 1.78/0.98  
% 1.78/0.98  fof(f13,axiom,(
% 1.78/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (m1_connsp_2(X1,X0,X2) => r2_hidden(X2,X1)))))),
% 1.78/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.78/0.98  
% 1.78/0.98  fof(f32,plain,(
% 1.78/0.98    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.78/0.98    inference(ennf_transformation,[],[f13])).
% 1.78/0.98  
% 1.78/0.98  fof(f33,plain,(
% 1.78/0.98    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.78/0.98    inference(flattening,[],[f32])).
% 1.78/0.98  
% 1.78/0.98  fof(f67,plain,(
% 1.78/0.98    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.78/0.98    inference(cnf_transformation,[],[f33])).
% 1.78/0.98  
% 1.78/0.98  fof(f7,axiom,(
% 1.78/0.98    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 1.78/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.78/0.98  
% 1.78/0.98  fof(f20,plain,(
% 1.78/0.98    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.78/0.98    inference(ennf_transformation,[],[f7])).
% 1.78/0.98  
% 1.78/0.98  fof(f21,plain,(
% 1.78/0.98    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.78/0.98    inference(flattening,[],[f20])).
% 1.78/0.98  
% 1.78/0.98  fof(f59,plain,(
% 1.78/0.98    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.78/0.98    inference(cnf_transformation,[],[f21])).
% 1.78/0.98  
% 1.78/0.98  fof(f78,plain,(
% 1.78/0.98    ( ! [X0,X1] : (k2_tarski(X1,X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.78/0.98    inference(definition_unfolding,[],[f59,f53])).
% 1.78/0.98  
% 1.78/0.98  fof(f4,axiom,(
% 1.78/0.98    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 1.78/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.78/0.98  
% 1.78/0.98  fof(f16,plain,(
% 1.78/0.98    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 1.78/0.98    inference(ennf_transformation,[],[f4])).
% 1.78/0.98  
% 1.78/0.98  fof(f56,plain,(
% 1.78/0.98    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 1.78/0.98    inference(cnf_transformation,[],[f16])).
% 1.78/0.98  
% 1.78/0.98  fof(f77,plain,(
% 1.78/0.98    ( ! [X0,X1] : (m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 1.78/0.98    inference(definition_unfolding,[],[f56,f53])).
% 1.78/0.98  
% 1.78/0.98  fof(f1,axiom,(
% 1.78/0.98    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.78/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.78/0.98  
% 1.78/0.98  fof(f36,plain,(
% 1.78/0.98    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.78/0.98    inference(nnf_transformation,[],[f1])).
% 1.78/0.98  
% 1.78/0.98  fof(f37,plain,(
% 1.78/0.98    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.78/0.98    inference(rectify,[],[f36])).
% 1.78/0.98  
% 1.78/0.98  fof(f38,plain,(
% 1.78/0.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 1.78/0.98    introduced(choice_axiom,[])).
% 1.78/0.98  
% 1.78/0.98  fof(f39,plain,(
% 1.78/0.98    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.78/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).
% 1.78/0.98  
% 1.78/0.98  fof(f51,plain,(
% 1.78/0.98    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.78/0.98    inference(cnf_transformation,[],[f39])).
% 1.78/0.98  
% 1.78/0.98  fof(f6,axiom,(
% 1.78/0.98    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.78/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.78/0.98  
% 1.78/0.98  fof(f18,plain,(
% 1.78/0.98    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.78/0.98    inference(ennf_transformation,[],[f6])).
% 1.78/0.98  
% 1.78/0.98  fof(f19,plain,(
% 1.78/0.98    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.78/0.98    inference(flattening,[],[f18])).
% 1.78/0.98  
% 1.78/0.98  fof(f58,plain,(
% 1.78/0.98    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 1.78/0.98    inference(cnf_transformation,[],[f19])).
% 1.78/0.98  
% 1.78/0.98  fof(f5,axiom,(
% 1.78/0.98    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 1.78/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.78/0.98  
% 1.78/0.98  fof(f17,plain,(
% 1.78/0.98    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 1.78/0.98    inference(ennf_transformation,[],[f5])).
% 1.78/0.98  
% 1.78/0.98  fof(f57,plain,(
% 1.78/0.98    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 1.78/0.98    inference(cnf_transformation,[],[f17])).
% 1.78/0.98  
% 1.78/0.98  fof(f61,plain,(
% 1.78/0.98    ( ! [X2,X0,X1] : (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.78/0.98    inference(cnf_transformation,[],[f41])).
% 1.78/0.98  
% 1.78/0.98  cnf(c_9,plain,
% 1.78/0.98      ( ~ m1_connsp_2(X0,X1,X2)
% 1.78/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.78/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.78/0.98      | r2_hidden(X2,k1_tops_1(X1,X0))
% 1.78/0.98      | v2_struct_0(X1)
% 1.78/0.98      | ~ v2_pre_topc(X1)
% 1.78/0.98      | ~ l1_pre_topc(X1) ),
% 1.78/0.98      inference(cnf_transformation,[],[f60]) ).
% 1.78/0.98  
% 1.78/0.98  cnf(c_12,plain,
% 1.78/0.98      ( ~ m1_connsp_2(X0,X1,X2)
% 1.78/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.78/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.78/0.98      | v2_struct_0(X1)
% 1.78/0.98      | ~ v2_pre_topc(X1)
% 1.78/0.98      | ~ l1_pre_topc(X1) ),
% 1.78/0.98      inference(cnf_transformation,[],[f64]) ).
% 1.78/0.98  
% 1.78/0.98  cnf(c_144,plain,
% 1.78/0.98      ( ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.78/0.98      | ~ m1_connsp_2(X0,X1,X2)
% 1.78/0.98      | r2_hidden(X2,k1_tops_1(X1,X0))
% 1.78/0.98      | v2_struct_0(X1)
% 1.78/0.98      | ~ v2_pre_topc(X1)
% 1.78/0.98      | ~ l1_pre_topc(X1) ),
% 1.78/0.98      inference(global_propositional_subsumption,
% 1.78/0.98                [status(thm)],
% 1.78/0.98                [c_9,c_12]) ).
% 1.78/0.98  
% 1.78/0.98  cnf(c_145,plain,
% 1.78/0.98      ( ~ m1_connsp_2(X0,X1,X2)
% 1.78/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.78/0.98      | r2_hidden(X2,k1_tops_1(X1,X0))
% 1.78/0.98      | v2_struct_0(X1)
% 1.78/0.98      | ~ v2_pre_topc(X1)
% 1.78/0.98      | ~ l1_pre_topc(X1) ),
% 1.78/0.98      inference(renaming,[status(thm)],[c_144]) ).
% 1.78/0.98  
% 1.78/0.98  cnf(c_22,negated_conjecture,
% 1.78/0.98      ( ~ v2_struct_0(sK2) ),
% 1.78/0.98      inference(cnf_transformation,[],[f68]) ).
% 1.78/0.98  
% 1.78/0.98  cnf(c_402,plain,
% 1.78/0.98      ( ~ m1_connsp_2(X0,X1,X2)
% 1.78/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.78/0.98      | r2_hidden(X2,k1_tops_1(X1,X0))
% 1.78/0.98      | ~ v2_pre_topc(X1)
% 1.78/0.98      | ~ l1_pre_topc(X1)
% 1.78/0.98      | sK2 != X1 ),
% 1.78/0.98      inference(resolution_lifted,[status(thm)],[c_145,c_22]) ).
% 1.78/0.98  
% 1.78/0.98  cnf(c_403,plain,
% 1.78/0.98      ( ~ m1_connsp_2(X0,sK2,X1)
% 1.78/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.78/0.98      | r2_hidden(X1,k1_tops_1(sK2,X0))
% 1.78/0.98      | ~ v2_pre_topc(sK2)
% 1.78/0.98      | ~ l1_pre_topc(sK2) ),
% 1.78/0.98      inference(unflattening,[status(thm)],[c_402]) ).
% 1.78/0.98  
% 1.78/0.98  cnf(c_21,negated_conjecture,
% 1.78/0.98      ( v2_pre_topc(sK2) ),
% 1.78/0.98      inference(cnf_transformation,[],[f69]) ).
% 1.78/0.98  
% 1.78/0.98  cnf(c_20,negated_conjecture,
% 1.78/0.98      ( l1_pre_topc(sK2) ),
% 1.78/0.98      inference(cnf_transformation,[],[f70]) ).
% 1.78/0.98  
% 1.78/0.98  cnf(c_407,plain,
% 1.78/0.98      ( ~ m1_connsp_2(X0,sK2,X1)
% 1.78/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.78/0.98      | r2_hidden(X1,k1_tops_1(sK2,X0)) ),
% 1.78/0.98      inference(global_propositional_subsumption,
% 1.78/0.98                [status(thm)],
% 1.78/0.98                [c_403,c_21,c_20]) ).
% 1.78/0.98  
% 1.78/0.98  cnf(c_1893,plain,
% 1.78/0.98      ( ~ m1_connsp_2(X0_47,sK2,X1_47)
% 1.78/0.98      | ~ m1_subset_1(X1_47,u1_struct_0(sK2))
% 1.78/0.98      | r2_hidden(X1_47,k1_tops_1(sK2,X0_47)) ),
% 1.78/0.98      inference(subtyping,[status(esa)],[c_407]) ).
% 1.78/0.98  
% 1.78/0.98  cnf(c_2242,plain,
% 1.78/0.98      ( m1_connsp_2(X0_47,sK2,X1_47) != iProver_top
% 1.78/0.98      | m1_subset_1(X1_47,u1_struct_0(sK2)) != iProver_top
% 1.78/0.98      | r2_hidden(X1_47,k1_tops_1(sK2,X0_47)) = iProver_top ),
% 1.78/0.98      inference(predicate_to_equality,[status(thm)],[c_1893]) ).
% 1.78/0.98  
% 1.78/0.98  cnf(c_2,plain,
% 1.78/0.98      ( r1_tarski(k2_tarski(X0,X0),X1) | ~ r2_hidden(X0,X1) ),
% 1.78/0.98      inference(cnf_transformation,[],[f75]) ).
% 1.78/0.98  
% 1.78/0.98  cnf(c_191,plain,
% 1.78/0.98      ( ~ r2_hidden(X0,X1) | r1_tarski(k2_tarski(X0,X0),X1) ),
% 1.78/0.98      inference(prop_impl,[status(thm)],[c_2]) ).
% 1.78/0.98  
% 1.78/0.98  cnf(c_192,plain,
% 1.78/0.98      ( r1_tarski(k2_tarski(X0,X0),X1) | ~ r2_hidden(X0,X1) ),
% 1.78/0.98      inference(renaming,[status(thm)],[c_191]) ).
% 1.78/0.98  
% 1.78/0.98  cnf(c_16,negated_conjecture,
% 1.78/0.98      ( ~ m2_connsp_2(sK4,sK2,k6_domain_1(u1_struct_0(sK2),sK3))
% 1.78/0.98      | ~ m1_connsp_2(sK4,sK2,sK3) ),
% 1.78/0.98      inference(cnf_transformation,[],[f74]) ).
% 1.78/0.98  
% 1.78/0.98  cnf(c_193,plain,
% 1.78/0.98      ( ~ m1_connsp_2(sK4,sK2,sK3)
% 1.78/0.98      | ~ m2_connsp_2(sK4,sK2,k6_domain_1(u1_struct_0(sK2),sK3)) ),
% 1.78/0.98      inference(prop_impl,[status(thm)],[c_16]) ).
% 1.78/0.98  
% 1.78/0.98  cnf(c_194,plain,
% 1.78/0.98      ( ~ m2_connsp_2(sK4,sK2,k6_domain_1(u1_struct_0(sK2),sK3))
% 1.78/0.98      | ~ m1_connsp_2(sK4,sK2,sK3) ),
% 1.78/0.98      inference(renaming,[status(thm)],[c_193]) ).
% 1.78/0.98  
% 1.78/0.98  cnf(c_10,plain,
% 1.78/0.98      ( m2_connsp_2(X0,X1,X2)
% 1.78/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.78/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.78/0.98      | ~ r1_tarski(X2,k1_tops_1(X1,X0))
% 1.78/0.98      | ~ v2_pre_topc(X1)
% 1.78/0.98      | ~ l1_pre_topc(X1) ),
% 1.78/0.98      inference(cnf_transformation,[],[f63]) ).
% 1.78/0.98  
% 1.78/0.98  cnf(c_547,plain,
% 1.78/0.98      ( m2_connsp_2(X0,X1,X2)
% 1.78/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.78/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.78/0.98      | ~ r1_tarski(X2,k1_tops_1(X1,X0))
% 1.78/0.98      | ~ v2_pre_topc(X1)
% 1.78/0.98      | sK2 != X1 ),
% 1.78/0.98      inference(resolution_lifted,[status(thm)],[c_10,c_20]) ).
% 1.78/0.98  
% 1.78/0.98  cnf(c_548,plain,
% 1.78/0.98      ( m2_connsp_2(X0,sK2,X1)
% 1.78/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.78/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.78/0.98      | ~ r1_tarski(X1,k1_tops_1(sK2,X0))
% 1.78/0.98      | ~ v2_pre_topc(sK2) ),
% 1.78/0.98      inference(unflattening,[status(thm)],[c_547]) ).
% 1.78/0.98  
% 1.78/0.98  cnf(c_552,plain,
% 1.78/0.98      ( ~ r1_tarski(X1,k1_tops_1(sK2,X0))
% 1.78/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.78/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.78/0.98      | m2_connsp_2(X0,sK2,X1) ),
% 1.78/0.98      inference(global_propositional_subsumption,
% 1.78/0.98                [status(thm)],
% 1.78/0.98                [c_548,c_21]) ).
% 1.78/0.98  
% 1.78/0.98  cnf(c_553,plain,
% 1.78/0.98      ( m2_connsp_2(X0,sK2,X1)
% 1.78/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.78/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.78/0.98      | ~ r1_tarski(X1,k1_tops_1(sK2,X0)) ),
% 1.78/0.98      inference(renaming,[status(thm)],[c_552]) ).
% 1.78/0.98  
% 1.78/0.98  cnf(c_644,plain,
% 1.78/0.98      ( ~ m1_connsp_2(sK4,sK2,sK3)
% 1.78/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.78/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.78/0.98      | ~ r1_tarski(X1,k1_tops_1(sK2,X0))
% 1.78/0.98      | k6_domain_1(u1_struct_0(sK2),sK3) != X1
% 1.78/0.98      | sK2 != sK2
% 1.78/0.98      | sK4 != X0 ),
% 1.78/0.98      inference(resolution_lifted,[status(thm)],[c_194,c_553]) ).
% 1.78/0.98  
% 1.78/0.98  cnf(c_645,plain,
% 1.78/0.98      ( ~ m1_connsp_2(sK4,sK2,sK3)
% 1.78/0.98      | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.78/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.78/0.98      | ~ r1_tarski(k6_domain_1(u1_struct_0(sK2),sK3),k1_tops_1(sK2,sK4)) ),
% 1.78/0.98      inference(unflattening,[status(thm)],[c_644]) ).
% 1.78/0.98  
% 1.78/0.98  cnf(c_18,negated_conjecture,
% 1.78/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 1.78/0.98      inference(cnf_transformation,[],[f72]) ).
% 1.78/0.98  
% 1.78/0.98  cnf(c_647,plain,
% 1.78/0.98      ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.78/0.98      | ~ m1_connsp_2(sK4,sK2,sK3)
% 1.78/0.98      | ~ r1_tarski(k6_domain_1(u1_struct_0(sK2),sK3),k1_tops_1(sK2,sK4)) ),
% 1.78/0.98      inference(global_propositional_subsumption,
% 1.78/0.98                [status(thm)],
% 1.78/0.98                [c_645,c_18]) ).
% 1.78/0.98  
% 1.78/0.98  cnf(c_648,plain,
% 1.78/0.98      ( ~ m1_connsp_2(sK4,sK2,sK3)
% 1.78/0.98      | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.78/0.98      | ~ r1_tarski(k6_domain_1(u1_struct_0(sK2),sK3),k1_tops_1(sK2,sK4)) ),
% 1.78/0.98      inference(renaming,[status(thm)],[c_647]) ).
% 1.78/0.98  
% 1.78/0.98  cnf(c_671,plain,
% 1.78/0.98      ( ~ m1_connsp_2(sK4,sK2,sK3)
% 1.78/0.98      | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.78/0.98      | ~ r2_hidden(X0,X1)
% 1.78/0.98      | k1_tops_1(sK2,sK4) != X1
% 1.78/0.98      | k6_domain_1(u1_struct_0(sK2),sK3) != k2_tarski(X0,X0) ),
% 1.78/0.98      inference(resolution_lifted,[status(thm)],[c_192,c_648]) ).
% 1.78/0.98  
% 1.78/0.98  cnf(c_672,plain,
% 1.78/0.98      ( ~ m1_connsp_2(sK4,sK2,sK3)
% 1.78/0.98      | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.78/0.98      | ~ r2_hidden(X0,k1_tops_1(sK2,sK4))
% 1.78/0.98      | k6_domain_1(u1_struct_0(sK2),sK3) != k2_tarski(X0,X0) ),
% 1.78/0.98      inference(unflattening,[status(thm)],[c_671]) ).
% 1.78/0.98  
% 1.78/0.98  cnf(c_1889,plain,
% 1.78/0.98      ( ~ m1_connsp_2(sK4,sK2,sK3)
% 1.78/0.98      | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.78/0.98      | ~ r2_hidden(X0_47,k1_tops_1(sK2,sK4))
% 1.78/0.98      | k6_domain_1(u1_struct_0(sK2),sK3) != k2_tarski(X0_47,X0_47) ),
% 1.78/0.98      inference(subtyping,[status(esa)],[c_672]) ).
% 1.78/0.98  
% 1.78/0.98  cnf(c_1903,plain,
% 1.78/0.98      ( ~ r2_hidden(X0_47,k1_tops_1(sK2,sK4))
% 1.78/0.98      | k6_domain_1(u1_struct_0(sK2),sK3) != k2_tarski(X0_47,X0_47)
% 1.78/0.98      | ~ sP0_iProver_split ),
% 1.78/0.98      inference(splitting,
% 1.78/0.98                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 1.78/0.98                [c_1889]) ).
% 1.78/0.98  
% 1.78/0.98  cnf(c_2247,plain,
% 1.78/0.98      ( k6_domain_1(u1_struct_0(sK2),sK3) != k2_tarski(X0_47,X0_47)
% 1.78/0.98      | r2_hidden(X0_47,k1_tops_1(sK2,sK4)) != iProver_top
% 1.78/0.98      | sP0_iProver_split != iProver_top ),
% 1.78/0.98      inference(predicate_to_equality,[status(thm)],[c_1903]) ).
% 1.78/0.98  
% 1.78/0.98  cnf(c_19,negated_conjecture,
% 1.78/0.98      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 1.78/0.98      inference(cnf_transformation,[],[f71]) ).
% 1.78/0.98  
% 1.78/0.98  cnf(c_26,plain,
% 1.78/0.98      ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
% 1.78/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 1.78/0.98  
% 1.78/0.98  cnf(c_14,plain,
% 1.78/0.98      ( m1_connsp_2(sK1(X0,X1),X0,X1)
% 1.78/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.78/0.98      | v2_struct_0(X0)
% 1.78/0.98      | ~ v2_pre_topc(X0)
% 1.78/0.98      | ~ l1_pre_topc(X0) ),
% 1.78/0.98      inference(cnf_transformation,[],[f66]) ).
% 1.78/0.98  
% 1.78/0.98  cnf(c_384,plain,
% 1.78/0.98      ( m1_connsp_2(sK1(X0,X1),X0,X1)
% 1.78/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.78/0.98      | ~ v2_pre_topc(X0)
% 1.78/0.98      | ~ l1_pre_topc(X0)
% 1.78/0.98      | sK2 != X0 ),
% 1.78/0.98      inference(resolution_lifted,[status(thm)],[c_14,c_22]) ).
% 1.78/0.98  
% 1.78/0.98  cnf(c_385,plain,
% 1.78/0.98      ( m1_connsp_2(sK1(sK2,X0),sK2,X0)
% 1.78/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.78/0.98      | ~ v2_pre_topc(sK2)
% 1.78/0.98      | ~ l1_pre_topc(sK2) ),
% 1.78/0.98      inference(unflattening,[status(thm)],[c_384]) ).
% 1.78/0.98  
% 1.78/0.98  cnf(c_389,plain,
% 1.78/0.98      ( m1_connsp_2(sK1(sK2,X0),sK2,X0)
% 1.78/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 1.78/0.98      inference(global_propositional_subsumption,
% 1.78/0.98                [status(thm)],
% 1.78/0.98                [c_385,c_21,c_20]) ).
% 1.78/0.98  
% 1.78/0.98  cnf(c_1894,plain,
% 1.78/0.98      ( m1_connsp_2(sK1(sK2,X0_47),sK2,X0_47)
% 1.78/0.98      | ~ m1_subset_1(X0_47,u1_struct_0(sK2)) ),
% 1.78/0.98      inference(subtyping,[status(esa)],[c_389]) ).
% 1.78/0.98  
% 1.78/0.98  cnf(c_1943,plain,
% 1.78/0.98      ( m1_connsp_2(sK1(sK2,sK3),sK2,sK3)
% 1.78/0.98      | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 1.78/0.98      inference(instantiation,[status(thm)],[c_1894]) ).
% 1.78/0.98  
% 1.78/0.98  cnf(c_1942,plain,
% 1.78/0.98      ( m1_connsp_2(sK1(sK2,X0_47),sK2,X0_47) = iProver_top
% 1.78/0.98      | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top ),
% 1.78/0.98      inference(predicate_to_equality,[status(thm)],[c_1894]) ).
% 1.78/0.98  
% 1.78/0.98  cnf(c_1944,plain,
% 1.78/0.98      ( m1_connsp_2(sK1(sK2,sK3),sK2,sK3) = iProver_top
% 1.78/0.98      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 1.78/0.98      inference(instantiation,[status(thm)],[c_1942]) ).
% 1.78/0.98  
% 1.78/0.98  cnf(c_1904,plain,
% 1.78/0.98      ( ~ m1_connsp_2(sK4,sK2,sK3)
% 1.78/0.98      | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.78/0.98      | sP0_iProver_split ),
% 1.78/0.98      inference(splitting,
% 1.78/0.98                [splitting(split),new_symbols(definition,[])],
% 1.78/0.98                [c_1889]) ).
% 1.78/0.98  
% 1.78/0.98  cnf(c_1957,plain,
% 1.78/0.98      ( m1_connsp_2(sK4,sK2,sK3) != iProver_top
% 1.78/0.98      | m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.78/0.98      | sP0_iProver_split = iProver_top ),
% 1.78/0.98      inference(predicate_to_equality,[status(thm)],[c_1904]) ).
% 1.78/0.98  
% 1.78/0.98  cnf(c_1958,plain,
% 1.78/0.98      ( k6_domain_1(u1_struct_0(sK2),sK3) != k2_tarski(X0_47,X0_47)
% 1.78/0.98      | r2_hidden(X0_47,k1_tops_1(sK2,sK4)) != iProver_top
% 1.78/0.98      | sP0_iProver_split != iProver_top ),
% 1.78/0.98      inference(predicate_to_equality,[status(thm)],[c_1903]) ).
% 1.78/0.98  
% 1.78/0.98  cnf(c_3,plain,
% 1.78/0.98      ( ~ r1_tarski(k2_tarski(X0,X0),X1) | r2_hidden(X0,X1) ),
% 1.78/0.98      inference(cnf_transformation,[],[f76]) ).
% 1.78/0.98  
% 1.78/0.98  cnf(c_189,plain,
% 1.78/0.98      ( r2_hidden(X0,X1) | ~ r1_tarski(k2_tarski(X0,X0),X1) ),
% 1.78/0.98      inference(prop_impl,[status(thm)],[c_3]) ).
% 1.78/0.98  
% 1.78/0.98  cnf(c_190,plain,
% 1.78/0.98      ( ~ r1_tarski(k2_tarski(X0,X0),X1) | r2_hidden(X0,X1) ),
% 1.78/0.98      inference(renaming,[status(thm)],[c_189]) ).
% 1.78/0.98  
% 1.78/0.98  cnf(c_17,negated_conjecture,
% 1.78/0.98      ( m2_connsp_2(sK4,sK2,k6_domain_1(u1_struct_0(sK2),sK3))
% 1.78/0.98      | m1_connsp_2(sK4,sK2,sK3) ),
% 1.78/0.98      inference(cnf_transformation,[],[f73]) ).
% 1.78/0.98  
% 1.78/0.98  cnf(c_195,plain,
% 1.78/0.98      ( m1_connsp_2(sK4,sK2,sK3)
% 1.78/0.98      | m2_connsp_2(sK4,sK2,k6_domain_1(u1_struct_0(sK2),sK3)) ),
% 1.78/0.98      inference(prop_impl,[status(thm)],[c_17]) ).
% 1.78/0.98  
% 1.78/0.98  cnf(c_196,plain,
% 1.78/0.98      ( m2_connsp_2(sK4,sK2,k6_domain_1(u1_struct_0(sK2),sK3))
% 1.78/0.98      | m1_connsp_2(sK4,sK2,sK3) ),
% 1.78/0.98      inference(renaming,[status(thm)],[c_195]) ).
% 1.78/0.98  
% 1.78/0.98  cnf(c_11,plain,
% 1.78/0.98      ( ~ m2_connsp_2(X0,X1,X2)
% 1.78/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.78/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.78/0.98      | r1_tarski(X2,k1_tops_1(X1,X0))
% 1.78/0.98      | ~ v2_pre_topc(X1)
% 1.78/0.98      | ~ l1_pre_topc(X1) ),
% 1.78/0.98      inference(cnf_transformation,[],[f62]) ).
% 1.78/0.98  
% 1.78/0.98  cnf(c_13,plain,
% 1.78/0.98      ( ~ m2_connsp_2(X0,X1,X2)
% 1.78/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.78/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.78/0.98      | ~ v2_pre_topc(X1)
% 1.78/0.98      | ~ l1_pre_topc(X1) ),
% 1.78/0.98      inference(cnf_transformation,[],[f65]) ).
% 1.78/0.98  
% 1.78/0.98  cnf(c_138,plain,
% 1.78/0.98      ( ~ m2_connsp_2(X0,X1,X2)
% 1.78/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.78/0.98      | r1_tarski(X2,k1_tops_1(X1,X0))
% 1.78/0.98      | ~ v2_pre_topc(X1)
% 1.78/0.98      | ~ l1_pre_topc(X1) ),
% 1.78/0.98      inference(global_propositional_subsumption,
% 1.78/0.98                [status(thm)],
% 1.78/0.98                [c_11,c_13]) ).
% 1.78/0.98  
% 1.78/0.98  cnf(c_509,plain,
% 1.78/0.98      ( ~ m2_connsp_2(X0,X1,X2)
% 1.78/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.78/0.98      | r1_tarski(X2,k1_tops_1(X1,X0))
% 1.78/0.98      | ~ v2_pre_topc(X1)
% 1.78/0.98      | sK2 != X1 ),
% 1.78/0.98      inference(resolution_lifted,[status(thm)],[c_138,c_20]) ).
% 1.78/0.98  
% 1.78/0.98  cnf(c_510,plain,
% 1.78/0.98      ( ~ m2_connsp_2(X0,sK2,X1)
% 1.78/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.78/0.98      | r1_tarski(X1,k1_tops_1(sK2,X0))
% 1.78/0.98      | ~ v2_pre_topc(sK2) ),
% 1.78/0.98      inference(unflattening,[status(thm)],[c_509]) ).
% 1.78/0.98  
% 1.78/0.98  cnf(c_514,plain,
% 1.78/0.98      ( r1_tarski(X1,k1_tops_1(sK2,X0))
% 1.78/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.78/0.98      | ~ m2_connsp_2(X0,sK2,X1) ),
% 1.78/0.98      inference(global_propositional_subsumption,
% 1.78/0.98                [status(thm)],
% 1.78/0.98                [c_510,c_21]) ).
% 1.78/0.98  
% 1.78/0.98  cnf(c_515,plain,
% 1.78/0.98      ( ~ m2_connsp_2(X0,sK2,X1)
% 1.78/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.78/0.98      | r1_tarski(X1,k1_tops_1(sK2,X0)) ),
% 1.78/0.98      inference(renaming,[status(thm)],[c_514]) ).
% 1.78/0.98  
% 1.78/0.98  cnf(c_631,plain,
% 1.78/0.98      ( m1_connsp_2(sK4,sK2,sK3)
% 1.78/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.78/0.98      | r1_tarski(X0,k1_tops_1(sK2,X1))
% 1.78/0.98      | k6_domain_1(u1_struct_0(sK2),sK3) != X0
% 1.78/0.98      | sK2 != sK2
% 1.78/0.98      | sK4 != X1 ),
% 1.78/0.98      inference(resolution_lifted,[status(thm)],[c_196,c_515]) ).
% 1.78/0.98  
% 1.78/0.98  cnf(c_632,plain,
% 1.78/0.98      ( m1_connsp_2(sK4,sK2,sK3)
% 1.78/0.98      | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.78/0.98      | r1_tarski(k6_domain_1(u1_struct_0(sK2),sK3),k1_tops_1(sK2,sK4)) ),
% 1.78/0.98      inference(unflattening,[status(thm)],[c_631]) ).
% 1.78/0.98  
% 1.78/0.98  cnf(c_689,plain,
% 1.78/0.98      ( m1_connsp_2(sK4,sK2,sK3)
% 1.78/0.98      | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.78/0.98      | r2_hidden(X0,X1)
% 1.78/0.98      | k1_tops_1(sK2,sK4) != X1
% 1.78/0.98      | k6_domain_1(u1_struct_0(sK2),sK3) != k2_tarski(X0,X0) ),
% 1.78/0.98      inference(resolution_lifted,[status(thm)],[c_190,c_632]) ).
% 1.78/0.98  
% 1.78/0.98  cnf(c_690,plain,
% 1.78/0.98      ( m1_connsp_2(sK4,sK2,sK3)
% 1.78/0.98      | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.78/0.98      | r2_hidden(X0,k1_tops_1(sK2,sK4))
% 1.78/0.98      | k6_domain_1(u1_struct_0(sK2),sK3) != k2_tarski(X0,X0) ),
% 1.78/0.98      inference(unflattening,[status(thm)],[c_689]) ).
% 1.78/0.98  
% 1.78/0.98  cnf(c_1888,plain,
% 1.78/0.98      ( m1_connsp_2(sK4,sK2,sK3)
% 1.78/0.98      | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.78/0.98      | r2_hidden(X0_47,k1_tops_1(sK2,sK4))
% 1.78/0.98      | k6_domain_1(u1_struct_0(sK2),sK3) != k2_tarski(X0_47,X0_47) ),
% 1.78/0.98      inference(subtyping,[status(esa)],[c_690]) ).
% 1.78/0.98  
% 1.78/0.98  cnf(c_1906,plain,
% 1.78/0.98      ( m1_connsp_2(sK4,sK2,sK3)
% 1.78/0.98      | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.78/0.98      | sP1_iProver_split ),
% 1.78/0.98      inference(splitting,
% 1.78/0.98                [splitting(split),new_symbols(definition,[])],
% 1.78/0.98                [c_1888]) ).
% 1.78/0.98  
% 1.78/0.98  cnf(c_1961,plain,
% 1.78/0.98      ( m1_connsp_2(sK4,sK2,sK3) = iProver_top
% 1.78/0.98      | m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.78/0.98      | sP1_iProver_split = iProver_top ),
% 1.78/0.98      inference(predicate_to_equality,[status(thm)],[c_1906]) ).
% 1.78/0.98  
% 1.78/0.98  cnf(c_444,plain,
% 1.78/0.98      ( ~ m1_connsp_2(X0,X1,X2)
% 1.78/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.78/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.78/0.98      | ~ v2_pre_topc(X1)
% 1.78/0.98      | ~ l1_pre_topc(X1)
% 1.78/0.98      | sK2 != X1 ),
% 1.78/0.98      inference(resolution_lifted,[status(thm)],[c_12,c_22]) ).
% 1.78/0.98  
% 1.78/0.98  cnf(c_445,plain,
% 1.78/0.98      ( ~ m1_connsp_2(X0,sK2,X1)
% 1.78/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.78/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.78/0.98      | ~ v2_pre_topc(sK2)
% 1.78/0.98      | ~ l1_pre_topc(sK2) ),
% 1.78/0.98      inference(unflattening,[status(thm)],[c_444]) ).
% 1.78/0.98  
% 1.78/0.98  cnf(c_449,plain,
% 1.78/0.98      ( ~ m1_connsp_2(X0,sK2,X1)
% 1.78/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.78/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 1.78/0.98      inference(global_propositional_subsumption,
% 1.78/0.98                [status(thm)],
% 1.78/0.98                [c_445,c_21,c_20]) ).
% 1.78/0.98  
% 1.78/0.98  cnf(c_1891,plain,
% 1.78/0.98      ( ~ m1_connsp_2(X0_47,sK2,X1_47)
% 1.78/0.98      | ~ m1_subset_1(X1_47,u1_struct_0(sK2))
% 1.78/0.98      | m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 1.78/0.98      inference(subtyping,[status(esa)],[c_449]) ).
% 1.78/0.98  
% 1.78/0.98  cnf(c_2375,plain,
% 1.78/0.98      ( ~ m1_connsp_2(sK1(sK2,X0_47),sK2,X0_47)
% 1.78/0.98      | ~ m1_subset_1(X0_47,u1_struct_0(sK2))
% 1.78/0.98      | m1_subset_1(sK1(sK2,X0_47),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 1.78/0.98      inference(instantiation,[status(thm)],[c_1891]) ).
% 1.78/0.98  
% 1.78/0.98  cnf(c_2377,plain,
% 1.78/0.98      ( ~ m1_connsp_2(sK1(sK2,sK3),sK2,sK3)
% 1.78/0.98      | m1_subset_1(sK1(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.78/0.98      | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 1.78/0.98      inference(instantiation,[status(thm)],[c_2375]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_2376,plain,
% 1.78/0.99      ( m1_connsp_2(sK1(sK2,X0_47),sK2,X0_47) != iProver_top
% 1.78/0.99      | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
% 1.78/0.99      | m1_subset_1(sK1(sK2,X0_47),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 1.78/0.99      inference(predicate_to_equality,[status(thm)],[c_2375]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_2378,plain,
% 1.78/0.99      ( m1_connsp_2(sK1(sK2,sK3),sK2,sK3) != iProver_top
% 1.78/0.99      | m1_subset_1(sK1(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 1.78/0.99      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 1.78/0.99      inference(instantiation,[status(thm)],[c_2376]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_15,plain,
% 1.78/0.99      ( ~ m1_connsp_2(X0,X1,X2)
% 1.78/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.78/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.78/0.99      | r2_hidden(X2,X0)
% 1.78/0.99      | v2_struct_0(X1)
% 1.78/0.99      | ~ v2_pre_topc(X1)
% 1.78/0.99      | ~ l1_pre_topc(X1) ),
% 1.78/0.99      inference(cnf_transformation,[],[f67]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_128,plain,
% 1.78/0.99      ( ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.78/0.99      | ~ m1_connsp_2(X0,X1,X2)
% 1.78/0.99      | r2_hidden(X2,X0)
% 1.78/0.99      | v2_struct_0(X1)
% 1.78/0.99      | ~ v2_pre_topc(X1)
% 1.78/0.99      | ~ l1_pre_topc(X1) ),
% 1.78/0.99      inference(global_propositional_subsumption,
% 1.78/0.99                [status(thm)],
% 1.78/0.99                [c_15,c_12]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_129,plain,
% 1.78/0.99      ( ~ m1_connsp_2(X0,X1,X2)
% 1.78/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.78/0.99      | r2_hidden(X2,X0)
% 1.78/0.99      | v2_struct_0(X1)
% 1.78/0.99      | ~ v2_pre_topc(X1)
% 1.78/0.99      | ~ l1_pre_topc(X1) ),
% 1.78/0.99      inference(renaming,[status(thm)],[c_128]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_423,plain,
% 1.78/0.99      ( ~ m1_connsp_2(X0,X1,X2)
% 1.78/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.78/0.99      | r2_hidden(X2,X0)
% 1.78/0.99      | ~ v2_pre_topc(X1)
% 1.78/0.99      | ~ l1_pre_topc(X1)
% 1.78/0.99      | sK2 != X1 ),
% 1.78/0.99      inference(resolution_lifted,[status(thm)],[c_129,c_22]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_424,plain,
% 1.78/0.99      ( ~ m1_connsp_2(X0,sK2,X1)
% 1.78/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.78/0.99      | r2_hidden(X1,X0)
% 1.78/0.99      | ~ v2_pre_topc(sK2)
% 1.78/0.99      | ~ l1_pre_topc(sK2) ),
% 1.78/0.99      inference(unflattening,[status(thm)],[c_423]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_428,plain,
% 1.78/0.99      ( ~ m1_connsp_2(X0,sK2,X1)
% 1.78/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.78/0.99      | r2_hidden(X1,X0) ),
% 1.78/0.99      inference(global_propositional_subsumption,
% 1.78/0.99                [status(thm)],
% 1.78/0.99                [c_424,c_21,c_20]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_1892,plain,
% 1.78/0.99      ( ~ m1_connsp_2(X0_47,sK2,X1_47)
% 1.78/0.99      | ~ m1_subset_1(X1_47,u1_struct_0(sK2))
% 1.78/0.99      | r2_hidden(X1_47,X0_47) ),
% 1.78/0.99      inference(subtyping,[status(esa)],[c_428]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_2380,plain,
% 1.78/0.99      ( ~ m1_connsp_2(sK1(sK2,X0_47),sK2,X0_47)
% 1.78/0.99      | ~ m1_subset_1(X0_47,u1_struct_0(sK2))
% 1.78/0.99      | r2_hidden(X0_47,sK1(sK2,X0_47)) ),
% 1.78/0.99      inference(instantiation,[status(thm)],[c_1892]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_2382,plain,
% 1.78/0.99      ( ~ m1_connsp_2(sK1(sK2,sK3),sK2,sK3)
% 1.78/0.99      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 1.78/0.99      | r2_hidden(sK3,sK1(sK2,sK3)) ),
% 1.78/0.99      inference(instantiation,[status(thm)],[c_2380]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_2381,plain,
% 1.78/0.99      ( m1_connsp_2(sK1(sK2,X0_47),sK2,X0_47) != iProver_top
% 1.78/0.99      | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
% 1.78/0.99      | r2_hidden(X0_47,sK1(sK2,X0_47)) = iProver_top ),
% 1.78/0.99      inference(predicate_to_equality,[status(thm)],[c_2380]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_2383,plain,
% 1.78/0.99      ( m1_connsp_2(sK1(sK2,sK3),sK2,sK3) != iProver_top
% 1.78/0.99      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 1.78/0.99      | r2_hidden(sK3,sK1(sK2,sK3)) = iProver_top ),
% 1.78/0.99      inference(instantiation,[status(thm)],[c_2381]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_7,plain,
% 1.78/0.99      ( ~ m1_subset_1(X0,X1)
% 1.78/0.99      | v1_xboole_0(X1)
% 1.78/0.99      | k6_domain_1(X1,X0) = k2_tarski(X0,X0) ),
% 1.78/0.99      inference(cnf_transformation,[],[f78]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_1897,plain,
% 1.78/0.99      ( ~ m1_subset_1(X0_47,X1_47)
% 1.78/0.99      | v1_xboole_0(X1_47)
% 1.78/0.99      | k6_domain_1(X1_47,X0_47) = k2_tarski(X0_47,X0_47) ),
% 1.78/0.99      inference(subtyping,[status(esa)],[c_7]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_2408,plain,
% 1.78/0.99      ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 1.78/0.99      | v1_xboole_0(u1_struct_0(sK2))
% 1.78/0.99      | k6_domain_1(u1_struct_0(sK2),sK3) = k2_tarski(sK3,sK3) ),
% 1.78/0.99      inference(instantiation,[status(thm)],[c_1897]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_1908,plain,( X0_47 = X0_47 ),theory(equality) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_2533,plain,
% 1.78/0.99      ( u1_struct_0(sK2) = u1_struct_0(sK2) ),
% 1.78/0.99      inference(instantiation,[status(thm)],[c_1908]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_4,plain,
% 1.78/0.99      ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1))
% 1.78/0.99      | ~ r2_hidden(X0,X1) ),
% 1.78/0.99      inference(cnf_transformation,[],[f77]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_1900,plain,
% 1.78/0.99      ( m1_subset_1(k2_tarski(X0_47,X0_47),k1_zfmisc_1(X1_47))
% 1.78/0.99      | ~ r2_hidden(X0_47,X1_47) ),
% 1.78/0.99      inference(subtyping,[status(esa)],[c_4]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_2540,plain,
% 1.78/0.99      ( m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.78/0.99      | ~ r2_hidden(sK3,u1_struct_0(sK2)) ),
% 1.78/0.99      inference(instantiation,[status(thm)],[c_1900]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_2541,plain,
% 1.78/0.99      ( m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 1.78/0.99      | r2_hidden(sK3,u1_struct_0(sK2)) != iProver_top ),
% 1.78/0.99      inference(predicate_to_equality,[status(thm)],[c_2540]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_1,plain,
% 1.78/0.99      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 1.78/0.99      inference(cnf_transformation,[],[f51]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_1901,plain,
% 1.78/0.99      ( ~ r2_hidden(X0_47,X1_47) | ~ v1_xboole_0(X1_47) ),
% 1.78/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_2637,plain,
% 1.78/0.99      ( ~ r2_hidden(X0_47,sK1(sK2,X0_47))
% 1.78/0.99      | ~ v1_xboole_0(sK1(sK2,X0_47)) ),
% 1.78/0.99      inference(instantiation,[status(thm)],[c_1901]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_2639,plain,
% 1.78/0.99      ( ~ r2_hidden(sK3,sK1(sK2,sK3)) | ~ v1_xboole_0(sK1(sK2,sK3)) ),
% 1.78/0.99      inference(instantiation,[status(thm)],[c_2637]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_2638,plain,
% 1.78/0.99      ( r2_hidden(X0_47,sK1(sK2,X0_47)) != iProver_top
% 1.78/0.99      | v1_xboole_0(sK1(sK2,X0_47)) != iProver_top ),
% 1.78/0.99      inference(predicate_to_equality,[status(thm)],[c_2637]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_2640,plain,
% 1.78/0.99      ( r2_hidden(sK3,sK1(sK2,sK3)) != iProver_top
% 1.78/0.99      | v1_xboole_0(sK1(sK2,sK3)) != iProver_top ),
% 1.78/0.99      inference(instantiation,[status(thm)],[c_2638]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_1895,negated_conjecture,
% 1.78/0.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 1.78/0.99      inference(subtyping,[status(esa)],[c_19]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_2240,plain,
% 1.78/0.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
% 1.78/0.99      inference(predicate_to_equality,[status(thm)],[c_1895]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_6,plain,
% 1.78/0.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 1.78/0.99      inference(cnf_transformation,[],[f58]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_1898,plain,
% 1.78/0.99      ( ~ m1_subset_1(X0_47,X1_47)
% 1.78/0.99      | r2_hidden(X0_47,X1_47)
% 1.78/0.99      | v1_xboole_0(X1_47) ),
% 1.78/0.99      inference(subtyping,[status(esa)],[c_6]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_2237,plain,
% 1.78/0.99      ( m1_subset_1(X0_47,X1_47) != iProver_top
% 1.78/0.99      | r2_hidden(X0_47,X1_47) = iProver_top
% 1.78/0.99      | v1_xboole_0(X1_47) = iProver_top ),
% 1.78/0.99      inference(predicate_to_equality,[status(thm)],[c_1898]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_2687,plain,
% 1.78/0.99      ( r2_hidden(sK3,u1_struct_0(sK2)) = iProver_top
% 1.78/0.99      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 1.78/0.99      inference(superposition,[status(thm)],[c_2240,c_2237]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_1911,plain,
% 1.78/0.99      ( X0_47 != X1_47 | k1_zfmisc_1(X0_47) = k1_zfmisc_1(X1_47) ),
% 1.78/0.99      theory(equality) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_2565,plain,
% 1.78/0.99      ( X0_47 != u1_struct_0(sK2)
% 1.78/0.99      | k1_zfmisc_1(X0_47) = k1_zfmisc_1(u1_struct_0(sK2)) ),
% 1.78/0.99      inference(instantiation,[status(thm)],[c_1911]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_2772,plain,
% 1.78/0.99      ( u1_struct_0(sK2) != u1_struct_0(sK2)
% 1.78/0.99      | k1_zfmisc_1(u1_struct_0(sK2)) = k1_zfmisc_1(u1_struct_0(sK2)) ),
% 1.78/0.99      inference(instantiation,[status(thm)],[c_2565]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_5,plain,
% 1.78/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.78/0.99      | ~ v1_xboole_0(X1)
% 1.78/0.99      | v1_xboole_0(X0) ),
% 1.78/0.99      inference(cnf_transformation,[],[f57]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_1899,plain,
% 1.78/0.99      ( ~ m1_subset_1(X0_47,k1_zfmisc_1(X1_47))
% 1.78/0.99      | ~ v1_xboole_0(X1_47)
% 1.78/0.99      | v1_xboole_0(X0_47) ),
% 1.78/0.99      inference(subtyping,[status(esa)],[c_5]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_2448,plain,
% 1.78/0.99      ( ~ m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.78/0.99      | v1_xboole_0(X0_47)
% 1.78/0.99      | ~ v1_xboole_0(u1_struct_0(sK2)) ),
% 1.78/0.99      inference(instantiation,[status(thm)],[c_1899]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_2777,plain,
% 1.78/0.99      ( ~ m1_subset_1(sK1(sK2,X0_47),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.78/0.99      | v1_xboole_0(sK1(sK2,X0_47))
% 1.78/0.99      | ~ v1_xboole_0(u1_struct_0(sK2)) ),
% 1.78/0.99      inference(instantiation,[status(thm)],[c_2448]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_2779,plain,
% 1.78/0.99      ( ~ m1_subset_1(sK1(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.78/0.99      | v1_xboole_0(sK1(sK2,sK3))
% 1.78/0.99      | ~ v1_xboole_0(u1_struct_0(sK2)) ),
% 1.78/0.99      inference(instantiation,[status(thm)],[c_2777]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_2778,plain,
% 1.78/0.99      ( m1_subset_1(sK1(sK2,X0_47),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.78/0.99      | v1_xboole_0(sK1(sK2,X0_47)) = iProver_top
% 1.78/0.99      | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 1.78/0.99      inference(predicate_to_equality,[status(thm)],[c_2777]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_2780,plain,
% 1.78/0.99      ( m1_subset_1(sK1(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.78/0.99      | v1_xboole_0(sK1(sK2,sK3)) = iProver_top
% 1.78/0.99      | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 1.78/0.99      inference(instantiation,[status(thm)],[c_2778]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_1912,plain,
% 1.78/0.99      ( ~ m1_subset_1(X0_47,X1_47)
% 1.78/0.99      | m1_subset_1(X2_47,X3_47)
% 1.78/0.99      | X2_47 != X0_47
% 1.78/0.99      | X3_47 != X1_47 ),
% 1.78/0.99      theory(equality) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_2714,plain,
% 1.78/0.99      ( m1_subset_1(X0_47,X1_47)
% 1.78/0.99      | ~ m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.78/0.99      | X0_47 != k2_tarski(sK3,sK3)
% 1.78/0.99      | X1_47 != k1_zfmisc_1(u1_struct_0(sK2)) ),
% 1.78/0.99      inference(instantiation,[status(thm)],[c_1912]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_2998,plain,
% 1.78/0.99      ( m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),X0_47)
% 1.78/0.99      | ~ m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.78/0.99      | X0_47 != k1_zfmisc_1(u1_struct_0(sK2))
% 1.78/0.99      | k6_domain_1(u1_struct_0(sK2),sK3) != k2_tarski(sK3,sK3) ),
% 1.78/0.99      inference(instantiation,[status(thm)],[c_2714]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_3186,plain,
% 1.78/0.99      ( m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.78/0.99      | ~ m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.78/0.99      | k6_domain_1(u1_struct_0(sK2),sK3) != k2_tarski(sK3,sK3)
% 1.78/0.99      | k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(u1_struct_0(sK2)) ),
% 1.78/0.99      inference(instantiation,[status(thm)],[c_2998]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_3187,plain,
% 1.78/0.99      ( k6_domain_1(u1_struct_0(sK2),sK3) != k2_tarski(sK3,sK3)
% 1.78/0.99      | k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(u1_struct_0(sK2))
% 1.78/0.99      | m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 1.78/0.99      | m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 1.78/0.99      inference(predicate_to_equality,[status(thm)],[c_3186]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_1905,plain,
% 1.78/0.99      ( r2_hidden(X0_47,k1_tops_1(sK2,sK4))
% 1.78/0.99      | k6_domain_1(u1_struct_0(sK2),sK3) != k2_tarski(X0_47,X0_47)
% 1.78/0.99      | ~ sP1_iProver_split ),
% 1.78/0.99      inference(splitting,
% 1.78/0.99                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 1.78/0.99                [c_1888]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_2249,plain,
% 1.78/0.99      ( k6_domain_1(u1_struct_0(sK2),sK3) != k2_tarski(X0_47,X0_47)
% 1.78/0.99      | r2_hidden(X0_47,k1_tops_1(sK2,sK4)) = iProver_top
% 1.78/0.99      | sP1_iProver_split != iProver_top ),
% 1.78/0.99      inference(predicate_to_equality,[status(thm)],[c_1905]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_27,plain,
% 1.78/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 1.78/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_1960,plain,
% 1.78/0.99      ( k6_domain_1(u1_struct_0(sK2),sK3) != k2_tarski(sK3,sK3)
% 1.78/0.99      | r2_hidden(sK3,k1_tops_1(sK2,sK4)) != iProver_top
% 1.78/0.99      | sP0_iProver_split != iProver_top ),
% 1.78/0.99      inference(instantiation,[status(thm)],[c_1958]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_1962,plain,
% 1.78/0.99      ( k6_domain_1(u1_struct_0(sK2),sK3) != k2_tarski(X0_47,X0_47)
% 1.78/0.99      | r2_hidden(X0_47,k1_tops_1(sK2,sK4)) = iProver_top
% 1.78/0.99      | sP1_iProver_split != iProver_top ),
% 1.78/0.99      inference(predicate_to_equality,[status(thm)],[c_1905]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_1964,plain,
% 1.78/0.99      ( k6_domain_1(u1_struct_0(sK2),sK3) != k2_tarski(sK3,sK3)
% 1.78/0.99      | r2_hidden(sK3,k1_tops_1(sK2,sK4)) = iProver_top
% 1.78/0.99      | sP1_iProver_split != iProver_top ),
% 1.78/0.99      inference(instantiation,[status(thm)],[c_1962]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_8,plain,
% 1.78/0.99      ( m1_connsp_2(X0,X1,X2)
% 1.78/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.78/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.78/0.99      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 1.78/0.99      | v2_struct_0(X1)
% 1.78/0.99      | ~ v2_pre_topc(X1)
% 1.78/0.99      | ~ l1_pre_topc(X1) ),
% 1.78/0.99      inference(cnf_transformation,[],[f61]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_465,plain,
% 1.78/0.99      ( m1_connsp_2(X0,X1,X2)
% 1.78/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.78/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.78/0.99      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 1.78/0.99      | ~ v2_pre_topc(X1)
% 1.78/0.99      | ~ l1_pre_topc(X1)
% 1.78/0.99      | sK2 != X1 ),
% 1.78/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_22]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_466,plain,
% 1.78/0.99      ( m1_connsp_2(X0,sK2,X1)
% 1.78/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.78/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.78/0.99      | ~ r2_hidden(X1,k1_tops_1(sK2,X0))
% 1.78/0.99      | ~ v2_pre_topc(sK2)
% 1.78/0.99      | ~ l1_pre_topc(sK2) ),
% 1.78/0.99      inference(unflattening,[status(thm)],[c_465]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_470,plain,
% 1.78/0.99      ( m1_connsp_2(X0,sK2,X1)
% 1.78/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.78/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.78/0.99      | ~ r2_hidden(X1,k1_tops_1(sK2,X0)) ),
% 1.78/0.99      inference(global_propositional_subsumption,
% 1.78/0.99                [status(thm)],
% 1.78/0.99                [c_466,c_21,c_20]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_1890,plain,
% 1.78/0.99      ( m1_connsp_2(X0_47,sK2,X1_47)
% 1.78/0.99      | ~ m1_subset_1(X1_47,u1_struct_0(sK2))
% 1.78/0.99      | ~ m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.78/0.99      | ~ r2_hidden(X1_47,k1_tops_1(sK2,X0_47)) ),
% 1.78/0.99      inference(subtyping,[status(esa)],[c_470]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_2390,plain,
% 1.78/0.99      ( m1_connsp_2(sK4,sK2,X0_47)
% 1.78/0.99      | ~ m1_subset_1(X0_47,u1_struct_0(sK2))
% 1.78/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.78/0.99      | ~ r2_hidden(X0_47,k1_tops_1(sK2,sK4)) ),
% 1.78/0.99      inference(instantiation,[status(thm)],[c_1890]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_2391,plain,
% 1.78/0.99      ( m1_connsp_2(sK4,sK2,X0_47) = iProver_top
% 1.78/0.99      | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
% 1.78/0.99      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.78/0.99      | r2_hidden(X0_47,k1_tops_1(sK2,sK4)) != iProver_top ),
% 1.78/0.99      inference(predicate_to_equality,[status(thm)],[c_2390]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_2393,plain,
% 1.78/0.99      ( m1_connsp_2(sK4,sK2,sK3) = iProver_top
% 1.78/0.99      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 1.78/0.99      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.78/0.99      | r2_hidden(sK3,k1_tops_1(sK2,sK4)) != iProver_top ),
% 1.78/0.99      inference(instantiation,[status(thm)],[c_2391]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_3288,plain,
% 1.78/0.99      ( sP1_iProver_split != iProver_top ),
% 1.78/0.99      inference(global_propositional_subsumption,
% 1.78/0.99                [status(thm)],
% 1.78/0.99                [c_2249,c_19,c_26,c_27,c_1943,c_1944,c_1957,c_1960,
% 1.78/0.99                 c_1964,c_2377,c_2378,c_2382,c_2383,c_2393,c_2408,c_2533,
% 1.78/0.99                 c_2541,c_2639,c_2640,c_2687,c_2772,c_2779,c_2780,c_3187]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_3393,plain,
% 1.78/0.99      ( r2_hidden(X0_47,k1_tops_1(sK2,sK4)) != iProver_top
% 1.78/0.99      | k6_domain_1(u1_struct_0(sK2),sK3) != k2_tarski(X0_47,X0_47) ),
% 1.78/0.99      inference(global_propositional_subsumption,
% 1.78/0.99                [status(thm)],
% 1.78/0.99                [c_2247,c_19,c_26,c_27,c_1943,c_1944,c_1957,c_1958,
% 1.78/0.99                 c_1960,c_1961,c_1964,c_2377,c_2378,c_2382,c_2383,c_2393,
% 1.78/0.99                 c_2408,c_2533,c_2541,c_2639,c_2640,c_2687,c_2772,c_2779,
% 1.78/0.99                 c_2780,c_3187]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_3394,plain,
% 1.78/0.99      ( k6_domain_1(u1_struct_0(sK2),sK3) != k2_tarski(X0_47,X0_47)
% 1.78/0.99      | r2_hidden(X0_47,k1_tops_1(sK2,sK4)) != iProver_top ),
% 1.78/0.99      inference(renaming,[status(thm)],[c_3393]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_2238,plain,
% 1.78/0.99      ( k6_domain_1(X0_47,X1_47) = k2_tarski(X1_47,X1_47)
% 1.78/0.99      | m1_subset_1(X1_47,X0_47) != iProver_top
% 1.78/0.99      | v1_xboole_0(X0_47) = iProver_top ),
% 1.78/0.99      inference(predicate_to_equality,[status(thm)],[c_1897]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_3066,plain,
% 1.78/0.99      ( k6_domain_1(u1_struct_0(sK2),sK3) = k2_tarski(sK3,sK3)
% 1.78/0.99      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 1.78/0.99      inference(superposition,[status(thm)],[c_2240,c_2238]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_3098,plain,
% 1.78/0.99      ( k6_domain_1(u1_struct_0(sK2),sK3) = k2_tarski(sK3,sK3) ),
% 1.78/0.99      inference(global_propositional_subsumption,
% 1.78/0.99                [status(thm)],
% 1.78/0.99                [c_3066,c_19,c_1943,c_2377,c_2382,c_2408,c_2639,c_2779]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_3399,plain,
% 1.78/0.99      ( k2_tarski(X0_47,X0_47) != k2_tarski(sK3,sK3)
% 1.78/0.99      | r2_hidden(X0_47,k1_tops_1(sK2,sK4)) != iProver_top ),
% 1.78/0.99      inference(light_normalisation,[status(thm)],[c_3394,c_3098]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_3405,plain,
% 1.78/0.99      ( r2_hidden(sK3,k1_tops_1(sK2,sK4)) != iProver_top ),
% 1.78/0.99      inference(equality_resolution,[status(thm)],[c_3399]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_3409,plain,
% 1.78/0.99      ( m1_connsp_2(sK4,sK2,sK3) != iProver_top
% 1.78/0.99      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 1.78/0.99      inference(superposition,[status(thm)],[c_2242,c_3405]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(contradiction,plain,
% 1.78/0.99      ( $false ),
% 1.78/0.99      inference(minisat,
% 1.78/0.99                [status(thm)],
% 1.78/0.99                [c_3409,c_3288,c_3187,c_2780,c_2779,c_2772,c_2687,c_2640,
% 1.78/0.99                 c_2639,c_2541,c_2533,c_2408,c_2383,c_2382,c_2378,c_2377,
% 1.78/0.99                 c_1961,c_1944,c_1943,c_26,c_19]) ).
% 1.78/0.99  
% 1.78/0.99  
% 1.78/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 1.78/0.99  
% 1.78/0.99  ------                               Statistics
% 1.78/0.99  
% 1.78/0.99  ------ General
% 1.78/0.99  
% 1.78/0.99  abstr_ref_over_cycles:                  0
% 1.78/0.99  abstr_ref_under_cycles:                 0
% 1.78/0.99  gc_basic_clause_elim:                   0
% 1.78/0.99  forced_gc_time:                         0
% 1.78/0.99  parsing_time:                           0.011
% 1.78/0.99  unif_index_cands_time:                  0.
% 1.78/0.99  unif_index_add_time:                    0.
% 1.78/0.99  orderings_time:                         0.
% 1.78/0.99  out_proof_time:                         0.018
% 1.78/0.99  total_time:                             0.134
% 1.78/0.99  num_of_symbols:                         54
% 1.78/0.99  num_of_terms:                           2333
% 1.78/0.99  
% 1.78/0.99  ------ Preprocessing
% 1.78/0.99  
% 1.78/0.99  num_of_splits:                          2
% 1.78/0.99  num_of_split_atoms:                     2
% 1.78/0.99  num_of_reused_defs:                     0
% 1.78/0.99  num_eq_ax_congr_red:                    22
% 1.78/0.99  num_of_sem_filtered_clauses:            1
% 1.78/0.99  num_of_subtypes:                        2
% 1.78/0.99  monotx_restored_types:                  0
% 1.78/0.99  sat_num_of_epr_types:                   0
% 1.78/0.99  sat_num_of_non_cyclic_types:            0
% 1.78/0.99  sat_guarded_non_collapsed_types:        0
% 1.78/0.99  num_pure_diseq_elim:                    0
% 1.78/0.99  simp_replaced_by:                       0
% 1.78/0.99  res_preprocessed:                       89
% 1.78/0.99  prep_upred:                             0
% 1.78/0.99  prep_unflattend:                        114
% 1.78/0.99  smt_new_axioms:                         0
% 1.78/0.99  pred_elim_cands:                        4
% 1.78/0.99  pred_elim:                              5
% 1.78/0.99  pred_elim_cl:                           8
% 1.78/0.99  pred_elim_cycles:                       11
% 1.78/0.99  merged_defs:                            4
% 1.78/0.99  merged_defs_ncl:                        0
% 1.78/0.99  bin_hyper_res:                          4
% 1.78/0.99  prep_cycles:                            4
% 1.78/0.99  pred_elim_time:                         0.028
% 1.78/0.99  splitting_time:                         0.
% 1.78/0.99  sem_filter_time:                        0.
% 1.78/0.99  monotx_time:                            0.
% 1.78/0.99  subtype_inf_time:                       0.
% 1.78/0.99  
% 1.78/0.99  ------ Problem properties
% 1.78/0.99  
% 1.78/0.99  clauses:                                17
% 1.78/0.99  conjectures:                            2
% 1.78/0.99  epr:                                    2
% 1.78/0.99  horn:                                   13
% 1.78/0.99  ground:                                 4
% 1.78/0.99  unary:                                  2
% 1.78/0.99  binary:                                 4
% 1.78/0.99  lits:                                   44
% 1.78/0.99  lits_eq:                                3
% 1.78/0.99  fd_pure:                                0
% 1.78/0.99  fd_pseudo:                              0
% 1.78/0.99  fd_cond:                                0
% 1.78/0.99  fd_pseudo_cond:                         0
% 1.78/0.99  ac_symbols:                             0
% 1.78/0.99  
% 1.78/0.99  ------ Propositional Solver
% 1.78/0.99  
% 1.78/0.99  prop_solver_calls:                      27
% 1.78/0.99  prop_fast_solver_calls:                 928
% 1.78/0.99  smt_solver_calls:                       0
% 1.78/0.99  smt_fast_solver_calls:                  0
% 1.78/0.99  prop_num_of_clauses:                    872
% 1.78/0.99  prop_preprocess_simplified:             3548
% 1.78/0.99  prop_fo_subsumed:                       34
% 1.78/0.99  prop_solver_time:                       0.
% 1.78/0.99  smt_solver_time:                        0.
% 1.78/0.99  smt_fast_solver_time:                   0.
% 1.78/0.99  prop_fast_solver_time:                  0.
% 1.78/0.99  prop_unsat_core_time:                   0.
% 1.78/0.99  
% 1.78/0.99  ------ QBF
% 1.78/0.99  
% 1.78/0.99  qbf_q_res:                              0
% 1.78/0.99  qbf_num_tautologies:                    0
% 1.78/0.99  qbf_prep_cycles:                        0
% 1.78/0.99  
% 1.78/0.99  ------ BMC1
% 1.78/0.99  
% 1.78/0.99  bmc1_current_bound:                     -1
% 1.78/0.99  bmc1_last_solved_bound:                 -1
% 1.78/0.99  bmc1_unsat_core_size:                   -1
% 1.78/0.99  bmc1_unsat_core_parents_size:           -1
% 1.78/0.99  bmc1_merge_next_fun:                    0
% 1.78/0.99  bmc1_unsat_core_clauses_time:           0.
% 1.78/0.99  
% 1.78/0.99  ------ Instantiation
% 1.78/0.99  
% 1.78/0.99  inst_num_of_clauses:                    183
% 1.78/0.99  inst_num_in_passive:                    21
% 1.78/0.99  inst_num_in_active:                     131
% 1.78/0.99  inst_num_in_unprocessed:                31
% 1.78/0.99  inst_num_of_loops:                      150
% 1.78/0.99  inst_num_of_learning_restarts:          0
% 1.78/0.99  inst_num_moves_active_passive:          16
% 1.78/0.99  inst_lit_activity:                      0
% 1.78/0.99  inst_lit_activity_moves:                0
% 1.78/0.99  inst_num_tautologies:                   0
% 1.78/0.99  inst_num_prop_implied:                  0
% 1.78/0.99  inst_num_existing_simplified:           0
% 1.78/0.99  inst_num_eq_res_simplified:             0
% 1.78/0.99  inst_num_child_elim:                    0
% 1.78/0.99  inst_num_of_dismatching_blockings:      25
% 1.78/0.99  inst_num_of_non_proper_insts:           149
% 1.78/0.99  inst_num_of_duplicates:                 0
% 1.78/0.99  inst_inst_num_from_inst_to_res:         0
% 1.78/0.99  inst_dismatching_checking_time:         0.
% 1.78/0.99  
% 1.78/0.99  ------ Resolution
% 1.78/0.99  
% 1.78/0.99  res_num_of_clauses:                     0
% 1.78/0.99  res_num_in_passive:                     0
% 1.78/0.99  res_num_in_active:                      0
% 1.78/0.99  res_num_of_loops:                       93
% 1.78/0.99  res_forward_subset_subsumed:            15
% 1.78/0.99  res_backward_subset_subsumed:           0
% 1.78/0.99  res_forward_subsumed:                   0
% 1.78/0.99  res_backward_subsumed:                  0
% 1.78/0.99  res_forward_subsumption_resolution:     0
% 1.78/0.99  res_backward_subsumption_resolution:    0
% 1.78/0.99  res_clause_to_clause_subsumption:       89
% 1.78/0.99  res_orphan_elimination:                 0
% 1.78/0.99  res_tautology_del:                      55
% 1.78/0.99  res_num_eq_res_simplified:              0
% 1.78/0.99  res_num_sel_changes:                    0
% 1.78/0.99  res_moves_from_active_to_pass:          0
% 1.78/0.99  
% 1.78/0.99  ------ Superposition
% 1.78/0.99  
% 1.78/0.99  sup_time_total:                         0.
% 1.78/0.99  sup_time_generating:                    0.
% 1.78/0.99  sup_time_sim_full:                      0.
% 1.78/0.99  sup_time_sim_immed:                     0.
% 1.78/0.99  
% 1.78/0.99  sup_num_of_clauses:                     37
% 1.78/0.99  sup_num_in_active:                      29
% 1.78/0.99  sup_num_in_passive:                     8
% 1.78/0.99  sup_num_of_loops:                       29
% 1.78/0.99  sup_fw_superposition:                   18
% 1.78/0.99  sup_bw_superposition:                   5
% 1.78/0.99  sup_immediate_simplified:               2
% 1.78/0.99  sup_given_eliminated:                   0
% 1.78/0.99  comparisons_done:                       0
% 1.78/0.99  comparisons_avoided:                    0
% 1.78/0.99  
% 1.78/0.99  ------ Simplifications
% 1.78/0.99  
% 1.78/0.99  
% 1.78/0.99  sim_fw_subset_subsumed:                 2
% 1.78/0.99  sim_bw_subset_subsumed:                 1
% 1.78/0.99  sim_fw_subsumed:                        0
% 1.78/0.99  sim_bw_subsumed:                        0
% 1.78/0.99  sim_fw_subsumption_res:                 0
% 1.78/0.99  sim_bw_subsumption_res:                 0
% 1.78/0.99  sim_tautology_del:                      3
% 1.78/0.99  sim_eq_tautology_del:                   0
% 1.78/0.99  sim_eq_res_simp:                        0
% 1.78/0.99  sim_fw_demodulated:                     0
% 1.78/0.99  sim_bw_demodulated:                     0
% 1.78/0.99  sim_light_normalised:                   1
% 1.78/0.99  sim_joinable_taut:                      0
% 1.78/0.99  sim_joinable_simp:                      0
% 1.78/0.99  sim_ac_normalised:                      0
% 1.78/0.99  sim_smt_subsumption:                    0
% 1.78/0.99  
%------------------------------------------------------------------------------
