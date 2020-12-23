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
% DateTime   : Thu Dec  3 12:18:28 EST 2020

% Result     : Theorem 2.74s
% Output     : CNFRefutation 2.74s
% Verified   : 
% Statistics : Number of formulae       :  190 (1662 expanded)
%              Number of clauses        :  116 ( 419 expanded)
%              Number of leaves         :   20 ( 424 expanded)
%              Depth                    :   31
%              Number of atoms          :  717 (10578 expanded)
%              Number of equality atoms :  139 ( 381 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f15])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

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
    inference(nnf_transformation,[],[f36])).

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
    inference(flattening,[],[f44])).

fof(f48,plain,(
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

fof(f47,plain,(
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

fof(f46,plain,
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

fof(f49,plain,
    ( ( ~ m1_connsp_2(sK3,sK1,sK2)
      | ~ m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2)) )
    & ( m1_connsp_2(sK3,sK1,sK2)
      | m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2)) )
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f45,f48,f47,f46])).

fof(f72,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f49])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f69,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f71,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f60,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f74,plain,
    ( m1_connsp_2(sK3,sK1,sK2)
    | m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2)) ),
    inference(cnf_transformation,[],[f49])).

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
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

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

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f70,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f49])).

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
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m2_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X2] :
          ( m2_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m2_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m2_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m2_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f75,plain,
    ( ~ m1_connsp_2(sK3,sK1,sK2)
    | ~ m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2)) ),
    inference(cnf_transformation,[],[f49])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f73,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f49])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( m2_connsp_2(X2,X0,X1)
      | ~ r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f6,axiom,(
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
    inference(ennf_transformation,[],[f6])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f38,plain,(
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
    inference(rectify,[],[f37])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK0(X0,X1) != X0
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( sK0(X0,X1) = X0
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK0(X0,X1) != X0
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( sK0(X0,X1) = X0
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f38,f39])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f76,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f51])).

fof(f77,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f76])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1565,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1567,plain,
    ( k6_domain_1(X0,X1) = k1_tarski(X1)
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2632,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK2) = k1_tarski(sK2)
    | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1565,c_1567])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_23,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_11,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_53,plain,
    ( v2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_10,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_56,plain,
    ( ~ l1_pre_topc(sK1)
    | l1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1700,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1))
    | k6_domain_1(u1_struct_0(sK1),sK2) = k1_tarski(sK2) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2825,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK2) = k1_tarski(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2632,c_25,c_23,c_22,c_53,c_56,c_1700])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_211,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_6])).

cnf(c_20,negated_conjecture,
    ( m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2))
    | m1_connsp_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_215,plain,
    ( m1_connsp_2(sK3,sK1,sK2)
    | m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2)) ),
    inference(prop_impl,[status(thm)],[c_20])).

cnf(c_216,plain,
    ( m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2))
    | m1_connsp_2(sK3,sK1,sK2) ),
    inference(renaming,[status(thm)],[c_215])).

cnf(c_14,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_17,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_156,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X0,X1,X2)
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14,c_17])).

cnf(c_157,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_156])).

cnf(c_482,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_157,c_25])).

cnf(c_483,plain,
    ( ~ m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | r2_hidden(X1,k1_tops_1(sK1,X0))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_482])).

cnf(c_24,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_487,plain,
    ( ~ m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | r2_hidden(X1,k1_tops_1(sK1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_483,c_24,c_23])).

cnf(c_788,plain,
    ( m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | r2_hidden(X0,k1_tops_1(sK1,X1))
    | sK2 != X0
    | sK1 != sK1
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_216,c_487])).

cnf(c_789,plain,
    ( m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
    inference(unflattening,[status(thm)],[c_788])).

cnf(c_791,plain,
    ( m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2))
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_789,c_22])).

cnf(c_16,plain,
    ( ~ m2_connsp_2(X0,X1,X2)
    | r1_tarski(X2,k1_tops_1(X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_18,plain,
    ( ~ m2_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_150,plain,
    ( r1_tarski(X2,k1_tops_1(X1,X0))
    | ~ m2_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_16,c_18])).

cnf(c_151,plain,
    ( ~ m2_connsp_2(X0,X1,X2)
    | r1_tarski(X2,k1_tops_1(X1,X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_150])).

cnf(c_629,plain,
    ( ~ m2_connsp_2(X0,X1,X2)
    | r1_tarski(X2,k1_tops_1(X1,X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_151,c_23])).

cnf(c_630,plain,
    ( ~ m2_connsp_2(X0,sK1,X1)
    | r1_tarski(X1,k1_tops_1(sK1,X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_629])).

cnf(c_634,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(X1,k1_tops_1(sK1,X0))
    | ~ m2_connsp_2(X0,sK1,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_630,c_24])).

cnf(c_635,plain,
    ( ~ m2_connsp_2(X0,sK1,X1)
    | r1_tarski(X1,k1_tops_1(sK1,X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(renaming,[status(thm)],[c_634])).

cnf(c_827,plain,
    ( r1_tarski(X0,k1_tops_1(sK1,X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | k6_domain_1(u1_struct_0(sK1),sK2) != X0
    | sK1 != sK1
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_791,c_635])).

cnf(c_828,plain,
    ( r1_tarski(k6_domain_1(u1_struct_0(sK1),sK2),k1_tops_1(sK1,sK3))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
    inference(unflattening,[status(thm)],[c_827])).

cnf(c_910,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | k1_tops_1(sK1,sK3) != X1
    | k6_domain_1(u1_struct_0(sK1),sK2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_211,c_828])).

cnf(c_911,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(k1_tops_1(sK1,sK3)))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
    inference(unflattening,[status(thm)],[c_910])).

cnf(c_1560,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(k1_tops_1(sK1,sK3))) = iProver_top
    | m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_911])).

cnf(c_2831,plain,
    ( m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(k1_tops_1(sK1,sK3))) = iProver_top
    | m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2825,c_1560])).

cnf(c_26,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_28,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_29,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_52,plain,
    ( v2_struct_0(X0) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_54,plain,
    ( v2_struct_0(sK1) = iProver_top
    | l1_struct_0(sK1) != iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_52])).

cnf(c_55,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_57,plain,
    ( l1_pre_topc(sK1) != iProver_top
    | l1_struct_0(sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_55])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1694,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | r2_hidden(sK2,u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1695,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | r2_hidden(sK2,u1_struct_0(sK1)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1694])).

cnf(c_4,plain,
    ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1749,plain,
    ( m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK2,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1750,plain,
    ( m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | r2_hidden(sK2,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1749])).

cnf(c_7,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_209,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_7])).

cnf(c_19,negated_conjecture,
    ( ~ m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2))
    | ~ m1_connsp_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_213,plain,
    ( ~ m1_connsp_2(sK3,sK1,sK2)
    | ~ m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2)) ),
    inference(prop_impl,[status(thm)],[c_19])).

cnf(c_214,plain,
    ( ~ m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2))
    | ~ m1_connsp_2(sK3,sK1,sK2) ),
    inference(renaming,[status(thm)],[c_213])).

cnf(c_13,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_524,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_25])).

cnf(c_525,plain,
    ( m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X1,k1_tops_1(sK1,X0))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_524])).

cnf(c_529,plain,
    ( m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X1,k1_tops_1(sK1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_525,c_24,c_23])).

cnf(c_802,plain,
    ( ~ m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X0,k1_tops_1(sK1,X1))
    | sK2 != X0
    | sK1 != sK1
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_214,c_529])).

cnf(c_803,plain,
    ( ~ m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
    inference(unflattening,[status(thm)],[c_802])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_805,plain,
    ( ~ m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2))
    | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_803,c_22,c_21])).

cnf(c_15,plain,
    ( m2_connsp_2(X0,X1,X2)
    | ~ r1_tarski(X2,k1_tops_1(X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_667,plain,
    ( m2_connsp_2(X0,X1,X2)
    | ~ r1_tarski(X2,k1_tops_1(X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_23])).

cnf(c_668,plain,
    ( m2_connsp_2(X0,sK1,X1)
    | ~ r1_tarski(X1,k1_tops_1(sK1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_667])).

cnf(c_672,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X1,k1_tops_1(sK1,X0))
    | m2_connsp_2(X0,sK1,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_668,c_24])).

cnf(c_673,plain,
    ( m2_connsp_2(X0,sK1,X1)
    | ~ r1_tarski(X1,k1_tops_1(sK1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(renaming,[status(thm)],[c_672])).

cnf(c_840,plain,
    ( ~ r1_tarski(X0,k1_tops_1(sK1,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | k6_domain_1(u1_struct_0(sK1),sK2) != X0
    | sK1 != sK1
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_805,c_673])).

cnf(c_841,plain,
    ( ~ r1_tarski(k6_domain_1(u1_struct_0(sK1),sK2),k1_tops_1(sK1,sK3))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
    inference(unflattening,[status(thm)],[c_840])).

cnf(c_843,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(k6_domain_1(u1_struct_0(sK1),sK2),k1_tops_1(sK1,sK3))
    | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_841,c_21])).

cnf(c_844,plain,
    ( ~ r1_tarski(k6_domain_1(u1_struct_0(sK1),sK2),k1_tops_1(sK1,sK3))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
    inference(renaming,[status(thm)],[c_843])).

cnf(c_879,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | k1_tops_1(sK1,sK3) != X1
    | k6_domain_1(u1_struct_0(sK1),sK2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_209,c_844])).

cnf(c_880,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(k1_tops_1(sK1,sK3)))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
    inference(unflattening,[status(thm)],[c_879])).

cnf(c_1563,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(k1_tops_1(sK1,sK3))) != iProver_top
    | m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_880])).

cnf(c_2832,plain,
    ( m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(k1_tops_1(sK1,sK3))) != iProver_top
    | m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2825,c_1563])).

cnf(c_3263,plain,
    ( m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(k1_tops_1(sK1,sK3))) != iProver_top
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2832,c_26,c_28,c_29,c_54,c_57,c_1695,c_1750])).

cnf(c_1571,plain,
    ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3269,plain,
    ( r2_hidden(sK2,k1_tops_1(sK1,sK3)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3263,c_1571])).

cnf(c_3336,plain,
    ( m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(k1_tops_1(sK1,sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2831,c_26,c_28,c_29,c_54,c_57,c_1695,c_1750,c_3269])).

cnf(c_8,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1569,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3343,plain,
    ( m1_subset_1(X0,k1_tops_1(sK1,sK3)) = iProver_top
    | r2_hidden(X0,k1_tarski(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3336,c_1569])).

cnf(c_1570,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3764,plain,
    ( r2_hidden(X0,k1_tops_1(sK1,sK3)) = iProver_top
    | r2_hidden(X0,k1_tarski(sK2)) != iProver_top
    | v1_xboole_0(k1_tops_1(sK1,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3343,c_1570])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_271,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(bin_hyper_res,[status(thm)],[c_9,c_211])).

cnf(c_892,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X0,X1)
    | r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | ~ v1_xboole_0(X2)
    | k1_tops_1(sK1,sK3) != X2
    | k6_domain_1(u1_struct_0(sK1),sK2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_271,c_828])).

cnf(c_893,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X0,k6_domain_1(u1_struct_0(sK1),sK2))
    | r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | ~ v1_xboole_0(k1_tops_1(sK1,sK3)) ),
    inference(unflattening,[status(thm)],[c_892])).

cnf(c_1269,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | ~ v1_xboole_0(k1_tops_1(sK1,sK3))
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_893])).

cnf(c_1290,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top
    | v1_xboole_0(k1_tops_1(sK1,sK3)) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1269])).

cnf(c_1271,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1950,plain,
    ( k1_zfmisc_1(u1_struct_0(sK1)) = k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1271])).

cnf(c_2,plain,
    ( r2_hidden(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1573,plain,
    ( r2_hidden(X0,k1_tarski(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1268,plain,
    ( ~ r2_hidden(X0,k6_domain_1(u1_struct_0(sK1),sK2))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_893])).

cnf(c_1562,plain,
    ( r2_hidden(X0,k6_domain_1(u1_struct_0(sK1),sK2)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1268])).

cnf(c_2833,plain,
    ( r2_hidden(X0,k1_tarski(sK2)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(demodulation,[status(thm)],[c_2825,c_1562])).

cnf(c_3114,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_1573,c_2833])).

cnf(c_1275,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1845,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | X1 != k1_zfmisc_1(u1_struct_0(sK1))
    | X0 != k1_tarski(sK2) ),
    inference(instantiation,[status(thm)],[c_1275])).

cnf(c_2481,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),X0)
    | ~ m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | X0 != k1_zfmisc_1(u1_struct_0(sK1))
    | k6_domain_1(u1_struct_0(sK1),sK2) != k1_tarski(sK2) ),
    inference(instantiation,[status(thm)],[c_1845])).

cnf(c_3128,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | k6_domain_1(u1_struct_0(sK1),sK2) != k1_tarski(sK2)
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_2481])).

cnf(c_3129,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK2) != k1_tarski(sK2)
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
    | m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3128])).

cnf(c_4081,plain,
    ( r2_hidden(X0,k1_tarski(sK2)) != iProver_top
    | r2_hidden(X0,k1_tops_1(sK1,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3764,c_25,c_26,c_23,c_28,c_22,c_29,c_53,c_54,c_56,c_57,c_1290,c_1695,c_1700,c_1750,c_1950,c_3114,c_3129,c_3269])).

cnf(c_4082,plain,
    ( r2_hidden(X0,k1_tops_1(sK1,sK3)) = iProver_top
    | r2_hidden(X0,k1_tarski(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4081])).

cnf(c_4090,plain,
    ( r2_hidden(sK2,k1_tarski(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4082,c_3269])).

cnf(c_2240,plain,
    ( r2_hidden(sK2,k1_tarski(sK2)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2241,plain,
    ( r2_hidden(sK2,k1_tarski(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2240])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4090,c_2241])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:23:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 2.74/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.74/0.98  
% 2.74/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.74/0.98  
% 2.74/0.98  ------  iProver source info
% 2.74/0.98  
% 2.74/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.74/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.74/0.98  git: non_committed_changes: false
% 2.74/0.98  git: last_make_outside_of_git: false
% 2.74/0.98  
% 2.74/0.98  ------ 
% 2.74/0.98  
% 2.74/0.98  ------ Input Options
% 2.74/0.98  
% 2.74/0.98  --out_options                           all
% 2.74/0.98  --tptp_safe_out                         true
% 2.74/0.98  --problem_path                          ""
% 2.74/0.98  --include_path                          ""
% 2.74/0.98  --clausifier                            res/vclausify_rel
% 2.74/0.98  --clausifier_options                    --mode clausify
% 2.74/0.98  --stdin                                 false
% 2.74/0.98  --stats_out                             all
% 2.74/0.98  
% 2.74/0.98  ------ General Options
% 2.74/0.98  
% 2.74/0.98  --fof                                   false
% 2.74/0.98  --time_out_real                         305.
% 2.74/0.98  --time_out_virtual                      -1.
% 2.74/0.98  --symbol_type_check                     false
% 2.74/0.98  --clausify_out                          false
% 2.74/0.98  --sig_cnt_out                           false
% 2.74/0.98  --trig_cnt_out                          false
% 2.74/0.98  --trig_cnt_out_tolerance                1.
% 2.74/0.98  --trig_cnt_out_sk_spl                   false
% 2.74/0.98  --abstr_cl_out                          false
% 2.74/0.98  
% 2.74/0.98  ------ Global Options
% 2.74/0.98  
% 2.74/0.98  --schedule                              default
% 2.74/0.98  --add_important_lit                     false
% 2.74/0.98  --prop_solver_per_cl                    1000
% 2.74/0.98  --min_unsat_core                        false
% 2.74/0.98  --soft_assumptions                      false
% 2.74/0.98  --soft_lemma_size                       3
% 2.74/0.98  --prop_impl_unit_size                   0
% 2.74/0.98  --prop_impl_unit                        []
% 2.74/0.98  --share_sel_clauses                     true
% 2.74/0.98  --reset_solvers                         false
% 2.74/0.98  --bc_imp_inh                            [conj_cone]
% 2.74/0.98  --conj_cone_tolerance                   3.
% 2.74/0.98  --extra_neg_conj                        none
% 2.74/0.98  --large_theory_mode                     true
% 2.74/0.98  --prolific_symb_bound                   200
% 2.74/0.98  --lt_threshold                          2000
% 2.74/0.98  --clause_weak_htbl                      true
% 2.74/0.98  --gc_record_bc_elim                     false
% 2.74/0.98  
% 2.74/0.98  ------ Preprocessing Options
% 2.74/0.98  
% 2.74/0.98  --preprocessing_flag                    true
% 2.74/0.98  --time_out_prep_mult                    0.1
% 2.74/0.98  --splitting_mode                        input
% 2.74/0.98  --splitting_grd                         true
% 2.74/0.98  --splitting_cvd                         false
% 2.74/0.98  --splitting_cvd_svl                     false
% 2.74/0.98  --splitting_nvd                         32
% 2.74/0.98  --sub_typing                            true
% 2.74/0.98  --prep_gs_sim                           true
% 2.74/0.98  --prep_unflatten                        true
% 2.74/0.98  --prep_res_sim                          true
% 2.74/0.98  --prep_upred                            true
% 2.74/0.98  --prep_sem_filter                       exhaustive
% 2.74/0.98  --prep_sem_filter_out                   false
% 2.74/0.98  --pred_elim                             true
% 2.74/0.98  --res_sim_input                         true
% 2.74/0.98  --eq_ax_congr_red                       true
% 2.74/0.98  --pure_diseq_elim                       true
% 2.74/0.98  --brand_transform                       false
% 2.74/0.98  --non_eq_to_eq                          false
% 2.74/0.98  --prep_def_merge                        true
% 2.74/0.98  --prep_def_merge_prop_impl              false
% 2.74/0.98  --prep_def_merge_mbd                    true
% 2.74/0.98  --prep_def_merge_tr_red                 false
% 2.74/0.98  --prep_def_merge_tr_cl                  false
% 2.74/0.98  --smt_preprocessing                     true
% 2.74/0.98  --smt_ac_axioms                         fast
% 2.74/0.98  --preprocessed_out                      false
% 2.74/0.98  --preprocessed_stats                    false
% 2.74/0.98  
% 2.74/0.98  ------ Abstraction refinement Options
% 2.74/0.98  
% 2.74/0.98  --abstr_ref                             []
% 2.74/0.98  --abstr_ref_prep                        false
% 2.74/0.98  --abstr_ref_until_sat                   false
% 2.74/0.98  --abstr_ref_sig_restrict                funpre
% 2.74/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.74/0.98  --abstr_ref_under                       []
% 2.74/0.98  
% 2.74/0.98  ------ SAT Options
% 2.74/0.98  
% 2.74/0.98  --sat_mode                              false
% 2.74/0.98  --sat_fm_restart_options                ""
% 2.74/0.98  --sat_gr_def                            false
% 2.74/0.98  --sat_epr_types                         true
% 2.74/0.98  --sat_non_cyclic_types                  false
% 2.74/0.98  --sat_finite_models                     false
% 2.74/0.98  --sat_fm_lemmas                         false
% 2.74/0.98  --sat_fm_prep                           false
% 2.74/0.98  --sat_fm_uc_incr                        true
% 2.74/0.98  --sat_out_model                         small
% 2.74/0.98  --sat_out_clauses                       false
% 2.74/0.98  
% 2.74/0.98  ------ QBF Options
% 2.74/0.98  
% 2.74/0.98  --qbf_mode                              false
% 2.74/0.98  --qbf_elim_univ                         false
% 2.74/0.98  --qbf_dom_inst                          none
% 2.74/0.98  --qbf_dom_pre_inst                      false
% 2.74/0.98  --qbf_sk_in                             false
% 2.74/0.98  --qbf_pred_elim                         true
% 2.74/0.98  --qbf_split                             512
% 2.74/0.98  
% 2.74/0.98  ------ BMC1 Options
% 2.74/0.98  
% 2.74/0.98  --bmc1_incremental                      false
% 2.74/0.98  --bmc1_axioms                           reachable_all
% 2.74/0.98  --bmc1_min_bound                        0
% 2.74/0.98  --bmc1_max_bound                        -1
% 2.74/0.98  --bmc1_max_bound_default                -1
% 2.74/0.98  --bmc1_symbol_reachability              true
% 2.74/0.98  --bmc1_property_lemmas                  false
% 2.74/0.98  --bmc1_k_induction                      false
% 2.74/0.98  --bmc1_non_equiv_states                 false
% 2.74/0.98  --bmc1_deadlock                         false
% 2.74/0.98  --bmc1_ucm                              false
% 2.74/0.98  --bmc1_add_unsat_core                   none
% 2.74/0.98  --bmc1_unsat_core_children              false
% 2.74/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.74/0.98  --bmc1_out_stat                         full
% 2.74/0.98  --bmc1_ground_init                      false
% 2.74/0.98  --bmc1_pre_inst_next_state              false
% 2.74/0.98  --bmc1_pre_inst_state                   false
% 2.74/0.98  --bmc1_pre_inst_reach_state             false
% 2.74/0.98  --bmc1_out_unsat_core                   false
% 2.74/0.98  --bmc1_aig_witness_out                  false
% 2.74/0.98  --bmc1_verbose                          false
% 2.74/0.98  --bmc1_dump_clauses_tptp                false
% 2.74/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.74/0.98  --bmc1_dump_file                        -
% 2.74/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.74/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.74/0.98  --bmc1_ucm_extend_mode                  1
% 2.74/0.98  --bmc1_ucm_init_mode                    2
% 2.74/0.98  --bmc1_ucm_cone_mode                    none
% 2.74/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.74/0.98  --bmc1_ucm_relax_model                  4
% 2.74/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.74/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.74/0.98  --bmc1_ucm_layered_model                none
% 2.74/0.98  --bmc1_ucm_max_lemma_size               10
% 2.74/0.98  
% 2.74/0.98  ------ AIG Options
% 2.74/0.98  
% 2.74/0.98  --aig_mode                              false
% 2.74/0.98  
% 2.74/0.98  ------ Instantiation Options
% 2.74/0.98  
% 2.74/0.98  --instantiation_flag                    true
% 2.74/0.98  --inst_sos_flag                         false
% 2.74/0.98  --inst_sos_phase                        true
% 2.74/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.74/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.74/0.98  --inst_lit_sel_side                     num_symb
% 2.74/0.98  --inst_solver_per_active                1400
% 2.74/0.98  --inst_solver_calls_frac                1.
% 2.74/0.98  --inst_passive_queue_type               priority_queues
% 2.74/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.74/0.98  --inst_passive_queues_freq              [25;2]
% 2.74/0.98  --inst_dismatching                      true
% 2.74/0.98  --inst_eager_unprocessed_to_passive     true
% 2.74/0.98  --inst_prop_sim_given                   true
% 2.74/0.98  --inst_prop_sim_new                     false
% 2.74/0.98  --inst_subs_new                         false
% 2.74/0.98  --inst_eq_res_simp                      false
% 2.74/0.98  --inst_subs_given                       false
% 2.74/0.98  --inst_orphan_elimination               true
% 2.74/0.98  --inst_learning_loop_flag               true
% 2.74/0.98  --inst_learning_start                   3000
% 2.74/0.98  --inst_learning_factor                  2
% 2.74/0.98  --inst_start_prop_sim_after_learn       3
% 2.74/0.98  --inst_sel_renew                        solver
% 2.74/0.98  --inst_lit_activity_flag                true
% 2.74/0.98  --inst_restr_to_given                   false
% 2.74/0.98  --inst_activity_threshold               500
% 2.74/0.98  --inst_out_proof                        true
% 2.74/0.98  
% 2.74/0.98  ------ Resolution Options
% 2.74/0.98  
% 2.74/0.98  --resolution_flag                       true
% 2.74/0.98  --res_lit_sel                           adaptive
% 2.74/0.98  --res_lit_sel_side                      none
% 2.74/0.98  --res_ordering                          kbo
% 2.74/0.98  --res_to_prop_solver                    active
% 2.74/0.98  --res_prop_simpl_new                    false
% 2.74/0.98  --res_prop_simpl_given                  true
% 2.74/0.98  --res_passive_queue_type                priority_queues
% 2.74/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.74/0.98  --res_passive_queues_freq               [15;5]
% 2.74/0.98  --res_forward_subs                      full
% 2.74/0.98  --res_backward_subs                     full
% 2.74/0.98  --res_forward_subs_resolution           true
% 2.74/0.98  --res_backward_subs_resolution          true
% 2.74/0.98  --res_orphan_elimination                true
% 2.74/0.98  --res_time_limit                        2.
% 2.74/0.98  --res_out_proof                         true
% 2.74/0.98  
% 2.74/0.98  ------ Superposition Options
% 2.74/0.98  
% 2.74/0.98  --superposition_flag                    true
% 2.74/0.98  --sup_passive_queue_type                priority_queues
% 2.74/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.74/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.74/0.98  --demod_completeness_check              fast
% 2.74/0.98  --demod_use_ground                      true
% 2.74/0.98  --sup_to_prop_solver                    passive
% 2.74/0.98  --sup_prop_simpl_new                    true
% 2.74/0.98  --sup_prop_simpl_given                  true
% 2.74/0.98  --sup_fun_splitting                     false
% 2.74/0.98  --sup_smt_interval                      50000
% 2.74/0.98  
% 2.74/0.98  ------ Superposition Simplification Setup
% 2.74/0.98  
% 2.74/0.98  --sup_indices_passive                   []
% 2.74/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.74/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.74/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.74/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.74/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.74/0.98  --sup_full_bw                           [BwDemod]
% 2.74/0.98  --sup_immed_triv                        [TrivRules]
% 2.74/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.74/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.74/0.98  --sup_immed_bw_main                     []
% 2.74/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.74/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.74/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.74/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.74/0.98  
% 2.74/0.98  ------ Combination Options
% 2.74/0.98  
% 2.74/0.98  --comb_res_mult                         3
% 2.74/0.98  --comb_sup_mult                         2
% 2.74/0.98  --comb_inst_mult                        10
% 2.74/0.98  
% 2.74/0.98  ------ Debug Options
% 2.74/0.98  
% 2.74/0.98  --dbg_backtrace                         false
% 2.74/0.98  --dbg_dump_prop_clauses                 false
% 2.74/0.98  --dbg_dump_prop_clauses_file            -
% 2.74/0.98  --dbg_out_stat                          false
% 2.74/0.98  ------ Parsing...
% 2.74/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.74/0.98  
% 2.74/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 2.74/0.98  
% 2.74/0.98  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.74/0.98  
% 2.74/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.74/0.98  ------ Proving...
% 2.74/0.98  ------ Problem Properties 
% 2.74/0.98  
% 2.74/0.98  
% 2.74/0.98  clauses                                 16
% 2.74/0.98  conjectures                             2
% 2.74/0.98  EPR                                     1
% 2.74/0.98  Horn                                    11
% 2.74/0.98  unary                                   4
% 2.74/0.98  binary                                  3
% 2.74/0.98  lits                                    38
% 2.74/0.98  lits eq                                 6
% 2.74/0.98  fd_pure                                 0
% 2.74/0.98  fd_pseudo                               0
% 2.74/0.98  fd_cond                                 0
% 2.74/0.98  fd_pseudo_cond                          2
% 2.74/0.98  AC symbols                              0
% 2.74/0.98  
% 2.74/0.98  ------ Schedule dynamic 5 is on 
% 2.74/0.98  
% 2.74/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.74/0.98  
% 2.74/0.98  
% 2.74/0.98  ------ 
% 2.74/0.98  Current options:
% 2.74/0.98  ------ 
% 2.74/0.98  
% 2.74/0.98  ------ Input Options
% 2.74/0.98  
% 2.74/0.98  --out_options                           all
% 2.74/0.98  --tptp_safe_out                         true
% 2.74/0.98  --problem_path                          ""
% 2.74/0.98  --include_path                          ""
% 2.74/0.98  --clausifier                            res/vclausify_rel
% 2.74/0.98  --clausifier_options                    --mode clausify
% 2.74/0.98  --stdin                                 false
% 2.74/0.98  --stats_out                             all
% 2.74/0.98  
% 2.74/0.98  ------ General Options
% 2.74/0.98  
% 2.74/0.98  --fof                                   false
% 2.74/0.98  --time_out_real                         305.
% 2.74/0.98  --time_out_virtual                      -1.
% 2.74/0.98  --symbol_type_check                     false
% 2.74/0.98  --clausify_out                          false
% 2.74/0.98  --sig_cnt_out                           false
% 2.74/0.98  --trig_cnt_out                          false
% 2.74/0.98  --trig_cnt_out_tolerance                1.
% 2.74/0.98  --trig_cnt_out_sk_spl                   false
% 2.74/0.98  --abstr_cl_out                          false
% 2.74/0.98  
% 2.74/0.98  ------ Global Options
% 2.74/0.98  
% 2.74/0.98  --schedule                              default
% 2.74/0.98  --add_important_lit                     false
% 2.74/0.98  --prop_solver_per_cl                    1000
% 2.74/0.98  --min_unsat_core                        false
% 2.74/0.98  --soft_assumptions                      false
% 2.74/0.98  --soft_lemma_size                       3
% 2.74/0.98  --prop_impl_unit_size                   0
% 2.74/0.98  --prop_impl_unit                        []
% 2.74/0.98  --share_sel_clauses                     true
% 2.74/0.98  --reset_solvers                         false
% 2.74/0.98  --bc_imp_inh                            [conj_cone]
% 2.74/0.98  --conj_cone_tolerance                   3.
% 2.74/0.98  --extra_neg_conj                        none
% 2.74/0.98  --large_theory_mode                     true
% 2.74/0.98  --prolific_symb_bound                   200
% 2.74/0.98  --lt_threshold                          2000
% 2.74/0.98  --clause_weak_htbl                      true
% 2.74/0.98  --gc_record_bc_elim                     false
% 2.74/0.98  
% 2.74/0.98  ------ Preprocessing Options
% 2.74/0.98  
% 2.74/0.98  --preprocessing_flag                    true
% 2.74/0.98  --time_out_prep_mult                    0.1
% 2.74/0.98  --splitting_mode                        input
% 2.74/0.98  --splitting_grd                         true
% 2.74/0.98  --splitting_cvd                         false
% 2.74/0.98  --splitting_cvd_svl                     false
% 2.74/0.98  --splitting_nvd                         32
% 2.74/0.98  --sub_typing                            true
% 2.74/0.98  --prep_gs_sim                           true
% 2.74/0.98  --prep_unflatten                        true
% 2.74/0.98  --prep_res_sim                          true
% 2.74/0.98  --prep_upred                            true
% 2.74/0.98  --prep_sem_filter                       exhaustive
% 2.74/0.98  --prep_sem_filter_out                   false
% 2.74/0.98  --pred_elim                             true
% 2.74/0.98  --res_sim_input                         true
% 2.74/0.98  --eq_ax_congr_red                       true
% 2.74/0.98  --pure_diseq_elim                       true
% 2.74/0.98  --brand_transform                       false
% 2.74/0.98  --non_eq_to_eq                          false
% 2.74/0.98  --prep_def_merge                        true
% 2.74/0.98  --prep_def_merge_prop_impl              false
% 2.74/0.98  --prep_def_merge_mbd                    true
% 2.74/0.98  --prep_def_merge_tr_red                 false
% 2.74/0.98  --prep_def_merge_tr_cl                  false
% 2.74/0.98  --smt_preprocessing                     true
% 2.74/0.98  --smt_ac_axioms                         fast
% 2.74/0.98  --preprocessed_out                      false
% 2.74/0.98  --preprocessed_stats                    false
% 2.74/0.98  
% 2.74/0.98  ------ Abstraction refinement Options
% 2.74/0.98  
% 2.74/0.98  --abstr_ref                             []
% 2.74/0.98  --abstr_ref_prep                        false
% 2.74/0.98  --abstr_ref_until_sat                   false
% 2.74/0.98  --abstr_ref_sig_restrict                funpre
% 2.74/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.74/0.98  --abstr_ref_under                       []
% 2.74/0.98  
% 2.74/0.98  ------ SAT Options
% 2.74/0.98  
% 2.74/0.98  --sat_mode                              false
% 2.74/0.98  --sat_fm_restart_options                ""
% 2.74/0.98  --sat_gr_def                            false
% 2.74/0.98  --sat_epr_types                         true
% 2.74/0.98  --sat_non_cyclic_types                  false
% 2.74/0.98  --sat_finite_models                     false
% 2.74/0.98  --sat_fm_lemmas                         false
% 2.74/0.98  --sat_fm_prep                           false
% 2.74/0.98  --sat_fm_uc_incr                        true
% 2.74/0.98  --sat_out_model                         small
% 2.74/0.98  --sat_out_clauses                       false
% 2.74/0.98  
% 2.74/0.98  ------ QBF Options
% 2.74/0.98  
% 2.74/0.98  --qbf_mode                              false
% 2.74/0.98  --qbf_elim_univ                         false
% 2.74/0.98  --qbf_dom_inst                          none
% 2.74/0.98  --qbf_dom_pre_inst                      false
% 2.74/0.98  --qbf_sk_in                             false
% 2.74/0.98  --qbf_pred_elim                         true
% 2.74/0.98  --qbf_split                             512
% 2.74/0.98  
% 2.74/0.98  ------ BMC1 Options
% 2.74/0.98  
% 2.74/0.98  --bmc1_incremental                      false
% 2.74/0.98  --bmc1_axioms                           reachable_all
% 2.74/0.98  --bmc1_min_bound                        0
% 2.74/0.98  --bmc1_max_bound                        -1
% 2.74/0.98  --bmc1_max_bound_default                -1
% 2.74/0.98  --bmc1_symbol_reachability              true
% 2.74/0.98  --bmc1_property_lemmas                  false
% 2.74/0.98  --bmc1_k_induction                      false
% 2.74/0.98  --bmc1_non_equiv_states                 false
% 2.74/0.98  --bmc1_deadlock                         false
% 2.74/0.98  --bmc1_ucm                              false
% 2.74/0.98  --bmc1_add_unsat_core                   none
% 2.74/0.98  --bmc1_unsat_core_children              false
% 2.74/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.74/0.98  --bmc1_out_stat                         full
% 2.74/0.98  --bmc1_ground_init                      false
% 2.74/0.98  --bmc1_pre_inst_next_state              false
% 2.74/0.98  --bmc1_pre_inst_state                   false
% 2.74/0.98  --bmc1_pre_inst_reach_state             false
% 2.74/0.98  --bmc1_out_unsat_core                   false
% 2.74/0.98  --bmc1_aig_witness_out                  false
% 2.74/0.98  --bmc1_verbose                          false
% 2.74/0.98  --bmc1_dump_clauses_tptp                false
% 2.74/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.74/0.98  --bmc1_dump_file                        -
% 2.74/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.74/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.74/0.98  --bmc1_ucm_extend_mode                  1
% 2.74/0.98  --bmc1_ucm_init_mode                    2
% 2.74/0.98  --bmc1_ucm_cone_mode                    none
% 2.74/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.74/0.98  --bmc1_ucm_relax_model                  4
% 2.74/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.74/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.74/0.98  --bmc1_ucm_layered_model                none
% 2.74/0.98  --bmc1_ucm_max_lemma_size               10
% 2.74/0.98  
% 2.74/0.98  ------ AIG Options
% 2.74/0.98  
% 2.74/0.98  --aig_mode                              false
% 2.74/0.98  
% 2.74/0.98  ------ Instantiation Options
% 2.74/0.98  
% 2.74/0.98  --instantiation_flag                    true
% 2.74/0.98  --inst_sos_flag                         false
% 2.74/0.98  --inst_sos_phase                        true
% 2.74/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.74/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.74/0.98  --inst_lit_sel_side                     none
% 2.74/0.98  --inst_solver_per_active                1400
% 2.74/0.98  --inst_solver_calls_frac                1.
% 2.74/0.98  --inst_passive_queue_type               priority_queues
% 2.74/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.74/0.98  --inst_passive_queues_freq              [25;2]
% 2.74/0.98  --inst_dismatching                      true
% 2.74/0.98  --inst_eager_unprocessed_to_passive     true
% 2.74/0.98  --inst_prop_sim_given                   true
% 2.74/0.98  --inst_prop_sim_new                     false
% 2.74/0.98  --inst_subs_new                         false
% 2.74/0.98  --inst_eq_res_simp                      false
% 2.74/0.98  --inst_subs_given                       false
% 2.74/0.98  --inst_orphan_elimination               true
% 2.74/0.98  --inst_learning_loop_flag               true
% 2.74/0.98  --inst_learning_start                   3000
% 2.74/0.98  --inst_learning_factor                  2
% 2.74/0.98  --inst_start_prop_sim_after_learn       3
% 2.74/0.98  --inst_sel_renew                        solver
% 2.74/0.98  --inst_lit_activity_flag                true
% 2.74/0.98  --inst_restr_to_given                   false
% 2.74/0.98  --inst_activity_threshold               500
% 2.74/0.98  --inst_out_proof                        true
% 2.74/0.98  
% 2.74/0.98  ------ Resolution Options
% 2.74/0.98  
% 2.74/0.98  --resolution_flag                       false
% 2.74/0.98  --res_lit_sel                           adaptive
% 2.74/0.98  --res_lit_sel_side                      none
% 2.74/0.98  --res_ordering                          kbo
% 2.74/0.98  --res_to_prop_solver                    active
% 2.74/0.98  --res_prop_simpl_new                    false
% 2.74/0.98  --res_prop_simpl_given                  true
% 2.74/0.98  --res_passive_queue_type                priority_queues
% 2.74/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.74/0.98  --res_passive_queues_freq               [15;5]
% 2.74/0.98  --res_forward_subs                      full
% 2.74/0.98  --res_backward_subs                     full
% 2.74/0.98  --res_forward_subs_resolution           true
% 2.74/0.98  --res_backward_subs_resolution          true
% 2.74/0.98  --res_orphan_elimination                true
% 2.74/0.98  --res_time_limit                        2.
% 2.74/0.98  --res_out_proof                         true
% 2.74/0.98  
% 2.74/0.98  ------ Superposition Options
% 2.74/0.98  
% 2.74/0.98  --superposition_flag                    true
% 2.74/0.98  --sup_passive_queue_type                priority_queues
% 2.74/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.74/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.74/0.98  --demod_completeness_check              fast
% 2.74/0.98  --demod_use_ground                      true
% 2.74/0.98  --sup_to_prop_solver                    passive
% 2.74/0.98  --sup_prop_simpl_new                    true
% 2.74/0.98  --sup_prop_simpl_given                  true
% 2.74/0.98  --sup_fun_splitting                     false
% 2.74/0.98  --sup_smt_interval                      50000
% 2.74/0.98  
% 2.74/0.98  ------ Superposition Simplification Setup
% 2.74/0.98  
% 2.74/0.98  --sup_indices_passive                   []
% 2.74/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.74/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.74/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.74/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.74/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.74/0.98  --sup_full_bw                           [BwDemod]
% 2.74/0.98  --sup_immed_triv                        [TrivRules]
% 2.74/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.74/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.74/0.98  --sup_immed_bw_main                     []
% 2.74/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.74/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.74/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.74/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.74/0.98  
% 2.74/0.98  ------ Combination Options
% 2.74/0.98  
% 2.74/0.98  --comb_res_mult                         3
% 2.74/0.98  --comb_sup_mult                         2
% 2.74/0.98  --comb_inst_mult                        10
% 2.74/0.98  
% 2.74/0.98  ------ Debug Options
% 2.74/0.98  
% 2.74/0.98  --dbg_backtrace                         false
% 2.74/0.98  --dbg_dump_prop_clauses                 false
% 2.74/0.98  --dbg_dump_prop_clauses_file            -
% 2.74/0.98  --dbg_out_stat                          false
% 2.74/0.98  
% 2.74/0.98  
% 2.74/0.98  
% 2.74/0.98  
% 2.74/0.98  ------ Proving...
% 2.74/0.98  
% 2.74/0.98  
% 2.74/0.98  % SZS status Theorem for theBenchmark.p
% 2.74/0.98  
% 2.74/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.74/0.98  
% 2.74/0.98  fof(f14,conjecture,(
% 2.74/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) <=> m1_connsp_2(X2,X0,X1)))))),
% 2.74/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/0.98  
% 2.74/0.98  fof(f15,negated_conjecture,(
% 2.74/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) <=> m1_connsp_2(X2,X0,X1)))))),
% 2.74/0.98    inference(negated_conjecture,[],[f14])).
% 2.74/0.98  
% 2.74/0.98  fof(f35,plain,(
% 2.74/0.98    ? [X0] : (? [X1] : (? [X2] : ((m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) <~> m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.74/0.98    inference(ennf_transformation,[],[f15])).
% 2.74/0.98  
% 2.74/0.98  fof(f36,plain,(
% 2.74/0.98    ? [X0] : (? [X1] : (? [X2] : ((m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) <~> m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.74/0.98    inference(flattening,[],[f35])).
% 2.74/0.98  
% 2.74/0.98  fof(f44,plain,(
% 2.74/0.98    ? [X0] : (? [X1] : (? [X2] : (((~m1_connsp_2(X2,X0,X1) | ~m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & (m1_connsp_2(X2,X0,X1) | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.74/0.98    inference(nnf_transformation,[],[f36])).
% 2.74/0.98  
% 2.74/0.98  fof(f45,plain,(
% 2.74/0.98    ? [X0] : (? [X1] : (? [X2] : ((~m1_connsp_2(X2,X0,X1) | ~m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & (m1_connsp_2(X2,X0,X1) | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.74/0.98    inference(flattening,[],[f44])).
% 2.74/0.98  
% 2.74/0.98  fof(f48,plain,(
% 2.74/0.98    ( ! [X0,X1] : (? [X2] : ((~m1_connsp_2(X2,X0,X1) | ~m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & (m1_connsp_2(X2,X0,X1) | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => ((~m1_connsp_2(sK3,X0,X1) | ~m2_connsp_2(sK3,X0,k6_domain_1(u1_struct_0(X0),X1))) & (m1_connsp_2(sK3,X0,X1) | m2_connsp_2(sK3,X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.74/0.98    introduced(choice_axiom,[])).
% 2.74/0.98  
% 2.74/0.98  fof(f47,plain,(
% 2.74/0.98    ( ! [X0] : (? [X1] : (? [X2] : ((~m1_connsp_2(X2,X0,X1) | ~m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & (m1_connsp_2(X2,X0,X1) | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : ((~m1_connsp_2(X2,X0,sK2) | ~m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),sK2))) & (m1_connsp_2(X2,X0,sK2) | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),sK2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK2,u1_struct_0(X0)))) )),
% 2.74/0.98    introduced(choice_axiom,[])).
% 2.74/0.98  
% 2.74/0.98  fof(f46,plain,(
% 2.74/0.98    ? [X0] : (? [X1] : (? [X2] : ((~m1_connsp_2(X2,X0,X1) | ~m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & (m1_connsp_2(X2,X0,X1) | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~m1_connsp_2(X2,sK1,X1) | ~m2_connsp_2(X2,sK1,k6_domain_1(u1_struct_0(sK1),X1))) & (m1_connsp_2(X2,sK1,X1) | m2_connsp_2(X2,sK1,k6_domain_1(u1_struct_0(sK1),X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X1,u1_struct_0(sK1))) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 2.74/0.98    introduced(choice_axiom,[])).
% 2.74/0.98  
% 2.74/0.98  fof(f49,plain,(
% 2.74/0.98    (((~m1_connsp_2(sK3,sK1,sK2) | ~m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2))) & (m1_connsp_2(sK3,sK1,sK2) | m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK2,u1_struct_0(sK1))) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 2.74/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f45,f48,f47,f46])).
% 2.74/0.98  
% 2.74/0.98  fof(f72,plain,(
% 2.74/0.98    m1_subset_1(sK2,u1_struct_0(sK1))),
% 2.74/0.98    inference(cnf_transformation,[],[f49])).
% 2.74/0.98  
% 2.74/0.98  fof(f9,axiom,(
% 2.74/0.98    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 2.74/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/0.98  
% 2.74/0.98  fof(f25,plain,(
% 2.74/0.98    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.74/0.98    inference(ennf_transformation,[],[f9])).
% 2.74/0.98  
% 2.74/0.98  fof(f26,plain,(
% 2.74/0.98    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.74/0.98    inference(flattening,[],[f25])).
% 2.74/0.98  
% 2.74/0.98  fof(f62,plain,(
% 2.74/0.98    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.74/0.98    inference(cnf_transformation,[],[f26])).
% 2.74/0.98  
% 2.74/0.98  fof(f69,plain,(
% 2.74/0.98    ~v2_struct_0(sK1)),
% 2.74/0.98    inference(cnf_transformation,[],[f49])).
% 2.74/0.98  
% 2.74/0.98  fof(f71,plain,(
% 2.74/0.98    l1_pre_topc(sK1)),
% 2.74/0.98    inference(cnf_transformation,[],[f49])).
% 2.74/0.98  
% 2.74/0.98  fof(f8,axiom,(
% 2.74/0.98    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.74/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/0.98  
% 2.74/0.98  fof(f23,plain,(
% 2.74/0.98    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.74/0.98    inference(ennf_transformation,[],[f8])).
% 2.74/0.98  
% 2.74/0.98  fof(f24,plain,(
% 2.74/0.98    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.74/0.98    inference(flattening,[],[f23])).
% 2.74/0.98  
% 2.74/0.98  fof(f61,plain,(
% 2.74/0.98    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.74/0.98    inference(cnf_transformation,[],[f24])).
% 2.74/0.98  
% 2.74/0.98  fof(f7,axiom,(
% 2.74/0.98    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.74/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/0.98  
% 2.74/0.98  fof(f22,plain,(
% 2.74/0.98    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.74/0.98    inference(ennf_transformation,[],[f7])).
% 2.74/0.98  
% 2.74/0.98  fof(f60,plain,(
% 2.74/0.98    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.74/0.98    inference(cnf_transformation,[],[f22])).
% 2.74/0.98  
% 2.74/0.98  fof(f4,axiom,(
% 2.74/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.74/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/0.98  
% 2.74/0.98  fof(f41,plain,(
% 2.74/0.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.74/0.98    inference(nnf_transformation,[],[f4])).
% 2.74/0.98  
% 2.74/0.98  fof(f57,plain,(
% 2.74/0.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.74/0.98    inference(cnf_transformation,[],[f41])).
% 2.74/0.98  
% 2.74/0.98  fof(f74,plain,(
% 2.74/0.98    m1_connsp_2(sK3,sK1,sK2) | m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2))),
% 2.74/0.98    inference(cnf_transformation,[],[f49])).
% 2.74/0.98  
% 2.74/0.98  fof(f10,axiom,(
% 2.74/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 2.74/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/0.98  
% 2.74/0.98  fof(f27,plain,(
% 2.74/0.98    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.74/0.98    inference(ennf_transformation,[],[f10])).
% 2.74/0.98  
% 2.74/0.98  fof(f28,plain,(
% 2.74/0.98    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.74/0.98    inference(flattening,[],[f27])).
% 2.74/0.98  
% 2.74/0.98  fof(f42,plain,(
% 2.74/0.98    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.74/0.98    inference(nnf_transformation,[],[f28])).
% 2.74/0.98  
% 2.74/0.98  fof(f63,plain,(
% 2.74/0.98    ( ! [X2,X0,X1] : (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.74/0.98    inference(cnf_transformation,[],[f42])).
% 2.74/0.98  
% 2.74/0.98  fof(f12,axiom,(
% 2.74/0.98    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.74/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/0.98  
% 2.74/0.98  fof(f31,plain,(
% 2.74/0.98    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.74/0.98    inference(ennf_transformation,[],[f12])).
% 2.74/0.98  
% 2.74/0.98  fof(f32,plain,(
% 2.74/0.98    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.74/0.98    inference(flattening,[],[f31])).
% 2.74/0.98  
% 2.74/0.98  fof(f67,plain,(
% 2.74/0.98    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.74/0.98    inference(cnf_transformation,[],[f32])).
% 2.74/0.98  
% 2.74/0.98  fof(f70,plain,(
% 2.74/0.98    v2_pre_topc(sK1)),
% 2.74/0.98    inference(cnf_transformation,[],[f49])).
% 2.74/0.98  
% 2.74/0.98  fof(f11,axiom,(
% 2.74/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 2.74/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/0.98  
% 2.74/0.98  fof(f29,plain,(
% 2.74/0.98    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.74/0.98    inference(ennf_transformation,[],[f11])).
% 2.74/0.98  
% 2.74/0.98  fof(f30,plain,(
% 2.74/0.98    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.74/0.98    inference(flattening,[],[f29])).
% 2.74/0.98  
% 2.74/0.98  fof(f43,plain,(
% 2.74/0.98    ! [X0] : (! [X1] : (! [X2] : (((m2_connsp_2(X2,X0,X1) | ~r1_tarski(X1,k1_tops_1(X0,X2))) & (r1_tarski(X1,k1_tops_1(X0,X2)) | ~m2_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.74/0.98    inference(nnf_transformation,[],[f30])).
% 2.74/0.98  
% 2.74/0.98  fof(f65,plain,(
% 2.74/0.98    ( ! [X2,X0,X1] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~m2_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.74/0.98    inference(cnf_transformation,[],[f43])).
% 2.74/0.98  
% 2.74/0.98  fof(f13,axiom,(
% 2.74/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X2] : (m2_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.74/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/0.98  
% 2.74/0.98  fof(f33,plain,(
% 2.74/0.98    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.74/0.98    inference(ennf_transformation,[],[f13])).
% 2.74/0.98  
% 2.74/0.98  fof(f34,plain,(
% 2.74/0.98    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.74/0.98    inference(flattening,[],[f33])).
% 2.74/0.98  
% 2.74/0.98  fof(f68,plain,(
% 2.74/0.98    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.74/0.98    inference(cnf_transformation,[],[f34])).
% 2.74/0.98  
% 2.74/0.98  fof(f3,axiom,(
% 2.74/0.98    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.74/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/0.98  
% 2.74/0.98  fof(f17,plain,(
% 2.74/0.98    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.74/0.98    inference(ennf_transformation,[],[f3])).
% 2.74/0.98  
% 2.74/0.98  fof(f18,plain,(
% 2.74/0.98    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.74/0.98    inference(flattening,[],[f17])).
% 2.74/0.98  
% 2.74/0.98  fof(f55,plain,(
% 2.74/0.98    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.74/0.98    inference(cnf_transformation,[],[f18])).
% 2.74/0.98  
% 2.74/0.98  fof(f2,axiom,(
% 2.74/0.98    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 2.74/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/0.98  
% 2.74/0.98  fof(f16,plain,(
% 2.74/0.98    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 2.74/0.98    inference(ennf_transformation,[],[f2])).
% 2.74/0.98  
% 2.74/0.98  fof(f54,plain,(
% 2.74/0.98    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 2.74/0.98    inference(cnf_transformation,[],[f16])).
% 2.74/0.98  
% 2.74/0.98  fof(f56,plain,(
% 2.74/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.74/0.98    inference(cnf_transformation,[],[f41])).
% 2.74/0.98  
% 2.74/0.98  fof(f75,plain,(
% 2.74/0.98    ~m1_connsp_2(sK3,sK1,sK2) | ~m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2))),
% 2.74/0.98    inference(cnf_transformation,[],[f49])).
% 2.74/0.98  
% 2.74/0.98  fof(f64,plain,(
% 2.74/0.98    ( ! [X2,X0,X1] : (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.74/0.98    inference(cnf_transformation,[],[f42])).
% 2.74/0.98  
% 2.74/0.98  fof(f73,plain,(
% 2.74/0.98    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 2.74/0.98    inference(cnf_transformation,[],[f49])).
% 2.74/0.98  
% 2.74/0.98  fof(f66,plain,(
% 2.74/0.98    ( ! [X2,X0,X1] : (m2_connsp_2(X2,X0,X1) | ~r1_tarski(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.74/0.98    inference(cnf_transformation,[],[f43])).
% 2.74/0.98  
% 2.74/0.98  fof(f5,axiom,(
% 2.74/0.98    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.74/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/0.98  
% 2.74/0.98  fof(f19,plain,(
% 2.74/0.98    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.74/0.98    inference(ennf_transformation,[],[f5])).
% 2.74/0.98  
% 2.74/0.98  fof(f20,plain,(
% 2.74/0.98    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.74/0.98    inference(flattening,[],[f19])).
% 2.74/0.98  
% 2.74/0.98  fof(f58,plain,(
% 2.74/0.98    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.74/0.98    inference(cnf_transformation,[],[f20])).
% 2.74/0.98  
% 2.74/0.98  fof(f6,axiom,(
% 2.74/0.98    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.74/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/0.98  
% 2.74/0.98  fof(f21,plain,(
% 2.74/0.98    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.74/0.98    inference(ennf_transformation,[],[f6])).
% 2.74/0.98  
% 2.74/0.98  fof(f59,plain,(
% 2.74/0.98    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.74/0.98    inference(cnf_transformation,[],[f21])).
% 2.74/0.98  
% 2.74/0.98  fof(f1,axiom,(
% 2.74/0.98    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 2.74/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/0.98  
% 2.74/0.98  fof(f37,plain,(
% 2.74/0.98    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 2.74/0.98    inference(nnf_transformation,[],[f1])).
% 2.74/0.98  
% 2.74/0.98  fof(f38,plain,(
% 2.74/0.98    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.74/0.98    inference(rectify,[],[f37])).
% 2.74/0.98  
% 2.74/0.98  fof(f39,plain,(
% 2.74/0.98    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1))))),
% 2.74/0.98    introduced(choice_axiom,[])).
% 2.74/0.98  
% 2.74/0.98  fof(f40,plain,(
% 2.74/0.98    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.74/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f38,f39])).
% 2.74/0.98  
% 2.74/0.98  fof(f51,plain,(
% 2.74/0.98    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 2.74/0.98    inference(cnf_transformation,[],[f40])).
% 2.74/0.98  
% 2.74/0.98  fof(f76,plain,(
% 2.74/0.98    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 2.74/0.98    inference(equality_resolution,[],[f51])).
% 2.74/0.98  
% 2.74/0.98  fof(f77,plain,(
% 2.74/0.98    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 2.74/0.98    inference(equality_resolution,[],[f76])).
% 2.74/0.98  
% 2.74/0.98  cnf(c_22,negated_conjecture,
% 2.74/0.98      ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 2.74/0.98      inference(cnf_transformation,[],[f72]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_1565,plain,
% 2.74/0.98      ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
% 2.74/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_12,plain,
% 2.74/0.98      ( ~ m1_subset_1(X0,X1)
% 2.74/0.98      | v1_xboole_0(X1)
% 2.74/0.98      | k6_domain_1(X1,X0) = k1_tarski(X0) ),
% 2.74/0.98      inference(cnf_transformation,[],[f62]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_1567,plain,
% 2.74/0.98      ( k6_domain_1(X0,X1) = k1_tarski(X1)
% 2.74/0.98      | m1_subset_1(X1,X0) != iProver_top
% 2.74/0.98      | v1_xboole_0(X0) = iProver_top ),
% 2.74/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_2632,plain,
% 2.74/0.98      ( k6_domain_1(u1_struct_0(sK1),sK2) = k1_tarski(sK2)
% 2.74/0.98      | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
% 2.74/0.98      inference(superposition,[status(thm)],[c_1565,c_1567]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_25,negated_conjecture,
% 2.74/0.98      ( ~ v2_struct_0(sK1) ),
% 2.74/0.98      inference(cnf_transformation,[],[f69]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_23,negated_conjecture,
% 2.74/0.98      ( l1_pre_topc(sK1) ),
% 2.74/0.98      inference(cnf_transformation,[],[f71]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_11,plain,
% 2.74/0.98      ( v2_struct_0(X0)
% 2.74/0.98      | ~ l1_struct_0(X0)
% 2.74/0.98      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.74/0.98      inference(cnf_transformation,[],[f61]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_53,plain,
% 2.74/0.98      ( v2_struct_0(sK1)
% 2.74/0.98      | ~ l1_struct_0(sK1)
% 2.74/0.98      | ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 2.74/0.98      inference(instantiation,[status(thm)],[c_11]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_10,plain,
% 2.74/0.98      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 2.74/0.98      inference(cnf_transformation,[],[f60]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_56,plain,
% 2.74/0.98      ( ~ l1_pre_topc(sK1) | l1_struct_0(sK1) ),
% 2.74/0.98      inference(instantiation,[status(thm)],[c_10]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_1700,plain,
% 2.74/0.98      ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 2.74/0.98      | v1_xboole_0(u1_struct_0(sK1))
% 2.74/0.98      | k6_domain_1(u1_struct_0(sK1),sK2) = k1_tarski(sK2) ),
% 2.74/0.98      inference(instantiation,[status(thm)],[c_12]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_2825,plain,
% 2.74/0.98      ( k6_domain_1(u1_struct_0(sK1),sK2) = k1_tarski(sK2) ),
% 2.74/0.98      inference(global_propositional_subsumption,
% 2.74/0.98                [status(thm)],
% 2.74/0.98                [c_2632,c_25,c_23,c_22,c_53,c_56,c_1700]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_6,plain,
% 2.74/0.98      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.74/0.98      inference(cnf_transformation,[],[f57]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_211,plain,
% 2.74/0.98      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.74/0.98      inference(prop_impl,[status(thm)],[c_6]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_20,negated_conjecture,
% 2.74/0.98      ( m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2))
% 2.74/0.98      | m1_connsp_2(sK3,sK1,sK2) ),
% 2.74/0.98      inference(cnf_transformation,[],[f74]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_215,plain,
% 2.74/0.98      ( m1_connsp_2(sK3,sK1,sK2)
% 2.74/0.98      | m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2)) ),
% 2.74/0.98      inference(prop_impl,[status(thm)],[c_20]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_216,plain,
% 2.74/0.98      ( m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2))
% 2.74/0.98      | m1_connsp_2(sK3,sK1,sK2) ),
% 2.74/0.98      inference(renaming,[status(thm)],[c_215]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_14,plain,
% 2.74/0.98      ( ~ m1_connsp_2(X0,X1,X2)
% 2.74/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.74/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.74/0.98      | r2_hidden(X2,k1_tops_1(X1,X0))
% 2.74/0.98      | ~ v2_pre_topc(X1)
% 2.74/0.98      | v2_struct_0(X1)
% 2.74/0.98      | ~ l1_pre_topc(X1) ),
% 2.74/0.98      inference(cnf_transformation,[],[f63]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_17,plain,
% 2.74/0.98      ( ~ m1_connsp_2(X0,X1,X2)
% 2.74/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.74/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.74/0.98      | ~ v2_pre_topc(X1)
% 2.74/0.98      | v2_struct_0(X1)
% 2.74/0.98      | ~ l1_pre_topc(X1) ),
% 2.74/0.98      inference(cnf_transformation,[],[f67]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_156,plain,
% 2.74/0.98      ( ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.74/0.98      | ~ m1_connsp_2(X0,X1,X2)
% 2.74/0.98      | r2_hidden(X2,k1_tops_1(X1,X0))
% 2.74/0.98      | ~ v2_pre_topc(X1)
% 2.74/0.98      | v2_struct_0(X1)
% 2.74/0.98      | ~ l1_pre_topc(X1) ),
% 2.74/0.98      inference(global_propositional_subsumption,
% 2.74/0.98                [status(thm)],
% 2.74/0.98                [c_14,c_17]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_157,plain,
% 2.74/0.98      ( ~ m1_connsp_2(X0,X1,X2)
% 2.74/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.74/0.98      | r2_hidden(X2,k1_tops_1(X1,X0))
% 2.74/0.98      | ~ v2_pre_topc(X1)
% 2.74/0.98      | v2_struct_0(X1)
% 2.74/0.98      | ~ l1_pre_topc(X1) ),
% 2.74/0.98      inference(renaming,[status(thm)],[c_156]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_482,plain,
% 2.74/0.98      ( ~ m1_connsp_2(X0,X1,X2)
% 2.74/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.74/0.98      | r2_hidden(X2,k1_tops_1(X1,X0))
% 2.74/0.98      | ~ v2_pre_topc(X1)
% 2.74/0.98      | ~ l1_pre_topc(X1)
% 2.74/0.98      | sK1 != X1 ),
% 2.74/0.98      inference(resolution_lifted,[status(thm)],[c_157,c_25]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_483,plain,
% 2.74/0.98      ( ~ m1_connsp_2(X0,sK1,X1)
% 2.74/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.74/0.98      | r2_hidden(X1,k1_tops_1(sK1,X0))
% 2.74/0.98      | ~ v2_pre_topc(sK1)
% 2.74/0.98      | ~ l1_pre_topc(sK1) ),
% 2.74/0.98      inference(unflattening,[status(thm)],[c_482]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_24,negated_conjecture,
% 2.74/0.98      ( v2_pre_topc(sK1) ),
% 2.74/0.98      inference(cnf_transformation,[],[f70]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_487,plain,
% 2.74/0.98      ( ~ m1_connsp_2(X0,sK1,X1)
% 2.74/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.74/0.98      | r2_hidden(X1,k1_tops_1(sK1,X0)) ),
% 2.74/0.98      inference(global_propositional_subsumption,
% 2.74/0.98                [status(thm)],
% 2.74/0.98                [c_483,c_24,c_23]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_788,plain,
% 2.74/0.98      ( m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2))
% 2.74/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.74/0.98      | r2_hidden(X0,k1_tops_1(sK1,X1))
% 2.74/0.98      | sK2 != X0
% 2.74/0.98      | sK1 != sK1
% 2.74/0.98      | sK3 != X1 ),
% 2.74/0.98      inference(resolution_lifted,[status(thm)],[c_216,c_487]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_789,plain,
% 2.74/0.98      ( m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2))
% 2.74/0.98      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 2.74/0.98      | r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
% 2.74/0.98      inference(unflattening,[status(thm)],[c_788]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_791,plain,
% 2.74/0.98      ( m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2))
% 2.74/0.98      | r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
% 2.74/0.98      inference(global_propositional_subsumption,
% 2.74/0.98                [status(thm)],
% 2.74/0.98                [c_789,c_22]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_16,plain,
% 2.74/0.98      ( ~ m2_connsp_2(X0,X1,X2)
% 2.74/0.98      | r1_tarski(X2,k1_tops_1(X1,X0))
% 2.74/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.74/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.74/0.98      | ~ v2_pre_topc(X1)
% 2.74/0.98      | ~ l1_pre_topc(X1) ),
% 2.74/0.98      inference(cnf_transformation,[],[f65]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_18,plain,
% 2.74/0.98      ( ~ m2_connsp_2(X0,X1,X2)
% 2.74/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.74/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.74/0.98      | ~ v2_pre_topc(X1)
% 2.74/0.98      | ~ l1_pre_topc(X1) ),
% 2.74/0.98      inference(cnf_transformation,[],[f68]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_150,plain,
% 2.74/0.98      ( r1_tarski(X2,k1_tops_1(X1,X0))
% 2.74/0.98      | ~ m2_connsp_2(X0,X1,X2)
% 2.74/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.74/0.98      | ~ v2_pre_topc(X1)
% 2.74/0.98      | ~ l1_pre_topc(X1) ),
% 2.74/0.98      inference(global_propositional_subsumption,
% 2.74/0.98                [status(thm)],
% 2.74/0.98                [c_16,c_18]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_151,plain,
% 2.74/0.98      ( ~ m2_connsp_2(X0,X1,X2)
% 2.74/0.98      | r1_tarski(X2,k1_tops_1(X1,X0))
% 2.74/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.74/0.98      | ~ v2_pre_topc(X1)
% 2.74/0.98      | ~ l1_pre_topc(X1) ),
% 2.74/0.98      inference(renaming,[status(thm)],[c_150]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_629,plain,
% 2.74/0.98      ( ~ m2_connsp_2(X0,X1,X2)
% 2.74/0.98      | r1_tarski(X2,k1_tops_1(X1,X0))
% 2.74/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.74/0.98      | ~ v2_pre_topc(X1)
% 2.74/0.98      | sK1 != X1 ),
% 2.74/0.98      inference(resolution_lifted,[status(thm)],[c_151,c_23]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_630,plain,
% 2.74/0.98      ( ~ m2_connsp_2(X0,sK1,X1)
% 2.74/0.98      | r1_tarski(X1,k1_tops_1(sK1,X0))
% 2.74/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.74/0.98      | ~ v2_pre_topc(sK1) ),
% 2.74/0.98      inference(unflattening,[status(thm)],[c_629]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_634,plain,
% 2.74/0.98      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.74/0.98      | r1_tarski(X1,k1_tops_1(sK1,X0))
% 2.74/0.98      | ~ m2_connsp_2(X0,sK1,X1) ),
% 2.74/0.98      inference(global_propositional_subsumption,
% 2.74/0.98                [status(thm)],
% 2.74/0.98                [c_630,c_24]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_635,plain,
% 2.74/0.98      ( ~ m2_connsp_2(X0,sK1,X1)
% 2.74/0.98      | r1_tarski(X1,k1_tops_1(sK1,X0))
% 2.74/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.74/0.98      inference(renaming,[status(thm)],[c_634]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_827,plain,
% 2.74/0.98      ( r1_tarski(X0,k1_tops_1(sK1,X1))
% 2.74/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.74/0.98      | r2_hidden(sK2,k1_tops_1(sK1,sK3))
% 2.74/0.98      | k6_domain_1(u1_struct_0(sK1),sK2) != X0
% 2.74/0.98      | sK1 != sK1
% 2.74/0.98      | sK3 != X1 ),
% 2.74/0.98      inference(resolution_lifted,[status(thm)],[c_791,c_635]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_828,plain,
% 2.74/0.98      ( r1_tarski(k6_domain_1(u1_struct_0(sK1),sK2),k1_tops_1(sK1,sK3))
% 2.74/0.98      | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.74/0.98      | r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
% 2.74/0.98      inference(unflattening,[status(thm)],[c_827]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_910,plain,
% 2.74/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.74/0.98      | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.74/0.98      | r2_hidden(sK2,k1_tops_1(sK1,sK3))
% 2.74/0.98      | k1_tops_1(sK1,sK3) != X1
% 2.74/0.98      | k6_domain_1(u1_struct_0(sK1),sK2) != X0 ),
% 2.74/0.98      inference(resolution_lifted,[status(thm)],[c_211,c_828]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_911,plain,
% 2.74/0.98      ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(k1_tops_1(sK1,sK3)))
% 2.74/0.98      | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.74/0.98      | r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
% 2.74/0.98      inference(unflattening,[status(thm)],[c_910]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_1560,plain,
% 2.74/0.98      ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(k1_tops_1(sK1,sK3))) = iProver_top
% 2.74/0.98      | m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.74/0.98      | r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top ),
% 2.74/0.98      inference(predicate_to_equality,[status(thm)],[c_911]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_2831,plain,
% 2.74/0.98      ( m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(k1_tops_1(sK1,sK3))) = iProver_top
% 2.74/0.98      | m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.74/0.98      | r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top ),
% 2.74/0.98      inference(demodulation,[status(thm)],[c_2825,c_1560]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_26,plain,
% 2.74/0.98      ( v2_struct_0(sK1) != iProver_top ),
% 2.74/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_28,plain,
% 2.74/0.98      ( l1_pre_topc(sK1) = iProver_top ),
% 2.74/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_29,plain,
% 2.74/0.98      ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
% 2.74/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_52,plain,
% 2.74/0.98      ( v2_struct_0(X0) = iProver_top
% 2.74/0.98      | l1_struct_0(X0) != iProver_top
% 2.74/0.98      | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
% 2.74/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_54,plain,
% 2.74/0.98      ( v2_struct_0(sK1) = iProver_top
% 2.74/0.98      | l1_struct_0(sK1) != iProver_top
% 2.74/0.98      | v1_xboole_0(u1_struct_0(sK1)) != iProver_top ),
% 2.74/0.98      inference(instantiation,[status(thm)],[c_52]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_55,plain,
% 2.74/0.98      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 2.74/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_57,plain,
% 2.74/0.98      ( l1_pre_topc(sK1) != iProver_top
% 2.74/0.98      | l1_struct_0(sK1) = iProver_top ),
% 2.74/0.98      inference(instantiation,[status(thm)],[c_55]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_5,plain,
% 2.74/0.98      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.74/0.98      inference(cnf_transformation,[],[f55]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_1694,plain,
% 2.74/0.98      ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 2.74/0.98      | r2_hidden(sK2,u1_struct_0(sK1))
% 2.74/0.98      | v1_xboole_0(u1_struct_0(sK1)) ),
% 2.74/0.98      inference(instantiation,[status(thm)],[c_5]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_1695,plain,
% 2.74/0.98      ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 2.74/0.98      | r2_hidden(sK2,u1_struct_0(sK1)) = iProver_top
% 2.74/0.98      | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
% 2.74/0.98      inference(predicate_to_equality,[status(thm)],[c_1694]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_4,plain,
% 2.74/0.98      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~ r2_hidden(X0,X1) ),
% 2.74/0.98      inference(cnf_transformation,[],[f54]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_1749,plain,
% 2.74/0.98      ( m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.74/0.98      | ~ r2_hidden(sK2,u1_struct_0(sK1)) ),
% 2.74/0.98      inference(instantiation,[status(thm)],[c_4]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_1750,plain,
% 2.74/0.98      ( m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 2.74/0.98      | r2_hidden(sK2,u1_struct_0(sK1)) != iProver_top ),
% 2.74/0.98      inference(predicate_to_equality,[status(thm)],[c_1749]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_7,plain,
% 2.74/0.98      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.74/0.98      inference(cnf_transformation,[],[f56]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_209,plain,
% 2.74/0.98      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.74/0.98      inference(prop_impl,[status(thm)],[c_7]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_19,negated_conjecture,
% 2.74/0.98      ( ~ m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2))
% 2.74/0.98      | ~ m1_connsp_2(sK3,sK1,sK2) ),
% 2.74/0.98      inference(cnf_transformation,[],[f75]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_213,plain,
% 2.74/0.98      ( ~ m1_connsp_2(sK3,sK1,sK2)
% 2.74/0.98      | ~ m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2)) ),
% 2.74/0.98      inference(prop_impl,[status(thm)],[c_19]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_214,plain,
% 2.74/0.98      ( ~ m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2))
% 2.74/0.98      | ~ m1_connsp_2(sK3,sK1,sK2) ),
% 2.74/0.98      inference(renaming,[status(thm)],[c_213]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_13,plain,
% 2.74/0.98      ( m1_connsp_2(X0,X1,X2)
% 2.74/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.74/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.74/0.98      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 2.74/0.98      | ~ v2_pre_topc(X1)
% 2.74/0.98      | v2_struct_0(X1)
% 2.74/0.98      | ~ l1_pre_topc(X1) ),
% 2.74/0.98      inference(cnf_transformation,[],[f64]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_524,plain,
% 2.74/0.98      ( m1_connsp_2(X0,X1,X2)
% 2.74/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.74/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.74/0.98      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 2.74/0.98      | ~ v2_pre_topc(X1)
% 2.74/0.98      | ~ l1_pre_topc(X1)
% 2.74/0.98      | sK1 != X1 ),
% 2.74/0.98      inference(resolution_lifted,[status(thm)],[c_13,c_25]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_525,plain,
% 2.74/0.98      ( m1_connsp_2(X0,sK1,X1)
% 2.74/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.74/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.74/0.98      | ~ r2_hidden(X1,k1_tops_1(sK1,X0))
% 2.74/0.98      | ~ v2_pre_topc(sK1)
% 2.74/0.98      | ~ l1_pre_topc(sK1) ),
% 2.74/0.98      inference(unflattening,[status(thm)],[c_524]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_529,plain,
% 2.74/0.98      ( m1_connsp_2(X0,sK1,X1)
% 2.74/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.74/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.74/0.98      | ~ r2_hidden(X1,k1_tops_1(sK1,X0)) ),
% 2.74/0.98      inference(global_propositional_subsumption,
% 2.74/0.98                [status(thm)],
% 2.74/0.98                [c_525,c_24,c_23]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_802,plain,
% 2.74/0.98      ( ~ m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2))
% 2.74/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.74/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.74/0.98      | ~ r2_hidden(X0,k1_tops_1(sK1,X1))
% 2.74/0.98      | sK2 != X0
% 2.74/0.98      | sK1 != sK1
% 2.74/0.98      | sK3 != X1 ),
% 2.74/0.98      inference(resolution_lifted,[status(thm)],[c_214,c_529]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_803,plain,
% 2.74/0.98      ( ~ m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2))
% 2.74/0.98      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 2.74/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.74/0.98      | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
% 2.74/0.98      inference(unflattening,[status(thm)],[c_802]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_21,negated_conjecture,
% 2.74/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.74/0.98      inference(cnf_transformation,[],[f73]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_805,plain,
% 2.74/0.98      ( ~ m2_connsp_2(sK3,sK1,k6_domain_1(u1_struct_0(sK1),sK2))
% 2.74/0.98      | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
% 2.74/0.98      inference(global_propositional_subsumption,
% 2.74/0.98                [status(thm)],
% 2.74/0.98                [c_803,c_22,c_21]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_15,plain,
% 2.74/0.98      ( m2_connsp_2(X0,X1,X2)
% 2.74/0.98      | ~ r1_tarski(X2,k1_tops_1(X1,X0))
% 2.74/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.74/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.74/0.98      | ~ v2_pre_topc(X1)
% 2.74/0.98      | ~ l1_pre_topc(X1) ),
% 2.74/0.98      inference(cnf_transformation,[],[f66]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_667,plain,
% 2.74/0.98      ( m2_connsp_2(X0,X1,X2)
% 2.74/0.98      | ~ r1_tarski(X2,k1_tops_1(X1,X0))
% 2.74/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.74/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.74/0.98      | ~ v2_pre_topc(X1)
% 2.74/0.98      | sK1 != X1 ),
% 2.74/0.98      inference(resolution_lifted,[status(thm)],[c_15,c_23]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_668,plain,
% 2.74/0.98      ( m2_connsp_2(X0,sK1,X1)
% 2.74/0.98      | ~ r1_tarski(X1,k1_tops_1(sK1,X0))
% 2.74/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.74/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.74/0.98      | ~ v2_pre_topc(sK1) ),
% 2.74/0.98      inference(unflattening,[status(thm)],[c_667]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_672,plain,
% 2.74/0.98      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.74/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.74/0.98      | ~ r1_tarski(X1,k1_tops_1(sK1,X0))
% 2.74/0.98      | m2_connsp_2(X0,sK1,X1) ),
% 2.74/0.98      inference(global_propositional_subsumption,
% 2.74/0.98                [status(thm)],
% 2.74/0.98                [c_668,c_24]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_673,plain,
% 2.74/0.98      ( m2_connsp_2(X0,sK1,X1)
% 2.74/0.98      | ~ r1_tarski(X1,k1_tops_1(sK1,X0))
% 2.74/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.74/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.74/0.98      inference(renaming,[status(thm)],[c_672]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_840,plain,
% 2.74/0.98      ( ~ r1_tarski(X0,k1_tops_1(sK1,X1))
% 2.74/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.74/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.74/0.98      | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3))
% 2.74/0.98      | k6_domain_1(u1_struct_0(sK1),sK2) != X0
% 2.74/0.98      | sK1 != sK1
% 2.74/0.98      | sK3 != X1 ),
% 2.74/0.98      inference(resolution_lifted,[status(thm)],[c_805,c_673]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_841,plain,
% 2.74/0.98      ( ~ r1_tarski(k6_domain_1(u1_struct_0(sK1),sK2),k1_tops_1(sK1,sK3))
% 2.74/0.98      | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.74/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.74/0.98      | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
% 2.74/0.98      inference(unflattening,[status(thm)],[c_840]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_843,plain,
% 2.74/0.98      ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.74/0.98      | ~ r1_tarski(k6_domain_1(u1_struct_0(sK1),sK2),k1_tops_1(sK1,sK3))
% 2.74/0.98      | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
% 2.74/0.98      inference(global_propositional_subsumption,
% 2.74/0.98                [status(thm)],
% 2.74/0.98                [c_841,c_21]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_844,plain,
% 2.74/0.98      ( ~ r1_tarski(k6_domain_1(u1_struct_0(sK1),sK2),k1_tops_1(sK1,sK3))
% 2.74/0.98      | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.74/0.98      | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
% 2.74/0.98      inference(renaming,[status(thm)],[c_843]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_879,plain,
% 2.74/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.74/0.98      | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.74/0.98      | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3))
% 2.74/0.98      | k1_tops_1(sK1,sK3) != X1
% 2.74/0.98      | k6_domain_1(u1_struct_0(sK1),sK2) != X0 ),
% 2.74/0.98      inference(resolution_lifted,[status(thm)],[c_209,c_844]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_880,plain,
% 2.74/0.98      ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(k1_tops_1(sK1,sK3)))
% 2.74/0.98      | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.74/0.98      | ~ r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
% 2.74/0.98      inference(unflattening,[status(thm)],[c_879]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_1563,plain,
% 2.74/0.98      ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(k1_tops_1(sK1,sK3))) != iProver_top
% 2.74/0.98      | m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.74/0.98      | r2_hidden(sK2,k1_tops_1(sK1,sK3)) != iProver_top ),
% 2.74/0.98      inference(predicate_to_equality,[status(thm)],[c_880]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_2832,plain,
% 2.74/0.98      ( m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(k1_tops_1(sK1,sK3))) != iProver_top
% 2.74/0.98      | m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.74/0.98      | r2_hidden(sK2,k1_tops_1(sK1,sK3)) != iProver_top ),
% 2.74/0.98      inference(demodulation,[status(thm)],[c_2825,c_1563]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_3263,plain,
% 2.74/0.98      ( m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(k1_tops_1(sK1,sK3))) != iProver_top
% 2.74/0.98      | r2_hidden(sK2,k1_tops_1(sK1,sK3)) != iProver_top ),
% 2.74/0.98      inference(global_propositional_subsumption,
% 2.74/0.98                [status(thm)],
% 2.74/0.98                [c_2832,c_26,c_28,c_29,c_54,c_57,c_1695,c_1750]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_1571,plain,
% 2.74/0.98      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) = iProver_top
% 2.74/0.98      | r2_hidden(X0,X1) != iProver_top ),
% 2.74/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_3269,plain,
% 2.74/0.98      ( r2_hidden(sK2,k1_tops_1(sK1,sK3)) != iProver_top ),
% 2.74/0.98      inference(forward_subsumption_resolution,
% 2.74/0.98                [status(thm)],
% 2.74/0.98                [c_3263,c_1571]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_3336,plain,
% 2.74/0.98      ( m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(k1_tops_1(sK1,sK3))) = iProver_top ),
% 2.74/0.98      inference(global_propositional_subsumption,
% 2.74/0.98                [status(thm)],
% 2.74/0.98                [c_2831,c_26,c_28,c_29,c_54,c_57,c_1695,c_1750,c_3269]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_8,plain,
% 2.74/0.98      ( m1_subset_1(X0,X1)
% 2.74/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.74/0.98      | ~ r2_hidden(X0,X2) ),
% 2.74/0.98      inference(cnf_transformation,[],[f58]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_1569,plain,
% 2.74/0.98      ( m1_subset_1(X0,X1) = iProver_top
% 2.74/0.98      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 2.74/0.98      | r2_hidden(X0,X2) != iProver_top ),
% 2.74/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_3343,plain,
% 2.74/0.98      ( m1_subset_1(X0,k1_tops_1(sK1,sK3)) = iProver_top
% 2.74/0.98      | r2_hidden(X0,k1_tarski(sK2)) != iProver_top ),
% 2.74/0.98      inference(superposition,[status(thm)],[c_3336,c_1569]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_1570,plain,
% 2.74/0.98      ( m1_subset_1(X0,X1) != iProver_top
% 2.74/0.98      | r2_hidden(X0,X1) = iProver_top
% 2.74/0.98      | v1_xboole_0(X1) = iProver_top ),
% 2.74/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_3764,plain,
% 2.74/0.98      ( r2_hidden(X0,k1_tops_1(sK1,sK3)) = iProver_top
% 2.74/0.98      | r2_hidden(X0,k1_tarski(sK2)) != iProver_top
% 2.74/0.98      | v1_xboole_0(k1_tops_1(sK1,sK3)) = iProver_top ),
% 2.74/0.98      inference(superposition,[status(thm)],[c_3343,c_1570]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_9,plain,
% 2.74/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.74/0.98      | ~ r2_hidden(X2,X0)
% 2.74/0.98      | ~ v1_xboole_0(X1) ),
% 2.74/0.98      inference(cnf_transformation,[],[f59]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_271,plain,
% 2.74/0.98      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | ~ v1_xboole_0(X1) ),
% 2.74/0.98      inference(bin_hyper_res,[status(thm)],[c_9,c_211]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_892,plain,
% 2.74/0.98      ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.74/0.98      | ~ r2_hidden(X0,X1)
% 2.74/0.98      | r2_hidden(sK2,k1_tops_1(sK1,sK3))
% 2.74/0.98      | ~ v1_xboole_0(X2)
% 2.74/0.98      | k1_tops_1(sK1,sK3) != X2
% 2.74/0.98      | k6_domain_1(u1_struct_0(sK1),sK2) != X1 ),
% 2.74/0.98      inference(resolution_lifted,[status(thm)],[c_271,c_828]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_893,plain,
% 2.74/0.98      ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.74/0.98      | ~ r2_hidden(X0,k6_domain_1(u1_struct_0(sK1),sK2))
% 2.74/0.98      | r2_hidden(sK2,k1_tops_1(sK1,sK3))
% 2.74/0.98      | ~ v1_xboole_0(k1_tops_1(sK1,sK3)) ),
% 2.74/0.98      inference(unflattening,[status(thm)],[c_892]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_1269,plain,
% 2.74/0.98      ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.74/0.98      | r2_hidden(sK2,k1_tops_1(sK1,sK3))
% 2.74/0.98      | ~ v1_xboole_0(k1_tops_1(sK1,sK3))
% 2.74/0.98      | sP0_iProver_split ),
% 2.74/0.98      inference(splitting,
% 2.74/0.98                [splitting(split),new_symbols(definition,[])],
% 2.74/0.98                [c_893]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_1290,plain,
% 2.74/0.98      ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.74/0.98      | r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top
% 2.74/0.98      | v1_xboole_0(k1_tops_1(sK1,sK3)) != iProver_top
% 2.74/0.98      | sP0_iProver_split = iProver_top ),
% 2.74/0.98      inference(predicate_to_equality,[status(thm)],[c_1269]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_1271,plain,( X0 = X0 ),theory(equality) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_1950,plain,
% 2.74/0.98      ( k1_zfmisc_1(u1_struct_0(sK1)) = k1_zfmisc_1(u1_struct_0(sK1)) ),
% 2.74/0.98      inference(instantiation,[status(thm)],[c_1271]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_2,plain,
% 2.74/0.98      ( r2_hidden(X0,k1_tarski(X0)) ),
% 2.74/0.98      inference(cnf_transformation,[],[f77]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_1573,plain,
% 2.74/0.98      ( r2_hidden(X0,k1_tarski(X0)) = iProver_top ),
% 2.74/0.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_1268,plain,
% 2.74/0.98      ( ~ r2_hidden(X0,k6_domain_1(u1_struct_0(sK1),sK2))
% 2.74/0.98      | ~ sP0_iProver_split ),
% 2.74/0.98      inference(splitting,
% 2.74/0.98                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.74/0.98                [c_893]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_1562,plain,
% 2.74/0.98      ( r2_hidden(X0,k6_domain_1(u1_struct_0(sK1),sK2)) != iProver_top
% 2.74/0.98      | sP0_iProver_split != iProver_top ),
% 2.74/0.98      inference(predicate_to_equality,[status(thm)],[c_1268]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_2833,plain,
% 2.74/0.98      ( r2_hidden(X0,k1_tarski(sK2)) != iProver_top
% 2.74/0.98      | sP0_iProver_split != iProver_top ),
% 2.74/0.98      inference(demodulation,[status(thm)],[c_2825,c_1562]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_3114,plain,
% 2.74/0.98      ( sP0_iProver_split != iProver_top ),
% 2.74/0.98      inference(superposition,[status(thm)],[c_1573,c_2833]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_1275,plain,
% 2.74/0.98      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.74/0.98      theory(equality) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_1845,plain,
% 2.74/0.98      ( m1_subset_1(X0,X1)
% 2.74/0.98      | ~ m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.74/0.98      | X1 != k1_zfmisc_1(u1_struct_0(sK1))
% 2.74/0.98      | X0 != k1_tarski(sK2) ),
% 2.74/0.98      inference(instantiation,[status(thm)],[c_1275]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_2481,plain,
% 2.74/0.98      ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),X0)
% 2.74/0.98      | ~ m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.74/0.98      | X0 != k1_zfmisc_1(u1_struct_0(sK1))
% 2.74/0.98      | k6_domain_1(u1_struct_0(sK1),sK2) != k1_tarski(sK2) ),
% 2.74/0.98      inference(instantiation,[status(thm)],[c_1845]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_3128,plain,
% 2.74/0.98      ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.74/0.98      | ~ m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.74/0.98      | k6_domain_1(u1_struct_0(sK1),sK2) != k1_tarski(sK2)
% 2.74/0.98      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 2.74/0.98      inference(instantiation,[status(thm)],[c_2481]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_3129,plain,
% 2.74/0.98      ( k6_domain_1(u1_struct_0(sK1),sK2) != k1_tarski(sK2)
% 2.74/0.98      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
% 2.74/0.98      | m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 2.74/0.98      | m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.74/0.98      inference(predicate_to_equality,[status(thm)],[c_3128]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_4081,plain,
% 2.74/0.98      ( r2_hidden(X0,k1_tarski(sK2)) != iProver_top
% 2.74/0.98      | r2_hidden(X0,k1_tops_1(sK1,sK3)) = iProver_top ),
% 2.74/0.98      inference(global_propositional_subsumption,
% 2.74/0.98                [status(thm)],
% 2.74/0.98                [c_3764,c_25,c_26,c_23,c_28,c_22,c_29,c_53,c_54,c_56,
% 2.74/0.98                 c_57,c_1290,c_1695,c_1700,c_1750,c_1950,c_3114,c_3129,
% 2.74/0.98                 c_3269]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_4082,plain,
% 2.74/0.98      ( r2_hidden(X0,k1_tops_1(sK1,sK3)) = iProver_top
% 2.74/0.98      | r2_hidden(X0,k1_tarski(sK2)) != iProver_top ),
% 2.74/0.98      inference(renaming,[status(thm)],[c_4081]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_4090,plain,
% 2.74/0.98      ( r2_hidden(sK2,k1_tarski(sK2)) != iProver_top ),
% 2.74/0.98      inference(superposition,[status(thm)],[c_4082,c_3269]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_2240,plain,
% 2.74/0.98      ( r2_hidden(sK2,k1_tarski(sK2)) ),
% 2.74/0.98      inference(instantiation,[status(thm)],[c_2]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(c_2241,plain,
% 2.74/0.98      ( r2_hidden(sK2,k1_tarski(sK2)) = iProver_top ),
% 2.74/0.98      inference(predicate_to_equality,[status(thm)],[c_2240]) ).
% 2.74/0.98  
% 2.74/0.98  cnf(contradiction,plain,
% 2.74/0.98      ( $false ),
% 2.74/0.98      inference(minisat,[status(thm)],[c_4090,c_2241]) ).
% 2.74/0.98  
% 2.74/0.98  
% 2.74/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.74/0.98  
% 2.74/0.98  ------                               Statistics
% 2.74/0.98  
% 2.74/0.98  ------ General
% 2.74/0.98  
% 2.74/0.98  abstr_ref_over_cycles:                  0
% 2.74/0.98  abstr_ref_under_cycles:                 0
% 2.74/0.98  gc_basic_clause_elim:                   0
% 2.74/0.98  forced_gc_time:                         0
% 2.74/0.98  parsing_time:                           0.01
% 2.74/0.98  unif_index_cands_time:                  0.
% 2.74/0.98  unif_index_add_time:                    0.
% 2.74/0.98  orderings_time:                         0.
% 2.74/0.98  out_proof_time:                         0.01
% 2.74/0.98  total_time:                             0.148
% 2.74/0.98  num_of_symbols:                         51
% 2.74/0.98  num_of_terms:                           3530
% 2.74/0.98  
% 2.74/0.98  ------ Preprocessing
% 2.74/0.98  
% 2.74/0.98  num_of_splits:                          1
% 2.74/0.98  num_of_split_atoms:                     1
% 2.74/0.98  num_of_reused_defs:                     0
% 2.74/0.98  num_eq_ax_congr_red:                    13
% 2.74/0.98  num_of_sem_filtered_clauses:            1
% 2.74/0.98  num_of_subtypes:                        0
% 2.74/0.98  monotx_restored_types:                  0
% 2.74/0.98  sat_num_of_epr_types:                   0
% 2.74/0.98  sat_num_of_non_cyclic_types:            0
% 2.74/0.98  sat_guarded_non_collapsed_types:        0
% 2.74/0.98  num_pure_diseq_elim:                    0
% 2.74/0.98  simp_replaced_by:                       0
% 2.74/0.98  res_preprocessed:                       92
% 2.74/0.98  prep_upred:                             0
% 2.74/0.98  prep_unflattend:                        43
% 2.74/0.98  smt_new_axioms:                         0
% 2.74/0.98  pred_elim_cands:                        3
% 2.74/0.98  pred_elim:                              7
% 2.74/0.98  pred_elim_cl:                           11
% 2.74/0.98  pred_elim_cycles:                       12
% 2.74/0.98  merged_defs:                            4
% 2.74/0.98  merged_defs_ncl:                        0
% 2.74/0.98  bin_hyper_res:                          5
% 2.74/0.98  prep_cycles:                            4
% 2.74/0.98  pred_elim_time:                         0.014
% 2.74/0.98  splitting_time:                         0.
% 2.74/0.98  sem_filter_time:                        0.
% 2.74/0.98  monotx_time:                            0.
% 2.74/0.98  subtype_inf_time:                       0.
% 2.74/0.98  
% 2.74/0.98  ------ Problem properties
% 2.74/0.98  
% 2.74/0.98  clauses:                                16
% 2.74/0.98  conjectures:                            2
% 2.74/0.98  epr:                                    1
% 2.74/0.98  horn:                                   11
% 2.74/0.98  ground:                                 6
% 2.74/0.98  unary:                                  4
% 2.74/0.98  binary:                                 3
% 2.74/0.98  lits:                                   38
% 2.74/0.98  lits_eq:                                6
% 2.74/0.98  fd_pure:                                0
% 2.74/0.98  fd_pseudo:                              0
% 2.74/0.98  fd_cond:                                0
% 2.74/0.98  fd_pseudo_cond:                         2
% 2.74/0.98  ac_symbols:                             0
% 2.74/0.98  
% 2.74/0.98  ------ Propositional Solver
% 2.74/0.98  
% 2.74/0.98  prop_solver_calls:                      27
% 2.74/0.98  prop_fast_solver_calls:                 792
% 2.74/0.98  smt_solver_calls:                       0
% 2.74/0.98  smt_fast_solver_calls:                  0
% 2.74/0.98  prop_num_of_clauses:                    1465
% 2.74/0.98  prop_preprocess_simplified:             4424
% 2.74/0.98  prop_fo_subsumed:                       34
% 2.74/0.98  prop_solver_time:                       0.
% 2.74/0.98  smt_solver_time:                        0.
% 2.74/0.98  smt_fast_solver_time:                   0.
% 2.74/0.98  prop_fast_solver_time:                  0.
% 2.74/0.98  prop_unsat_core_time:                   0.
% 2.74/0.98  
% 2.74/0.98  ------ QBF
% 2.74/0.98  
% 2.74/0.98  qbf_q_res:                              0
% 2.74/0.98  qbf_num_tautologies:                    0
% 2.74/0.98  qbf_prep_cycles:                        0
% 2.74/0.98  
% 2.74/0.98  ------ BMC1
% 2.74/0.98  
% 2.74/0.98  bmc1_current_bound:                     -1
% 2.74/0.98  bmc1_last_solved_bound:                 -1
% 2.74/0.98  bmc1_unsat_core_size:                   -1
% 2.74/0.98  bmc1_unsat_core_parents_size:           -1
% 2.74/0.98  bmc1_merge_next_fun:                    0
% 2.74/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.74/0.98  
% 2.74/0.98  ------ Instantiation
% 2.74/0.98  
% 2.74/0.98  inst_num_of_clauses:                    393
% 2.74/0.98  inst_num_in_passive:                    54
% 2.74/0.98  inst_num_in_active:                     172
% 2.74/0.98  inst_num_in_unprocessed:                167
% 2.74/0.98  inst_num_of_loops:                      200
% 2.74/0.98  inst_num_of_learning_restarts:          0
% 2.74/0.98  inst_num_moves_active_passive:          26
% 2.74/0.98  inst_lit_activity:                      0
% 2.74/0.98  inst_lit_activity_moves:                0
% 2.74/0.98  inst_num_tautologies:                   0
% 2.74/0.98  inst_num_prop_implied:                  0
% 2.74/0.98  inst_num_existing_simplified:           0
% 2.74/0.98  inst_num_eq_res_simplified:             0
% 2.74/0.98  inst_num_child_elim:                    0
% 2.74/0.98  inst_num_of_dismatching_blockings:      140
% 2.74/0.98  inst_num_of_non_proper_insts:           366
% 2.74/0.98  inst_num_of_duplicates:                 0
% 2.74/0.98  inst_inst_num_from_inst_to_res:         0
% 2.74/0.98  inst_dismatching_checking_time:         0.
% 2.74/0.98  
% 2.74/0.98  ------ Resolution
% 2.74/0.98  
% 2.74/0.98  res_num_of_clauses:                     0
% 2.74/0.98  res_num_in_passive:                     0
% 2.74/0.98  res_num_in_active:                      0
% 2.74/0.98  res_num_of_loops:                       96
% 2.74/0.98  res_forward_subset_subsumed:            38
% 2.74/0.98  res_backward_subset_subsumed:           0
% 2.74/0.98  res_forward_subsumed:                   0
% 2.74/0.98  res_backward_subsumed:                  0
% 2.74/0.98  res_forward_subsumption_resolution:     0
% 2.74/0.98  res_backward_subsumption_resolution:    0
% 2.74/0.98  res_clause_to_clause_subsumption:       166
% 2.74/0.98  res_orphan_elimination:                 0
% 2.74/0.98  res_tautology_del:                      45
% 2.74/0.98  res_num_eq_res_simplified:              0
% 2.74/0.98  res_num_sel_changes:                    0
% 2.74/0.98  res_moves_from_active_to_pass:          0
% 2.74/0.98  
% 2.74/0.98  ------ Superposition
% 2.74/0.98  
% 2.74/0.98  sup_time_total:                         0.
% 2.74/0.98  sup_time_generating:                    0.
% 2.74/0.98  sup_time_sim_full:                      0.
% 2.74/0.98  sup_time_sim_immed:                     0.
% 2.74/0.98  
% 2.74/0.98  sup_num_of_clauses:                     44
% 2.74/0.98  sup_num_in_active:                      33
% 2.74/0.98  sup_num_in_passive:                     11
% 2.74/0.98  sup_num_of_loops:                       39
% 2.74/0.98  sup_fw_superposition:                   26
% 2.74/0.98  sup_bw_superposition:                   16
% 2.74/0.98  sup_immediate_simplified:               7
% 2.74/0.98  sup_given_eliminated:                   1
% 2.74/0.98  comparisons_done:                       0
% 2.74/0.98  comparisons_avoided:                    7
% 2.74/0.98  
% 2.74/0.98  ------ Simplifications
% 2.74/0.98  
% 2.74/0.98  
% 2.74/0.98  sim_fw_subset_subsumed:                 7
% 2.74/0.98  sim_bw_subset_subsumed:                 0
% 2.74/0.98  sim_fw_subsumed:                        0
% 2.74/0.98  sim_bw_subsumed:                        1
% 2.74/0.98  sim_fw_subsumption_res:                 1
% 2.74/0.98  sim_bw_subsumption_res:                 0
% 2.74/0.98  sim_tautology_del:                      1
% 2.74/0.98  sim_eq_tautology_del:                   1
% 2.74/0.98  sim_eq_res_simp:                        0
% 2.74/0.98  sim_fw_demodulated:                     0
% 2.74/0.98  sim_bw_demodulated:                     6
% 2.74/0.98  sim_light_normalised:                   0
% 2.74/0.98  sim_joinable_taut:                      0
% 2.74/0.98  sim_joinable_simp:                      0
% 2.74/0.98  sim_ac_normalised:                      0
% 2.74/0.98  sim_smt_subsumption:                    0
% 2.74/0.98  
%------------------------------------------------------------------------------
