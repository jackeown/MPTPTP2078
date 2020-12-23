%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:25:44 EST 2020

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :  222 (1430 expanded)
%              Number of clauses        :  152 ( 487 expanded)
%              Number of leaves         :   20 ( 278 expanded)
%              Depth                    :   30
%              Number of atoms          :  819 (7062 expanded)
%              Number of equality atoms :  283 ( 762 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f52,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ? [X2] :
                  ( ~ v1_subset_1(X2,u1_struct_0(X0))
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v1_subset_1(X2,u1_struct_0(X0))
                  | u1_struct_0(X1) != X2
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ? [X2] :
                  ( ~ v1_subset_1(X2,u1_struct_0(X0))
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v1_subset_1(X3,u1_struct_0(X0))
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f42])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v1_subset_1(X2,u1_struct_0(X0))
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_subset_1(sK0(X0,X1),u1_struct_0(X0))
        & u1_struct_0(X1) = sK0(X0,X1)
        & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ( ~ v1_subset_1(sK0(X0,X1),u1_struct_0(X0))
                & u1_struct_0(X1) = sK0(X0,X1)
                & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v1_subset_1(X3,u1_struct_0(X0))
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f43,f44])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( v1_tex_2(k1_tex_2(X0,X1),X0)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f48,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f50,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),sK2),u1_struct_0(X0))
          | ~ v1_tex_2(k1_tex_2(X0,sK2),X0) )
        & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),sK2),u1_struct_0(X0))
          | v1_tex_2(k1_tex_2(X0,sK2),X0) )
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
              | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
            & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
              | v1_tex_2(k1_tex_2(X0,X1),X0) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),X1),u1_struct_0(sK1))
            | ~ v1_tex_2(k1_tex_2(sK1,X1),sK1) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),X1),u1_struct_0(sK1))
            | v1_tex_2(k1_tex_2(sK1,X1),sK1) )
          & m1_subset_1(X1,u1_struct_0(sK1)) )
      & l1_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
      | ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1) )
    & ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
      | v1_tex_2(k1_tex_2(sK1,sK2),sK1) )
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l1_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f48,f50,f49])).

fof(f76,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f73,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f72,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f74,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f51])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | ~ v1_subset_1(sK0(X0,X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f59,plain,(
    ! [X0,X3,X1] :
      ( v1_subset_1(X3,u1_struct_0(X0))
      | u1_struct_0(X1) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f59])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f75,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f11,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_zfmisc_1(X0)
          | ~ v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_zfmisc_1(X0)
          | ~ v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(X0)
      | ~ v1_subset_1(k6_domain_1(X0,X1),X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v7_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f23,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f55,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f53,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ~ v1_xboole_0(X1)
           => ( ~ v1_subset_1(X1,u1_struct_0(X0))
              & ~ v1_xboole_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_subset_1(X1,u1_struct_0(X0))
            & ~ v1_xboole_0(X1) )
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_subset_1(X1,u1_struct_0(X0))
            & ~ v1_xboole_0(X1) )
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(X1,u1_struct_0(X0))
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | u1_struct_0(X1) = sK0(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_0,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_19,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v7_struct_0(X0)
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_414,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v7_struct_0(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_0,c_19])).

cnf(c_3972,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(X0_46),X0_45),u1_struct_0(X0_46))
    | ~ m1_subset_1(X0_45,u1_struct_0(X0_46))
    | v7_struct_0(X0_46)
    | v2_struct_0(X0_46)
    | ~ l1_pre_topc(X0_46) ),
    inference(subtyping,[status(esa)],[c_414])).

cnf(c_4498,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(X0_46),X0_45),u1_struct_0(X0_46)) = iProver_top
    | m1_subset_1(X0_45,u1_struct_0(X0_46)) != iProver_top
    | v7_struct_0(X0_46) = iProver_top
    | v2_struct_0(X0_46) = iProver_top
    | l1_pre_topc(X0_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3972])).

cnf(c_9,plain,
    ( v1_tex_2(X0,X1)
    | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_20,negated_conjecture,
    ( ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_191,plain,
    ( ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) ),
    inference(prop_impl,[status(thm)],[c_20])).

cnf(c_819,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0)
    | k1_tex_2(sK1,sK2) != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_191])).

cnf(c_820,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | m1_subset_1(sK0(sK1,k1_tex_2(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_819])).

cnf(c_23,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_822,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
    | m1_subset_1(sK0(sK1,k1_tex_2(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_820,c_23])).

cnf(c_823,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | m1_subset_1(sK0(sK1,k1_tex_2(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1) ),
    inference(renaming,[status(thm)],[c_822])).

cnf(c_3964,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | m1_subset_1(sK0(sK1,k1_tex_2(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1) ),
    inference(subtyping,[status(esa)],[c_823])).

cnf(c_4506,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK0(sK1,k1_tex_2(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3964])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_25,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_26,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_27,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_824,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK0(sK1,k1_tex_2(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_823])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_pre_topc(k1_tex_2(X1,X0),X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_3979,plain,
    ( ~ m1_subset_1(X0_45,u1_struct_0(X0_46))
    | m1_pre_topc(k1_tex_2(X0_46,X0_45),X0_46)
    | v2_struct_0(X0_46)
    | ~ l1_pre_topc(X0_46) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_4023,plain,
    ( m1_subset_1(X0_45,u1_struct_0(X0_46)) != iProver_top
    | m1_pre_topc(k1_tex_2(X0_46,X0_45),X0_46) = iProver_top
    | v2_struct_0(X0_46) = iProver_top
    | l1_pre_topc(X0_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3979])).

cnf(c_4025,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(k1_tex_2(sK1,sK2),sK1) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4023])).

cnf(c_5242,plain,
    ( m1_subset_1(sK0(sK1,k1_tex_2(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4506,c_25,c_26,c_27,c_824,c_4025])).

cnf(c_5243,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK0(sK1,k1_tex_2(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(renaming,[status(thm)],[c_5242])).

cnf(c_11,plain,
    ( v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_3981,plain,
    ( v1_subset_1(X0_45,X1_45)
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(X1_45))
    | X0_45 = X1_45 ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_4489,plain,
    ( X0_45 = X1_45
    | v1_subset_1(X0_45,X1_45) = iProver_top
    | m1_subset_1(X0_45,k1_zfmisc_1(X1_45)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3981])).

cnf(c_5248,plain,
    ( sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(sK1)
    | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top
    | v1_subset_1(sK0(sK1,k1_tex_2(sK1,sK2)),u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5243,c_4489])).

cnf(c_821,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK0(sK1,k1_tex_2(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_820])).

cnf(c_7,plain,
    ( v1_tex_2(X0,X1)
    | ~ v1_subset_1(sK0(X1,X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_853,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | ~ v1_subset_1(sK0(X0,X1),u1_struct_0(X0))
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0)
    | k1_tex_2(sK1,sK2) != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_191])).

cnf(c_854,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | ~ v1_subset_1(sK0(sK1,k1_tex_2(sK1,sK2)),u1_struct_0(sK1))
    | ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_853])).

cnf(c_855,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top
    | v1_subset_1(sK0(sK1,k1_tex_2(sK1,sK2)),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_854])).

cnf(c_4792,plain,
    ( v1_subset_1(X0_45,u1_struct_0(sK1))
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK1)))
    | X0_45 = u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_3981])).

cnf(c_4891,plain,
    ( v1_subset_1(sK0(sK1,k1_tex_2(sK1,sK2)),u1_struct_0(sK1))
    | ~ m1_subset_1(sK0(sK1,k1_tex_2(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
    | sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_4792])).

cnf(c_4892,plain,
    ( sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(sK1)
    | v1_subset_1(sK0(sK1,k1_tex_2(sK1,sK2)),u1_struct_0(sK1)) = iProver_top
    | m1_subset_1(sK0(sK1,k1_tex_2(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4891])).

cnf(c_5908,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top
    | sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5248,c_25,c_26,c_27,c_821,c_855,c_4025,c_4892])).

cnf(c_5909,plain,
    ( sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(sK1)
    | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5908])).

cnf(c_5915,plain,
    ( sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(sK1)
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | v7_struct_0(sK1) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4498,c_5909])).

cnf(c_6425,plain,
    ( sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(sK1)
    | v7_struct_0(sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5915,c_25,c_26,c_27])).

cnf(c_10,plain,
    ( ~ v1_tex_2(X0,X1)
    | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_4,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_149,plain,
    ( v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10,c_4])).

cnf(c_150,plain,
    ( ~ v1_tex_2(X0,X1)
    | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_149])).

cnf(c_21,negated_conjecture,
    ( v1_tex_2(k1_tex_2(sK1,sK2),sK1)
    | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_193,plain,
    ( v1_tex_2(k1_tex_2(sK1,sK2),sK1)
    | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) ),
    inference(prop_impl,[status(thm)],[c_21])).

cnf(c_870,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | k1_tex_2(sK1,sK2) != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_150,c_193])).

cnf(c_871,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1))
    | ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_870])).

cnf(c_873,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
    | v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1))
    | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_871,c_23])).

cnf(c_874,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1))
    | ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1) ),
    inference(renaming,[status(thm)],[c_873])).

cnf(c_3961,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1))
    | ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1) ),
    inference(subtyping,[status(esa)],[c_874])).

cnf(c_4509,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) = iProver_top
    | v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1)) = iProver_top
    | m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3961])).

cnf(c_4024,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_3979])).

cnf(c_4132,plain,
    ( v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1))
    | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3961,c_24,c_23,c_22,c_871,c_4024])).

cnf(c_4133,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_4132])).

cnf(c_4134,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) = iProver_top
    | v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4133])).

cnf(c_5673,plain,
    ( v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1)) = iProver_top
    | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4509,c_4134])).

cnf(c_5674,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) = iProver_top
    | v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1)) = iProver_top ),
    inference(renaming,[status(thm)],[c_5673])).

cnf(c_17,plain,
    ( ~ v1_subset_1(k6_domain_1(X0,X1),X0)
    | ~ m1_subset_1(X1,X0)
    | ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_3976,plain,
    ( ~ v1_subset_1(k6_domain_1(X0_45,X1_45),X0_45)
    | ~ m1_subset_1(X1_45,X0_45)
    | ~ v1_zfmisc_1(X0_45)
    | v1_xboole_0(X0_45) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_4494,plain,
    ( v1_subset_1(k6_domain_1(X0_45,X1_45),X0_45) != iProver_top
    | m1_subset_1(X1_45,X0_45) != iProver_top
    | v1_zfmisc_1(X0_45) != iProver_top
    | v1_xboole_0(X0_45) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3976])).

cnf(c_5681,plain,
    ( v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1)) = iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK1)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5674,c_4494])).

cnf(c_2,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_77,plain,
    ( v2_struct_0(X0) = iProver_top
    | v1_xboole_0(u1_struct_0(X0)) != iProver_top
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_79,plain,
    ( v2_struct_0(sK1) = iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) != iProver_top
    | l1_struct_0(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_77])).

cnf(c_81,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_83,plain,
    ( l1_pre_topc(sK1) != iProver_top
    | l1_struct_0(sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_81])).

cnf(c_3990,plain,
    ( X0_46 != X1_46
    | u1_struct_0(X0_46) = u1_struct_0(X1_46) ),
    theory(equality)).

cnf(c_4003,plain,
    ( sK1 != sK1
    | u1_struct_0(sK1) = u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_3990])).

cnf(c_3986,plain,
    ( X0_46 = X0_46 ),
    theory(equality)).

cnf(c_4016,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_3986])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v7_struct_0(k1_tex_2(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_3977,plain,
    ( ~ m1_subset_1(X0_45,u1_struct_0(X0_46))
    | v7_struct_0(k1_tex_2(X0_46,X0_45))
    | v2_struct_0(X0_46)
    | ~ l1_pre_topc(X0_46) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_4029,plain,
    ( m1_subset_1(X0_45,u1_struct_0(X0_46)) != iProver_top
    | v7_struct_0(k1_tex_2(X0_46,X0_45)) = iProver_top
    | v2_struct_0(X0_46) = iProver_top
    | l1_pre_topc(X0_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3977])).

cnf(c_4031,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | v7_struct_0(k1_tex_2(sK1,sK2)) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4029])).

cnf(c_3982,plain,
    ( m1_subset_1(u1_struct_0(X0_46),k1_zfmisc_1(u1_struct_0(X1_46)))
    | ~ m1_pre_topc(X0_46,X1_46)
    | ~ l1_pre_topc(X1_46) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_4724,plain,
    ( m1_subset_1(u1_struct_0(k1_tex_2(X0_46,X0_45)),k1_zfmisc_1(u1_struct_0(X0_46)))
    | ~ m1_pre_topc(k1_tex_2(X0_46,X0_45),X0_46)
    | ~ l1_pre_topc(X0_46) ),
    inference(instantiation,[status(thm)],[c_3982])).

cnf(c_4725,plain,
    ( m1_subset_1(u1_struct_0(k1_tex_2(X0_46,X0_45)),k1_zfmisc_1(u1_struct_0(X0_46))) = iProver_top
    | m1_pre_topc(k1_tex_2(X0_46,X0_45),X0_46) != iProver_top
    | l1_pre_topc(X0_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4724])).

cnf(c_4727,plain,
    ( m1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4725])).

cnf(c_3,plain,
    ( ~ v7_struct_0(X0)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_454,plain,
    ( ~ v7_struct_0(X0)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_0,c_3])).

cnf(c_3970,plain,
    ( ~ v7_struct_0(X0_46)
    | v1_zfmisc_1(u1_struct_0(X0_46))
    | ~ l1_pre_topc(X0_46) ),
    inference(subtyping,[status(esa)],[c_454])).

cnf(c_4820,plain,
    ( ~ v7_struct_0(k1_tex_2(X0_46,X0_45))
    | v1_zfmisc_1(u1_struct_0(k1_tex_2(X0_46,X0_45)))
    | ~ l1_pre_topc(k1_tex_2(X0_46,X0_45)) ),
    inference(instantiation,[status(thm)],[c_3970])).

cnf(c_4821,plain,
    ( v7_struct_0(k1_tex_2(X0_46,X0_45)) != iProver_top
    | v1_zfmisc_1(u1_struct_0(k1_tex_2(X0_46,X0_45))) = iProver_top
    | l1_pre_topc(k1_tex_2(X0_46,X0_45)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4820])).

cnf(c_4823,plain,
    ( v7_struct_0(k1_tex_2(sK1,sK2)) != iProver_top
    | v1_zfmisc_1(u1_struct_0(k1_tex_2(sK1,sK2))) = iProver_top
    | l1_pre_topc(k1_tex_2(sK1,sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4821])).

cnf(c_4491,plain,
    ( m1_subset_1(X0_45,u1_struct_0(X0_46)) != iProver_top
    | m1_pre_topc(k1_tex_2(X0_46,X0_45),X0_46) = iProver_top
    | v2_struct_0(X0_46) = iProver_top
    | l1_pre_topc(X0_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3979])).

cnf(c_1,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_3983,plain,
    ( ~ m1_pre_topc(X0_46,X1_46)
    | ~ l1_pre_topc(X1_46)
    | l1_pre_topc(X0_46) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_4487,plain,
    ( m1_pre_topc(X0_46,X1_46) != iProver_top
    | l1_pre_topc(X1_46) != iProver_top
    | l1_pre_topc(X0_46) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3983])).

cnf(c_4876,plain,
    ( m1_subset_1(X0_45,u1_struct_0(X0_46)) != iProver_top
    | v2_struct_0(X0_46) = iProver_top
    | l1_pre_topc(X0_46) != iProver_top
    | l1_pre_topc(k1_tex_2(X0_46,X0_45)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4491,c_4487])).

cnf(c_4878,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(k1_tex_2(sK1,sK2)) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4876])).

cnf(c_4894,plain,
    ( v1_subset_1(u1_struct_0(k1_tex_2(sK1,X0_45)),u1_struct_0(sK1))
    | ~ m1_subset_1(u1_struct_0(k1_tex_2(sK1,X0_45)),k1_zfmisc_1(u1_struct_0(sK1)))
    | u1_struct_0(k1_tex_2(sK1,X0_45)) = u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_4792])).

cnf(c_4896,plain,
    ( u1_struct_0(k1_tex_2(sK1,X0_45)) = u1_struct_0(sK1)
    | v1_subset_1(u1_struct_0(k1_tex_2(sK1,X0_45)),u1_struct_0(sK1)) = iProver_top
    | m1_subset_1(u1_struct_0(k1_tex_2(sK1,X0_45)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4894])).

cnf(c_4898,plain,
    ( u1_struct_0(k1_tex_2(sK1,sK2)) = u1_struct_0(sK1)
    | v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1)) = iProver_top
    | m1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4896])).

cnf(c_3993,plain,
    ( ~ v1_zfmisc_1(X0_45)
    | v1_zfmisc_1(X1_45)
    | X1_45 != X0_45 ),
    theory(equality)).

cnf(c_4770,plain,
    ( v1_zfmisc_1(X0_45)
    | ~ v1_zfmisc_1(u1_struct_0(X0_46))
    | X0_45 != u1_struct_0(X0_46) ),
    inference(instantiation,[status(thm)],[c_3993])).

cnf(c_5109,plain,
    ( v1_zfmisc_1(X0_45)
    | ~ v1_zfmisc_1(u1_struct_0(k1_tex_2(X0_46,X1_45)))
    | X0_45 != u1_struct_0(k1_tex_2(X0_46,X1_45)) ),
    inference(instantiation,[status(thm)],[c_4770])).

cnf(c_5942,plain,
    ( v1_zfmisc_1(u1_struct_0(X0_46))
    | ~ v1_zfmisc_1(u1_struct_0(k1_tex_2(X1_46,X0_45)))
    | u1_struct_0(X0_46) != u1_struct_0(k1_tex_2(X1_46,X0_45)) ),
    inference(instantiation,[status(thm)],[c_5109])).

cnf(c_5944,plain,
    ( u1_struct_0(X0_46) != u1_struct_0(k1_tex_2(X1_46,X0_45))
    | v1_zfmisc_1(u1_struct_0(X0_46)) = iProver_top
    | v1_zfmisc_1(u1_struct_0(k1_tex_2(X1_46,X0_45))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5942])).

cnf(c_5946,plain,
    ( u1_struct_0(sK1) != u1_struct_0(k1_tex_2(sK1,sK2))
    | v1_zfmisc_1(u1_struct_0(k1_tex_2(sK1,sK2))) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK1)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_5944])).

cnf(c_3987,plain,
    ( X0_45 != X1_45
    | X2_45 != X1_45
    | X2_45 = X0_45 ),
    theory(equality)).

cnf(c_4914,plain,
    ( X0_45 != X1_45
    | u1_struct_0(sK1) != X1_45
    | u1_struct_0(sK1) = X0_45 ),
    inference(instantiation,[status(thm)],[c_3987])).

cnf(c_5002,plain,
    ( X0_45 != u1_struct_0(sK1)
    | u1_struct_0(sK1) = X0_45
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_4914])).

cnf(c_5221,plain,
    ( u1_struct_0(X0_46) != u1_struct_0(sK1)
    | u1_struct_0(sK1) = u1_struct_0(X0_46)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_5002])).

cnf(c_5999,plain,
    ( u1_struct_0(k1_tex_2(X0_46,X0_45)) != u1_struct_0(sK1)
    | u1_struct_0(sK1) = u1_struct_0(k1_tex_2(X0_46,X0_45))
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_5221])).

cnf(c_6005,plain,
    ( u1_struct_0(k1_tex_2(sK1,sK2)) != u1_struct_0(sK1)
    | u1_struct_0(sK1) = u1_struct_0(k1_tex_2(sK1,sK2))
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_5999])).

cnf(c_6050,plain,
    ( v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5681,c_25,c_26,c_27,c_79,c_83,c_4003,c_4016,c_4025,c_4031,c_4727,c_4823,c_4878,c_4898,c_5946,c_6005])).

cnf(c_4488,plain,
    ( m1_subset_1(u1_struct_0(X0_46),k1_zfmisc_1(u1_struct_0(X1_46))) = iProver_top
    | m1_pre_topc(X0_46,X1_46) != iProver_top
    | l1_pre_topc(X1_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3982])).

cnf(c_5,plain,
    ( ~ v1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v7_struct_0(X1)
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_482,plain,
    ( ~ v1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v7_struct_0(X1)
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_pre_topc(X2)
    | X1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_5])).

cnf(c_483,plain,
    ( ~ v1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v7_struct_0(X1)
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_482])).

cnf(c_3968,plain,
    ( ~ v1_subset_1(X0_45,u1_struct_0(X0_46))
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(X0_46)))
    | ~ v7_struct_0(X0_46)
    | v2_struct_0(X0_46)
    | v1_xboole_0(X0_45)
    | ~ l1_pre_topc(X0_46) ),
    inference(subtyping,[status(esa)],[c_483])).

cnf(c_4502,plain,
    ( v1_subset_1(X0_45,u1_struct_0(X0_46)) != iProver_top
    | m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(X0_46))) != iProver_top
    | v7_struct_0(X0_46) != iProver_top
    | v2_struct_0(X0_46) = iProver_top
    | v1_xboole_0(X0_45) = iProver_top
    | l1_pre_topc(X0_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3968])).

cnf(c_6064,plain,
    ( v1_subset_1(u1_struct_0(X0_46),u1_struct_0(X1_46)) != iProver_top
    | m1_pre_topc(X0_46,X1_46) != iProver_top
    | v7_struct_0(X1_46) != iProver_top
    | v2_struct_0(X1_46) = iProver_top
    | v1_xboole_0(u1_struct_0(X0_46)) = iProver_top
    | l1_pre_topc(X1_46) != iProver_top ),
    inference(superposition,[status(thm)],[c_4488,c_4502])).

cnf(c_6297,plain,
    ( m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top
    | v7_struct_0(sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v1_xboole_0(u1_struct_0(k1_tex_2(sK1,sK2))) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_6050,c_6064])).

cnf(c_6432,plain,
    ( v1_xboole_0(u1_struct_0(k1_tex_2(sK1,sK2))) = iProver_top
    | v7_struct_0(sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6297,c_25,c_26,c_27,c_4025])).

cnf(c_6433,plain,
    ( v7_struct_0(sK1) != iProver_top
    | v1_xboole_0(u1_struct_0(k1_tex_2(sK1,sK2))) = iProver_top ),
    inference(renaming,[status(thm)],[c_6432])).

cnf(c_468,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_0,c_2])).

cnf(c_3969,plain,
    ( v2_struct_0(X0_46)
    | ~ v1_xboole_0(u1_struct_0(X0_46))
    | ~ l1_pre_topc(X0_46) ),
    inference(subtyping,[status(esa)],[c_468])).

cnf(c_4501,plain,
    ( v2_struct_0(X0_46) = iProver_top
    | v1_xboole_0(u1_struct_0(X0_46)) != iProver_top
    | l1_pre_topc(X0_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3969])).

cnf(c_6438,plain,
    ( v7_struct_0(sK1) != iProver_top
    | v2_struct_0(k1_tex_2(sK1,sK2)) = iProver_top
    | l1_pre_topc(k1_tex_2(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6433,c_4501])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k1_tex_2(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_3978,plain,
    ( ~ m1_subset_1(X0_45,u1_struct_0(X0_46))
    | v2_struct_0(X0_46)
    | ~ v2_struct_0(k1_tex_2(X0_46,X0_45))
    | ~ l1_pre_topc(X0_46) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_4026,plain,
    ( m1_subset_1(X0_45,u1_struct_0(X0_46)) != iProver_top
    | v2_struct_0(X0_46) = iProver_top
    | v2_struct_0(k1_tex_2(X0_46,X0_45)) != iProver_top
    | l1_pre_topc(X0_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3978])).

cnf(c_4028,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | v2_struct_0(k1_tex_2(sK1,sK2)) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4026])).

cnf(c_6526,plain,
    ( v7_struct_0(sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6438,c_25,c_26,c_27,c_4028,c_4878])).

cnf(c_6531,plain,
    ( sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(sK1) ),
    inference(superposition,[status(thm)],[c_6425,c_6526])).

cnf(c_8,plain,
    ( v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK0(X1,X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_836,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | k1_tex_2(sK1,sK2) != X0
    | sK0(X1,X0) = u1_struct_0(X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_191])).

cnf(c_837,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
    | ~ l1_pre_topc(sK1)
    | sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(k1_tex_2(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_836])).

cnf(c_839,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(k1_tex_2(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_837,c_23])).

cnf(c_840,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
    | sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(k1_tex_2(sK1,sK2)) ),
    inference(renaming,[status(thm)],[c_839])).

cnf(c_3963,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
    | sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(k1_tex_2(sK1,sK2)) ),
    inference(subtyping,[status(esa)],[c_840])).

cnf(c_4507,plain,
    ( sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(k1_tex_2(sK1,sK2))
    | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3963])).

cnf(c_4055,plain,
    ( sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(k1_tex_2(sK1,sK2))
    | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3963])).

cnf(c_5196,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top
    | sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(k1_tex_2(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4507,c_25,c_26,c_27,c_4025,c_4055])).

cnf(c_5197,plain,
    ( sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(k1_tex_2(sK1,sK2))
    | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5196])).

cnf(c_6536,plain,
    ( u1_struct_0(k1_tex_2(sK1,sK2)) = u1_struct_0(sK1)
    | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6531,c_5197])).

cnf(c_3975,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_4495,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3975])).

cnf(c_5349,plain,
    ( m1_subset_1(X0_45,u1_struct_0(X0_46)) != iProver_top
    | v7_struct_0(X0_46) = iProver_top
    | v1_zfmisc_1(u1_struct_0(X0_46)) != iProver_top
    | v2_struct_0(X0_46) = iProver_top
    | v1_xboole_0(u1_struct_0(X0_46)) = iProver_top
    | l1_pre_topc(X0_46) != iProver_top ),
    inference(superposition,[status(thm)],[c_4498,c_4494])).

cnf(c_4045,plain,
    ( v2_struct_0(X0_46) = iProver_top
    | v1_xboole_0(u1_struct_0(X0_46)) != iProver_top
    | l1_pre_topc(X0_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3969])).

cnf(c_6152,plain,
    ( v2_struct_0(X0_46) = iProver_top
    | v1_zfmisc_1(u1_struct_0(X0_46)) != iProver_top
    | v7_struct_0(X0_46) = iProver_top
    | m1_subset_1(X0_45,u1_struct_0(X0_46)) != iProver_top
    | l1_pre_topc(X0_46) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5349,c_4045])).

cnf(c_6153,plain,
    ( m1_subset_1(X0_45,u1_struct_0(X0_46)) != iProver_top
    | v7_struct_0(X0_46) = iProver_top
    | v1_zfmisc_1(u1_struct_0(X0_46)) != iProver_top
    | v2_struct_0(X0_46) = iProver_top
    | l1_pre_topc(X0_46) != iProver_top ),
    inference(renaming,[status(thm)],[c_6152])).

cnf(c_6163,plain,
    ( v7_struct_0(sK1) = iProver_top
    | v1_zfmisc_1(u1_struct_0(sK1)) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4495,c_6153])).

cnf(c_6166,plain,
    ( v7_struct_0(sK1) = iProver_top
    | v1_zfmisc_1(u1_struct_0(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6163,c_25,c_26])).

cnf(c_4038,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(X0_46),X0_45),u1_struct_0(X0_46)) = iProver_top
    | m1_subset_1(X0_45,u1_struct_0(X0_46)) != iProver_top
    | v7_struct_0(X0_46) = iProver_top
    | v2_struct_0(X0_46) = iProver_top
    | l1_pre_topc(X0_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3972])).

cnf(c_4040,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) = iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | v7_struct_0(sK1) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4038])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6536,c_6438,c_6166,c_6005,c_5946,c_4878,c_4823,c_4040,c_4031,c_4028,c_4016,c_4003,c_27,c_26,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n019.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:03:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 1.60/1.02  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.60/1.02  
% 1.60/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.60/1.02  
% 1.60/1.02  ------  iProver source info
% 1.60/1.02  
% 1.60/1.02  git: date: 2020-06-30 10:37:57 +0100
% 1.60/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.60/1.02  git: non_committed_changes: false
% 1.60/1.02  git: last_make_outside_of_git: false
% 1.60/1.02  
% 1.60/1.02  ------ 
% 1.60/1.02  
% 1.60/1.02  ------ Input Options
% 1.60/1.02  
% 1.60/1.02  --out_options                           all
% 1.60/1.02  --tptp_safe_out                         true
% 1.60/1.02  --problem_path                          ""
% 1.60/1.02  --include_path                          ""
% 1.60/1.02  --clausifier                            res/vclausify_rel
% 1.60/1.02  --clausifier_options                    --mode clausify
% 1.60/1.02  --stdin                                 false
% 1.60/1.02  --stats_out                             all
% 1.60/1.02  
% 1.60/1.02  ------ General Options
% 1.60/1.02  
% 1.60/1.02  --fof                                   false
% 1.60/1.02  --time_out_real                         305.
% 1.60/1.02  --time_out_virtual                      -1.
% 1.60/1.02  --symbol_type_check                     false
% 1.60/1.02  --clausify_out                          false
% 1.60/1.02  --sig_cnt_out                           false
% 1.60/1.02  --trig_cnt_out                          false
% 1.60/1.02  --trig_cnt_out_tolerance                1.
% 1.60/1.02  --trig_cnt_out_sk_spl                   false
% 1.60/1.02  --abstr_cl_out                          false
% 1.60/1.02  
% 1.60/1.02  ------ Global Options
% 1.60/1.02  
% 1.60/1.02  --schedule                              default
% 1.60/1.02  --add_important_lit                     false
% 1.60/1.02  --prop_solver_per_cl                    1000
% 1.60/1.02  --min_unsat_core                        false
% 1.60/1.02  --soft_assumptions                      false
% 1.60/1.02  --soft_lemma_size                       3
% 1.60/1.02  --prop_impl_unit_size                   0
% 1.60/1.02  --prop_impl_unit                        []
% 1.60/1.02  --share_sel_clauses                     true
% 1.60/1.02  --reset_solvers                         false
% 1.60/1.02  --bc_imp_inh                            [conj_cone]
% 1.60/1.02  --conj_cone_tolerance                   3.
% 1.60/1.02  --extra_neg_conj                        none
% 1.60/1.02  --large_theory_mode                     true
% 1.60/1.02  --prolific_symb_bound                   200
% 1.60/1.02  --lt_threshold                          2000
% 1.60/1.02  --clause_weak_htbl                      true
% 1.60/1.02  --gc_record_bc_elim                     false
% 2.15/1.02  
% 2.15/1.02  ------ Preprocessing Options
% 2.15/1.02  
% 2.15/1.02  --preprocessing_flag                    true
% 2.15/1.02  --time_out_prep_mult                    0.1
% 2.15/1.02  --splitting_mode                        input
% 2.15/1.02  --splitting_grd                         true
% 2.15/1.02  --splitting_cvd                         false
% 2.15/1.02  --splitting_cvd_svl                     false
% 2.15/1.02  --splitting_nvd                         32
% 2.15/1.02  --sub_typing                            true
% 2.15/1.02  --prep_gs_sim                           true
% 2.15/1.02  --prep_unflatten                        true
% 2.15/1.02  --prep_res_sim                          true
% 2.15/1.02  --prep_upred                            true
% 2.15/1.02  --prep_sem_filter                       exhaustive
% 2.15/1.02  --prep_sem_filter_out                   false
% 2.15/1.02  --pred_elim                             true
% 2.15/1.02  --res_sim_input                         true
% 2.15/1.02  --eq_ax_congr_red                       true
% 2.15/1.02  --pure_diseq_elim                       true
% 2.15/1.02  --brand_transform                       false
% 2.15/1.02  --non_eq_to_eq                          false
% 2.15/1.02  --prep_def_merge                        true
% 2.15/1.02  --prep_def_merge_prop_impl              false
% 2.15/1.02  --prep_def_merge_mbd                    true
% 2.15/1.02  --prep_def_merge_tr_red                 false
% 2.15/1.02  --prep_def_merge_tr_cl                  false
% 2.15/1.02  --smt_preprocessing                     true
% 2.15/1.02  --smt_ac_axioms                         fast
% 2.15/1.02  --preprocessed_out                      false
% 2.15/1.02  --preprocessed_stats                    false
% 2.15/1.02  
% 2.15/1.02  ------ Abstraction refinement Options
% 2.15/1.02  
% 2.15/1.02  --abstr_ref                             []
% 2.15/1.02  --abstr_ref_prep                        false
% 2.15/1.02  --abstr_ref_until_sat                   false
% 2.15/1.02  --abstr_ref_sig_restrict                funpre
% 2.15/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.15/1.02  --abstr_ref_under                       []
% 2.15/1.02  
% 2.15/1.02  ------ SAT Options
% 2.15/1.02  
% 2.15/1.02  --sat_mode                              false
% 2.15/1.02  --sat_fm_restart_options                ""
% 2.15/1.02  --sat_gr_def                            false
% 2.15/1.02  --sat_epr_types                         true
% 2.15/1.02  --sat_non_cyclic_types                  false
% 2.15/1.02  --sat_finite_models                     false
% 2.15/1.02  --sat_fm_lemmas                         false
% 2.15/1.02  --sat_fm_prep                           false
% 2.15/1.02  --sat_fm_uc_incr                        true
% 2.15/1.02  --sat_out_model                         small
% 2.15/1.02  --sat_out_clauses                       false
% 2.15/1.02  
% 2.15/1.02  ------ QBF Options
% 2.15/1.02  
% 2.15/1.02  --qbf_mode                              false
% 2.15/1.02  --qbf_elim_univ                         false
% 2.15/1.02  --qbf_dom_inst                          none
% 2.15/1.02  --qbf_dom_pre_inst                      false
% 2.15/1.02  --qbf_sk_in                             false
% 2.15/1.02  --qbf_pred_elim                         true
% 2.15/1.02  --qbf_split                             512
% 2.15/1.02  
% 2.15/1.02  ------ BMC1 Options
% 2.15/1.02  
% 2.15/1.02  --bmc1_incremental                      false
% 2.15/1.02  --bmc1_axioms                           reachable_all
% 2.15/1.02  --bmc1_min_bound                        0
% 2.15/1.02  --bmc1_max_bound                        -1
% 2.15/1.02  --bmc1_max_bound_default                -1
% 2.15/1.02  --bmc1_symbol_reachability              true
% 2.15/1.02  --bmc1_property_lemmas                  false
% 2.15/1.02  --bmc1_k_induction                      false
% 2.15/1.02  --bmc1_non_equiv_states                 false
% 2.15/1.02  --bmc1_deadlock                         false
% 2.15/1.02  --bmc1_ucm                              false
% 2.15/1.02  --bmc1_add_unsat_core                   none
% 2.15/1.02  --bmc1_unsat_core_children              false
% 2.15/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.15/1.02  --bmc1_out_stat                         full
% 2.15/1.02  --bmc1_ground_init                      false
% 2.15/1.02  --bmc1_pre_inst_next_state              false
% 2.15/1.02  --bmc1_pre_inst_state                   false
% 2.15/1.02  --bmc1_pre_inst_reach_state             false
% 2.15/1.02  --bmc1_out_unsat_core                   false
% 2.15/1.02  --bmc1_aig_witness_out                  false
% 2.15/1.02  --bmc1_verbose                          false
% 2.15/1.02  --bmc1_dump_clauses_tptp                false
% 2.15/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.15/1.02  --bmc1_dump_file                        -
% 2.15/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.15/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.15/1.02  --bmc1_ucm_extend_mode                  1
% 2.15/1.02  --bmc1_ucm_init_mode                    2
% 2.15/1.02  --bmc1_ucm_cone_mode                    none
% 2.15/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.15/1.02  --bmc1_ucm_relax_model                  4
% 2.15/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.15/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.15/1.02  --bmc1_ucm_layered_model                none
% 2.15/1.02  --bmc1_ucm_max_lemma_size               10
% 2.15/1.02  
% 2.15/1.02  ------ AIG Options
% 2.15/1.02  
% 2.15/1.02  --aig_mode                              false
% 2.15/1.02  
% 2.15/1.02  ------ Instantiation Options
% 2.15/1.02  
% 2.15/1.02  --instantiation_flag                    true
% 2.15/1.02  --inst_sos_flag                         false
% 2.15/1.02  --inst_sos_phase                        true
% 2.15/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.15/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.15/1.02  --inst_lit_sel_side                     num_symb
% 2.15/1.02  --inst_solver_per_active                1400
% 2.15/1.02  --inst_solver_calls_frac                1.
% 2.15/1.02  --inst_passive_queue_type               priority_queues
% 2.15/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.15/1.02  --inst_passive_queues_freq              [25;2]
% 2.15/1.02  --inst_dismatching                      true
% 2.15/1.02  --inst_eager_unprocessed_to_passive     true
% 2.15/1.02  --inst_prop_sim_given                   true
% 2.15/1.02  --inst_prop_sim_new                     false
% 2.15/1.02  --inst_subs_new                         false
% 2.15/1.02  --inst_eq_res_simp                      false
% 2.15/1.02  --inst_subs_given                       false
% 2.15/1.02  --inst_orphan_elimination               true
% 2.15/1.02  --inst_learning_loop_flag               true
% 2.15/1.02  --inst_learning_start                   3000
% 2.15/1.02  --inst_learning_factor                  2
% 2.15/1.02  --inst_start_prop_sim_after_learn       3
% 2.15/1.02  --inst_sel_renew                        solver
% 2.15/1.02  --inst_lit_activity_flag                true
% 2.15/1.02  --inst_restr_to_given                   false
% 2.15/1.02  --inst_activity_threshold               500
% 2.15/1.02  --inst_out_proof                        true
% 2.15/1.02  
% 2.15/1.02  ------ Resolution Options
% 2.15/1.02  
% 2.15/1.02  --resolution_flag                       true
% 2.15/1.02  --res_lit_sel                           adaptive
% 2.15/1.02  --res_lit_sel_side                      none
% 2.15/1.02  --res_ordering                          kbo
% 2.15/1.02  --res_to_prop_solver                    active
% 2.15/1.02  --res_prop_simpl_new                    false
% 2.15/1.02  --res_prop_simpl_given                  true
% 2.15/1.02  --res_passive_queue_type                priority_queues
% 2.15/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.15/1.02  --res_passive_queues_freq               [15;5]
% 2.15/1.02  --res_forward_subs                      full
% 2.15/1.02  --res_backward_subs                     full
% 2.15/1.02  --res_forward_subs_resolution           true
% 2.15/1.02  --res_backward_subs_resolution          true
% 2.15/1.02  --res_orphan_elimination                true
% 2.15/1.02  --res_time_limit                        2.
% 2.15/1.02  --res_out_proof                         true
% 2.15/1.02  
% 2.15/1.02  ------ Superposition Options
% 2.15/1.02  
% 2.15/1.02  --superposition_flag                    true
% 2.15/1.02  --sup_passive_queue_type                priority_queues
% 2.15/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.15/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.15/1.02  --demod_completeness_check              fast
% 2.15/1.02  --demod_use_ground                      true
% 2.15/1.02  --sup_to_prop_solver                    passive
% 2.15/1.02  --sup_prop_simpl_new                    true
% 2.15/1.02  --sup_prop_simpl_given                  true
% 2.15/1.02  --sup_fun_splitting                     false
% 2.15/1.02  --sup_smt_interval                      50000
% 2.15/1.02  
% 2.15/1.02  ------ Superposition Simplification Setup
% 2.15/1.02  
% 2.15/1.02  --sup_indices_passive                   []
% 2.15/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.15/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.15/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.15/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.15/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.15/1.02  --sup_full_bw                           [BwDemod]
% 2.15/1.02  --sup_immed_triv                        [TrivRules]
% 2.15/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.15/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.15/1.02  --sup_immed_bw_main                     []
% 2.15/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.15/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.15/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.15/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.15/1.02  
% 2.15/1.02  ------ Combination Options
% 2.15/1.02  
% 2.15/1.02  --comb_res_mult                         3
% 2.15/1.02  --comb_sup_mult                         2
% 2.15/1.02  --comb_inst_mult                        10
% 2.15/1.02  
% 2.15/1.02  ------ Debug Options
% 2.15/1.02  
% 2.15/1.02  --dbg_backtrace                         false
% 2.15/1.02  --dbg_dump_prop_clauses                 false
% 2.15/1.02  --dbg_dump_prop_clauses_file            -
% 2.15/1.02  --dbg_out_stat                          false
% 2.15/1.02  ------ Parsing...
% 2.15/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.15/1.02  
% 2.15/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.15/1.02  
% 2.15/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.15/1.02  
% 2.15/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.15/1.02  ------ Proving...
% 2.15/1.02  ------ Problem Properties 
% 2.15/1.02  
% 2.15/1.02  
% 2.15/1.02  clauses                                 23
% 2.15/1.02  conjectures                             3
% 2.15/1.02  EPR                                     3
% 2.15/1.02  Horn                                    15
% 2.15/1.02  unary                                   3
% 2.15/1.02  binary                                  1
% 2.15/1.02  lits                                    76
% 2.15/1.02  lits eq                                 3
% 2.15/1.02  fd_pure                                 0
% 2.15/1.02  fd_pseudo                               0
% 2.15/1.02  fd_cond                                 0
% 2.15/1.02  fd_pseudo_cond                          1
% 2.15/1.02  AC symbols                              0
% 2.15/1.02  
% 2.15/1.02  ------ Schedule dynamic 5 is on 
% 2.15/1.02  
% 2.15/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.15/1.02  
% 2.15/1.02  
% 2.15/1.02  ------ 
% 2.15/1.02  Current options:
% 2.15/1.02  ------ 
% 2.15/1.02  
% 2.15/1.02  ------ Input Options
% 2.15/1.02  
% 2.15/1.02  --out_options                           all
% 2.15/1.02  --tptp_safe_out                         true
% 2.15/1.02  --problem_path                          ""
% 2.15/1.02  --include_path                          ""
% 2.15/1.02  --clausifier                            res/vclausify_rel
% 2.15/1.02  --clausifier_options                    --mode clausify
% 2.15/1.02  --stdin                                 false
% 2.15/1.02  --stats_out                             all
% 2.15/1.02  
% 2.15/1.02  ------ General Options
% 2.15/1.02  
% 2.15/1.02  --fof                                   false
% 2.15/1.02  --time_out_real                         305.
% 2.15/1.02  --time_out_virtual                      -1.
% 2.15/1.02  --symbol_type_check                     false
% 2.15/1.02  --clausify_out                          false
% 2.15/1.02  --sig_cnt_out                           false
% 2.15/1.02  --trig_cnt_out                          false
% 2.15/1.02  --trig_cnt_out_tolerance                1.
% 2.15/1.02  --trig_cnt_out_sk_spl                   false
% 2.15/1.02  --abstr_cl_out                          false
% 2.15/1.02  
% 2.15/1.02  ------ Global Options
% 2.15/1.02  
% 2.15/1.02  --schedule                              default
% 2.15/1.02  --add_important_lit                     false
% 2.15/1.02  --prop_solver_per_cl                    1000
% 2.15/1.02  --min_unsat_core                        false
% 2.15/1.02  --soft_assumptions                      false
% 2.15/1.02  --soft_lemma_size                       3
% 2.15/1.02  --prop_impl_unit_size                   0
% 2.15/1.02  --prop_impl_unit                        []
% 2.15/1.02  --share_sel_clauses                     true
% 2.15/1.02  --reset_solvers                         false
% 2.15/1.02  --bc_imp_inh                            [conj_cone]
% 2.15/1.02  --conj_cone_tolerance                   3.
% 2.15/1.02  --extra_neg_conj                        none
% 2.15/1.02  --large_theory_mode                     true
% 2.15/1.02  --prolific_symb_bound                   200
% 2.15/1.02  --lt_threshold                          2000
% 2.15/1.02  --clause_weak_htbl                      true
% 2.15/1.02  --gc_record_bc_elim                     false
% 2.15/1.02  
% 2.15/1.02  ------ Preprocessing Options
% 2.15/1.02  
% 2.15/1.02  --preprocessing_flag                    true
% 2.15/1.02  --time_out_prep_mult                    0.1
% 2.15/1.02  --splitting_mode                        input
% 2.15/1.02  --splitting_grd                         true
% 2.15/1.02  --splitting_cvd                         false
% 2.15/1.02  --splitting_cvd_svl                     false
% 2.15/1.02  --splitting_nvd                         32
% 2.15/1.02  --sub_typing                            true
% 2.15/1.02  --prep_gs_sim                           true
% 2.15/1.02  --prep_unflatten                        true
% 2.15/1.02  --prep_res_sim                          true
% 2.15/1.02  --prep_upred                            true
% 2.15/1.02  --prep_sem_filter                       exhaustive
% 2.15/1.02  --prep_sem_filter_out                   false
% 2.15/1.02  --pred_elim                             true
% 2.15/1.02  --res_sim_input                         true
% 2.15/1.02  --eq_ax_congr_red                       true
% 2.15/1.02  --pure_diseq_elim                       true
% 2.15/1.02  --brand_transform                       false
% 2.15/1.02  --non_eq_to_eq                          false
% 2.15/1.02  --prep_def_merge                        true
% 2.15/1.02  --prep_def_merge_prop_impl              false
% 2.15/1.02  --prep_def_merge_mbd                    true
% 2.15/1.02  --prep_def_merge_tr_red                 false
% 2.15/1.02  --prep_def_merge_tr_cl                  false
% 2.15/1.02  --smt_preprocessing                     true
% 2.15/1.02  --smt_ac_axioms                         fast
% 2.15/1.02  --preprocessed_out                      false
% 2.15/1.02  --preprocessed_stats                    false
% 2.15/1.02  
% 2.15/1.02  ------ Abstraction refinement Options
% 2.15/1.02  
% 2.15/1.02  --abstr_ref                             []
% 2.15/1.02  --abstr_ref_prep                        false
% 2.15/1.02  --abstr_ref_until_sat                   false
% 2.15/1.02  --abstr_ref_sig_restrict                funpre
% 2.15/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.15/1.02  --abstr_ref_under                       []
% 2.15/1.02  
% 2.15/1.02  ------ SAT Options
% 2.15/1.02  
% 2.15/1.02  --sat_mode                              false
% 2.15/1.02  --sat_fm_restart_options                ""
% 2.15/1.02  --sat_gr_def                            false
% 2.15/1.02  --sat_epr_types                         true
% 2.15/1.02  --sat_non_cyclic_types                  false
% 2.15/1.02  --sat_finite_models                     false
% 2.15/1.02  --sat_fm_lemmas                         false
% 2.15/1.02  --sat_fm_prep                           false
% 2.15/1.02  --sat_fm_uc_incr                        true
% 2.15/1.02  --sat_out_model                         small
% 2.15/1.02  --sat_out_clauses                       false
% 2.15/1.02  
% 2.15/1.02  ------ QBF Options
% 2.15/1.02  
% 2.15/1.02  --qbf_mode                              false
% 2.15/1.02  --qbf_elim_univ                         false
% 2.15/1.02  --qbf_dom_inst                          none
% 2.15/1.02  --qbf_dom_pre_inst                      false
% 2.15/1.02  --qbf_sk_in                             false
% 2.15/1.02  --qbf_pred_elim                         true
% 2.15/1.02  --qbf_split                             512
% 2.15/1.02  
% 2.15/1.02  ------ BMC1 Options
% 2.15/1.02  
% 2.15/1.02  --bmc1_incremental                      false
% 2.15/1.02  --bmc1_axioms                           reachable_all
% 2.15/1.02  --bmc1_min_bound                        0
% 2.15/1.02  --bmc1_max_bound                        -1
% 2.15/1.02  --bmc1_max_bound_default                -1
% 2.15/1.02  --bmc1_symbol_reachability              true
% 2.15/1.02  --bmc1_property_lemmas                  false
% 2.15/1.02  --bmc1_k_induction                      false
% 2.15/1.02  --bmc1_non_equiv_states                 false
% 2.15/1.02  --bmc1_deadlock                         false
% 2.15/1.02  --bmc1_ucm                              false
% 2.15/1.02  --bmc1_add_unsat_core                   none
% 2.15/1.02  --bmc1_unsat_core_children              false
% 2.15/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.15/1.02  --bmc1_out_stat                         full
% 2.15/1.02  --bmc1_ground_init                      false
% 2.15/1.02  --bmc1_pre_inst_next_state              false
% 2.15/1.02  --bmc1_pre_inst_state                   false
% 2.15/1.02  --bmc1_pre_inst_reach_state             false
% 2.15/1.02  --bmc1_out_unsat_core                   false
% 2.15/1.02  --bmc1_aig_witness_out                  false
% 2.15/1.02  --bmc1_verbose                          false
% 2.15/1.02  --bmc1_dump_clauses_tptp                false
% 2.15/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.15/1.02  --bmc1_dump_file                        -
% 2.15/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.15/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.15/1.02  --bmc1_ucm_extend_mode                  1
% 2.15/1.02  --bmc1_ucm_init_mode                    2
% 2.15/1.02  --bmc1_ucm_cone_mode                    none
% 2.15/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.15/1.02  --bmc1_ucm_relax_model                  4
% 2.15/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.15/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.15/1.02  --bmc1_ucm_layered_model                none
% 2.15/1.02  --bmc1_ucm_max_lemma_size               10
% 2.15/1.02  
% 2.15/1.02  ------ AIG Options
% 2.15/1.02  
% 2.15/1.02  --aig_mode                              false
% 2.15/1.02  
% 2.15/1.02  ------ Instantiation Options
% 2.15/1.02  
% 2.15/1.02  --instantiation_flag                    true
% 2.15/1.02  --inst_sos_flag                         false
% 2.15/1.02  --inst_sos_phase                        true
% 2.15/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.15/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.15/1.02  --inst_lit_sel_side                     none
% 2.15/1.02  --inst_solver_per_active                1400
% 2.15/1.02  --inst_solver_calls_frac                1.
% 2.15/1.02  --inst_passive_queue_type               priority_queues
% 2.15/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.15/1.02  --inst_passive_queues_freq              [25;2]
% 2.15/1.02  --inst_dismatching                      true
% 2.15/1.02  --inst_eager_unprocessed_to_passive     true
% 2.15/1.02  --inst_prop_sim_given                   true
% 2.15/1.02  --inst_prop_sim_new                     false
% 2.15/1.02  --inst_subs_new                         false
% 2.15/1.02  --inst_eq_res_simp                      false
% 2.15/1.02  --inst_subs_given                       false
% 2.15/1.02  --inst_orphan_elimination               true
% 2.15/1.02  --inst_learning_loop_flag               true
% 2.15/1.02  --inst_learning_start                   3000
% 2.15/1.02  --inst_learning_factor                  2
% 2.15/1.02  --inst_start_prop_sim_after_learn       3
% 2.15/1.02  --inst_sel_renew                        solver
% 2.15/1.02  --inst_lit_activity_flag                true
% 2.15/1.02  --inst_restr_to_given                   false
% 2.15/1.02  --inst_activity_threshold               500
% 2.15/1.02  --inst_out_proof                        true
% 2.15/1.02  
% 2.15/1.02  ------ Resolution Options
% 2.15/1.02  
% 2.15/1.02  --resolution_flag                       false
% 2.15/1.02  --res_lit_sel                           adaptive
% 2.15/1.02  --res_lit_sel_side                      none
% 2.15/1.02  --res_ordering                          kbo
% 2.15/1.02  --res_to_prop_solver                    active
% 2.15/1.02  --res_prop_simpl_new                    false
% 2.15/1.02  --res_prop_simpl_given                  true
% 2.15/1.02  --res_passive_queue_type                priority_queues
% 2.15/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.15/1.02  --res_passive_queues_freq               [15;5]
% 2.15/1.02  --res_forward_subs                      full
% 2.15/1.02  --res_backward_subs                     full
% 2.15/1.02  --res_forward_subs_resolution           true
% 2.15/1.02  --res_backward_subs_resolution          true
% 2.15/1.02  --res_orphan_elimination                true
% 2.15/1.02  --res_time_limit                        2.
% 2.15/1.02  --res_out_proof                         true
% 2.15/1.02  
% 2.15/1.02  ------ Superposition Options
% 2.15/1.02  
% 2.15/1.02  --superposition_flag                    true
% 2.15/1.02  --sup_passive_queue_type                priority_queues
% 2.15/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.15/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.15/1.02  --demod_completeness_check              fast
% 2.15/1.02  --demod_use_ground                      true
% 2.15/1.02  --sup_to_prop_solver                    passive
% 2.15/1.02  --sup_prop_simpl_new                    true
% 2.15/1.02  --sup_prop_simpl_given                  true
% 2.15/1.02  --sup_fun_splitting                     false
% 2.15/1.02  --sup_smt_interval                      50000
% 2.15/1.02  
% 2.15/1.02  ------ Superposition Simplification Setup
% 2.15/1.02  
% 2.15/1.02  --sup_indices_passive                   []
% 2.15/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.15/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.15/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.15/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.15/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.15/1.02  --sup_full_bw                           [BwDemod]
% 2.15/1.02  --sup_immed_triv                        [TrivRules]
% 2.15/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.15/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.15/1.02  --sup_immed_bw_main                     []
% 2.15/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.15/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.15/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.15/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.15/1.02  
% 2.15/1.02  ------ Combination Options
% 2.15/1.02  
% 2.15/1.02  --comb_res_mult                         3
% 2.15/1.02  --comb_sup_mult                         2
% 2.15/1.02  --comb_inst_mult                        10
% 2.15/1.02  
% 2.15/1.02  ------ Debug Options
% 2.15/1.02  
% 2.15/1.02  --dbg_backtrace                         false
% 2.15/1.02  --dbg_dump_prop_clauses                 false
% 2.15/1.02  --dbg_dump_prop_clauses_file            -
% 2.15/1.02  --dbg_out_stat                          false
% 2.15/1.02  
% 2.15/1.02  
% 2.15/1.02  
% 2.15/1.02  
% 2.15/1.02  ------ Proving...
% 2.15/1.02  
% 2.15/1.02  
% 2.15/1.02  % SZS status Theorem for theBenchmark.p
% 2.15/1.02  
% 2.15/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 2.15/1.02  
% 2.15/1.02  fof(f1,axiom,(
% 2.15/1.02    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.15/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.15/1.02  
% 2.15/1.02  fof(f18,plain,(
% 2.15/1.02    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.15/1.02    inference(ennf_transformation,[],[f1])).
% 2.15/1.02  
% 2.15/1.02  fof(f52,plain,(
% 2.15/1.02    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.15/1.02    inference(cnf_transformation,[],[f18])).
% 2.15/1.02  
% 2.15/1.02  fof(f13,axiom,(
% 2.15/1.02    ! [X0] : ((l1_struct_0(X0) & ~v7_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))))),
% 2.15/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.15/1.02  
% 2.15/1.02  fof(f38,plain,(
% 2.15/1.02    ! [X0] : (! [X1] : (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_struct_0(X0) | v7_struct_0(X0) | v2_struct_0(X0)))),
% 2.15/1.02    inference(ennf_transformation,[],[f13])).
% 2.15/1.02  
% 2.15/1.02  fof(f39,plain,(
% 2.15/1.02    ! [X0] : (! [X1] : (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_struct_0(X0) | v7_struct_0(X0) | v2_struct_0(X0))),
% 2.15/1.02    inference(flattening,[],[f38])).
% 2.15/1.02  
% 2.15/1.02  fof(f71,plain,(
% 2.15/1.02    ( ! [X0,X1] : (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_struct_0(X0) | v7_struct_0(X0) | v2_struct_0(X0)) )),
% 2.15/1.02    inference(cnf_transformation,[],[f39])).
% 2.15/1.02  
% 2.15/1.02  fof(f7,axiom,(
% 2.15/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v1_subset_1(X2,u1_struct_0(X0)))))))),
% 2.15/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.15/1.02  
% 2.15/1.02  fof(f27,plain,(
% 2.15/1.02    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : ((v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.15/1.02    inference(ennf_transformation,[],[f7])).
% 2.15/1.02  
% 2.15/1.02  fof(f28,plain,(
% 2.15/1.02    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.15/1.02    inference(flattening,[],[f27])).
% 2.15/1.02  
% 2.15/1.02  fof(f42,plain,(
% 2.15/1.02    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.15/1.02    inference(nnf_transformation,[],[f28])).
% 2.15/1.02  
% 2.15/1.02  fof(f43,plain,(
% 2.15/1.02    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.15/1.02    inference(rectify,[],[f42])).
% 2.15/1.02  
% 2.15/1.02  fof(f44,plain,(
% 2.15/1.02    ! [X1,X0] : (? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_subset_1(sK0(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK0(X0,X1) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.15/1.02    introduced(choice_axiom,[])).
% 2.15/1.02  
% 2.15/1.02  fof(f45,plain,(
% 2.15/1.02    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | (~v1_subset_1(sK0(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK0(X0,X1) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.15/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f43,f44])).
% 2.15/1.02  
% 2.15/1.02  fof(f60,plain,(
% 2.15/1.02    ( ! [X0,X1] : (v1_tex_2(X1,X0) | m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.15/1.02    inference(cnf_transformation,[],[f45])).
% 2.15/1.02  
% 2.15/1.02  fof(f14,conjecture,(
% 2.15/1.02    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 2.15/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.15/1.02  
% 2.15/1.02  fof(f15,negated_conjecture,(
% 2.15/1.02    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 2.15/1.02    inference(negated_conjecture,[],[f14])).
% 2.15/1.02  
% 2.15/1.02  fof(f40,plain,(
% 2.15/1.02    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.15/1.02    inference(ennf_transformation,[],[f15])).
% 2.15/1.02  
% 2.15/1.02  fof(f41,plain,(
% 2.15/1.02    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.15/1.02    inference(flattening,[],[f40])).
% 2.15/1.02  
% 2.15/1.02  fof(f47,plain,(
% 2.15/1.02    ? [X0] : (? [X1] : (((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.15/1.02    inference(nnf_transformation,[],[f41])).
% 2.15/1.02  
% 2.15/1.02  fof(f48,plain,(
% 2.15/1.02    ? [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.15/1.02    inference(flattening,[],[f47])).
% 2.15/1.02  
% 2.15/1.02  fof(f50,plain,(
% 2.15/1.02    ( ! [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) => ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),sK2),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,sK2),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),sK2),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,sK2),X0)) & m1_subset_1(sK2,u1_struct_0(X0)))) )),
% 2.15/1.02    introduced(choice_axiom,[])).
% 2.15/1.02  
% 2.15/1.02  fof(f49,plain,(
% 2.15/1.02    ? [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(sK1),X1),u1_struct_0(sK1)) | ~v1_tex_2(k1_tex_2(sK1,X1),sK1)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK1),X1),u1_struct_0(sK1)) | v1_tex_2(k1_tex_2(sK1,X1),sK1)) & m1_subset_1(X1,u1_struct_0(sK1))) & l1_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 2.15/1.02    introduced(choice_axiom,[])).
% 2.15/1.02  
% 2.15/1.02  fof(f51,plain,(
% 2.15/1.02    ((~v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) | ~v1_tex_2(k1_tex_2(sK1,sK2),sK1)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) | v1_tex_2(k1_tex_2(sK1,sK2),sK1)) & m1_subset_1(sK2,u1_struct_0(sK1))) & l1_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 2.15/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f48,f50,f49])).
% 2.15/1.02  
% 2.15/1.02  fof(f76,plain,(
% 2.15/1.02    ~v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) | ~v1_tex_2(k1_tex_2(sK1,sK2),sK1)),
% 2.15/1.02    inference(cnf_transformation,[],[f51])).
% 2.15/1.02  
% 2.15/1.02  fof(f73,plain,(
% 2.15/1.02    l1_pre_topc(sK1)),
% 2.15/1.02    inference(cnf_transformation,[],[f51])).
% 2.15/1.02  
% 2.15/1.02  fof(f72,plain,(
% 2.15/1.02    ~v2_struct_0(sK1)),
% 2.15/1.02    inference(cnf_transformation,[],[f51])).
% 2.15/1.02  
% 2.15/1.02  fof(f74,plain,(
% 2.15/1.02    m1_subset_1(sK2,u1_struct_0(sK1))),
% 2.15/1.02    inference(cnf_transformation,[],[f51])).
% 2.15/1.02  
% 2.15/1.02  fof(f9,axiom,(
% 2.15/1.02    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 2.15/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.15/1.02  
% 2.15/1.02  fof(f17,plain,(
% 2.15/1.02    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 2.15/1.02    inference(pure_predicate_removal,[],[f9])).
% 2.15/1.02  
% 2.15/1.02  fof(f30,plain,(
% 2.15/1.02    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.15/1.02    inference(ennf_transformation,[],[f17])).
% 2.15/1.02  
% 2.15/1.02  fof(f31,plain,(
% 2.15/1.02    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.15/1.02    inference(flattening,[],[f30])).
% 2.15/1.02  
% 2.15/1.02  fof(f66,plain,(
% 2.15/1.02    ( ! [X0,X1] : (m1_pre_topc(k1_tex_2(X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.15/1.02    inference(cnf_transformation,[],[f31])).
% 2.15/1.02  
% 2.15/1.02  fof(f8,axiom,(
% 2.15/1.02    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 2.15/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.15/1.02  
% 2.15/1.02  fof(f29,plain,(
% 2.15/1.02    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.15/1.02    inference(ennf_transformation,[],[f8])).
% 2.15/1.02  
% 2.15/1.02  fof(f46,plain,(
% 2.15/1.02    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.15/1.02    inference(nnf_transformation,[],[f29])).
% 2.15/1.02  
% 2.15/1.02  fof(f64,plain,(
% 2.15/1.02    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.15/1.02    inference(cnf_transformation,[],[f46])).
% 2.15/1.02  
% 2.15/1.02  fof(f62,plain,(
% 2.15/1.02    ( ! [X0,X1] : (v1_tex_2(X1,X0) | ~v1_subset_1(sK0(X0,X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.15/1.02    inference(cnf_transformation,[],[f45])).
% 2.15/1.02  
% 2.15/1.02  fof(f59,plain,(
% 2.15/1.02    ( ! [X0,X3,X1] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.15/1.02    inference(cnf_transformation,[],[f45])).
% 2.15/1.02  
% 2.15/1.02  fof(f77,plain,(
% 2.15/1.02    ( ! [X0,X1] : (v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.15/1.02    inference(equality_resolution,[],[f59])).
% 2.15/1.02  
% 2.15/1.02  fof(f5,axiom,(
% 2.15/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.15/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.15/1.02  
% 2.15/1.02  fof(f24,plain,(
% 2.15/1.02    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.15/1.02    inference(ennf_transformation,[],[f5])).
% 2.15/1.02  
% 2.15/1.02  fof(f56,plain,(
% 2.15/1.02    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.15/1.02    inference(cnf_transformation,[],[f24])).
% 2.15/1.02  
% 2.15/1.02  fof(f75,plain,(
% 2.15/1.02    v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) | v1_tex_2(k1_tex_2(sK1,sK2),sK1)),
% 2.15/1.02    inference(cnf_transformation,[],[f51])).
% 2.15/1.02  
% 2.15/1.02  fof(f11,axiom,(
% 2.15/1.02    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 2.15/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.15/1.02  
% 2.15/1.02  fof(f34,plain,(
% 2.15/1.02    ! [X0] : (! [X1] : ((~v1_zfmisc_1(X0) | ~v1_subset_1(k6_domain_1(X0,X1),X0)) | ~m1_subset_1(X1,X0)) | v1_xboole_0(X0))),
% 2.15/1.02    inference(ennf_transformation,[],[f11])).
% 2.15/1.02  
% 2.15/1.02  fof(f35,plain,(
% 2.15/1.02    ! [X0] : (! [X1] : (~v1_zfmisc_1(X0) | ~v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | v1_xboole_0(X0))),
% 2.15/1.02    inference(flattening,[],[f34])).
% 2.15/1.02  
% 2.15/1.02  fof(f69,plain,(
% 2.15/1.02    ( ! [X0,X1] : (~v1_zfmisc_1(X0) | ~v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.15/1.02    inference(cnf_transformation,[],[f35])).
% 2.15/1.02  
% 2.15/1.02  fof(f3,axiom,(
% 2.15/1.02    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.15/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.15/1.02  
% 2.15/1.02  fof(f20,plain,(
% 2.15/1.02    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.15/1.02    inference(ennf_transformation,[],[f3])).
% 2.15/1.02  
% 2.15/1.02  fof(f21,plain,(
% 2.15/1.02    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.15/1.02    inference(flattening,[],[f20])).
% 2.15/1.02  
% 2.15/1.02  fof(f54,plain,(
% 2.15/1.02    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.15/1.02    inference(cnf_transformation,[],[f21])).
% 2.15/1.02  
% 2.15/1.02  fof(f10,axiom,(
% 2.15/1.02    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 2.15/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.15/1.02  
% 2.15/1.02  fof(f16,plain,(
% 2.15/1.02    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 2.15/1.02    inference(pure_predicate_removal,[],[f10])).
% 2.15/1.02  
% 2.15/1.02  fof(f32,plain,(
% 2.15/1.02    ! [X0,X1] : ((v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.15/1.02    inference(ennf_transformation,[],[f16])).
% 2.15/1.02  
% 2.15/1.02  fof(f33,plain,(
% 2.15/1.02    ! [X0,X1] : ((v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.15/1.02    inference(flattening,[],[f32])).
% 2.15/1.02  
% 2.15/1.02  fof(f68,plain,(
% 2.15/1.02    ( ! [X0,X1] : (v7_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.15/1.02    inference(cnf_transformation,[],[f33])).
% 2.15/1.02  
% 2.15/1.02  fof(f4,axiom,(
% 2.15/1.02    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 2.15/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.15/1.02  
% 2.15/1.02  fof(f22,plain,(
% 2.15/1.02    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 2.15/1.02    inference(ennf_transformation,[],[f4])).
% 2.15/1.02  
% 2.15/1.02  fof(f23,plain,(
% 2.15/1.02    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 2.15/1.02    inference(flattening,[],[f22])).
% 2.15/1.02  
% 2.15/1.02  fof(f55,plain,(
% 2.15/1.02    ( ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0)) )),
% 2.15/1.02    inference(cnf_transformation,[],[f23])).
% 2.15/1.02  
% 2.15/1.02  fof(f2,axiom,(
% 2.15/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.15/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.15/1.02  
% 2.15/1.02  fof(f19,plain,(
% 2.15/1.02    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.15/1.02    inference(ennf_transformation,[],[f2])).
% 2.15/1.02  
% 2.15/1.02  fof(f53,plain,(
% 2.15/1.02    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.15/1.02    inference(cnf_transformation,[],[f19])).
% 2.15/1.02  
% 2.15/1.02  fof(f6,axiom,(
% 2.15/1.02    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (~v1_xboole_0(X1) => (~v1_subset_1(X1,u1_struct_0(X0)) & ~v1_xboole_0(X1)))))),
% 2.15/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.15/1.02  
% 2.15/1.02  fof(f25,plain,(
% 2.15/1.02    ! [X0] : (! [X1] : (((~v1_subset_1(X1,u1_struct_0(X0)) & ~v1_xboole_0(X1)) | v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_struct_0(X0) | ~v7_struct_0(X0) | v2_struct_0(X0)))),
% 2.15/1.02    inference(ennf_transformation,[],[f6])).
% 2.15/1.02  
% 2.15/1.02  fof(f26,plain,(
% 2.15/1.02    ! [X0] : (! [X1] : ((~v1_subset_1(X1,u1_struct_0(X0)) & ~v1_xboole_0(X1)) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_struct_0(X0) | ~v7_struct_0(X0) | v2_struct_0(X0))),
% 2.15/1.02    inference(flattening,[],[f25])).
% 2.15/1.02  
% 2.15/1.02  fof(f58,plain,(
% 2.15/1.02    ( ! [X0,X1] : (~v1_subset_1(X1,u1_struct_0(X0)) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0) | ~v7_struct_0(X0) | v2_struct_0(X0)) )),
% 2.15/1.02    inference(cnf_transformation,[],[f26])).
% 2.15/1.02  
% 2.15/1.02  fof(f67,plain,(
% 2.15/1.02    ( ! [X0,X1] : (~v2_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.15/1.02    inference(cnf_transformation,[],[f33])).
% 2.15/1.02  
% 2.15/1.02  fof(f61,plain,(
% 2.15/1.02    ( ! [X0,X1] : (v1_tex_2(X1,X0) | u1_struct_0(X1) = sK0(X0,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.15/1.02    inference(cnf_transformation,[],[f45])).
% 2.15/1.02  
% 2.15/1.02  cnf(c_0,plain,
% 2.15/1.02      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 2.15/1.02      inference(cnf_transformation,[],[f52]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_19,plain,
% 2.15/1.02      ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
% 2.15/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.15/1.02      | v7_struct_0(X0)
% 2.15/1.02      | v2_struct_0(X0)
% 2.15/1.02      | ~ l1_struct_0(X0) ),
% 2.15/1.02      inference(cnf_transformation,[],[f71]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_414,plain,
% 2.15/1.02      ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
% 2.15/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.15/1.02      | v7_struct_0(X0)
% 2.15/1.02      | v2_struct_0(X0)
% 2.15/1.02      | ~ l1_pre_topc(X0) ),
% 2.15/1.02      inference(resolution,[status(thm)],[c_0,c_19]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_3972,plain,
% 2.15/1.02      ( v1_subset_1(k6_domain_1(u1_struct_0(X0_46),X0_45),u1_struct_0(X0_46))
% 2.15/1.02      | ~ m1_subset_1(X0_45,u1_struct_0(X0_46))
% 2.15/1.02      | v7_struct_0(X0_46)
% 2.15/1.02      | v2_struct_0(X0_46)
% 2.15/1.02      | ~ l1_pre_topc(X0_46) ),
% 2.15/1.02      inference(subtyping,[status(esa)],[c_414]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_4498,plain,
% 2.15/1.02      ( v1_subset_1(k6_domain_1(u1_struct_0(X0_46),X0_45),u1_struct_0(X0_46)) = iProver_top
% 2.15/1.02      | m1_subset_1(X0_45,u1_struct_0(X0_46)) != iProver_top
% 2.15/1.02      | v7_struct_0(X0_46) = iProver_top
% 2.15/1.02      | v2_struct_0(X0_46) = iProver_top
% 2.15/1.02      | l1_pre_topc(X0_46) != iProver_top ),
% 2.15/1.02      inference(predicate_to_equality,[status(thm)],[c_3972]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_9,plain,
% 2.15/1.02      ( v1_tex_2(X0,X1)
% 2.15/1.02      | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.15/1.02      | ~ m1_pre_topc(X0,X1)
% 2.15/1.02      | ~ l1_pre_topc(X1) ),
% 2.15/1.02      inference(cnf_transformation,[],[f60]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_20,negated_conjecture,
% 2.15/1.02      ( ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1)
% 2.15/1.02      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) ),
% 2.15/1.02      inference(cnf_transformation,[],[f76]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_191,plain,
% 2.15/1.02      ( ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1)
% 2.15/1.02      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) ),
% 2.15/1.02      inference(prop_impl,[status(thm)],[c_20]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_819,plain,
% 2.15/1.02      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 2.15/1.02      | m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
% 2.15/1.02      | ~ m1_pre_topc(X1,X0)
% 2.15/1.02      | ~ l1_pre_topc(X0)
% 2.15/1.02      | k1_tex_2(sK1,sK2) != X1
% 2.15/1.02      | sK1 != X0 ),
% 2.15/1.02      inference(resolution_lifted,[status(thm)],[c_9,c_191]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_820,plain,
% 2.15/1.02      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 2.15/1.02      | m1_subset_1(sK0(sK1,k1_tex_2(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.15/1.02      | ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
% 2.15/1.02      | ~ l1_pre_topc(sK1) ),
% 2.15/1.02      inference(unflattening,[status(thm)],[c_819]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_23,negated_conjecture,
% 2.15/1.02      ( l1_pre_topc(sK1) ),
% 2.15/1.02      inference(cnf_transformation,[],[f73]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_822,plain,
% 2.15/1.02      ( ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
% 2.15/1.02      | m1_subset_1(sK0(sK1,k1_tex_2(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.15/1.02      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) ),
% 2.15/1.02      inference(global_propositional_subsumption,
% 2.15/1.02                [status(thm)],
% 2.15/1.02                [c_820,c_23]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_823,plain,
% 2.15/1.02      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 2.15/1.02      | m1_subset_1(sK0(sK1,k1_tex_2(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.15/1.02      | ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1) ),
% 2.15/1.02      inference(renaming,[status(thm)],[c_822]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_3964,plain,
% 2.15/1.02      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 2.15/1.02      | m1_subset_1(sK0(sK1,k1_tex_2(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.15/1.02      | ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1) ),
% 2.15/1.02      inference(subtyping,[status(esa)],[c_823]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_4506,plain,
% 2.15/1.02      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top
% 2.15/1.02      | m1_subset_1(sK0(sK1,k1_tex_2(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 2.15/1.02      | m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top ),
% 2.15/1.02      inference(predicate_to_equality,[status(thm)],[c_3964]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_24,negated_conjecture,
% 2.15/1.02      ( ~ v2_struct_0(sK1) ),
% 2.15/1.02      inference(cnf_transformation,[],[f72]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_25,plain,
% 2.15/1.02      ( v2_struct_0(sK1) != iProver_top ),
% 2.15/1.02      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_26,plain,
% 2.15/1.02      ( l1_pre_topc(sK1) = iProver_top ),
% 2.15/1.02      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_22,negated_conjecture,
% 2.15/1.02      ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 2.15/1.02      inference(cnf_transformation,[],[f74]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_27,plain,
% 2.15/1.02      ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
% 2.15/1.02      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_824,plain,
% 2.15/1.02      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top
% 2.15/1.02      | m1_subset_1(sK0(sK1,k1_tex_2(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 2.15/1.02      | m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top ),
% 2.15/1.02      inference(predicate_to_equality,[status(thm)],[c_823]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_13,plain,
% 2.15/1.02      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.15/1.02      | m1_pre_topc(k1_tex_2(X1,X0),X1)
% 2.15/1.02      | v2_struct_0(X1)
% 2.15/1.02      | ~ l1_pre_topc(X1) ),
% 2.15/1.02      inference(cnf_transformation,[],[f66]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_3979,plain,
% 2.15/1.02      ( ~ m1_subset_1(X0_45,u1_struct_0(X0_46))
% 2.15/1.02      | m1_pre_topc(k1_tex_2(X0_46,X0_45),X0_46)
% 2.15/1.02      | v2_struct_0(X0_46)
% 2.15/1.02      | ~ l1_pre_topc(X0_46) ),
% 2.15/1.02      inference(subtyping,[status(esa)],[c_13]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_4023,plain,
% 2.15/1.02      ( m1_subset_1(X0_45,u1_struct_0(X0_46)) != iProver_top
% 2.15/1.02      | m1_pre_topc(k1_tex_2(X0_46,X0_45),X0_46) = iProver_top
% 2.15/1.02      | v2_struct_0(X0_46) = iProver_top
% 2.15/1.02      | l1_pre_topc(X0_46) != iProver_top ),
% 2.15/1.02      inference(predicate_to_equality,[status(thm)],[c_3979]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_4025,plain,
% 2.15/1.02      ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 2.15/1.02      | m1_pre_topc(k1_tex_2(sK1,sK2),sK1) = iProver_top
% 2.15/1.02      | v2_struct_0(sK1) = iProver_top
% 2.15/1.02      | l1_pre_topc(sK1) != iProver_top ),
% 2.15/1.02      inference(instantiation,[status(thm)],[c_4023]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_5242,plain,
% 2.15/1.02      ( m1_subset_1(sK0(sK1,k1_tex_2(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 2.15/1.02      | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top ),
% 2.15/1.02      inference(global_propositional_subsumption,
% 2.15/1.02                [status(thm)],
% 2.15/1.02                [c_4506,c_25,c_26,c_27,c_824,c_4025]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_5243,plain,
% 2.15/1.02      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top
% 2.15/1.02      | m1_subset_1(sK0(sK1,k1_tex_2(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.15/1.02      inference(renaming,[status(thm)],[c_5242]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_11,plain,
% 2.15/1.02      ( v1_subset_1(X0,X1)
% 2.15/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.15/1.02      | X0 = X1 ),
% 2.15/1.02      inference(cnf_transformation,[],[f64]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_3981,plain,
% 2.15/1.02      ( v1_subset_1(X0_45,X1_45)
% 2.15/1.02      | ~ m1_subset_1(X0_45,k1_zfmisc_1(X1_45))
% 2.15/1.02      | X0_45 = X1_45 ),
% 2.15/1.02      inference(subtyping,[status(esa)],[c_11]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_4489,plain,
% 2.15/1.02      ( X0_45 = X1_45
% 2.15/1.02      | v1_subset_1(X0_45,X1_45) = iProver_top
% 2.15/1.02      | m1_subset_1(X0_45,k1_zfmisc_1(X1_45)) != iProver_top ),
% 2.15/1.02      inference(predicate_to_equality,[status(thm)],[c_3981]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_5248,plain,
% 2.15/1.02      ( sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(sK1)
% 2.15/1.02      | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top
% 2.15/1.02      | v1_subset_1(sK0(sK1,k1_tex_2(sK1,sK2)),u1_struct_0(sK1)) = iProver_top ),
% 2.15/1.02      inference(superposition,[status(thm)],[c_5243,c_4489]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_821,plain,
% 2.15/1.02      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top
% 2.15/1.02      | m1_subset_1(sK0(sK1,k1_tex_2(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 2.15/1.02      | m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top
% 2.15/1.02      | l1_pre_topc(sK1) != iProver_top ),
% 2.15/1.02      inference(predicate_to_equality,[status(thm)],[c_820]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_7,plain,
% 2.15/1.02      ( v1_tex_2(X0,X1)
% 2.15/1.02      | ~ v1_subset_1(sK0(X1,X0),u1_struct_0(X1))
% 2.15/1.02      | ~ m1_pre_topc(X0,X1)
% 2.15/1.02      | ~ l1_pre_topc(X1) ),
% 2.15/1.02      inference(cnf_transformation,[],[f62]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_853,plain,
% 2.15/1.02      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 2.15/1.02      | ~ v1_subset_1(sK0(X0,X1),u1_struct_0(X0))
% 2.15/1.02      | ~ m1_pre_topc(X1,X0)
% 2.15/1.02      | ~ l1_pre_topc(X0)
% 2.15/1.02      | k1_tex_2(sK1,sK2) != X1
% 2.15/1.02      | sK1 != X0 ),
% 2.15/1.02      inference(resolution_lifted,[status(thm)],[c_7,c_191]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_854,plain,
% 2.15/1.02      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 2.15/1.02      | ~ v1_subset_1(sK0(sK1,k1_tex_2(sK1,sK2)),u1_struct_0(sK1))
% 2.15/1.02      | ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
% 2.15/1.02      | ~ l1_pre_topc(sK1) ),
% 2.15/1.02      inference(unflattening,[status(thm)],[c_853]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_855,plain,
% 2.15/1.02      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top
% 2.15/1.02      | v1_subset_1(sK0(sK1,k1_tex_2(sK1,sK2)),u1_struct_0(sK1)) != iProver_top
% 2.15/1.02      | m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top
% 2.15/1.02      | l1_pre_topc(sK1) != iProver_top ),
% 2.15/1.02      inference(predicate_to_equality,[status(thm)],[c_854]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_4792,plain,
% 2.15/1.02      ( v1_subset_1(X0_45,u1_struct_0(sK1))
% 2.15/1.02      | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.15/1.02      | X0_45 = u1_struct_0(sK1) ),
% 2.15/1.02      inference(instantiation,[status(thm)],[c_3981]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_4891,plain,
% 2.15/1.02      ( v1_subset_1(sK0(sK1,k1_tex_2(sK1,sK2)),u1_struct_0(sK1))
% 2.15/1.02      | ~ m1_subset_1(sK0(sK1,k1_tex_2(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.15/1.02      | sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(sK1) ),
% 2.15/1.02      inference(instantiation,[status(thm)],[c_4792]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_4892,plain,
% 2.15/1.02      ( sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(sK1)
% 2.15/1.02      | v1_subset_1(sK0(sK1,k1_tex_2(sK1,sK2)),u1_struct_0(sK1)) = iProver_top
% 2.15/1.02      | m1_subset_1(sK0(sK1,k1_tex_2(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.15/1.02      inference(predicate_to_equality,[status(thm)],[c_4891]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_5908,plain,
% 2.15/1.02      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top
% 2.15/1.02      | sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(sK1) ),
% 2.15/1.02      inference(global_propositional_subsumption,
% 2.15/1.02                [status(thm)],
% 2.15/1.02                [c_5248,c_25,c_26,c_27,c_821,c_855,c_4025,c_4892]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_5909,plain,
% 2.15/1.02      ( sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(sK1)
% 2.15/1.02      | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top ),
% 2.15/1.02      inference(renaming,[status(thm)],[c_5908]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_5915,plain,
% 2.15/1.02      ( sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(sK1)
% 2.15/1.02      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 2.15/1.02      | v7_struct_0(sK1) = iProver_top
% 2.15/1.02      | v2_struct_0(sK1) = iProver_top
% 2.15/1.02      | l1_pre_topc(sK1) != iProver_top ),
% 2.15/1.02      inference(superposition,[status(thm)],[c_4498,c_5909]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_6425,plain,
% 2.15/1.02      ( sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(sK1)
% 2.15/1.02      | v7_struct_0(sK1) = iProver_top ),
% 2.15/1.02      inference(global_propositional_subsumption,
% 2.15/1.02                [status(thm)],
% 2.15/1.02                [c_5915,c_25,c_26,c_27]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_10,plain,
% 2.15/1.02      ( ~ v1_tex_2(X0,X1)
% 2.15/1.02      | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
% 2.15/1.02      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.15/1.02      | ~ m1_pre_topc(X0,X1)
% 2.15/1.02      | ~ l1_pre_topc(X1) ),
% 2.15/1.02      inference(cnf_transformation,[],[f77]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_4,plain,
% 2.15/1.02      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.15/1.02      | ~ m1_pre_topc(X0,X1)
% 2.15/1.02      | ~ l1_pre_topc(X1) ),
% 2.15/1.02      inference(cnf_transformation,[],[f56]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_149,plain,
% 2.15/1.02      ( v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
% 2.15/1.02      | ~ v1_tex_2(X0,X1)
% 2.15/1.02      | ~ m1_pre_topc(X0,X1)
% 2.15/1.02      | ~ l1_pre_topc(X1) ),
% 2.15/1.02      inference(global_propositional_subsumption,
% 2.15/1.02                [status(thm)],
% 2.15/1.02                [c_10,c_4]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_150,plain,
% 2.15/1.02      ( ~ v1_tex_2(X0,X1)
% 2.15/1.02      | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
% 2.15/1.02      | ~ m1_pre_topc(X0,X1)
% 2.15/1.02      | ~ l1_pre_topc(X1) ),
% 2.15/1.02      inference(renaming,[status(thm)],[c_149]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_21,negated_conjecture,
% 2.15/1.02      ( v1_tex_2(k1_tex_2(sK1,sK2),sK1)
% 2.15/1.02      | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) ),
% 2.15/1.02      inference(cnf_transformation,[],[f75]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_193,plain,
% 2.15/1.02      ( v1_tex_2(k1_tex_2(sK1,sK2),sK1)
% 2.15/1.02      | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) ),
% 2.15/1.02      inference(prop_impl,[status(thm)],[c_21]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_870,plain,
% 2.15/1.02      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 2.15/1.02      | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
% 2.15/1.02      | ~ m1_pre_topc(X0,X1)
% 2.15/1.02      | ~ l1_pre_topc(X1)
% 2.15/1.02      | k1_tex_2(sK1,sK2) != X0
% 2.15/1.02      | sK1 != X1 ),
% 2.15/1.02      inference(resolution_lifted,[status(thm)],[c_150,c_193]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_871,plain,
% 2.15/1.02      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 2.15/1.02      | v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1))
% 2.15/1.02      | ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
% 2.15/1.02      | ~ l1_pre_topc(sK1) ),
% 2.15/1.02      inference(unflattening,[status(thm)],[c_870]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_873,plain,
% 2.15/1.02      ( ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
% 2.15/1.02      | v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1))
% 2.15/1.02      | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) ),
% 2.15/1.02      inference(global_propositional_subsumption,
% 2.15/1.02                [status(thm)],
% 2.15/1.02                [c_871,c_23]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_874,plain,
% 2.15/1.02      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 2.15/1.02      | v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1))
% 2.15/1.02      | ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1) ),
% 2.15/1.02      inference(renaming,[status(thm)],[c_873]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_3961,plain,
% 2.15/1.02      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 2.15/1.02      | v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1))
% 2.15/1.02      | ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1) ),
% 2.15/1.02      inference(subtyping,[status(esa)],[c_874]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_4509,plain,
% 2.15/1.02      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) = iProver_top
% 2.15/1.02      | v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1)) = iProver_top
% 2.15/1.02      | m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top ),
% 2.15/1.02      inference(predicate_to_equality,[status(thm)],[c_3961]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_4024,plain,
% 2.15/1.02      ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 2.15/1.02      | m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
% 2.15/1.02      | v2_struct_0(sK1)
% 2.15/1.02      | ~ l1_pre_topc(sK1) ),
% 2.15/1.02      inference(instantiation,[status(thm)],[c_3979]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_4132,plain,
% 2.15/1.02      ( v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1))
% 2.15/1.02      | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) ),
% 2.15/1.02      inference(global_propositional_subsumption,
% 2.15/1.02                [status(thm)],
% 2.15/1.02                [c_3961,c_24,c_23,c_22,c_871,c_4024]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_4133,plain,
% 2.15/1.02      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 2.15/1.02      | v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1)) ),
% 2.15/1.02      inference(renaming,[status(thm)],[c_4132]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_4134,plain,
% 2.15/1.02      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) = iProver_top
% 2.15/1.02      | v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1)) = iProver_top ),
% 2.15/1.02      inference(predicate_to_equality,[status(thm)],[c_4133]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_5673,plain,
% 2.15/1.02      ( v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1)) = iProver_top
% 2.15/1.02      | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) = iProver_top ),
% 2.15/1.02      inference(global_propositional_subsumption,
% 2.15/1.02                [status(thm)],
% 2.15/1.02                [c_4509,c_4134]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_5674,plain,
% 2.15/1.02      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) = iProver_top
% 2.15/1.02      | v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1)) = iProver_top ),
% 2.15/1.02      inference(renaming,[status(thm)],[c_5673]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_17,plain,
% 2.15/1.02      ( ~ v1_subset_1(k6_domain_1(X0,X1),X0)
% 2.15/1.02      | ~ m1_subset_1(X1,X0)
% 2.15/1.02      | ~ v1_zfmisc_1(X0)
% 2.15/1.02      | v1_xboole_0(X0) ),
% 2.15/1.02      inference(cnf_transformation,[],[f69]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_3976,plain,
% 2.15/1.02      ( ~ v1_subset_1(k6_domain_1(X0_45,X1_45),X0_45)
% 2.15/1.02      | ~ m1_subset_1(X1_45,X0_45)
% 2.15/1.02      | ~ v1_zfmisc_1(X0_45)
% 2.15/1.02      | v1_xboole_0(X0_45) ),
% 2.15/1.02      inference(subtyping,[status(esa)],[c_17]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_4494,plain,
% 2.15/1.02      ( v1_subset_1(k6_domain_1(X0_45,X1_45),X0_45) != iProver_top
% 2.15/1.02      | m1_subset_1(X1_45,X0_45) != iProver_top
% 2.15/1.02      | v1_zfmisc_1(X0_45) != iProver_top
% 2.15/1.02      | v1_xboole_0(X0_45) = iProver_top ),
% 2.15/1.02      inference(predicate_to_equality,[status(thm)],[c_3976]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_5681,plain,
% 2.15/1.02      ( v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1)) = iProver_top
% 2.15/1.02      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 2.15/1.02      | v1_zfmisc_1(u1_struct_0(sK1)) != iProver_top
% 2.15/1.02      | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
% 2.15/1.02      inference(superposition,[status(thm)],[c_5674,c_4494]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_2,plain,
% 2.15/1.02      ( v2_struct_0(X0)
% 2.15/1.02      | ~ v1_xboole_0(u1_struct_0(X0))
% 2.15/1.02      | ~ l1_struct_0(X0) ),
% 2.15/1.02      inference(cnf_transformation,[],[f54]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_77,plain,
% 2.15/1.02      ( v2_struct_0(X0) = iProver_top
% 2.15/1.02      | v1_xboole_0(u1_struct_0(X0)) != iProver_top
% 2.15/1.02      | l1_struct_0(X0) != iProver_top ),
% 2.15/1.02      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_79,plain,
% 2.15/1.02      ( v2_struct_0(sK1) = iProver_top
% 2.15/1.02      | v1_xboole_0(u1_struct_0(sK1)) != iProver_top
% 2.15/1.02      | l1_struct_0(sK1) != iProver_top ),
% 2.15/1.02      inference(instantiation,[status(thm)],[c_77]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_81,plain,
% 2.15/1.02      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 2.15/1.02      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_83,plain,
% 2.15/1.02      ( l1_pre_topc(sK1) != iProver_top
% 2.15/1.02      | l1_struct_0(sK1) = iProver_top ),
% 2.15/1.02      inference(instantiation,[status(thm)],[c_81]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_3990,plain,
% 2.15/1.02      ( X0_46 != X1_46 | u1_struct_0(X0_46) = u1_struct_0(X1_46) ),
% 2.15/1.02      theory(equality) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_4003,plain,
% 2.15/1.02      ( sK1 != sK1 | u1_struct_0(sK1) = u1_struct_0(sK1) ),
% 2.15/1.02      inference(instantiation,[status(thm)],[c_3990]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_3986,plain,( X0_46 = X0_46 ),theory(equality) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_4016,plain,
% 2.15/1.02      ( sK1 = sK1 ),
% 2.15/1.02      inference(instantiation,[status(thm)],[c_3986]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_15,plain,
% 2.15/1.02      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.15/1.02      | v7_struct_0(k1_tex_2(X1,X0))
% 2.15/1.02      | v2_struct_0(X1)
% 2.15/1.02      | ~ l1_pre_topc(X1) ),
% 2.15/1.02      inference(cnf_transformation,[],[f68]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_3977,plain,
% 2.15/1.02      ( ~ m1_subset_1(X0_45,u1_struct_0(X0_46))
% 2.15/1.02      | v7_struct_0(k1_tex_2(X0_46,X0_45))
% 2.15/1.02      | v2_struct_0(X0_46)
% 2.15/1.02      | ~ l1_pre_topc(X0_46) ),
% 2.15/1.02      inference(subtyping,[status(esa)],[c_15]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_4029,plain,
% 2.15/1.02      ( m1_subset_1(X0_45,u1_struct_0(X0_46)) != iProver_top
% 2.15/1.02      | v7_struct_0(k1_tex_2(X0_46,X0_45)) = iProver_top
% 2.15/1.02      | v2_struct_0(X0_46) = iProver_top
% 2.15/1.02      | l1_pre_topc(X0_46) != iProver_top ),
% 2.15/1.02      inference(predicate_to_equality,[status(thm)],[c_3977]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_4031,plain,
% 2.15/1.02      ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 2.15/1.02      | v7_struct_0(k1_tex_2(sK1,sK2)) = iProver_top
% 2.15/1.02      | v2_struct_0(sK1) = iProver_top
% 2.15/1.02      | l1_pre_topc(sK1) != iProver_top ),
% 2.15/1.02      inference(instantiation,[status(thm)],[c_4029]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_3982,plain,
% 2.15/1.02      ( m1_subset_1(u1_struct_0(X0_46),k1_zfmisc_1(u1_struct_0(X1_46)))
% 2.15/1.02      | ~ m1_pre_topc(X0_46,X1_46)
% 2.15/1.02      | ~ l1_pre_topc(X1_46) ),
% 2.15/1.02      inference(subtyping,[status(esa)],[c_4]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_4724,plain,
% 2.15/1.02      ( m1_subset_1(u1_struct_0(k1_tex_2(X0_46,X0_45)),k1_zfmisc_1(u1_struct_0(X0_46)))
% 2.15/1.02      | ~ m1_pre_topc(k1_tex_2(X0_46,X0_45),X0_46)
% 2.15/1.02      | ~ l1_pre_topc(X0_46) ),
% 2.15/1.02      inference(instantiation,[status(thm)],[c_3982]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_4725,plain,
% 2.15/1.02      ( m1_subset_1(u1_struct_0(k1_tex_2(X0_46,X0_45)),k1_zfmisc_1(u1_struct_0(X0_46))) = iProver_top
% 2.15/1.02      | m1_pre_topc(k1_tex_2(X0_46,X0_45),X0_46) != iProver_top
% 2.15/1.02      | l1_pre_topc(X0_46) != iProver_top ),
% 2.15/1.02      inference(predicate_to_equality,[status(thm)],[c_4724]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_4727,plain,
% 2.15/1.02      ( m1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 2.15/1.02      | m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top
% 2.15/1.02      | l1_pre_topc(sK1) != iProver_top ),
% 2.15/1.02      inference(instantiation,[status(thm)],[c_4725]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_3,plain,
% 2.15/1.02      ( ~ v7_struct_0(X0)
% 2.15/1.02      | v1_zfmisc_1(u1_struct_0(X0))
% 2.15/1.02      | ~ l1_struct_0(X0) ),
% 2.15/1.02      inference(cnf_transformation,[],[f55]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_454,plain,
% 2.15/1.02      ( ~ v7_struct_0(X0)
% 2.15/1.02      | v1_zfmisc_1(u1_struct_0(X0))
% 2.15/1.02      | ~ l1_pre_topc(X0) ),
% 2.15/1.02      inference(resolution,[status(thm)],[c_0,c_3]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_3970,plain,
% 2.15/1.02      ( ~ v7_struct_0(X0_46)
% 2.15/1.02      | v1_zfmisc_1(u1_struct_0(X0_46))
% 2.15/1.02      | ~ l1_pre_topc(X0_46) ),
% 2.15/1.02      inference(subtyping,[status(esa)],[c_454]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_4820,plain,
% 2.15/1.02      ( ~ v7_struct_0(k1_tex_2(X0_46,X0_45))
% 2.15/1.02      | v1_zfmisc_1(u1_struct_0(k1_tex_2(X0_46,X0_45)))
% 2.15/1.02      | ~ l1_pre_topc(k1_tex_2(X0_46,X0_45)) ),
% 2.15/1.02      inference(instantiation,[status(thm)],[c_3970]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_4821,plain,
% 2.15/1.02      ( v7_struct_0(k1_tex_2(X0_46,X0_45)) != iProver_top
% 2.15/1.02      | v1_zfmisc_1(u1_struct_0(k1_tex_2(X0_46,X0_45))) = iProver_top
% 2.15/1.02      | l1_pre_topc(k1_tex_2(X0_46,X0_45)) != iProver_top ),
% 2.15/1.02      inference(predicate_to_equality,[status(thm)],[c_4820]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_4823,plain,
% 2.15/1.02      ( v7_struct_0(k1_tex_2(sK1,sK2)) != iProver_top
% 2.15/1.02      | v1_zfmisc_1(u1_struct_0(k1_tex_2(sK1,sK2))) = iProver_top
% 2.15/1.02      | l1_pre_topc(k1_tex_2(sK1,sK2)) != iProver_top ),
% 2.15/1.02      inference(instantiation,[status(thm)],[c_4821]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_4491,plain,
% 2.15/1.02      ( m1_subset_1(X0_45,u1_struct_0(X0_46)) != iProver_top
% 2.15/1.02      | m1_pre_topc(k1_tex_2(X0_46,X0_45),X0_46) = iProver_top
% 2.15/1.02      | v2_struct_0(X0_46) = iProver_top
% 2.15/1.02      | l1_pre_topc(X0_46) != iProver_top ),
% 2.15/1.02      inference(predicate_to_equality,[status(thm)],[c_3979]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_1,plain,
% 2.15/1.02      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.15/1.02      inference(cnf_transformation,[],[f53]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_3983,plain,
% 2.15/1.02      ( ~ m1_pre_topc(X0_46,X1_46)
% 2.15/1.02      | ~ l1_pre_topc(X1_46)
% 2.15/1.02      | l1_pre_topc(X0_46) ),
% 2.15/1.02      inference(subtyping,[status(esa)],[c_1]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_4487,plain,
% 2.15/1.02      ( m1_pre_topc(X0_46,X1_46) != iProver_top
% 2.15/1.02      | l1_pre_topc(X1_46) != iProver_top
% 2.15/1.02      | l1_pre_topc(X0_46) = iProver_top ),
% 2.15/1.02      inference(predicate_to_equality,[status(thm)],[c_3983]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_4876,plain,
% 2.15/1.02      ( m1_subset_1(X0_45,u1_struct_0(X0_46)) != iProver_top
% 2.15/1.02      | v2_struct_0(X0_46) = iProver_top
% 2.15/1.02      | l1_pre_topc(X0_46) != iProver_top
% 2.15/1.02      | l1_pre_topc(k1_tex_2(X0_46,X0_45)) = iProver_top ),
% 2.15/1.02      inference(superposition,[status(thm)],[c_4491,c_4487]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_4878,plain,
% 2.15/1.02      ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 2.15/1.02      | v2_struct_0(sK1) = iProver_top
% 2.15/1.02      | l1_pre_topc(k1_tex_2(sK1,sK2)) = iProver_top
% 2.15/1.02      | l1_pre_topc(sK1) != iProver_top ),
% 2.15/1.02      inference(instantiation,[status(thm)],[c_4876]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_4894,plain,
% 2.15/1.02      ( v1_subset_1(u1_struct_0(k1_tex_2(sK1,X0_45)),u1_struct_0(sK1))
% 2.15/1.02      | ~ m1_subset_1(u1_struct_0(k1_tex_2(sK1,X0_45)),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.15/1.02      | u1_struct_0(k1_tex_2(sK1,X0_45)) = u1_struct_0(sK1) ),
% 2.15/1.02      inference(instantiation,[status(thm)],[c_4792]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_4896,plain,
% 2.15/1.02      ( u1_struct_0(k1_tex_2(sK1,X0_45)) = u1_struct_0(sK1)
% 2.15/1.02      | v1_subset_1(u1_struct_0(k1_tex_2(sK1,X0_45)),u1_struct_0(sK1)) = iProver_top
% 2.15/1.02      | m1_subset_1(u1_struct_0(k1_tex_2(sK1,X0_45)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.15/1.02      inference(predicate_to_equality,[status(thm)],[c_4894]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_4898,plain,
% 2.15/1.02      ( u1_struct_0(k1_tex_2(sK1,sK2)) = u1_struct_0(sK1)
% 2.15/1.02      | v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1)) = iProver_top
% 2.15/1.02      | m1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.15/1.02      inference(instantiation,[status(thm)],[c_4896]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_3993,plain,
% 2.15/1.02      ( ~ v1_zfmisc_1(X0_45) | v1_zfmisc_1(X1_45) | X1_45 != X0_45 ),
% 2.15/1.02      theory(equality) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_4770,plain,
% 2.15/1.02      ( v1_zfmisc_1(X0_45)
% 2.15/1.02      | ~ v1_zfmisc_1(u1_struct_0(X0_46))
% 2.15/1.02      | X0_45 != u1_struct_0(X0_46) ),
% 2.15/1.02      inference(instantiation,[status(thm)],[c_3993]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_5109,plain,
% 2.15/1.02      ( v1_zfmisc_1(X0_45)
% 2.15/1.02      | ~ v1_zfmisc_1(u1_struct_0(k1_tex_2(X0_46,X1_45)))
% 2.15/1.02      | X0_45 != u1_struct_0(k1_tex_2(X0_46,X1_45)) ),
% 2.15/1.02      inference(instantiation,[status(thm)],[c_4770]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_5942,plain,
% 2.15/1.02      ( v1_zfmisc_1(u1_struct_0(X0_46))
% 2.15/1.02      | ~ v1_zfmisc_1(u1_struct_0(k1_tex_2(X1_46,X0_45)))
% 2.15/1.02      | u1_struct_0(X0_46) != u1_struct_0(k1_tex_2(X1_46,X0_45)) ),
% 2.15/1.02      inference(instantiation,[status(thm)],[c_5109]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_5944,plain,
% 2.15/1.02      ( u1_struct_0(X0_46) != u1_struct_0(k1_tex_2(X1_46,X0_45))
% 2.15/1.02      | v1_zfmisc_1(u1_struct_0(X0_46)) = iProver_top
% 2.15/1.02      | v1_zfmisc_1(u1_struct_0(k1_tex_2(X1_46,X0_45))) != iProver_top ),
% 2.15/1.02      inference(predicate_to_equality,[status(thm)],[c_5942]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_5946,plain,
% 2.15/1.02      ( u1_struct_0(sK1) != u1_struct_0(k1_tex_2(sK1,sK2))
% 2.15/1.02      | v1_zfmisc_1(u1_struct_0(k1_tex_2(sK1,sK2))) != iProver_top
% 2.15/1.02      | v1_zfmisc_1(u1_struct_0(sK1)) = iProver_top ),
% 2.15/1.02      inference(instantiation,[status(thm)],[c_5944]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_3987,plain,
% 2.15/1.02      ( X0_45 != X1_45 | X2_45 != X1_45 | X2_45 = X0_45 ),
% 2.15/1.02      theory(equality) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_4914,plain,
% 2.15/1.02      ( X0_45 != X1_45
% 2.15/1.02      | u1_struct_0(sK1) != X1_45
% 2.15/1.02      | u1_struct_0(sK1) = X0_45 ),
% 2.15/1.02      inference(instantiation,[status(thm)],[c_3987]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_5002,plain,
% 2.15/1.02      ( X0_45 != u1_struct_0(sK1)
% 2.15/1.02      | u1_struct_0(sK1) = X0_45
% 2.15/1.02      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 2.15/1.02      inference(instantiation,[status(thm)],[c_4914]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_5221,plain,
% 2.15/1.02      ( u1_struct_0(X0_46) != u1_struct_0(sK1)
% 2.15/1.02      | u1_struct_0(sK1) = u1_struct_0(X0_46)
% 2.15/1.02      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 2.15/1.02      inference(instantiation,[status(thm)],[c_5002]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_5999,plain,
% 2.15/1.02      ( u1_struct_0(k1_tex_2(X0_46,X0_45)) != u1_struct_0(sK1)
% 2.15/1.02      | u1_struct_0(sK1) = u1_struct_0(k1_tex_2(X0_46,X0_45))
% 2.15/1.02      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 2.15/1.02      inference(instantiation,[status(thm)],[c_5221]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_6005,plain,
% 2.15/1.02      ( u1_struct_0(k1_tex_2(sK1,sK2)) != u1_struct_0(sK1)
% 2.15/1.02      | u1_struct_0(sK1) = u1_struct_0(k1_tex_2(sK1,sK2))
% 2.15/1.02      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 2.15/1.02      inference(instantiation,[status(thm)],[c_5999]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_6050,plain,
% 2.15/1.02      ( v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1)) = iProver_top ),
% 2.15/1.02      inference(global_propositional_subsumption,
% 2.15/1.02                [status(thm)],
% 2.15/1.02                [c_5681,c_25,c_26,c_27,c_79,c_83,c_4003,c_4016,c_4025,
% 2.15/1.02                 c_4031,c_4727,c_4823,c_4878,c_4898,c_5946,c_6005]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_4488,plain,
% 2.15/1.02      ( m1_subset_1(u1_struct_0(X0_46),k1_zfmisc_1(u1_struct_0(X1_46))) = iProver_top
% 2.15/1.02      | m1_pre_topc(X0_46,X1_46) != iProver_top
% 2.15/1.02      | l1_pre_topc(X1_46) != iProver_top ),
% 2.15/1.02      inference(predicate_to_equality,[status(thm)],[c_3982]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_5,plain,
% 2.15/1.02      ( ~ v1_subset_1(X0,u1_struct_0(X1))
% 2.15/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.15/1.02      | ~ v7_struct_0(X1)
% 2.15/1.02      | v2_struct_0(X1)
% 2.15/1.02      | v1_xboole_0(X0)
% 2.15/1.02      | ~ l1_struct_0(X1) ),
% 2.15/1.02      inference(cnf_transformation,[],[f58]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_482,plain,
% 2.15/1.02      ( ~ v1_subset_1(X0,u1_struct_0(X1))
% 2.15/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.15/1.02      | ~ v7_struct_0(X1)
% 2.15/1.02      | v2_struct_0(X1)
% 2.15/1.02      | v1_xboole_0(X0)
% 2.15/1.02      | ~ l1_pre_topc(X2)
% 2.15/1.02      | X1 != X2 ),
% 2.15/1.02      inference(resolution_lifted,[status(thm)],[c_0,c_5]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_483,plain,
% 2.15/1.02      ( ~ v1_subset_1(X0,u1_struct_0(X1))
% 2.15/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.15/1.02      | ~ v7_struct_0(X1)
% 2.15/1.02      | v2_struct_0(X1)
% 2.15/1.02      | v1_xboole_0(X0)
% 2.15/1.02      | ~ l1_pre_topc(X1) ),
% 2.15/1.02      inference(unflattening,[status(thm)],[c_482]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_3968,plain,
% 2.15/1.02      ( ~ v1_subset_1(X0_45,u1_struct_0(X0_46))
% 2.15/1.02      | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(X0_46)))
% 2.15/1.02      | ~ v7_struct_0(X0_46)
% 2.15/1.02      | v2_struct_0(X0_46)
% 2.15/1.02      | v1_xboole_0(X0_45)
% 2.15/1.02      | ~ l1_pre_topc(X0_46) ),
% 2.15/1.02      inference(subtyping,[status(esa)],[c_483]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_4502,plain,
% 2.15/1.02      ( v1_subset_1(X0_45,u1_struct_0(X0_46)) != iProver_top
% 2.15/1.02      | m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(X0_46))) != iProver_top
% 2.15/1.02      | v7_struct_0(X0_46) != iProver_top
% 2.15/1.02      | v2_struct_0(X0_46) = iProver_top
% 2.15/1.02      | v1_xboole_0(X0_45) = iProver_top
% 2.15/1.02      | l1_pre_topc(X0_46) != iProver_top ),
% 2.15/1.02      inference(predicate_to_equality,[status(thm)],[c_3968]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_6064,plain,
% 2.15/1.02      ( v1_subset_1(u1_struct_0(X0_46),u1_struct_0(X1_46)) != iProver_top
% 2.15/1.02      | m1_pre_topc(X0_46,X1_46) != iProver_top
% 2.15/1.02      | v7_struct_0(X1_46) != iProver_top
% 2.15/1.02      | v2_struct_0(X1_46) = iProver_top
% 2.15/1.02      | v1_xboole_0(u1_struct_0(X0_46)) = iProver_top
% 2.15/1.02      | l1_pre_topc(X1_46) != iProver_top ),
% 2.15/1.02      inference(superposition,[status(thm)],[c_4488,c_4502]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_6297,plain,
% 2.15/1.02      ( m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top
% 2.15/1.02      | v7_struct_0(sK1) != iProver_top
% 2.15/1.02      | v2_struct_0(sK1) = iProver_top
% 2.15/1.02      | v1_xboole_0(u1_struct_0(k1_tex_2(sK1,sK2))) = iProver_top
% 2.15/1.02      | l1_pre_topc(sK1) != iProver_top ),
% 2.15/1.02      inference(superposition,[status(thm)],[c_6050,c_6064]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_6432,plain,
% 2.15/1.02      ( v1_xboole_0(u1_struct_0(k1_tex_2(sK1,sK2))) = iProver_top
% 2.15/1.02      | v7_struct_0(sK1) != iProver_top ),
% 2.15/1.02      inference(global_propositional_subsumption,
% 2.15/1.02                [status(thm)],
% 2.15/1.02                [c_6297,c_25,c_26,c_27,c_4025]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_6433,plain,
% 2.15/1.02      ( v7_struct_0(sK1) != iProver_top
% 2.15/1.02      | v1_xboole_0(u1_struct_0(k1_tex_2(sK1,sK2))) = iProver_top ),
% 2.15/1.02      inference(renaming,[status(thm)],[c_6432]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_468,plain,
% 2.15/1.02      ( v2_struct_0(X0)
% 2.15/1.02      | ~ v1_xboole_0(u1_struct_0(X0))
% 2.15/1.02      | ~ l1_pre_topc(X0) ),
% 2.15/1.02      inference(resolution,[status(thm)],[c_0,c_2]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_3969,plain,
% 2.15/1.02      ( v2_struct_0(X0_46)
% 2.15/1.02      | ~ v1_xboole_0(u1_struct_0(X0_46))
% 2.15/1.02      | ~ l1_pre_topc(X0_46) ),
% 2.15/1.02      inference(subtyping,[status(esa)],[c_468]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_4501,plain,
% 2.15/1.02      ( v2_struct_0(X0_46) = iProver_top
% 2.15/1.02      | v1_xboole_0(u1_struct_0(X0_46)) != iProver_top
% 2.15/1.02      | l1_pre_topc(X0_46) != iProver_top ),
% 2.15/1.02      inference(predicate_to_equality,[status(thm)],[c_3969]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_6438,plain,
% 2.15/1.02      ( v7_struct_0(sK1) != iProver_top
% 2.15/1.02      | v2_struct_0(k1_tex_2(sK1,sK2)) = iProver_top
% 2.15/1.02      | l1_pre_topc(k1_tex_2(sK1,sK2)) != iProver_top ),
% 2.15/1.02      inference(superposition,[status(thm)],[c_6433,c_4501]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_16,plain,
% 2.15/1.02      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.15/1.02      | v2_struct_0(X1)
% 2.15/1.02      | ~ v2_struct_0(k1_tex_2(X1,X0))
% 2.15/1.02      | ~ l1_pre_topc(X1) ),
% 2.15/1.02      inference(cnf_transformation,[],[f67]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_3978,plain,
% 2.15/1.02      ( ~ m1_subset_1(X0_45,u1_struct_0(X0_46))
% 2.15/1.02      | v2_struct_0(X0_46)
% 2.15/1.02      | ~ v2_struct_0(k1_tex_2(X0_46,X0_45))
% 2.15/1.02      | ~ l1_pre_topc(X0_46) ),
% 2.15/1.02      inference(subtyping,[status(esa)],[c_16]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_4026,plain,
% 2.15/1.02      ( m1_subset_1(X0_45,u1_struct_0(X0_46)) != iProver_top
% 2.15/1.02      | v2_struct_0(X0_46) = iProver_top
% 2.15/1.02      | v2_struct_0(k1_tex_2(X0_46,X0_45)) != iProver_top
% 2.15/1.02      | l1_pre_topc(X0_46) != iProver_top ),
% 2.15/1.02      inference(predicate_to_equality,[status(thm)],[c_3978]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_4028,plain,
% 2.15/1.02      ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 2.15/1.02      | v2_struct_0(k1_tex_2(sK1,sK2)) != iProver_top
% 2.15/1.02      | v2_struct_0(sK1) = iProver_top
% 2.15/1.02      | l1_pre_topc(sK1) != iProver_top ),
% 2.15/1.02      inference(instantiation,[status(thm)],[c_4026]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_6526,plain,
% 2.15/1.02      ( v7_struct_0(sK1) != iProver_top ),
% 2.15/1.02      inference(global_propositional_subsumption,
% 2.15/1.02                [status(thm)],
% 2.15/1.02                [c_6438,c_25,c_26,c_27,c_4028,c_4878]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_6531,plain,
% 2.15/1.02      ( sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(sK1) ),
% 2.15/1.02      inference(superposition,[status(thm)],[c_6425,c_6526]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_8,plain,
% 2.15/1.02      ( v1_tex_2(X0,X1)
% 2.15/1.02      | ~ m1_pre_topc(X0,X1)
% 2.15/1.02      | ~ l1_pre_topc(X1)
% 2.15/1.02      | sK0(X1,X0) = u1_struct_0(X0) ),
% 2.15/1.02      inference(cnf_transformation,[],[f61]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_836,plain,
% 2.15/1.02      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 2.15/1.02      | ~ m1_pre_topc(X0,X1)
% 2.15/1.02      | ~ l1_pre_topc(X1)
% 2.15/1.02      | k1_tex_2(sK1,sK2) != X0
% 2.15/1.02      | sK0(X1,X0) = u1_struct_0(X0)
% 2.15/1.02      | sK1 != X1 ),
% 2.15/1.02      inference(resolution_lifted,[status(thm)],[c_8,c_191]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_837,plain,
% 2.15/1.02      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 2.15/1.02      | ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
% 2.15/1.02      | ~ l1_pre_topc(sK1)
% 2.15/1.02      | sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(k1_tex_2(sK1,sK2)) ),
% 2.15/1.02      inference(unflattening,[status(thm)],[c_836]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_839,plain,
% 2.15/1.02      ( ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
% 2.15/1.02      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 2.15/1.02      | sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(k1_tex_2(sK1,sK2)) ),
% 2.15/1.02      inference(global_propositional_subsumption,
% 2.15/1.02                [status(thm)],
% 2.15/1.02                [c_837,c_23]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_840,plain,
% 2.15/1.02      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 2.15/1.02      | ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
% 2.15/1.02      | sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(k1_tex_2(sK1,sK2)) ),
% 2.15/1.02      inference(renaming,[status(thm)],[c_839]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_3963,plain,
% 2.15/1.02      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 2.15/1.02      | ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
% 2.15/1.02      | sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(k1_tex_2(sK1,sK2)) ),
% 2.15/1.02      inference(subtyping,[status(esa)],[c_840]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_4507,plain,
% 2.15/1.02      ( sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(k1_tex_2(sK1,sK2))
% 2.15/1.02      | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top
% 2.15/1.02      | m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top ),
% 2.15/1.02      inference(predicate_to_equality,[status(thm)],[c_3963]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_4055,plain,
% 2.15/1.02      ( sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(k1_tex_2(sK1,sK2))
% 2.15/1.02      | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top
% 2.15/1.02      | m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top ),
% 2.15/1.02      inference(predicate_to_equality,[status(thm)],[c_3963]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_5196,plain,
% 2.15/1.02      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top
% 2.15/1.02      | sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(k1_tex_2(sK1,sK2)) ),
% 2.15/1.02      inference(global_propositional_subsumption,
% 2.15/1.02                [status(thm)],
% 2.15/1.02                [c_4507,c_25,c_26,c_27,c_4025,c_4055]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_5197,plain,
% 2.15/1.02      ( sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(k1_tex_2(sK1,sK2))
% 2.15/1.02      | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top ),
% 2.15/1.02      inference(renaming,[status(thm)],[c_5196]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_6536,plain,
% 2.15/1.02      ( u1_struct_0(k1_tex_2(sK1,sK2)) = u1_struct_0(sK1)
% 2.15/1.02      | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top ),
% 2.15/1.02      inference(demodulation,[status(thm)],[c_6531,c_5197]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_3975,negated_conjecture,
% 2.15/1.02      ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 2.15/1.02      inference(subtyping,[status(esa)],[c_22]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_4495,plain,
% 2.15/1.02      ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
% 2.15/1.02      inference(predicate_to_equality,[status(thm)],[c_3975]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_5349,plain,
% 2.15/1.02      ( m1_subset_1(X0_45,u1_struct_0(X0_46)) != iProver_top
% 2.15/1.02      | v7_struct_0(X0_46) = iProver_top
% 2.15/1.02      | v1_zfmisc_1(u1_struct_0(X0_46)) != iProver_top
% 2.15/1.02      | v2_struct_0(X0_46) = iProver_top
% 2.15/1.02      | v1_xboole_0(u1_struct_0(X0_46)) = iProver_top
% 2.15/1.02      | l1_pre_topc(X0_46) != iProver_top ),
% 2.15/1.02      inference(superposition,[status(thm)],[c_4498,c_4494]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_4045,plain,
% 2.15/1.02      ( v2_struct_0(X0_46) = iProver_top
% 2.15/1.02      | v1_xboole_0(u1_struct_0(X0_46)) != iProver_top
% 2.15/1.02      | l1_pre_topc(X0_46) != iProver_top ),
% 2.15/1.02      inference(predicate_to_equality,[status(thm)],[c_3969]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_6152,plain,
% 2.15/1.02      ( v2_struct_0(X0_46) = iProver_top
% 2.15/1.02      | v1_zfmisc_1(u1_struct_0(X0_46)) != iProver_top
% 2.15/1.02      | v7_struct_0(X0_46) = iProver_top
% 2.15/1.02      | m1_subset_1(X0_45,u1_struct_0(X0_46)) != iProver_top
% 2.15/1.02      | l1_pre_topc(X0_46) != iProver_top ),
% 2.15/1.02      inference(global_propositional_subsumption,
% 2.15/1.02                [status(thm)],
% 2.15/1.02                [c_5349,c_4045]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_6153,plain,
% 2.15/1.02      ( m1_subset_1(X0_45,u1_struct_0(X0_46)) != iProver_top
% 2.15/1.02      | v7_struct_0(X0_46) = iProver_top
% 2.15/1.02      | v1_zfmisc_1(u1_struct_0(X0_46)) != iProver_top
% 2.15/1.02      | v2_struct_0(X0_46) = iProver_top
% 2.15/1.02      | l1_pre_topc(X0_46) != iProver_top ),
% 2.15/1.02      inference(renaming,[status(thm)],[c_6152]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_6163,plain,
% 2.15/1.02      ( v7_struct_0(sK1) = iProver_top
% 2.15/1.02      | v1_zfmisc_1(u1_struct_0(sK1)) != iProver_top
% 2.15/1.02      | v2_struct_0(sK1) = iProver_top
% 2.15/1.02      | l1_pre_topc(sK1) != iProver_top ),
% 2.15/1.02      inference(superposition,[status(thm)],[c_4495,c_6153]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_6166,plain,
% 2.15/1.02      ( v7_struct_0(sK1) = iProver_top
% 2.15/1.02      | v1_zfmisc_1(u1_struct_0(sK1)) != iProver_top ),
% 2.15/1.02      inference(global_propositional_subsumption,
% 2.15/1.02                [status(thm)],
% 2.15/1.02                [c_6163,c_25,c_26]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_4038,plain,
% 2.15/1.02      ( v1_subset_1(k6_domain_1(u1_struct_0(X0_46),X0_45),u1_struct_0(X0_46)) = iProver_top
% 2.15/1.02      | m1_subset_1(X0_45,u1_struct_0(X0_46)) != iProver_top
% 2.15/1.02      | v7_struct_0(X0_46) = iProver_top
% 2.15/1.02      | v2_struct_0(X0_46) = iProver_top
% 2.15/1.02      | l1_pre_topc(X0_46) != iProver_top ),
% 2.15/1.02      inference(predicate_to_equality,[status(thm)],[c_3972]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(c_4040,plain,
% 2.15/1.02      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) = iProver_top
% 2.15/1.02      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 2.15/1.02      | v7_struct_0(sK1) = iProver_top
% 2.15/1.02      | v2_struct_0(sK1) = iProver_top
% 2.15/1.02      | l1_pre_topc(sK1) != iProver_top ),
% 2.15/1.02      inference(instantiation,[status(thm)],[c_4038]) ).
% 2.15/1.02  
% 2.15/1.02  cnf(contradiction,plain,
% 2.15/1.02      ( $false ),
% 2.15/1.02      inference(minisat,
% 2.15/1.02                [status(thm)],
% 2.15/1.02                [c_6536,c_6438,c_6166,c_6005,c_5946,c_4878,c_4823,c_4040,
% 2.15/1.02                 c_4031,c_4028,c_4016,c_4003,c_27,c_26,c_25]) ).
% 2.15/1.02  
% 2.15/1.02  
% 2.15/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 2.15/1.02  
% 2.15/1.02  ------                               Statistics
% 2.15/1.02  
% 2.15/1.02  ------ General
% 2.15/1.02  
% 2.15/1.02  abstr_ref_over_cycles:                  0
% 2.15/1.02  abstr_ref_under_cycles:                 0
% 2.15/1.02  gc_basic_clause_elim:                   0
% 2.15/1.02  forced_gc_time:                         0
% 2.15/1.02  parsing_time:                           0.032
% 2.15/1.02  unif_index_cands_time:                  0.
% 2.15/1.02  unif_index_add_time:                    0.
% 2.15/1.02  orderings_time:                         0.
% 2.15/1.02  out_proof_time:                         0.011
% 2.15/1.02  total_time:                             0.203
% 2.15/1.02  num_of_symbols:                         50
% 2.15/1.02  num_of_terms:                           3593
% 2.15/1.02  
% 2.15/1.02  ------ Preprocessing
% 2.15/1.02  
% 2.15/1.02  num_of_splits:                          0
% 2.15/1.02  num_of_split_atoms:                     0
% 2.15/1.02  num_of_reused_defs:                     0
% 2.15/1.02  num_eq_ax_congr_red:                    4
% 2.15/1.02  num_of_sem_filtered_clauses:            1
% 2.15/1.02  num_of_subtypes:                        2
% 2.15/1.02  monotx_restored_types:                  1
% 2.15/1.02  sat_num_of_epr_types:                   0
% 2.15/1.02  sat_num_of_non_cyclic_types:            0
% 2.15/1.02  sat_guarded_non_collapsed_types:        0
% 2.15/1.03  num_pure_diseq_elim:                    0
% 2.15/1.03  simp_replaced_by:                       0
% 2.15/1.03  res_preprocessed:                       125
% 2.15/1.03  prep_upred:                             0
% 2.15/1.03  prep_unflattend:                        146
% 2.15/1.03  smt_new_axioms:                         0
% 2.15/1.03  pred_elim_cands:                        8
% 2.15/1.03  pred_elim:                              2
% 2.15/1.03  pred_elim_cl:                           0
% 2.15/1.03  pred_elim_cycles:                       15
% 2.15/1.03  merged_defs:                            2
% 2.15/1.03  merged_defs_ncl:                        0
% 2.15/1.03  bin_hyper_res:                          2
% 2.15/1.03  prep_cycles:                            4
% 2.15/1.03  pred_elim_time:                         0.068
% 2.15/1.03  splitting_time:                         0.
% 2.15/1.03  sem_filter_time:                        0.
% 2.15/1.03  monotx_time:                            0.
% 2.15/1.03  subtype_inf_time:                       0.001
% 2.15/1.03  
% 2.15/1.03  ------ Problem properties
% 2.15/1.03  
% 2.15/1.03  clauses:                                23
% 2.15/1.03  conjectures:                            3
% 2.15/1.03  epr:                                    3
% 2.15/1.03  horn:                                   15
% 2.15/1.03  ground:                                 7
% 2.15/1.03  unary:                                  3
% 2.15/1.03  binary:                                 1
% 2.15/1.03  lits:                                   76
% 2.15/1.03  lits_eq:                                3
% 2.15/1.03  fd_pure:                                0
% 2.15/1.03  fd_pseudo:                              0
% 2.15/1.03  fd_cond:                                0
% 2.15/1.03  fd_pseudo_cond:                         1
% 2.15/1.03  ac_symbols:                             0
% 2.15/1.03  
% 2.15/1.03  ------ Propositional Solver
% 2.15/1.03  
% 2.15/1.03  prop_solver_calls:                      29
% 2.15/1.03  prop_fast_solver_calls:                 1748
% 2.15/1.03  smt_solver_calls:                       0
% 2.15/1.03  smt_fast_solver_calls:                  0
% 2.15/1.03  prop_num_of_clauses:                    1206
% 2.15/1.03  prop_preprocess_simplified:             5583
% 2.15/1.03  prop_fo_subsumed:                       57
% 2.15/1.03  prop_solver_time:                       0.
% 2.15/1.03  smt_solver_time:                        0.
% 2.15/1.03  smt_fast_solver_time:                   0.
% 2.15/1.03  prop_fast_solver_time:                  0.
% 2.15/1.03  prop_unsat_core_time:                   0.
% 2.15/1.03  
% 2.15/1.03  ------ QBF
% 2.15/1.03  
% 2.15/1.03  qbf_q_res:                              0
% 2.15/1.03  qbf_num_tautologies:                    0
% 2.15/1.03  qbf_prep_cycles:                        0
% 2.15/1.03  
% 2.15/1.03  ------ BMC1
% 2.15/1.03  
% 2.15/1.03  bmc1_current_bound:                     -1
% 2.15/1.03  bmc1_last_solved_bound:                 -1
% 2.15/1.03  bmc1_unsat_core_size:                   -1
% 2.15/1.03  bmc1_unsat_core_parents_size:           -1
% 2.15/1.03  bmc1_merge_next_fun:                    0
% 2.15/1.03  bmc1_unsat_core_clauses_time:           0.
% 2.15/1.03  
% 2.15/1.03  ------ Instantiation
% 2.15/1.03  
% 2.15/1.03  inst_num_of_clauses:                    343
% 2.15/1.03  inst_num_in_passive:                    134
% 2.15/1.03  inst_num_in_active:                     197
% 2.15/1.03  inst_num_in_unprocessed:                12
% 2.15/1.03  inst_num_of_loops:                      210
% 2.15/1.03  inst_num_of_learning_restarts:          0
% 2.15/1.03  inst_num_moves_active_passive:          9
% 2.15/1.03  inst_lit_activity:                      0
% 2.15/1.03  inst_lit_activity_moves:                0
% 2.15/1.03  inst_num_tautologies:                   0
% 2.15/1.03  inst_num_prop_implied:                  0
% 2.15/1.03  inst_num_existing_simplified:           0
% 2.15/1.03  inst_num_eq_res_simplified:             0
% 2.15/1.03  inst_num_child_elim:                    0
% 2.15/1.03  inst_num_of_dismatching_blockings:      102
% 2.15/1.03  inst_num_of_non_proper_insts:           377
% 2.15/1.03  inst_num_of_duplicates:                 0
% 2.15/1.03  inst_inst_num_from_inst_to_res:         0
% 2.15/1.03  inst_dismatching_checking_time:         0.
% 2.15/1.03  
% 2.15/1.03  ------ Resolution
% 2.15/1.03  
% 2.15/1.03  res_num_of_clauses:                     0
% 2.15/1.03  res_num_in_passive:                     0
% 2.15/1.03  res_num_in_active:                      0
% 2.15/1.03  res_num_of_loops:                       129
% 2.15/1.03  res_forward_subset_subsumed:            42
% 2.15/1.03  res_backward_subset_subsumed:           0
% 2.15/1.03  res_forward_subsumed:                   0
% 2.15/1.03  res_backward_subsumed:                  0
% 2.15/1.03  res_forward_subsumption_resolution:     2
% 2.15/1.03  res_backward_subsumption_resolution:    0
% 2.15/1.03  res_clause_to_clause_subsumption:       285
% 2.15/1.03  res_orphan_elimination:                 0
% 2.15/1.03  res_tautology_del:                      59
% 2.15/1.03  res_num_eq_res_simplified:              0
% 2.15/1.03  res_num_sel_changes:                    0
% 2.15/1.03  res_moves_from_active_to_pass:          0
% 2.15/1.03  
% 2.15/1.03  ------ Superposition
% 2.15/1.03  
% 2.15/1.03  sup_time_total:                         0.
% 2.15/1.03  sup_time_generating:                    0.
% 2.15/1.03  sup_time_sim_full:                      0.
% 2.15/1.03  sup_time_sim_immed:                     0.
% 2.15/1.03  
% 2.15/1.03  sup_num_of_clauses:                     42
% 2.15/1.03  sup_num_in_active:                      33
% 2.15/1.03  sup_num_in_passive:                     9
% 2.15/1.03  sup_num_of_loops:                       41
% 2.15/1.03  sup_fw_superposition:                   18
% 2.15/1.03  sup_bw_superposition:                   14
% 2.15/1.03  sup_immediate_simplified:               5
% 2.15/1.03  sup_given_eliminated:                   0
% 2.15/1.03  comparisons_done:                       0
% 2.15/1.03  comparisons_avoided:                    0
% 2.15/1.03  
% 2.15/1.03  ------ Simplifications
% 2.15/1.03  
% 2.15/1.03  
% 2.15/1.03  sim_fw_subset_subsumed:                 2
% 2.15/1.03  sim_bw_subset_subsumed:                 6
% 2.15/1.03  sim_fw_subsumed:                        3
% 2.15/1.03  sim_bw_subsumed:                        0
% 2.15/1.03  sim_fw_subsumption_res:                 0
% 2.15/1.03  sim_bw_subsumption_res:                 0
% 2.15/1.03  sim_tautology_del:                      2
% 2.15/1.03  sim_eq_tautology_del:                   1
% 2.15/1.03  sim_eq_res_simp:                        0
% 2.15/1.03  sim_fw_demodulated:                     0
% 2.15/1.03  sim_bw_demodulated:                     4
% 2.15/1.03  sim_light_normalised:                   0
% 2.15/1.03  sim_joinable_taut:                      0
% 2.15/1.03  sim_joinable_simp:                      0
% 2.15/1.03  sim_ac_normalised:                      0
% 2.15/1.03  sim_smt_subsumption:                    0
% 2.15/1.03  
%------------------------------------------------------------------------------
