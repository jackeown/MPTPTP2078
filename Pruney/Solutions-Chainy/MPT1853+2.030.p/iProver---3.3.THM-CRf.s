%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:25:40 EST 2020

% Result     : Theorem 2.35s
% Output     : CNFRefutation 2.35s
% Verified   : 
% Statistics : Number of formulae       :  221 (1377 expanded)
%              Number of clauses        :  145 ( 492 expanded)
%              Number of leaves         :   22 ( 251 expanded)
%              Depth                    :   19
%              Number of atoms          :  810 (6398 expanded)
%              Number of equality atoms :  235 ( 667 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f82,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f11,axiom,(
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

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f54,plain,(
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
    inference(nnf_transformation,[],[f38])).

fof(f55,plain,(
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
    inference(rectify,[],[f54])).

fof(f56,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v1_subset_1(X2,u1_struct_0(X0))
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_subset_1(sK1(X0,X1),u1_struct_0(X0))
        & u1_struct_0(X1) = sK1(X0,X1)
        & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ( ~ v1_subset_1(sK1(X0,X1),u1_struct_0(X0))
                & u1_struct_0(X1) = sK1(X0,X1)
                & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v1_subset_1(X3,u1_struct_0(X0))
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f55,f56])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | u1_struct_0(X1) = sK1(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f17,axiom,(
    ! [X0] :
      ( ( ~ v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f87,plain,(
    ! [X0,X1] :
      ( v1_subset_1(k6_domain_1(X0,X1),X0)
      | ~ m1_subset_1(X1,X0)
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_zfmisc_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f64,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f18,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( v1_tex_2(k1_tex_2(X0,X1),X0)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f50,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f51,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f50])).

fof(f59,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f51])).

fof(f60,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f59])).

fof(f62,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),sK3),u1_struct_0(X0))
          | ~ v1_tex_2(k1_tex_2(X0,sK3),X0) )
        & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),sK3),u1_struct_0(X0))
          | v1_tex_2(k1_tex_2(X0,sK3),X0) )
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,
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
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),X1),u1_struct_0(sK2))
            | ~ v1_tex_2(k1_tex_2(sK2,X1),sK2) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),X1),u1_struct_0(sK2))
            | v1_tex_2(k1_tex_2(sK2,X1),sK2) )
          & m1_subset_1(X1,u1_struct_0(sK2)) )
      & l1_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,
    ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
      | ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2) )
    & ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
      | v1_tex_2(k1_tex_2(sK2,sK3),sK2) )
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l1_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f60,f62,f61])).

fof(f92,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2) ),
    inference(cnf_transformation,[],[f63])).

fof(f90,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f63])).

fof(f91,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | v1_tex_2(k1_tex_2(sK2,sK3),sK2) ),
    inference(cnf_transformation,[],[f63])).

fof(f16,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_zfmisc_1(X0)
          | ~ v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_zfmisc_1(X0)
          | ~ v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(X0)
      | ~ v1_subset_1(k6_domain_1(X0,X1),X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f88,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f63])).

fof(f89,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f63])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f67,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f75,plain,(
    ! [X0,X3,X1] :
      ( v1_subset_1(X3,u1_struct_0(X0))
      | u1_struct_0(X1) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f93,plain,(
    ! [X0,X1] :
      ( v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f75])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f73,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( v1_subset_1(X1,X0)
           => v1_xboole_0(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f74,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ~ v1_subset_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f68,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f76,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f78,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | ~ v1_subset_1(sK1(X0,X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f31,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f70,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f84,plain,(
    ! [X0,X1] :
      ( v7_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_17,plain,
    ( m1_pre_topc(k1_tex_2(X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_6341,plain,
    ( m1_pre_topc(k1_tex_2(X0_47,X0_46),X0_47)
    | ~ m1_subset_1(X0_46,u1_struct_0(X0_47))
    | v2_struct_0(X0_47)
    | ~ l1_pre_topc(X0_47) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_7046,plain,
    ( m1_pre_topc(k1_tex_2(X0_47,X0_46),X0_47) = iProver_top
    | m1_subset_1(X0_46,u1_struct_0(X0_47)) != iProver_top
    | v2_struct_0(X0_47) = iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6341])).

cnf(c_12,plain,
    ( v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK1(X1,X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_6345,plain,
    ( v1_tex_2(X0_47,X1_47)
    | ~ m1_pre_topc(X0_47,X1_47)
    | ~ l1_pre_topc(X1_47)
    | sK1(X1_47,X0_47) = u1_struct_0(X0_47) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_7042,plain,
    ( sK1(X0_47,X1_47) = u1_struct_0(X1_47)
    | v1_tex_2(X1_47,X0_47) = iProver_top
    | m1_pre_topc(X1_47,X0_47) != iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6345])).

cnf(c_7984,plain,
    ( sK1(X0_47,k1_tex_2(X0_47,X0_46)) = u1_struct_0(k1_tex_2(X0_47,X0_46))
    | v1_tex_2(k1_tex_2(X0_47,X0_46),X0_47) = iProver_top
    | m1_subset_1(X0_46,u1_struct_0(X0_47)) != iProver_top
    | v2_struct_0(X0_47) = iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(superposition,[status(thm)],[c_7046,c_7042])).

cnf(c_23,plain,
    ( v1_subset_1(k6_domain_1(X0,X1),X0)
    | ~ m1_subset_1(X1,X0)
    | v1_xboole_0(X0)
    | v1_zfmisc_1(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_0,plain,
    ( ~ v1_xboole_0(X0)
    | v1_zfmisc_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_160,plain,
    ( ~ m1_subset_1(X1,X0)
    | v1_subset_1(k6_domain_1(X0,X1),X0)
    | v1_zfmisc_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_23,c_0])).

cnf(c_161,plain,
    ( v1_subset_1(k6_domain_1(X0,X1),X0)
    | ~ m1_subset_1(X1,X0)
    | v1_zfmisc_1(X0) ),
    inference(renaming,[status(thm)],[c_160])).

cnf(c_6332,plain,
    ( v1_subset_1(k6_domain_1(X0_46,X1_46),X0_46)
    | ~ m1_subset_1(X1_46,X0_46)
    | v1_zfmisc_1(X0_46) ),
    inference(subtyping,[status(esa)],[c_161])).

cnf(c_7055,plain,
    ( v1_subset_1(k6_domain_1(X0_46,X1_46),X0_46) = iProver_top
    | m1_subset_1(X1_46,X0_46) != iProver_top
    | v1_zfmisc_1(X0_46) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6332])).

cnf(c_24,negated_conjecture,
    ( ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_6337,negated_conjecture,
    ( ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_7050,plain,
    ( v1_tex_2(k1_tex_2(sK2,sK3),sK2) != iProver_top
    | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6337])).

cnf(c_8826,plain,
    ( v1_tex_2(k1_tex_2(sK2,sK3),sK2) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7055,c_7050])).

cnf(c_2445,plain,
    ( ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) ),
    inference(prop_impl,[status(thm)],[c_24])).

cnf(c_3560,plain,
    ( ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2)
    | ~ m1_subset_1(X0,X1)
    | v1_zfmisc_1(X1)
    | k6_domain_1(u1_struct_0(sK2),sK3) != k6_domain_1(X1,X0)
    | u1_struct_0(sK2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_161,c_2445])).

cnf(c_3561,plain,
    ( ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | v1_zfmisc_1(u1_struct_0(sK2))
    | k6_domain_1(u1_struct_0(sK2),sK3) != k6_domain_1(u1_struct_0(sK2),X0) ),
    inference(unflattening,[status(thm)],[c_3560])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_2191,plain,
    ( v1_subset_1(k6_domain_1(X0,X1),X0)
    | v1_zfmisc_1(X0)
    | u1_struct_0(sK2) != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_161,c_26])).

cnf(c_2192,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | v1_zfmisc_1(u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_2191])).

cnf(c_3563,plain,
    ( v1_zfmisc_1(u1_struct_0(sK2))
    | ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3561,c_24,c_2192])).

cnf(c_3564,plain,
    ( ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2)
    | v1_zfmisc_1(u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_3563])).

cnf(c_3565,plain,
    ( v1_tex_2(k1_tex_2(sK2,sK3),sK2) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3564])).

cnf(c_25,negated_conjecture,
    ( v1_tex_2(k1_tex_2(sK2,sK3),sK2)
    | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_6336,negated_conjecture,
    ( v1_tex_2(k1_tex_2(sK2,sK3),sK2)
    | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_7051,plain,
    ( v1_tex_2(k1_tex_2(sK2,sK3),sK2) = iProver_top
    | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6336])).

cnf(c_22,plain,
    ( ~ v1_subset_1(k6_domain_1(X0,X1),X0)
    | ~ m1_subset_1(X1,X0)
    | v1_xboole_0(X0)
    | ~ v1_zfmisc_1(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_6338,plain,
    ( ~ v1_subset_1(k6_domain_1(X0_46,X1_46),X0_46)
    | ~ m1_subset_1(X1_46,X0_46)
    | v1_xboole_0(X0_46)
    | ~ v1_zfmisc_1(X0_46) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_7049,plain,
    ( v1_subset_1(k6_domain_1(X0_46,X1_46),X0_46) != iProver_top
    | m1_subset_1(X1_46,X0_46) != iProver_top
    | v1_xboole_0(X0_46) = iProver_top
    | v1_zfmisc_1(X0_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6338])).

cnf(c_8083,plain,
    ( v1_tex_2(k1_tex_2(sK2,sK3),sK2) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top
    | v1_zfmisc_1(u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7051,c_7049])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_29,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_27,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_30,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_31,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_5,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_84,plain,
    ( v2_struct_0(X0) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_86,plain,
    ( v2_struct_0(sK2) = iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_84])).

cnf(c_3,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_88,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_90,plain,
    ( l1_pre_topc(sK2) != iProver_top
    | l1_struct_0(sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_88])).

cnf(c_14,plain,
    ( ~ v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_9,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_175,plain,
    ( v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X1)
    | ~ v1_tex_2(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14,c_9])).

cnf(c_176,plain,
    ( ~ v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_175])).

cnf(c_234,plain,
    ( v1_tex_2(k1_tex_2(sK2,sK3),sK2)
    | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) ),
    inference(prop_impl,[status(thm)],[c_25])).

cnf(c_730,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | k1_tex_2(sK2,sK3) != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_176,c_234])).

cnf(c_731,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
    | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | v1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_730])).

cnf(c_732,plain,
    ( m1_pre_topc(k1_tex_2(sK2,sK3),sK2) != iProver_top
    | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) = iProver_top
    | v1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),u1_struct_0(sK2)) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_731])).

cnf(c_2201,plain,
    ( ~ v1_subset_1(k6_domain_1(X0,X1),X0)
    | v1_xboole_0(X0)
    | ~ v1_zfmisc_1(X0)
    | u1_struct_0(sK2) != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_26])).

cnf(c_2202,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2))
    | ~ v1_zfmisc_1(u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_2201])).

cnf(c_2203,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top
    | v1_zfmisc_1(u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2202])).

cnf(c_6405,plain,
    ( m1_pre_topc(k1_tex_2(X0_47,X0_46),X0_47) = iProver_top
    | m1_subset_1(X0_46,u1_struct_0(X0_47)) != iProver_top
    | v2_struct_0(X0_47) = iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6341])).

cnf(c_6407,plain,
    ( m1_pre_topc(k1_tex_2(sK2,sK3),sK2) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6405])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k1_tex_2(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_6340,plain,
    ( ~ m1_subset_1(X0_46,u1_struct_0(X0_47))
    | v2_struct_0(X0_47)
    | ~ v2_struct_0(k1_tex_2(X0_47,X0_46))
    | ~ l1_pre_topc(X0_47) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_6408,plain,
    ( m1_subset_1(X0_46,u1_struct_0(X0_47)) != iProver_top
    | v2_struct_0(X0_47) = iProver_top
    | v2_struct_0(k1_tex_2(X0_47,X0_46)) != iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6340])).

cnf(c_6410,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | v2_struct_0(k1_tex_2(sK2,sK3)) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6408])).

cnf(c_6347,plain,
    ( ~ m1_pre_topc(X0_47,X1_47)
    | m1_subset_1(u1_struct_0(X0_47),k1_zfmisc_1(u1_struct_0(X1_47)))
    | ~ l1_pre_topc(X1_47) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_7303,plain,
    ( ~ m1_pre_topc(k1_tex_2(X0_47,X0_46),X0_47)
    | m1_subset_1(u1_struct_0(k1_tex_2(X0_47,X0_46)),k1_zfmisc_1(u1_struct_0(X0_47)))
    | ~ l1_pre_topc(X0_47) ),
    inference(instantiation,[status(thm)],[c_6347])).

cnf(c_7304,plain,
    ( m1_pre_topc(k1_tex_2(X0_47,X0_46),X0_47) != iProver_top
    | m1_subset_1(u1_struct_0(k1_tex_2(X0_47,X0_46)),k1_zfmisc_1(u1_struct_0(X0_47))) = iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7303])).

cnf(c_7306,plain,
    ( m1_pre_topc(k1_tex_2(sK2,sK3),sK2) != iProver_top
    | m1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7304])).

cnf(c_10,plain,
    ( ~ v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | ~ v1_zfmisc_1(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2,plain,
    ( ~ v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_185,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_subset_1(X0,X1)
    | v1_xboole_0(X0)
    | ~ v1_zfmisc_1(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10,c_2])).

cnf(c_186,plain,
    ( ~ v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | v1_xboole_0(X0)
    | ~ v1_zfmisc_1(X1) ),
    inference(renaming,[status(thm)],[c_185])).

cnf(c_6330,plain,
    ( ~ v1_subset_1(X0_46,X1_46)
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(X1_46))
    | v1_xboole_0(X0_46)
    | ~ v1_zfmisc_1(X1_46) ),
    inference(subtyping,[status(esa)],[c_186])).

cnf(c_7402,plain,
    ( ~ v1_subset_1(X0_46,u1_struct_0(sK2))
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(X0_46)
    | ~ v1_zfmisc_1(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_6330])).

cnf(c_7572,plain,
    ( ~ v1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),u1_struct_0(sK2))
    | ~ m1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(u1_struct_0(k1_tex_2(sK2,sK3)))
    | ~ v1_zfmisc_1(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_7402])).

cnf(c_7573,plain,
    ( v1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_xboole_0(u1_struct_0(k1_tex_2(sK2,sK3))) = iProver_top
    | v1_zfmisc_1(u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7572])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_6350,plain,
    ( ~ m1_pre_topc(X0_47,X1_47)
    | ~ l1_pre_topc(X1_47)
    | l1_pre_topc(X0_47) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_7037,plain,
    ( m1_pre_topc(X0_47,X1_47) != iProver_top
    | l1_pre_topc(X1_47) != iProver_top
    | l1_pre_topc(X0_47) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6350])).

cnf(c_7983,plain,
    ( m1_subset_1(X0_46,u1_struct_0(X0_47)) != iProver_top
    | v2_struct_0(X0_47) = iProver_top
    | l1_pre_topc(X0_47) != iProver_top
    | l1_pre_topc(k1_tex_2(X0_47,X0_46)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7046,c_7037])).

cnf(c_8004,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(k1_tex_2(sK2,sK3)) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7983])).

cnf(c_426,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_3,c_5])).

cnf(c_6329,plain,
    ( v2_struct_0(X0_47)
    | ~ l1_pre_topc(X0_47)
    | ~ v1_xboole_0(u1_struct_0(X0_47)) ),
    inference(subtyping,[status(esa)],[c_426])).

cnf(c_8054,plain,
    ( v2_struct_0(k1_tex_2(sK2,sK3))
    | ~ l1_pre_topc(k1_tex_2(sK2,sK3))
    | ~ v1_xboole_0(u1_struct_0(k1_tex_2(sK2,sK3))) ),
    inference(instantiation,[status(thm)],[c_6329])).

cnf(c_8055,plain,
    ( v2_struct_0(k1_tex_2(sK2,sK3)) = iProver_top
    | l1_pre_topc(k1_tex_2(sK2,sK3)) != iProver_top
    | v1_xboole_0(u1_struct_0(k1_tex_2(sK2,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8054])).

cnf(c_8086,plain,
    ( v1_zfmisc_1(u1_struct_0(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8083,c_29,c_30,c_31,c_86,c_90,c_732,c_2203,c_6407,c_6410,c_7306,c_7573,c_8004,c_8055])).

cnf(c_8886,plain,
    ( v1_tex_2(k1_tex_2(sK2,sK3),sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8826,c_29,c_30,c_31,c_86,c_90,c_732,c_2203,c_3565,c_6407,c_6410,c_7306,c_7573,c_8004,c_8055])).

cnf(c_9077,plain,
    ( sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(k1_tex_2(sK2,sK3))
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_7984,c_8886])).

cnf(c_7318,plain,
    ( v1_tex_2(k1_tex_2(X0_47,X0_46),X0_47)
    | ~ m1_pre_topc(k1_tex_2(X0_47,X0_46),X0_47)
    | ~ l1_pre_topc(X0_47)
    | sK1(X0_47,k1_tex_2(X0_47,X0_46)) = u1_struct_0(k1_tex_2(X0_47,X0_46)) ),
    inference(instantiation,[status(thm)],[c_6345])).

cnf(c_7319,plain,
    ( sK1(X0_47,k1_tex_2(X0_47,X0_46)) = u1_struct_0(k1_tex_2(X0_47,X0_46))
    | v1_tex_2(k1_tex_2(X0_47,X0_46),X0_47) = iProver_top
    | m1_pre_topc(k1_tex_2(X0_47,X0_46),X0_47) != iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7318])).

cnf(c_7321,plain,
    ( sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(k1_tex_2(sK2,sK3))
    | v1_tex_2(k1_tex_2(sK2,sK3),sK2) = iProver_top
    | m1_pre_topc(k1_tex_2(sK2,sK3),sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7319])).

cnf(c_9433,plain,
    ( sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(k1_tex_2(sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9077,c_29,c_30,c_31,c_86,c_90,c_732,c_2203,c_3565,c_6407,c_6410,c_7306,c_7321,c_7573,c_8004,c_8055])).

cnf(c_13,plain,
    ( v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | m1_subset_1(sK1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_6344,plain,
    ( v1_tex_2(X0_47,X1_47)
    | ~ m1_pre_topc(X0_47,X1_47)
    | m1_subset_1(sK1(X1_47,X0_47),k1_zfmisc_1(u1_struct_0(X1_47)))
    | ~ l1_pre_topc(X1_47) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_7043,plain,
    ( v1_tex_2(X0_47,X1_47) = iProver_top
    | m1_pre_topc(X0_47,X1_47) != iProver_top
    | m1_subset_1(sK1(X1_47,X0_47),k1_zfmisc_1(u1_struct_0(X1_47))) = iProver_top
    | l1_pre_topc(X1_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6344])).

cnf(c_15,plain,
    ( v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_6343,plain,
    ( v1_subset_1(X0_46,X1_46)
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(X1_46))
    | X0_46 = X1_46 ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_7044,plain,
    ( X0_46 = X1_46
    | v1_subset_1(X0_46,X1_46) = iProver_top
    | m1_subset_1(X0_46,k1_zfmisc_1(X1_46)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6343])).

cnf(c_8399,plain,
    ( sK1(X0_47,X1_47) = u1_struct_0(X0_47)
    | v1_tex_2(X1_47,X0_47) = iProver_top
    | m1_pre_topc(X1_47,X0_47) != iProver_top
    | v1_subset_1(sK1(X0_47,X1_47),u1_struct_0(X0_47)) = iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(superposition,[status(thm)],[c_7043,c_7044])).

cnf(c_11,plain,
    ( v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v1_subset_1(sK1(X1,X0),u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_6346,plain,
    ( v1_tex_2(X0_47,X1_47)
    | ~ m1_pre_topc(X0_47,X1_47)
    | ~ v1_subset_1(sK1(X1_47,X0_47),u1_struct_0(X1_47))
    | ~ l1_pre_topc(X1_47) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_7041,plain,
    ( v1_tex_2(X0_47,X1_47) = iProver_top
    | m1_pre_topc(X0_47,X1_47) != iProver_top
    | v1_subset_1(sK1(X1_47,X0_47),u1_struct_0(X1_47)) != iProver_top
    | l1_pre_topc(X1_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6346])).

cnf(c_9209,plain,
    ( sK1(X0_47,X1_47) = u1_struct_0(X0_47)
    | v1_tex_2(X1_47,X0_47) = iProver_top
    | m1_pre_topc(X1_47,X0_47) != iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8399,c_7041])).

cnf(c_9211,plain,
    ( sK1(X0_47,k1_tex_2(X0_47,X0_46)) = u1_struct_0(X0_47)
    | v1_tex_2(k1_tex_2(X0_47,X0_46),X0_47) = iProver_top
    | m1_subset_1(X0_46,u1_struct_0(X0_47)) != iProver_top
    | v2_struct_0(X0_47) = iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(superposition,[status(thm)],[c_7046,c_9209])).

cnf(c_9288,plain,
    ( sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(sK2)
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_9211,c_8886])).

cnf(c_232,plain,
    ( ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) ),
    inference(prop_impl,[status(thm)],[c_24])).

cnf(c_679,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | m1_subset_1(sK1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tex_2(sK2,sK3) != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_232])).

cnf(c_680,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | m1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_679])).

cnf(c_681,plain,
    ( m1_pre_topc(k1_tex_2(sK2,sK3),sK2) != iProver_top
    | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_680])).

cnf(c_713,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | ~ v1_subset_1(sK1(X1,X0),u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | k1_tex_2(sK2,sK3) != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_232])).

cnf(c_714,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | ~ v1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_713])).

cnf(c_715,plain,
    ( m1_pre_topc(k1_tex_2(sK2,sK3),sK2) != iProver_top
    | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) != iProver_top
    | v1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),u1_struct_0(sK2)) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_714])).

cnf(c_2193,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) = iProver_top
    | v1_zfmisc_1(u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2192])).

cnf(c_7383,plain,
    ( v1_subset_1(X0_46,u1_struct_0(sK2))
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK2)))
    | X0_46 = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_6343])).

cnf(c_7933,plain,
    ( v1_subset_1(sK1(sK2,k1_tex_2(sK2,X0_46)),u1_struct_0(sK2))
    | ~ m1_subset_1(sK1(sK2,k1_tex_2(sK2,X0_46)),k1_zfmisc_1(u1_struct_0(sK2)))
    | sK1(sK2,k1_tex_2(sK2,X0_46)) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_7383])).

cnf(c_7936,plain,
    ( sK1(sK2,k1_tex_2(sK2,X0_46)) = u1_struct_0(sK2)
    | v1_subset_1(sK1(sK2,k1_tex_2(sK2,X0_46)),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(sK1(sK2,k1_tex_2(sK2,X0_46)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7933])).

cnf(c_7938,plain,
    ( sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(sK2)
    | v1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7936])).

cnf(c_9316,plain,
    ( sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9288,c_29,c_30,c_31,c_86,c_90,c_681,c_715,c_732,c_2193,c_2203,c_6407,c_6410,c_7306,c_7573,c_7938,c_8004,c_8055])).

cnf(c_9435,plain,
    ( u1_struct_0(k1_tex_2(sK2,sK3)) = u1_struct_0(sK2) ),
    inference(light_normalisation,[status(thm)],[c_9433,c_9316])).

cnf(c_6357,plain,
    ( X0_46 != X1_46
    | X2_46 != X1_46
    | X2_46 = X0_46 ),
    theory(equality)).

cnf(c_7439,plain,
    ( X0_46 != X1_46
    | X0_46 = u1_struct_0(k1_tex_2(X0_47,X2_46))
    | u1_struct_0(k1_tex_2(X0_47,X2_46)) != X1_46 ),
    inference(instantiation,[status(thm)],[c_6357])).

cnf(c_7765,plain,
    ( X0_46 != u1_struct_0(X0_47)
    | X0_46 = u1_struct_0(k1_tex_2(X1_47,X1_46))
    | u1_struct_0(k1_tex_2(X1_47,X1_46)) != u1_struct_0(X0_47) ),
    inference(instantiation,[status(thm)],[c_7439])).

cnf(c_8731,plain,
    ( u1_struct_0(X0_47) != u1_struct_0(X1_47)
    | u1_struct_0(X0_47) = u1_struct_0(k1_tex_2(X2_47,X0_46))
    | u1_struct_0(k1_tex_2(X2_47,X0_46)) != u1_struct_0(X1_47) ),
    inference(instantiation,[status(thm)],[c_7765])).

cnf(c_8732,plain,
    ( u1_struct_0(k1_tex_2(sK2,sK3)) != u1_struct_0(sK2)
    | u1_struct_0(sK2) = u1_struct_0(k1_tex_2(sK2,sK3))
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_8731])).

cnf(c_6358,plain,
    ( ~ v1_zfmisc_1(X0_46)
    | v1_zfmisc_1(X1_46)
    | X1_46 != X0_46 ),
    theory(equality)).

cnf(c_7356,plain,
    ( v1_zfmisc_1(X0_46)
    | ~ v1_zfmisc_1(u1_struct_0(k1_tex_2(X0_47,X1_46)))
    | X0_46 != u1_struct_0(k1_tex_2(X0_47,X1_46)) ),
    inference(instantiation,[status(thm)],[c_6358])).

cnf(c_7426,plain,
    ( v1_zfmisc_1(u1_struct_0(X0_47))
    | ~ v1_zfmisc_1(u1_struct_0(k1_tex_2(X1_47,X0_46)))
    | u1_struct_0(X0_47) != u1_struct_0(k1_tex_2(X1_47,X0_46)) ),
    inference(instantiation,[status(thm)],[c_7356])).

cnf(c_7428,plain,
    ( u1_struct_0(X0_47) != u1_struct_0(k1_tex_2(X1_47,X0_46))
    | v1_zfmisc_1(u1_struct_0(X0_47)) = iProver_top
    | v1_zfmisc_1(u1_struct_0(k1_tex_2(X1_47,X0_46))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7426])).

cnf(c_7430,plain,
    ( u1_struct_0(sK2) != u1_struct_0(k1_tex_2(sK2,sK3))
    | v1_zfmisc_1(u1_struct_0(k1_tex_2(sK2,sK3))) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_7428])).

cnf(c_6,plain,
    ( ~ v7_struct_0(X0)
    | ~ l1_struct_0(X0)
    | v1_zfmisc_1(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_412,plain,
    ( ~ v7_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | v1_zfmisc_1(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_3,c_6])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v7_struct_0(k1_tex_2(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2594,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | v1_zfmisc_1(u1_struct_0(X2))
    | k1_tex_2(X1,X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_412,c_19])).

cnf(c_2595,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(k1_tex_2(X1,X0))
    | v1_zfmisc_1(u1_struct_0(k1_tex_2(X1,X0))) ),
    inference(unflattening,[status(thm)],[c_2594])).

cnf(c_448,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | v1_zfmisc_1(u1_struct_0(X2))
    | k1_tex_2(X1,X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_412,c_19])).

cnf(c_449,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(k1_tex_2(X1,X0))
    | v1_zfmisc_1(u1_struct_0(k1_tex_2(X1,X0))) ),
    inference(unflattening,[status(thm)],[c_448])).

cnf(c_1046,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X3)
    | X1 != X2
    | k1_tex_2(X1,X0) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_17])).

cnf(c_1047,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k1_tex_2(X1,X0)) ),
    inference(unflattening,[status(thm)],[c_1046])).

cnf(c_2597,plain,
    ( ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | v1_zfmisc_1(u1_struct_0(k1_tex_2(X1,X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2595,c_449,c_1047])).

cnf(c_2598,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_zfmisc_1(u1_struct_0(k1_tex_2(X1,X0))) ),
    inference(renaming,[status(thm)],[c_2597])).

cnf(c_6328,plain,
    ( ~ m1_subset_1(X0_46,u1_struct_0(X0_47))
    | v2_struct_0(X0_47)
    | ~ l1_pre_topc(X0_47)
    | v1_zfmisc_1(u1_struct_0(k1_tex_2(X0_47,X0_46))) ),
    inference(subtyping,[status(esa)],[c_2598])).

cnf(c_6430,plain,
    ( m1_subset_1(X0_46,u1_struct_0(X0_47)) != iProver_top
    | v2_struct_0(X0_47) = iProver_top
    | l1_pre_topc(X0_47) != iProver_top
    | v1_zfmisc_1(u1_struct_0(k1_tex_2(X0_47,X0_46))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6328])).

cnf(c_6432,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_zfmisc_1(u1_struct_0(k1_tex_2(sK2,sK3))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_6430])).

cnf(c_6356,plain,
    ( X0_47 = X0_47 ),
    theory(equality)).

cnf(c_6384,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_6356])).

cnf(c_6365,plain,
    ( X0_47 != X1_47
    | u1_struct_0(X0_47) = u1_struct_0(X1_47) ),
    theory(equality)).

cnf(c_6377,plain,
    ( sK2 != sK2
    | u1_struct_0(sK2) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_6365])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9435,c_8732,c_8086,c_7430,c_6432,c_6384,c_6377,c_31,c_30,c_29])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n016.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 11:05:19 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.35/0.97  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.35/0.97  
% 2.35/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.35/0.97  
% 2.35/0.97  ------  iProver source info
% 2.35/0.97  
% 2.35/0.97  git: date: 2020-06-30 10:37:57 +0100
% 2.35/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.35/0.97  git: non_committed_changes: false
% 2.35/0.97  git: last_make_outside_of_git: false
% 2.35/0.97  
% 2.35/0.97  ------ 
% 2.35/0.97  
% 2.35/0.97  ------ Input Options
% 2.35/0.97  
% 2.35/0.97  --out_options                           all
% 2.35/0.97  --tptp_safe_out                         true
% 2.35/0.97  --problem_path                          ""
% 2.35/0.97  --include_path                          ""
% 2.35/0.97  --clausifier                            res/vclausify_rel
% 2.35/0.97  --clausifier_options                    --mode clausify
% 2.35/0.97  --stdin                                 false
% 2.35/0.97  --stats_out                             all
% 2.35/0.97  
% 2.35/0.97  ------ General Options
% 2.35/0.97  
% 2.35/0.97  --fof                                   false
% 2.35/0.97  --time_out_real                         305.
% 2.35/0.97  --time_out_virtual                      -1.
% 2.35/0.97  --symbol_type_check                     false
% 2.35/0.97  --clausify_out                          false
% 2.35/0.97  --sig_cnt_out                           false
% 2.35/0.97  --trig_cnt_out                          false
% 2.35/0.97  --trig_cnt_out_tolerance                1.
% 2.35/0.97  --trig_cnt_out_sk_spl                   false
% 2.35/0.97  --abstr_cl_out                          false
% 2.35/0.97  
% 2.35/0.97  ------ Global Options
% 2.35/0.97  
% 2.35/0.97  --schedule                              default
% 2.35/0.97  --add_important_lit                     false
% 2.35/0.97  --prop_solver_per_cl                    1000
% 2.35/0.97  --min_unsat_core                        false
% 2.35/0.97  --soft_assumptions                      false
% 2.35/0.97  --soft_lemma_size                       3
% 2.35/0.97  --prop_impl_unit_size                   0
% 2.35/0.97  --prop_impl_unit                        []
% 2.35/0.97  --share_sel_clauses                     true
% 2.35/0.97  --reset_solvers                         false
% 2.35/0.97  --bc_imp_inh                            [conj_cone]
% 2.35/0.97  --conj_cone_tolerance                   3.
% 2.35/0.97  --extra_neg_conj                        none
% 2.35/0.97  --large_theory_mode                     true
% 2.35/0.97  --prolific_symb_bound                   200
% 2.35/0.97  --lt_threshold                          2000
% 2.35/0.97  --clause_weak_htbl                      true
% 2.35/0.97  --gc_record_bc_elim                     false
% 2.35/0.97  
% 2.35/0.97  ------ Preprocessing Options
% 2.35/0.97  
% 2.35/0.97  --preprocessing_flag                    true
% 2.35/0.97  --time_out_prep_mult                    0.1
% 2.35/0.97  --splitting_mode                        input
% 2.35/0.97  --splitting_grd                         true
% 2.35/0.97  --splitting_cvd                         false
% 2.35/0.97  --splitting_cvd_svl                     false
% 2.35/0.97  --splitting_nvd                         32
% 2.35/0.97  --sub_typing                            true
% 2.35/0.97  --prep_gs_sim                           true
% 2.35/0.97  --prep_unflatten                        true
% 2.35/0.97  --prep_res_sim                          true
% 2.35/0.97  --prep_upred                            true
% 2.35/0.97  --prep_sem_filter                       exhaustive
% 2.35/0.97  --prep_sem_filter_out                   false
% 2.35/0.97  --pred_elim                             true
% 2.35/0.97  --res_sim_input                         true
% 2.35/0.97  --eq_ax_congr_red                       true
% 2.35/0.97  --pure_diseq_elim                       true
% 2.35/0.97  --brand_transform                       false
% 2.35/0.97  --non_eq_to_eq                          false
% 2.35/0.97  --prep_def_merge                        true
% 2.35/0.97  --prep_def_merge_prop_impl              false
% 2.35/0.97  --prep_def_merge_mbd                    true
% 2.35/0.97  --prep_def_merge_tr_red                 false
% 2.35/0.97  --prep_def_merge_tr_cl                  false
% 2.35/0.97  --smt_preprocessing                     true
% 2.35/0.97  --smt_ac_axioms                         fast
% 2.35/0.97  --preprocessed_out                      false
% 2.35/0.97  --preprocessed_stats                    false
% 2.35/0.97  
% 2.35/0.97  ------ Abstraction refinement Options
% 2.35/0.97  
% 2.35/0.97  --abstr_ref                             []
% 2.35/0.97  --abstr_ref_prep                        false
% 2.35/0.97  --abstr_ref_until_sat                   false
% 2.35/0.97  --abstr_ref_sig_restrict                funpre
% 2.35/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.35/0.97  --abstr_ref_under                       []
% 2.35/0.97  
% 2.35/0.97  ------ SAT Options
% 2.35/0.97  
% 2.35/0.97  --sat_mode                              false
% 2.35/0.97  --sat_fm_restart_options                ""
% 2.35/0.97  --sat_gr_def                            false
% 2.35/0.97  --sat_epr_types                         true
% 2.35/0.97  --sat_non_cyclic_types                  false
% 2.35/0.97  --sat_finite_models                     false
% 2.35/0.97  --sat_fm_lemmas                         false
% 2.35/0.97  --sat_fm_prep                           false
% 2.35/0.97  --sat_fm_uc_incr                        true
% 2.35/0.97  --sat_out_model                         small
% 2.35/0.97  --sat_out_clauses                       false
% 2.35/0.97  
% 2.35/0.97  ------ QBF Options
% 2.35/0.97  
% 2.35/0.97  --qbf_mode                              false
% 2.35/0.97  --qbf_elim_univ                         false
% 2.35/0.97  --qbf_dom_inst                          none
% 2.35/0.97  --qbf_dom_pre_inst                      false
% 2.35/0.97  --qbf_sk_in                             false
% 2.35/0.97  --qbf_pred_elim                         true
% 2.35/0.97  --qbf_split                             512
% 2.35/0.97  
% 2.35/0.97  ------ BMC1 Options
% 2.35/0.97  
% 2.35/0.97  --bmc1_incremental                      false
% 2.35/0.97  --bmc1_axioms                           reachable_all
% 2.35/0.97  --bmc1_min_bound                        0
% 2.35/0.97  --bmc1_max_bound                        -1
% 2.35/0.97  --bmc1_max_bound_default                -1
% 2.35/0.97  --bmc1_symbol_reachability              true
% 2.35/0.97  --bmc1_property_lemmas                  false
% 2.35/0.97  --bmc1_k_induction                      false
% 2.35/0.97  --bmc1_non_equiv_states                 false
% 2.35/0.97  --bmc1_deadlock                         false
% 2.35/0.97  --bmc1_ucm                              false
% 2.35/0.97  --bmc1_add_unsat_core                   none
% 2.35/0.97  --bmc1_unsat_core_children              false
% 2.35/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.35/0.97  --bmc1_out_stat                         full
% 2.35/0.97  --bmc1_ground_init                      false
% 2.35/0.97  --bmc1_pre_inst_next_state              false
% 2.35/0.97  --bmc1_pre_inst_state                   false
% 2.35/0.97  --bmc1_pre_inst_reach_state             false
% 2.35/0.97  --bmc1_out_unsat_core                   false
% 2.35/0.97  --bmc1_aig_witness_out                  false
% 2.35/0.97  --bmc1_verbose                          false
% 2.35/0.97  --bmc1_dump_clauses_tptp                false
% 2.35/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.35/0.97  --bmc1_dump_file                        -
% 2.35/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.35/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.35/0.97  --bmc1_ucm_extend_mode                  1
% 2.35/0.97  --bmc1_ucm_init_mode                    2
% 2.35/0.97  --bmc1_ucm_cone_mode                    none
% 2.35/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.35/0.97  --bmc1_ucm_relax_model                  4
% 2.35/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.35/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.35/0.97  --bmc1_ucm_layered_model                none
% 2.35/0.97  --bmc1_ucm_max_lemma_size               10
% 2.35/0.97  
% 2.35/0.97  ------ AIG Options
% 2.35/0.97  
% 2.35/0.97  --aig_mode                              false
% 2.35/0.97  
% 2.35/0.97  ------ Instantiation Options
% 2.35/0.97  
% 2.35/0.97  --instantiation_flag                    true
% 2.35/0.97  --inst_sos_flag                         false
% 2.35/0.97  --inst_sos_phase                        true
% 2.35/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.35/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.35/0.97  --inst_lit_sel_side                     num_symb
% 2.35/0.97  --inst_solver_per_active                1400
% 2.35/0.97  --inst_solver_calls_frac                1.
% 2.35/0.97  --inst_passive_queue_type               priority_queues
% 2.35/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.35/0.97  --inst_passive_queues_freq              [25;2]
% 2.35/0.97  --inst_dismatching                      true
% 2.35/0.97  --inst_eager_unprocessed_to_passive     true
% 2.35/0.97  --inst_prop_sim_given                   true
% 2.35/0.97  --inst_prop_sim_new                     false
% 2.35/0.97  --inst_subs_new                         false
% 2.35/0.98  --inst_eq_res_simp                      false
% 2.35/0.98  --inst_subs_given                       false
% 2.35/0.98  --inst_orphan_elimination               true
% 2.35/0.98  --inst_learning_loop_flag               true
% 2.35/0.98  --inst_learning_start                   3000
% 2.35/0.98  --inst_learning_factor                  2
% 2.35/0.98  --inst_start_prop_sim_after_learn       3
% 2.35/0.98  --inst_sel_renew                        solver
% 2.35/0.98  --inst_lit_activity_flag                true
% 2.35/0.98  --inst_restr_to_given                   false
% 2.35/0.98  --inst_activity_threshold               500
% 2.35/0.98  --inst_out_proof                        true
% 2.35/0.98  
% 2.35/0.98  ------ Resolution Options
% 2.35/0.98  
% 2.35/0.98  --resolution_flag                       true
% 2.35/0.98  --res_lit_sel                           adaptive
% 2.35/0.98  --res_lit_sel_side                      none
% 2.35/0.98  --res_ordering                          kbo
% 2.35/0.98  --res_to_prop_solver                    active
% 2.35/0.98  --res_prop_simpl_new                    false
% 2.35/0.98  --res_prop_simpl_given                  true
% 2.35/0.98  --res_passive_queue_type                priority_queues
% 2.35/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.35/0.98  --res_passive_queues_freq               [15;5]
% 2.35/0.98  --res_forward_subs                      full
% 2.35/0.98  --res_backward_subs                     full
% 2.35/0.98  --res_forward_subs_resolution           true
% 2.35/0.98  --res_backward_subs_resolution          true
% 2.35/0.98  --res_orphan_elimination                true
% 2.35/0.98  --res_time_limit                        2.
% 2.35/0.98  --res_out_proof                         true
% 2.35/0.98  
% 2.35/0.98  ------ Superposition Options
% 2.35/0.98  
% 2.35/0.98  --superposition_flag                    true
% 2.35/0.98  --sup_passive_queue_type                priority_queues
% 2.35/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.35/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.35/0.98  --demod_completeness_check              fast
% 2.35/0.98  --demod_use_ground                      true
% 2.35/0.98  --sup_to_prop_solver                    passive
% 2.35/0.98  --sup_prop_simpl_new                    true
% 2.35/0.98  --sup_prop_simpl_given                  true
% 2.35/0.98  --sup_fun_splitting                     false
% 2.35/0.98  --sup_smt_interval                      50000
% 2.35/0.98  
% 2.35/0.98  ------ Superposition Simplification Setup
% 2.35/0.98  
% 2.35/0.98  --sup_indices_passive                   []
% 2.35/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.35/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.35/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.35/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.35/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.35/0.98  --sup_full_bw                           [BwDemod]
% 2.35/0.98  --sup_immed_triv                        [TrivRules]
% 2.35/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.35/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.35/0.98  --sup_immed_bw_main                     []
% 2.35/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.35/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.35/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.35/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.35/0.98  
% 2.35/0.98  ------ Combination Options
% 2.35/0.98  
% 2.35/0.98  --comb_res_mult                         3
% 2.35/0.98  --comb_sup_mult                         2
% 2.35/0.98  --comb_inst_mult                        10
% 2.35/0.98  
% 2.35/0.98  ------ Debug Options
% 2.35/0.98  
% 2.35/0.98  --dbg_backtrace                         false
% 2.35/0.98  --dbg_dump_prop_clauses                 false
% 2.35/0.98  --dbg_dump_prop_clauses_file            -
% 2.35/0.98  --dbg_out_stat                          false
% 2.35/0.98  ------ Parsing...
% 2.35/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.35/0.98  
% 2.35/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.35/0.98  
% 2.35/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.35/0.98  
% 2.35/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.35/0.98  ------ Proving...
% 2.35/0.98  ------ Problem Properties 
% 2.35/0.98  
% 2.35/0.98  
% 2.35/0.98  clauses                                 26
% 2.35/0.98  conjectures                             5
% 2.35/0.98  EPR                                     4
% 2.35/0.98  Horn                                    18
% 2.35/0.98  unary                                   3
% 2.35/0.98  binary                                  4
% 2.35/0.98  lits                                    78
% 2.35/0.98  lits eq                                 3
% 2.35/0.98  fd_pure                                 0
% 2.35/0.98  fd_pseudo                               0
% 2.35/0.98  fd_cond                                 0
% 2.35/0.98  fd_pseudo_cond                          1
% 2.35/0.98  AC symbols                              0
% 2.35/0.98  
% 2.35/0.98  ------ Schedule dynamic 5 is on 
% 2.35/0.98  
% 2.35/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.35/0.98  
% 2.35/0.98  
% 2.35/0.98  ------ 
% 2.35/0.98  Current options:
% 2.35/0.98  ------ 
% 2.35/0.98  
% 2.35/0.98  ------ Input Options
% 2.35/0.98  
% 2.35/0.98  --out_options                           all
% 2.35/0.98  --tptp_safe_out                         true
% 2.35/0.98  --problem_path                          ""
% 2.35/0.98  --include_path                          ""
% 2.35/0.98  --clausifier                            res/vclausify_rel
% 2.35/0.98  --clausifier_options                    --mode clausify
% 2.35/0.98  --stdin                                 false
% 2.35/0.98  --stats_out                             all
% 2.35/0.98  
% 2.35/0.98  ------ General Options
% 2.35/0.98  
% 2.35/0.98  --fof                                   false
% 2.35/0.98  --time_out_real                         305.
% 2.35/0.98  --time_out_virtual                      -1.
% 2.35/0.98  --symbol_type_check                     false
% 2.35/0.98  --clausify_out                          false
% 2.35/0.98  --sig_cnt_out                           false
% 2.35/0.98  --trig_cnt_out                          false
% 2.35/0.98  --trig_cnt_out_tolerance                1.
% 2.35/0.98  --trig_cnt_out_sk_spl                   false
% 2.35/0.98  --abstr_cl_out                          false
% 2.35/0.98  
% 2.35/0.98  ------ Global Options
% 2.35/0.98  
% 2.35/0.98  --schedule                              default
% 2.35/0.98  --add_important_lit                     false
% 2.35/0.98  --prop_solver_per_cl                    1000
% 2.35/0.98  --min_unsat_core                        false
% 2.35/0.98  --soft_assumptions                      false
% 2.35/0.98  --soft_lemma_size                       3
% 2.35/0.98  --prop_impl_unit_size                   0
% 2.35/0.98  --prop_impl_unit                        []
% 2.35/0.98  --share_sel_clauses                     true
% 2.35/0.98  --reset_solvers                         false
% 2.35/0.98  --bc_imp_inh                            [conj_cone]
% 2.35/0.98  --conj_cone_tolerance                   3.
% 2.35/0.98  --extra_neg_conj                        none
% 2.35/0.98  --large_theory_mode                     true
% 2.35/0.98  --prolific_symb_bound                   200
% 2.35/0.98  --lt_threshold                          2000
% 2.35/0.98  --clause_weak_htbl                      true
% 2.35/0.98  --gc_record_bc_elim                     false
% 2.35/0.98  
% 2.35/0.98  ------ Preprocessing Options
% 2.35/0.98  
% 2.35/0.98  --preprocessing_flag                    true
% 2.35/0.98  --time_out_prep_mult                    0.1
% 2.35/0.98  --splitting_mode                        input
% 2.35/0.98  --splitting_grd                         true
% 2.35/0.98  --splitting_cvd                         false
% 2.35/0.98  --splitting_cvd_svl                     false
% 2.35/0.98  --splitting_nvd                         32
% 2.35/0.98  --sub_typing                            true
% 2.35/0.98  --prep_gs_sim                           true
% 2.35/0.98  --prep_unflatten                        true
% 2.35/0.98  --prep_res_sim                          true
% 2.35/0.98  --prep_upred                            true
% 2.35/0.98  --prep_sem_filter                       exhaustive
% 2.35/0.98  --prep_sem_filter_out                   false
% 2.35/0.98  --pred_elim                             true
% 2.35/0.98  --res_sim_input                         true
% 2.35/0.98  --eq_ax_congr_red                       true
% 2.35/0.98  --pure_diseq_elim                       true
% 2.35/0.98  --brand_transform                       false
% 2.35/0.98  --non_eq_to_eq                          false
% 2.35/0.98  --prep_def_merge                        true
% 2.35/0.98  --prep_def_merge_prop_impl              false
% 2.35/0.98  --prep_def_merge_mbd                    true
% 2.35/0.98  --prep_def_merge_tr_red                 false
% 2.35/0.98  --prep_def_merge_tr_cl                  false
% 2.35/0.98  --smt_preprocessing                     true
% 2.35/0.98  --smt_ac_axioms                         fast
% 2.35/0.98  --preprocessed_out                      false
% 2.35/0.98  --preprocessed_stats                    false
% 2.35/0.98  
% 2.35/0.98  ------ Abstraction refinement Options
% 2.35/0.98  
% 2.35/0.98  --abstr_ref                             []
% 2.35/0.98  --abstr_ref_prep                        false
% 2.35/0.98  --abstr_ref_until_sat                   false
% 2.35/0.98  --abstr_ref_sig_restrict                funpre
% 2.35/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.35/0.98  --abstr_ref_under                       []
% 2.35/0.98  
% 2.35/0.98  ------ SAT Options
% 2.35/0.98  
% 2.35/0.98  --sat_mode                              false
% 2.35/0.98  --sat_fm_restart_options                ""
% 2.35/0.98  --sat_gr_def                            false
% 2.35/0.98  --sat_epr_types                         true
% 2.35/0.98  --sat_non_cyclic_types                  false
% 2.35/0.98  --sat_finite_models                     false
% 2.35/0.98  --sat_fm_lemmas                         false
% 2.35/0.98  --sat_fm_prep                           false
% 2.35/0.98  --sat_fm_uc_incr                        true
% 2.35/0.98  --sat_out_model                         small
% 2.35/0.98  --sat_out_clauses                       false
% 2.35/0.98  
% 2.35/0.98  ------ QBF Options
% 2.35/0.98  
% 2.35/0.98  --qbf_mode                              false
% 2.35/0.98  --qbf_elim_univ                         false
% 2.35/0.98  --qbf_dom_inst                          none
% 2.35/0.98  --qbf_dom_pre_inst                      false
% 2.35/0.98  --qbf_sk_in                             false
% 2.35/0.98  --qbf_pred_elim                         true
% 2.35/0.98  --qbf_split                             512
% 2.35/0.98  
% 2.35/0.98  ------ BMC1 Options
% 2.35/0.98  
% 2.35/0.98  --bmc1_incremental                      false
% 2.35/0.98  --bmc1_axioms                           reachable_all
% 2.35/0.98  --bmc1_min_bound                        0
% 2.35/0.98  --bmc1_max_bound                        -1
% 2.35/0.98  --bmc1_max_bound_default                -1
% 2.35/0.98  --bmc1_symbol_reachability              true
% 2.35/0.98  --bmc1_property_lemmas                  false
% 2.35/0.98  --bmc1_k_induction                      false
% 2.35/0.98  --bmc1_non_equiv_states                 false
% 2.35/0.98  --bmc1_deadlock                         false
% 2.35/0.98  --bmc1_ucm                              false
% 2.35/0.98  --bmc1_add_unsat_core                   none
% 2.35/0.98  --bmc1_unsat_core_children              false
% 2.35/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.35/0.98  --bmc1_out_stat                         full
% 2.35/0.98  --bmc1_ground_init                      false
% 2.35/0.98  --bmc1_pre_inst_next_state              false
% 2.35/0.98  --bmc1_pre_inst_state                   false
% 2.35/0.98  --bmc1_pre_inst_reach_state             false
% 2.35/0.98  --bmc1_out_unsat_core                   false
% 2.35/0.98  --bmc1_aig_witness_out                  false
% 2.35/0.98  --bmc1_verbose                          false
% 2.35/0.98  --bmc1_dump_clauses_tptp                false
% 2.35/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.35/0.98  --bmc1_dump_file                        -
% 2.35/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.35/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.35/0.98  --bmc1_ucm_extend_mode                  1
% 2.35/0.98  --bmc1_ucm_init_mode                    2
% 2.35/0.98  --bmc1_ucm_cone_mode                    none
% 2.35/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.35/0.98  --bmc1_ucm_relax_model                  4
% 2.35/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.35/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.35/0.98  --bmc1_ucm_layered_model                none
% 2.35/0.98  --bmc1_ucm_max_lemma_size               10
% 2.35/0.98  
% 2.35/0.98  ------ AIG Options
% 2.35/0.98  
% 2.35/0.98  --aig_mode                              false
% 2.35/0.98  
% 2.35/0.98  ------ Instantiation Options
% 2.35/0.98  
% 2.35/0.98  --instantiation_flag                    true
% 2.35/0.98  --inst_sos_flag                         false
% 2.35/0.98  --inst_sos_phase                        true
% 2.35/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.35/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.35/0.98  --inst_lit_sel_side                     none
% 2.35/0.98  --inst_solver_per_active                1400
% 2.35/0.98  --inst_solver_calls_frac                1.
% 2.35/0.98  --inst_passive_queue_type               priority_queues
% 2.35/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.35/0.98  --inst_passive_queues_freq              [25;2]
% 2.35/0.98  --inst_dismatching                      true
% 2.35/0.98  --inst_eager_unprocessed_to_passive     true
% 2.35/0.98  --inst_prop_sim_given                   true
% 2.35/0.98  --inst_prop_sim_new                     false
% 2.35/0.98  --inst_subs_new                         false
% 2.35/0.98  --inst_eq_res_simp                      false
% 2.35/0.98  --inst_subs_given                       false
% 2.35/0.98  --inst_orphan_elimination               true
% 2.35/0.98  --inst_learning_loop_flag               true
% 2.35/0.98  --inst_learning_start                   3000
% 2.35/0.98  --inst_learning_factor                  2
% 2.35/0.98  --inst_start_prop_sim_after_learn       3
% 2.35/0.98  --inst_sel_renew                        solver
% 2.35/0.98  --inst_lit_activity_flag                true
% 2.35/0.98  --inst_restr_to_given                   false
% 2.35/0.98  --inst_activity_threshold               500
% 2.35/0.98  --inst_out_proof                        true
% 2.35/0.98  
% 2.35/0.98  ------ Resolution Options
% 2.35/0.98  
% 2.35/0.98  --resolution_flag                       false
% 2.35/0.98  --res_lit_sel                           adaptive
% 2.35/0.98  --res_lit_sel_side                      none
% 2.35/0.98  --res_ordering                          kbo
% 2.35/0.98  --res_to_prop_solver                    active
% 2.35/0.98  --res_prop_simpl_new                    false
% 2.35/0.98  --res_prop_simpl_given                  true
% 2.35/0.98  --res_passive_queue_type                priority_queues
% 2.35/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.35/0.98  --res_passive_queues_freq               [15;5]
% 2.35/0.98  --res_forward_subs                      full
% 2.35/0.98  --res_backward_subs                     full
% 2.35/0.98  --res_forward_subs_resolution           true
% 2.35/0.98  --res_backward_subs_resolution          true
% 2.35/0.98  --res_orphan_elimination                true
% 2.35/0.98  --res_time_limit                        2.
% 2.35/0.98  --res_out_proof                         true
% 2.35/0.98  
% 2.35/0.98  ------ Superposition Options
% 2.35/0.98  
% 2.35/0.98  --superposition_flag                    true
% 2.35/0.98  --sup_passive_queue_type                priority_queues
% 2.35/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.35/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.35/0.98  --demod_completeness_check              fast
% 2.35/0.98  --demod_use_ground                      true
% 2.35/0.98  --sup_to_prop_solver                    passive
% 2.35/0.98  --sup_prop_simpl_new                    true
% 2.35/0.98  --sup_prop_simpl_given                  true
% 2.35/0.98  --sup_fun_splitting                     false
% 2.35/0.98  --sup_smt_interval                      50000
% 2.35/0.98  
% 2.35/0.98  ------ Superposition Simplification Setup
% 2.35/0.98  
% 2.35/0.98  --sup_indices_passive                   []
% 2.35/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.35/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.35/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.35/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.35/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.35/0.98  --sup_full_bw                           [BwDemod]
% 2.35/0.98  --sup_immed_triv                        [TrivRules]
% 2.35/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.35/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.35/0.98  --sup_immed_bw_main                     []
% 2.35/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.35/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.35/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.35/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.35/0.98  
% 2.35/0.98  ------ Combination Options
% 2.35/0.98  
% 2.35/0.98  --comb_res_mult                         3
% 2.35/0.98  --comb_sup_mult                         2
% 2.35/0.98  --comb_inst_mult                        10
% 2.35/0.98  
% 2.35/0.98  ------ Debug Options
% 2.35/0.98  
% 2.35/0.98  --dbg_backtrace                         false
% 2.35/0.98  --dbg_dump_prop_clauses                 false
% 2.35/0.98  --dbg_dump_prop_clauses_file            -
% 2.35/0.98  --dbg_out_stat                          false
% 2.35/0.98  
% 2.35/0.98  
% 2.35/0.98  
% 2.35/0.98  
% 2.35/0.98  ------ Proving...
% 2.35/0.98  
% 2.35/0.98  
% 2.35/0.98  % SZS status Theorem for theBenchmark.p
% 2.35/0.98  
% 2.35/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.35/0.98  
% 2.35/0.98  fof(f13,axiom,(
% 2.35/0.98    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 2.35/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.35/0.98  
% 2.35/0.98  fof(f22,plain,(
% 2.35/0.98    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 2.35/0.98    inference(pure_predicate_removal,[],[f13])).
% 2.35/0.98  
% 2.35/0.98  fof(f40,plain,(
% 2.35/0.98    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.35/0.98    inference(ennf_transformation,[],[f22])).
% 2.35/0.98  
% 2.35/0.98  fof(f41,plain,(
% 2.35/0.98    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.35/0.98    inference(flattening,[],[f40])).
% 2.35/0.98  
% 2.35/0.98  fof(f82,plain,(
% 2.35/0.98    ( ! [X0,X1] : (m1_pre_topc(k1_tex_2(X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.35/0.98    inference(cnf_transformation,[],[f41])).
% 2.35/0.98  
% 2.35/0.98  fof(f11,axiom,(
% 2.35/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v1_subset_1(X2,u1_struct_0(X0)))))))),
% 2.35/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.35/0.98  
% 2.35/0.98  fof(f37,plain,(
% 2.35/0.98    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : ((v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.35/0.98    inference(ennf_transformation,[],[f11])).
% 2.35/0.98  
% 2.35/0.98  fof(f38,plain,(
% 2.35/0.98    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.35/0.98    inference(flattening,[],[f37])).
% 2.35/0.98  
% 2.35/0.98  fof(f54,plain,(
% 2.35/0.98    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.35/0.98    inference(nnf_transformation,[],[f38])).
% 2.35/0.98  
% 2.35/0.98  fof(f55,plain,(
% 2.35/0.98    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.35/0.98    inference(rectify,[],[f54])).
% 2.35/0.98  
% 2.35/0.98  fof(f56,plain,(
% 2.35/0.98    ! [X1,X0] : (? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_subset_1(sK1(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK1(X0,X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.35/0.98    introduced(choice_axiom,[])).
% 2.35/0.98  
% 2.35/0.98  fof(f57,plain,(
% 2.35/0.98    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | (~v1_subset_1(sK1(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK1(X0,X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.35/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f55,f56])).
% 2.35/0.98  
% 2.35/0.98  fof(f77,plain,(
% 2.35/0.98    ( ! [X0,X1] : (v1_tex_2(X1,X0) | u1_struct_0(X1) = sK1(X0,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.35/0.98    inference(cnf_transformation,[],[f57])).
% 2.35/0.98  
% 2.35/0.98  fof(f17,axiom,(
% 2.35/0.98    ! [X0] : ((~v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,X0) => v1_subset_1(k6_domain_1(X0,X1),X0)))),
% 2.35/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.35/0.98  
% 2.35/0.98  fof(f48,plain,(
% 2.35/0.98    ! [X0] : (! [X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | (v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 2.35/0.98    inference(ennf_transformation,[],[f17])).
% 2.35/0.98  
% 2.35/0.98  fof(f49,plain,(
% 2.35/0.98    ! [X0] : (! [X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 2.35/0.98    inference(flattening,[],[f48])).
% 2.35/0.98  
% 2.35/0.98  fof(f87,plain,(
% 2.35/0.98    ( ! [X0,X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0) | v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 2.35/0.98    inference(cnf_transformation,[],[f49])).
% 2.35/0.98  
% 2.35/0.98  fof(f1,axiom,(
% 2.35/0.98    ! [X0] : (v1_xboole_0(X0) => v1_zfmisc_1(X0))),
% 2.35/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.35/0.98  
% 2.35/0.98  fof(f23,plain,(
% 2.35/0.98    ! [X0] : (v1_zfmisc_1(X0) | ~v1_xboole_0(X0))),
% 2.35/0.98    inference(ennf_transformation,[],[f1])).
% 2.35/0.98  
% 2.35/0.98  fof(f64,plain,(
% 2.35/0.98    ( ! [X0] : (v1_zfmisc_1(X0) | ~v1_xboole_0(X0)) )),
% 2.35/0.98    inference(cnf_transformation,[],[f23])).
% 2.35/0.98  
% 2.35/0.98  fof(f18,conjecture,(
% 2.35/0.98    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 2.35/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.35/0.98  
% 2.35/0.98  fof(f19,negated_conjecture,(
% 2.35/0.98    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 2.35/0.98    inference(negated_conjecture,[],[f18])).
% 2.35/0.98  
% 2.35/0.98  fof(f50,plain,(
% 2.35/0.98    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.35/0.98    inference(ennf_transformation,[],[f19])).
% 2.35/0.98  
% 2.35/0.98  fof(f51,plain,(
% 2.35/0.98    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.35/0.98    inference(flattening,[],[f50])).
% 2.35/0.98  
% 2.35/0.98  fof(f59,plain,(
% 2.35/0.98    ? [X0] : (? [X1] : (((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.35/0.98    inference(nnf_transformation,[],[f51])).
% 2.35/0.98  
% 2.35/0.98  fof(f60,plain,(
% 2.35/0.98    ? [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.35/0.98    inference(flattening,[],[f59])).
% 2.35/0.98  
% 2.35/0.98  fof(f62,plain,(
% 2.35/0.98    ( ! [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) => ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),sK3),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,sK3),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),sK3),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,sK3),X0)) & m1_subset_1(sK3,u1_struct_0(X0)))) )),
% 2.35/0.98    introduced(choice_axiom,[])).
% 2.35/0.98  
% 2.35/0.98  fof(f61,plain,(
% 2.35/0.98    ? [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(sK2),X1),u1_struct_0(sK2)) | ~v1_tex_2(k1_tex_2(sK2,X1),sK2)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK2),X1),u1_struct_0(sK2)) | v1_tex_2(k1_tex_2(sK2,X1),sK2)) & m1_subset_1(X1,u1_struct_0(sK2))) & l1_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 2.35/0.98    introduced(choice_axiom,[])).
% 2.35/0.98  
% 2.35/0.98  fof(f63,plain,(
% 2.35/0.98    ((~v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) | ~v1_tex_2(k1_tex_2(sK2,sK3),sK2)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) | v1_tex_2(k1_tex_2(sK2,sK3),sK2)) & m1_subset_1(sK3,u1_struct_0(sK2))) & l1_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 2.35/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f60,f62,f61])).
% 2.35/0.98  
% 2.35/0.98  fof(f92,plain,(
% 2.35/0.98    ~v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) | ~v1_tex_2(k1_tex_2(sK2,sK3),sK2)),
% 2.35/0.98    inference(cnf_transformation,[],[f63])).
% 2.35/0.98  
% 2.35/0.98  fof(f90,plain,(
% 2.35/0.98    m1_subset_1(sK3,u1_struct_0(sK2))),
% 2.35/0.98    inference(cnf_transformation,[],[f63])).
% 2.35/0.98  
% 2.35/0.98  fof(f91,plain,(
% 2.35/0.98    v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) | v1_tex_2(k1_tex_2(sK2,sK3),sK2)),
% 2.35/0.98    inference(cnf_transformation,[],[f63])).
% 2.35/0.98  
% 2.35/0.98  fof(f16,axiom,(
% 2.35/0.98    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 2.35/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.35/0.98  
% 2.35/0.98  fof(f46,plain,(
% 2.35/0.98    ! [X0] : (! [X1] : ((~v1_zfmisc_1(X0) | ~v1_subset_1(k6_domain_1(X0,X1),X0)) | ~m1_subset_1(X1,X0)) | v1_xboole_0(X0))),
% 2.35/0.98    inference(ennf_transformation,[],[f16])).
% 2.35/0.98  
% 2.35/0.98  fof(f47,plain,(
% 2.35/0.98    ! [X0] : (! [X1] : (~v1_zfmisc_1(X0) | ~v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | v1_xboole_0(X0))),
% 2.35/0.98    inference(flattening,[],[f46])).
% 2.35/0.98  
% 2.35/0.98  fof(f86,plain,(
% 2.35/0.98    ( ! [X0,X1] : (~v1_zfmisc_1(X0) | ~v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.35/0.98    inference(cnf_transformation,[],[f47])).
% 2.35/0.98  
% 2.35/0.98  fof(f88,plain,(
% 2.35/0.98    ~v2_struct_0(sK2)),
% 2.35/0.98    inference(cnf_transformation,[],[f63])).
% 2.35/0.98  
% 2.35/0.98  fof(f89,plain,(
% 2.35/0.98    l1_pre_topc(sK2)),
% 2.35/0.98    inference(cnf_transformation,[],[f63])).
% 2.35/0.98  
% 2.35/0.98  fof(f6,axiom,(
% 2.35/0.98    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.35/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.35/0.98  
% 2.35/0.98  fof(f28,plain,(
% 2.35/0.98    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.35/0.98    inference(ennf_transformation,[],[f6])).
% 2.35/0.98  
% 2.35/0.98  fof(f29,plain,(
% 2.35/0.98    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.35/0.98    inference(flattening,[],[f28])).
% 2.35/0.98  
% 2.35/0.98  fof(f69,plain,(
% 2.35/0.98    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.35/0.98    inference(cnf_transformation,[],[f29])).
% 2.35/0.98  
% 2.35/0.98  fof(f4,axiom,(
% 2.35/0.98    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.35/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.35/0.98  
% 2.35/0.98  fof(f26,plain,(
% 2.35/0.98    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.35/0.98    inference(ennf_transformation,[],[f4])).
% 2.35/0.98  
% 2.35/0.98  fof(f67,plain,(
% 2.35/0.98    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.35/0.98    inference(cnf_transformation,[],[f26])).
% 2.35/0.98  
% 2.35/0.98  fof(f75,plain,(
% 2.35/0.98    ( ! [X0,X3,X1] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.35/0.98    inference(cnf_transformation,[],[f57])).
% 2.35/0.98  
% 2.35/0.98  fof(f93,plain,(
% 2.35/0.98    ( ! [X0,X1] : (v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.35/0.98    inference(equality_resolution,[],[f75])).
% 2.35/0.98  
% 2.35/0.98  fof(f9,axiom,(
% 2.35/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.35/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.35/0.98  
% 2.35/0.98  fof(f34,plain,(
% 2.35/0.98    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.35/0.98    inference(ennf_transformation,[],[f9])).
% 2.35/0.98  
% 2.35/0.98  fof(f73,plain,(
% 2.35/0.98    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.35/0.98    inference(cnf_transformation,[],[f34])).
% 2.35/0.98  
% 2.35/0.98  fof(f14,axiom,(
% 2.35/0.98    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 2.35/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.35/0.98  
% 2.35/0.98  fof(f20,plain,(
% 2.35/0.98    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 2.35/0.98    inference(pure_predicate_removal,[],[f14])).
% 2.35/0.98  
% 2.35/0.98  fof(f42,plain,(
% 2.35/0.98    ! [X0,X1] : ((v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.35/0.98    inference(ennf_transformation,[],[f20])).
% 2.35/0.98  
% 2.35/0.98  fof(f43,plain,(
% 2.35/0.98    ! [X0,X1] : ((v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.35/0.98    inference(flattening,[],[f42])).
% 2.35/0.98  
% 2.35/0.98  fof(f83,plain,(
% 2.35/0.98    ( ! [X0,X1] : (~v2_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.35/0.98    inference(cnf_transformation,[],[f43])).
% 2.35/0.98  
% 2.35/0.98  fof(f10,axiom,(
% 2.35/0.98    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) => v1_xboole_0(X1))))),
% 2.35/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.35/0.98  
% 2.35/0.98  fof(f35,plain,(
% 2.35/0.98    ! [X0] : (! [X1] : ((v1_xboole_0(X1) | ~v1_subset_1(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | (~v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 2.35/0.98    inference(ennf_transformation,[],[f10])).
% 2.35/0.98  
% 2.35/0.98  fof(f36,plain,(
% 2.35/0.98    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 2.35/0.98    inference(flattening,[],[f35])).
% 2.35/0.98  
% 2.35/0.98  fof(f74,plain,(
% 2.35/0.98    ( ! [X0,X1] : (v1_xboole_0(X1) | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 2.35/0.98    inference(cnf_transformation,[],[f36])).
% 2.35/0.98  
% 2.35/0.98  fof(f3,axiom,(
% 2.35/0.98    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~v1_subset_1(X1,X0)))),
% 2.35/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.35/0.98  
% 2.35/0.98  fof(f25,plain,(
% 2.35/0.98    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 2.35/0.98    inference(ennf_transformation,[],[f3])).
% 2.35/0.98  
% 2.35/0.98  fof(f66,plain,(
% 2.35/0.98    ( ! [X0,X1] : (~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 2.35/0.98    inference(cnf_transformation,[],[f25])).
% 2.35/0.98  
% 2.35/0.98  fof(f5,axiom,(
% 2.35/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.35/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.35/0.98  
% 2.35/0.98  fof(f27,plain,(
% 2.35/0.98    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.35/0.98    inference(ennf_transformation,[],[f5])).
% 2.35/0.98  
% 2.35/0.98  fof(f68,plain,(
% 2.35/0.98    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.35/0.98    inference(cnf_transformation,[],[f27])).
% 2.35/0.98  
% 2.35/0.98  fof(f76,plain,(
% 2.35/0.98    ( ! [X0,X1] : (v1_tex_2(X1,X0) | m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.35/0.98    inference(cnf_transformation,[],[f57])).
% 2.35/0.98  
% 2.35/0.98  fof(f12,axiom,(
% 2.35/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 2.35/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.35/0.98  
% 2.35/0.98  fof(f39,plain,(
% 2.35/0.98    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.35/0.98    inference(ennf_transformation,[],[f12])).
% 2.35/0.98  
% 2.35/0.98  fof(f58,plain,(
% 2.35/0.98    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.35/0.98    inference(nnf_transformation,[],[f39])).
% 2.35/0.98  
% 2.35/0.98  fof(f80,plain,(
% 2.35/0.98    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.35/0.98    inference(cnf_transformation,[],[f58])).
% 2.35/0.98  
% 2.35/0.98  fof(f78,plain,(
% 2.35/0.98    ( ! [X0,X1] : (v1_tex_2(X1,X0) | ~v1_subset_1(sK1(X0,X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.35/0.98    inference(cnf_transformation,[],[f57])).
% 2.35/0.98  
% 2.35/0.98  fof(f7,axiom,(
% 2.35/0.98    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 2.35/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.35/0.98  
% 2.35/0.98  fof(f30,plain,(
% 2.35/0.98    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 2.35/0.98    inference(ennf_transformation,[],[f7])).
% 2.35/0.98  
% 2.35/0.98  fof(f31,plain,(
% 2.35/0.98    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 2.35/0.98    inference(flattening,[],[f30])).
% 2.35/0.98  
% 2.35/0.98  fof(f70,plain,(
% 2.35/0.98    ( ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0)) )),
% 2.35/0.98    inference(cnf_transformation,[],[f31])).
% 2.35/0.98  
% 2.35/0.98  fof(f84,plain,(
% 2.35/0.98    ( ! [X0,X1] : (v7_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.35/0.98    inference(cnf_transformation,[],[f43])).
% 2.35/0.98  
% 2.35/0.98  cnf(c_17,plain,
% 2.35/0.98      ( m1_pre_topc(k1_tex_2(X0,X1),X0)
% 2.35/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.35/0.98      | v2_struct_0(X0)
% 2.35/0.98      | ~ l1_pre_topc(X0) ),
% 2.35/0.98      inference(cnf_transformation,[],[f82]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_6341,plain,
% 2.35/0.98      ( m1_pre_topc(k1_tex_2(X0_47,X0_46),X0_47)
% 2.35/0.98      | ~ m1_subset_1(X0_46,u1_struct_0(X0_47))
% 2.35/0.98      | v2_struct_0(X0_47)
% 2.35/0.98      | ~ l1_pre_topc(X0_47) ),
% 2.35/0.98      inference(subtyping,[status(esa)],[c_17]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_7046,plain,
% 2.35/0.98      ( m1_pre_topc(k1_tex_2(X0_47,X0_46),X0_47) = iProver_top
% 2.35/0.98      | m1_subset_1(X0_46,u1_struct_0(X0_47)) != iProver_top
% 2.35/0.98      | v2_struct_0(X0_47) = iProver_top
% 2.35/0.98      | l1_pre_topc(X0_47) != iProver_top ),
% 2.35/0.98      inference(predicate_to_equality,[status(thm)],[c_6341]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_12,plain,
% 2.35/0.98      ( v1_tex_2(X0,X1)
% 2.35/0.98      | ~ m1_pre_topc(X0,X1)
% 2.35/0.98      | ~ l1_pre_topc(X1)
% 2.35/0.98      | sK1(X1,X0) = u1_struct_0(X0) ),
% 2.35/0.98      inference(cnf_transformation,[],[f77]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_6345,plain,
% 2.35/0.98      ( v1_tex_2(X0_47,X1_47)
% 2.35/0.98      | ~ m1_pre_topc(X0_47,X1_47)
% 2.35/0.98      | ~ l1_pre_topc(X1_47)
% 2.35/0.98      | sK1(X1_47,X0_47) = u1_struct_0(X0_47) ),
% 2.35/0.98      inference(subtyping,[status(esa)],[c_12]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_7042,plain,
% 2.35/0.98      ( sK1(X0_47,X1_47) = u1_struct_0(X1_47)
% 2.35/0.98      | v1_tex_2(X1_47,X0_47) = iProver_top
% 2.35/0.98      | m1_pre_topc(X1_47,X0_47) != iProver_top
% 2.35/0.98      | l1_pre_topc(X0_47) != iProver_top ),
% 2.35/0.98      inference(predicate_to_equality,[status(thm)],[c_6345]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_7984,plain,
% 2.35/0.98      ( sK1(X0_47,k1_tex_2(X0_47,X0_46)) = u1_struct_0(k1_tex_2(X0_47,X0_46))
% 2.35/0.98      | v1_tex_2(k1_tex_2(X0_47,X0_46),X0_47) = iProver_top
% 2.35/0.98      | m1_subset_1(X0_46,u1_struct_0(X0_47)) != iProver_top
% 2.35/0.98      | v2_struct_0(X0_47) = iProver_top
% 2.35/0.98      | l1_pre_topc(X0_47) != iProver_top ),
% 2.35/0.98      inference(superposition,[status(thm)],[c_7046,c_7042]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_23,plain,
% 2.35/0.98      ( v1_subset_1(k6_domain_1(X0,X1),X0)
% 2.35/0.98      | ~ m1_subset_1(X1,X0)
% 2.35/0.98      | v1_xboole_0(X0)
% 2.35/0.98      | v1_zfmisc_1(X0) ),
% 2.35/0.98      inference(cnf_transformation,[],[f87]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_0,plain,
% 2.35/0.98      ( ~ v1_xboole_0(X0) | v1_zfmisc_1(X0) ),
% 2.35/0.98      inference(cnf_transformation,[],[f64]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_160,plain,
% 2.35/0.98      ( ~ m1_subset_1(X1,X0)
% 2.35/0.98      | v1_subset_1(k6_domain_1(X0,X1),X0)
% 2.35/0.98      | v1_zfmisc_1(X0) ),
% 2.35/0.98      inference(global_propositional_subsumption,
% 2.35/0.98                [status(thm)],
% 2.35/0.98                [c_23,c_0]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_161,plain,
% 2.35/0.98      ( v1_subset_1(k6_domain_1(X0,X1),X0)
% 2.35/0.98      | ~ m1_subset_1(X1,X0)
% 2.35/0.98      | v1_zfmisc_1(X0) ),
% 2.35/0.98      inference(renaming,[status(thm)],[c_160]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_6332,plain,
% 2.35/0.98      ( v1_subset_1(k6_domain_1(X0_46,X1_46),X0_46)
% 2.35/0.98      | ~ m1_subset_1(X1_46,X0_46)
% 2.35/0.98      | v1_zfmisc_1(X0_46) ),
% 2.35/0.98      inference(subtyping,[status(esa)],[c_161]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_7055,plain,
% 2.35/0.98      ( v1_subset_1(k6_domain_1(X0_46,X1_46),X0_46) = iProver_top
% 2.35/0.98      | m1_subset_1(X1_46,X0_46) != iProver_top
% 2.35/0.98      | v1_zfmisc_1(X0_46) = iProver_top ),
% 2.35/0.98      inference(predicate_to_equality,[status(thm)],[c_6332]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_24,negated_conjecture,
% 2.35/0.98      ( ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2)
% 2.35/0.98      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) ),
% 2.35/0.98      inference(cnf_transformation,[],[f92]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_6337,negated_conjecture,
% 2.35/0.98      ( ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2)
% 2.35/0.98      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) ),
% 2.35/0.98      inference(subtyping,[status(esa)],[c_24]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_7050,plain,
% 2.35/0.98      ( v1_tex_2(k1_tex_2(sK2,sK3),sK2) != iProver_top
% 2.35/0.98      | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) != iProver_top ),
% 2.35/0.98      inference(predicate_to_equality,[status(thm)],[c_6337]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_8826,plain,
% 2.35/0.98      ( v1_tex_2(k1_tex_2(sK2,sK3),sK2) != iProver_top
% 2.35/0.98      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 2.35/0.98      | v1_zfmisc_1(u1_struct_0(sK2)) = iProver_top ),
% 2.35/0.98      inference(superposition,[status(thm)],[c_7055,c_7050]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_2445,plain,
% 2.35/0.98      ( ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2)
% 2.35/0.98      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) ),
% 2.35/0.98      inference(prop_impl,[status(thm)],[c_24]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_3560,plain,
% 2.35/0.98      ( ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2)
% 2.35/0.98      | ~ m1_subset_1(X0,X1)
% 2.35/0.98      | v1_zfmisc_1(X1)
% 2.35/0.98      | k6_domain_1(u1_struct_0(sK2),sK3) != k6_domain_1(X1,X0)
% 2.35/0.98      | u1_struct_0(sK2) != X1 ),
% 2.35/0.98      inference(resolution_lifted,[status(thm)],[c_161,c_2445]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_3561,plain,
% 2.35/0.98      ( ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2)
% 2.35/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.35/0.98      | v1_zfmisc_1(u1_struct_0(sK2))
% 2.35/0.98      | k6_domain_1(u1_struct_0(sK2),sK3) != k6_domain_1(u1_struct_0(sK2),X0) ),
% 2.35/0.98      inference(unflattening,[status(thm)],[c_3560]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_26,negated_conjecture,
% 2.35/0.98      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 2.35/0.98      inference(cnf_transformation,[],[f90]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_2191,plain,
% 2.35/0.98      ( v1_subset_1(k6_domain_1(X0,X1),X0)
% 2.35/0.98      | v1_zfmisc_1(X0)
% 2.35/0.98      | u1_struct_0(sK2) != X0
% 2.35/0.98      | sK3 != X1 ),
% 2.35/0.98      inference(resolution_lifted,[status(thm)],[c_161,c_26]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_2192,plain,
% 2.35/0.98      ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 2.35/0.98      | v1_zfmisc_1(u1_struct_0(sK2)) ),
% 2.35/0.98      inference(unflattening,[status(thm)],[c_2191]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_3563,plain,
% 2.35/0.98      ( v1_zfmisc_1(u1_struct_0(sK2))
% 2.35/0.98      | ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2) ),
% 2.35/0.98      inference(global_propositional_subsumption,
% 2.35/0.98                [status(thm)],
% 2.35/0.98                [c_3561,c_24,c_2192]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_3564,plain,
% 2.35/0.98      ( ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2)
% 2.35/0.98      | v1_zfmisc_1(u1_struct_0(sK2)) ),
% 2.35/0.98      inference(renaming,[status(thm)],[c_3563]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_3565,plain,
% 2.35/0.98      ( v1_tex_2(k1_tex_2(sK2,sK3),sK2) != iProver_top
% 2.35/0.98      | v1_zfmisc_1(u1_struct_0(sK2)) = iProver_top ),
% 2.35/0.98      inference(predicate_to_equality,[status(thm)],[c_3564]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_25,negated_conjecture,
% 2.35/0.98      ( v1_tex_2(k1_tex_2(sK2,sK3),sK2)
% 2.35/0.98      | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) ),
% 2.35/0.98      inference(cnf_transformation,[],[f91]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_6336,negated_conjecture,
% 2.35/0.98      ( v1_tex_2(k1_tex_2(sK2,sK3),sK2)
% 2.35/0.98      | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) ),
% 2.35/0.98      inference(subtyping,[status(esa)],[c_25]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_7051,plain,
% 2.35/0.98      ( v1_tex_2(k1_tex_2(sK2,sK3),sK2) = iProver_top
% 2.35/0.98      | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) = iProver_top ),
% 2.35/0.98      inference(predicate_to_equality,[status(thm)],[c_6336]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_22,plain,
% 2.35/0.98      ( ~ v1_subset_1(k6_domain_1(X0,X1),X0)
% 2.35/0.98      | ~ m1_subset_1(X1,X0)
% 2.35/0.98      | v1_xboole_0(X0)
% 2.35/0.98      | ~ v1_zfmisc_1(X0) ),
% 2.35/0.98      inference(cnf_transformation,[],[f86]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_6338,plain,
% 2.35/0.98      ( ~ v1_subset_1(k6_domain_1(X0_46,X1_46),X0_46)
% 2.35/0.98      | ~ m1_subset_1(X1_46,X0_46)
% 2.35/0.98      | v1_xboole_0(X0_46)
% 2.35/0.98      | ~ v1_zfmisc_1(X0_46) ),
% 2.35/0.98      inference(subtyping,[status(esa)],[c_22]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_7049,plain,
% 2.35/0.98      ( v1_subset_1(k6_domain_1(X0_46,X1_46),X0_46) != iProver_top
% 2.35/0.98      | m1_subset_1(X1_46,X0_46) != iProver_top
% 2.35/0.98      | v1_xboole_0(X0_46) = iProver_top
% 2.35/0.98      | v1_zfmisc_1(X0_46) != iProver_top ),
% 2.35/0.98      inference(predicate_to_equality,[status(thm)],[c_6338]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_8083,plain,
% 2.35/0.98      ( v1_tex_2(k1_tex_2(sK2,sK3),sK2) = iProver_top
% 2.35/0.98      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 2.35/0.98      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top
% 2.35/0.98      | v1_zfmisc_1(u1_struct_0(sK2)) != iProver_top ),
% 2.35/0.98      inference(superposition,[status(thm)],[c_7051,c_7049]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_28,negated_conjecture,
% 2.35/0.98      ( ~ v2_struct_0(sK2) ),
% 2.35/0.98      inference(cnf_transformation,[],[f88]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_29,plain,
% 2.35/0.98      ( v2_struct_0(sK2) != iProver_top ),
% 2.35/0.98      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_27,negated_conjecture,
% 2.35/0.98      ( l1_pre_topc(sK2) ),
% 2.35/0.98      inference(cnf_transformation,[],[f89]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_30,plain,
% 2.35/0.98      ( l1_pre_topc(sK2) = iProver_top ),
% 2.35/0.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_31,plain,
% 2.35/0.98      ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
% 2.35/0.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_5,plain,
% 2.35/0.98      ( v2_struct_0(X0)
% 2.35/0.98      | ~ l1_struct_0(X0)
% 2.35/0.98      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.35/0.98      inference(cnf_transformation,[],[f69]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_84,plain,
% 2.35/0.98      ( v2_struct_0(X0) = iProver_top
% 2.35/0.98      | l1_struct_0(X0) != iProver_top
% 2.35/0.98      | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
% 2.35/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_86,plain,
% 2.35/0.98      ( v2_struct_0(sK2) = iProver_top
% 2.35/0.98      | l1_struct_0(sK2) != iProver_top
% 2.35/0.98      | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 2.35/0.98      inference(instantiation,[status(thm)],[c_84]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_3,plain,
% 2.35/0.98      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 2.35/0.98      inference(cnf_transformation,[],[f67]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_88,plain,
% 2.35/0.98      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 2.35/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_90,plain,
% 2.35/0.98      ( l1_pre_topc(sK2) != iProver_top
% 2.35/0.98      | l1_struct_0(sK2) = iProver_top ),
% 2.35/0.98      inference(instantiation,[status(thm)],[c_88]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_14,plain,
% 2.35/0.98      ( ~ v1_tex_2(X0,X1)
% 2.35/0.98      | ~ m1_pre_topc(X0,X1)
% 2.35/0.98      | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
% 2.35/0.98      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.35/0.98      | ~ l1_pre_topc(X1) ),
% 2.35/0.98      inference(cnf_transformation,[],[f93]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_9,plain,
% 2.35/0.98      ( ~ m1_pre_topc(X0,X1)
% 2.35/0.98      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.35/0.98      | ~ l1_pre_topc(X1) ),
% 2.35/0.98      inference(cnf_transformation,[],[f73]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_175,plain,
% 2.35/0.98      ( v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
% 2.35/0.98      | ~ m1_pre_topc(X0,X1)
% 2.35/0.98      | ~ v1_tex_2(X0,X1)
% 2.35/0.98      | ~ l1_pre_topc(X1) ),
% 2.35/0.98      inference(global_propositional_subsumption,
% 2.35/0.98                [status(thm)],
% 2.35/0.98                [c_14,c_9]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_176,plain,
% 2.35/0.98      ( ~ v1_tex_2(X0,X1)
% 2.35/0.98      | ~ m1_pre_topc(X0,X1)
% 2.35/0.98      | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
% 2.35/0.98      | ~ l1_pre_topc(X1) ),
% 2.35/0.98      inference(renaming,[status(thm)],[c_175]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_234,plain,
% 2.35/0.98      ( v1_tex_2(k1_tex_2(sK2,sK3),sK2)
% 2.35/0.98      | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) ),
% 2.35/0.98      inference(prop_impl,[status(thm)],[c_25]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_730,plain,
% 2.35/0.98      ( ~ m1_pre_topc(X0,X1)
% 2.35/0.98      | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 2.35/0.98      | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
% 2.35/0.98      | ~ l1_pre_topc(X1)
% 2.35/0.98      | k1_tex_2(sK2,sK3) != X0
% 2.35/0.98      | sK2 != X1 ),
% 2.35/0.98      inference(resolution_lifted,[status(thm)],[c_176,c_234]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_731,plain,
% 2.35/0.98      ( ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
% 2.35/0.98      | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 2.35/0.98      | v1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),u1_struct_0(sK2))
% 2.35/0.98      | ~ l1_pre_topc(sK2) ),
% 2.35/0.98      inference(unflattening,[status(thm)],[c_730]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_732,plain,
% 2.35/0.98      ( m1_pre_topc(k1_tex_2(sK2,sK3),sK2) != iProver_top
% 2.35/0.98      | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) = iProver_top
% 2.35/0.98      | v1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),u1_struct_0(sK2)) = iProver_top
% 2.35/0.98      | l1_pre_topc(sK2) != iProver_top ),
% 2.35/0.98      inference(predicate_to_equality,[status(thm)],[c_731]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_2201,plain,
% 2.35/0.98      ( ~ v1_subset_1(k6_domain_1(X0,X1),X0)
% 2.35/0.98      | v1_xboole_0(X0)
% 2.35/0.98      | ~ v1_zfmisc_1(X0)
% 2.35/0.98      | u1_struct_0(sK2) != X0
% 2.35/0.98      | sK3 != X1 ),
% 2.35/0.98      inference(resolution_lifted,[status(thm)],[c_22,c_26]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_2202,plain,
% 2.35/0.98      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 2.35/0.98      | v1_xboole_0(u1_struct_0(sK2))
% 2.35/0.98      | ~ v1_zfmisc_1(u1_struct_0(sK2)) ),
% 2.35/0.98      inference(unflattening,[status(thm)],[c_2201]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_2203,plain,
% 2.35/0.98      ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) != iProver_top
% 2.35/0.98      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top
% 2.35/0.98      | v1_zfmisc_1(u1_struct_0(sK2)) != iProver_top ),
% 2.35/0.98      inference(predicate_to_equality,[status(thm)],[c_2202]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_6405,plain,
% 2.35/0.98      ( m1_pre_topc(k1_tex_2(X0_47,X0_46),X0_47) = iProver_top
% 2.35/0.98      | m1_subset_1(X0_46,u1_struct_0(X0_47)) != iProver_top
% 2.35/0.98      | v2_struct_0(X0_47) = iProver_top
% 2.35/0.98      | l1_pre_topc(X0_47) != iProver_top ),
% 2.35/0.98      inference(predicate_to_equality,[status(thm)],[c_6341]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_6407,plain,
% 2.35/0.98      ( m1_pre_topc(k1_tex_2(sK2,sK3),sK2) = iProver_top
% 2.35/0.98      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 2.35/0.98      | v2_struct_0(sK2) = iProver_top
% 2.35/0.98      | l1_pre_topc(sK2) != iProver_top ),
% 2.35/0.98      inference(instantiation,[status(thm)],[c_6405]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_20,plain,
% 2.35/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.35/0.98      | v2_struct_0(X1)
% 2.35/0.98      | ~ v2_struct_0(k1_tex_2(X1,X0))
% 2.35/0.98      | ~ l1_pre_topc(X1) ),
% 2.35/0.98      inference(cnf_transformation,[],[f83]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_6340,plain,
% 2.35/0.98      ( ~ m1_subset_1(X0_46,u1_struct_0(X0_47))
% 2.35/0.98      | v2_struct_0(X0_47)
% 2.35/0.98      | ~ v2_struct_0(k1_tex_2(X0_47,X0_46))
% 2.35/0.98      | ~ l1_pre_topc(X0_47) ),
% 2.35/0.98      inference(subtyping,[status(esa)],[c_20]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_6408,plain,
% 2.35/0.98      ( m1_subset_1(X0_46,u1_struct_0(X0_47)) != iProver_top
% 2.35/0.98      | v2_struct_0(X0_47) = iProver_top
% 2.35/0.98      | v2_struct_0(k1_tex_2(X0_47,X0_46)) != iProver_top
% 2.35/0.98      | l1_pre_topc(X0_47) != iProver_top ),
% 2.35/0.98      inference(predicate_to_equality,[status(thm)],[c_6340]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_6410,plain,
% 2.35/0.98      ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 2.35/0.98      | v2_struct_0(k1_tex_2(sK2,sK3)) != iProver_top
% 2.35/0.98      | v2_struct_0(sK2) = iProver_top
% 2.35/0.98      | l1_pre_topc(sK2) != iProver_top ),
% 2.35/0.98      inference(instantiation,[status(thm)],[c_6408]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_6347,plain,
% 2.35/0.98      ( ~ m1_pre_topc(X0_47,X1_47)
% 2.35/0.98      | m1_subset_1(u1_struct_0(X0_47),k1_zfmisc_1(u1_struct_0(X1_47)))
% 2.35/0.98      | ~ l1_pre_topc(X1_47) ),
% 2.35/0.98      inference(subtyping,[status(esa)],[c_9]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_7303,plain,
% 2.35/0.98      ( ~ m1_pre_topc(k1_tex_2(X0_47,X0_46),X0_47)
% 2.35/0.98      | m1_subset_1(u1_struct_0(k1_tex_2(X0_47,X0_46)),k1_zfmisc_1(u1_struct_0(X0_47)))
% 2.35/0.98      | ~ l1_pre_topc(X0_47) ),
% 2.35/0.98      inference(instantiation,[status(thm)],[c_6347]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_7304,plain,
% 2.35/0.98      ( m1_pre_topc(k1_tex_2(X0_47,X0_46),X0_47) != iProver_top
% 2.35/0.98      | m1_subset_1(u1_struct_0(k1_tex_2(X0_47,X0_46)),k1_zfmisc_1(u1_struct_0(X0_47))) = iProver_top
% 2.35/0.98      | l1_pre_topc(X0_47) != iProver_top ),
% 2.35/0.98      inference(predicate_to_equality,[status(thm)],[c_7303]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_7306,plain,
% 2.35/0.98      ( m1_pre_topc(k1_tex_2(sK2,sK3),sK2) != iProver_top
% 2.35/0.98      | m1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 2.35/0.98      | l1_pre_topc(sK2) != iProver_top ),
% 2.35/0.98      inference(instantiation,[status(thm)],[c_7304]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_10,plain,
% 2.35/0.98      ( ~ v1_subset_1(X0,X1)
% 2.35/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.35/0.98      | v1_xboole_0(X1)
% 2.35/0.98      | v1_xboole_0(X0)
% 2.35/0.98      | ~ v1_zfmisc_1(X1) ),
% 2.35/0.98      inference(cnf_transformation,[],[f74]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_2,plain,
% 2.35/0.98      ( ~ v1_subset_1(X0,X1)
% 2.35/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.35/0.98      | ~ v1_xboole_0(X1) ),
% 2.35/0.98      inference(cnf_transformation,[],[f66]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_185,plain,
% 2.35/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.35/0.98      | ~ v1_subset_1(X0,X1)
% 2.35/0.98      | v1_xboole_0(X0)
% 2.35/0.98      | ~ v1_zfmisc_1(X1) ),
% 2.35/0.98      inference(global_propositional_subsumption,
% 2.35/0.98                [status(thm)],
% 2.35/0.98                [c_10,c_2]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_186,plain,
% 2.35/0.98      ( ~ v1_subset_1(X0,X1)
% 2.35/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.35/0.98      | v1_xboole_0(X0)
% 2.35/0.98      | ~ v1_zfmisc_1(X1) ),
% 2.35/0.98      inference(renaming,[status(thm)],[c_185]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_6330,plain,
% 2.35/0.98      ( ~ v1_subset_1(X0_46,X1_46)
% 2.35/0.98      | ~ m1_subset_1(X0_46,k1_zfmisc_1(X1_46))
% 2.35/0.98      | v1_xboole_0(X0_46)
% 2.35/0.98      | ~ v1_zfmisc_1(X1_46) ),
% 2.35/0.98      inference(subtyping,[status(esa)],[c_186]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_7402,plain,
% 2.35/0.98      ( ~ v1_subset_1(X0_46,u1_struct_0(sK2))
% 2.35/0.98      | ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.35/0.98      | v1_xboole_0(X0_46)
% 2.35/0.98      | ~ v1_zfmisc_1(u1_struct_0(sK2)) ),
% 2.35/0.98      inference(instantiation,[status(thm)],[c_6330]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_7572,plain,
% 2.35/0.98      ( ~ v1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),u1_struct_0(sK2))
% 2.35/0.98      | ~ m1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.35/0.98      | v1_xboole_0(u1_struct_0(k1_tex_2(sK2,sK3)))
% 2.35/0.98      | ~ v1_zfmisc_1(u1_struct_0(sK2)) ),
% 2.35/0.98      inference(instantiation,[status(thm)],[c_7402]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_7573,plain,
% 2.35/0.98      ( v1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),u1_struct_0(sK2)) != iProver_top
% 2.35/0.98      | m1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.35/0.98      | v1_xboole_0(u1_struct_0(k1_tex_2(sK2,sK3))) = iProver_top
% 2.35/0.98      | v1_zfmisc_1(u1_struct_0(sK2)) != iProver_top ),
% 2.35/0.98      inference(predicate_to_equality,[status(thm)],[c_7572]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_4,plain,
% 2.35/0.98      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.35/0.98      inference(cnf_transformation,[],[f68]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_6350,plain,
% 2.35/0.98      ( ~ m1_pre_topc(X0_47,X1_47)
% 2.35/0.98      | ~ l1_pre_topc(X1_47)
% 2.35/0.98      | l1_pre_topc(X0_47) ),
% 2.35/0.98      inference(subtyping,[status(esa)],[c_4]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_7037,plain,
% 2.35/0.98      ( m1_pre_topc(X0_47,X1_47) != iProver_top
% 2.35/0.98      | l1_pre_topc(X1_47) != iProver_top
% 2.35/0.98      | l1_pre_topc(X0_47) = iProver_top ),
% 2.35/0.98      inference(predicate_to_equality,[status(thm)],[c_6350]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_7983,plain,
% 2.35/0.98      ( m1_subset_1(X0_46,u1_struct_0(X0_47)) != iProver_top
% 2.35/0.98      | v2_struct_0(X0_47) = iProver_top
% 2.35/0.98      | l1_pre_topc(X0_47) != iProver_top
% 2.35/0.98      | l1_pre_topc(k1_tex_2(X0_47,X0_46)) = iProver_top ),
% 2.35/0.98      inference(superposition,[status(thm)],[c_7046,c_7037]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_8004,plain,
% 2.35/0.98      ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 2.35/0.98      | v2_struct_0(sK2) = iProver_top
% 2.35/0.98      | l1_pre_topc(k1_tex_2(sK2,sK3)) = iProver_top
% 2.35/0.98      | l1_pre_topc(sK2) != iProver_top ),
% 2.35/0.98      inference(instantiation,[status(thm)],[c_7983]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_426,plain,
% 2.35/0.98      ( v2_struct_0(X0)
% 2.35/0.98      | ~ l1_pre_topc(X0)
% 2.35/0.98      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.35/0.98      inference(resolution,[status(thm)],[c_3,c_5]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_6329,plain,
% 2.35/0.98      ( v2_struct_0(X0_47)
% 2.35/0.98      | ~ l1_pre_topc(X0_47)
% 2.35/0.98      | ~ v1_xboole_0(u1_struct_0(X0_47)) ),
% 2.35/0.98      inference(subtyping,[status(esa)],[c_426]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_8054,plain,
% 2.35/0.98      ( v2_struct_0(k1_tex_2(sK2,sK3))
% 2.35/0.98      | ~ l1_pre_topc(k1_tex_2(sK2,sK3))
% 2.35/0.98      | ~ v1_xboole_0(u1_struct_0(k1_tex_2(sK2,sK3))) ),
% 2.35/0.98      inference(instantiation,[status(thm)],[c_6329]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_8055,plain,
% 2.35/0.98      ( v2_struct_0(k1_tex_2(sK2,sK3)) = iProver_top
% 2.35/0.98      | l1_pre_topc(k1_tex_2(sK2,sK3)) != iProver_top
% 2.35/0.98      | v1_xboole_0(u1_struct_0(k1_tex_2(sK2,sK3))) != iProver_top ),
% 2.35/0.98      inference(predicate_to_equality,[status(thm)],[c_8054]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_8086,plain,
% 2.35/0.98      ( v1_zfmisc_1(u1_struct_0(sK2)) != iProver_top ),
% 2.35/0.98      inference(global_propositional_subsumption,
% 2.35/0.98                [status(thm)],
% 2.35/0.98                [c_8083,c_29,c_30,c_31,c_86,c_90,c_732,c_2203,c_6407,
% 2.35/0.98                 c_6410,c_7306,c_7573,c_8004,c_8055]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_8886,plain,
% 2.35/0.98      ( v1_tex_2(k1_tex_2(sK2,sK3),sK2) != iProver_top ),
% 2.35/0.98      inference(global_propositional_subsumption,
% 2.35/0.98                [status(thm)],
% 2.35/0.98                [c_8826,c_29,c_30,c_31,c_86,c_90,c_732,c_2203,c_3565,
% 2.35/0.98                 c_6407,c_6410,c_7306,c_7573,c_8004,c_8055]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_9077,plain,
% 2.35/0.98      ( sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(k1_tex_2(sK2,sK3))
% 2.35/0.98      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 2.35/0.98      | v2_struct_0(sK2) = iProver_top
% 2.35/0.98      | l1_pre_topc(sK2) != iProver_top ),
% 2.35/0.98      inference(superposition,[status(thm)],[c_7984,c_8886]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_7318,plain,
% 2.35/0.98      ( v1_tex_2(k1_tex_2(X0_47,X0_46),X0_47)
% 2.35/0.98      | ~ m1_pre_topc(k1_tex_2(X0_47,X0_46),X0_47)
% 2.35/0.98      | ~ l1_pre_topc(X0_47)
% 2.35/0.98      | sK1(X0_47,k1_tex_2(X0_47,X0_46)) = u1_struct_0(k1_tex_2(X0_47,X0_46)) ),
% 2.35/0.98      inference(instantiation,[status(thm)],[c_6345]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_7319,plain,
% 2.35/0.98      ( sK1(X0_47,k1_tex_2(X0_47,X0_46)) = u1_struct_0(k1_tex_2(X0_47,X0_46))
% 2.35/0.98      | v1_tex_2(k1_tex_2(X0_47,X0_46),X0_47) = iProver_top
% 2.35/0.98      | m1_pre_topc(k1_tex_2(X0_47,X0_46),X0_47) != iProver_top
% 2.35/0.98      | l1_pre_topc(X0_47) != iProver_top ),
% 2.35/0.98      inference(predicate_to_equality,[status(thm)],[c_7318]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_7321,plain,
% 2.35/0.98      ( sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(k1_tex_2(sK2,sK3))
% 2.35/0.98      | v1_tex_2(k1_tex_2(sK2,sK3),sK2) = iProver_top
% 2.35/0.98      | m1_pre_topc(k1_tex_2(sK2,sK3),sK2) != iProver_top
% 2.35/0.98      | l1_pre_topc(sK2) != iProver_top ),
% 2.35/0.98      inference(instantiation,[status(thm)],[c_7319]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_9433,plain,
% 2.35/0.98      ( sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(k1_tex_2(sK2,sK3)) ),
% 2.35/0.98      inference(global_propositional_subsumption,
% 2.35/0.98                [status(thm)],
% 2.35/0.98                [c_9077,c_29,c_30,c_31,c_86,c_90,c_732,c_2203,c_3565,
% 2.35/0.98                 c_6407,c_6410,c_7306,c_7321,c_7573,c_8004,c_8055]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_13,plain,
% 2.35/0.98      ( v1_tex_2(X0,X1)
% 2.35/0.98      | ~ m1_pre_topc(X0,X1)
% 2.35/0.98      | m1_subset_1(sK1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.35/0.98      | ~ l1_pre_topc(X1) ),
% 2.35/0.98      inference(cnf_transformation,[],[f76]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_6344,plain,
% 2.35/0.98      ( v1_tex_2(X0_47,X1_47)
% 2.35/0.98      | ~ m1_pre_topc(X0_47,X1_47)
% 2.35/0.98      | m1_subset_1(sK1(X1_47,X0_47),k1_zfmisc_1(u1_struct_0(X1_47)))
% 2.35/0.98      | ~ l1_pre_topc(X1_47) ),
% 2.35/0.98      inference(subtyping,[status(esa)],[c_13]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_7043,plain,
% 2.35/0.98      ( v1_tex_2(X0_47,X1_47) = iProver_top
% 2.35/0.98      | m1_pre_topc(X0_47,X1_47) != iProver_top
% 2.35/0.98      | m1_subset_1(sK1(X1_47,X0_47),k1_zfmisc_1(u1_struct_0(X1_47))) = iProver_top
% 2.35/0.98      | l1_pre_topc(X1_47) != iProver_top ),
% 2.35/0.98      inference(predicate_to_equality,[status(thm)],[c_6344]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_15,plain,
% 2.35/0.98      ( v1_subset_1(X0,X1)
% 2.35/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.35/0.98      | X0 = X1 ),
% 2.35/0.98      inference(cnf_transformation,[],[f80]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_6343,plain,
% 2.35/0.98      ( v1_subset_1(X0_46,X1_46)
% 2.35/0.98      | ~ m1_subset_1(X0_46,k1_zfmisc_1(X1_46))
% 2.35/0.98      | X0_46 = X1_46 ),
% 2.35/0.98      inference(subtyping,[status(esa)],[c_15]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_7044,plain,
% 2.35/0.98      ( X0_46 = X1_46
% 2.35/0.98      | v1_subset_1(X0_46,X1_46) = iProver_top
% 2.35/0.98      | m1_subset_1(X0_46,k1_zfmisc_1(X1_46)) != iProver_top ),
% 2.35/0.98      inference(predicate_to_equality,[status(thm)],[c_6343]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_8399,plain,
% 2.35/0.98      ( sK1(X0_47,X1_47) = u1_struct_0(X0_47)
% 2.35/0.98      | v1_tex_2(X1_47,X0_47) = iProver_top
% 2.35/0.98      | m1_pre_topc(X1_47,X0_47) != iProver_top
% 2.35/0.98      | v1_subset_1(sK1(X0_47,X1_47),u1_struct_0(X0_47)) = iProver_top
% 2.35/0.98      | l1_pre_topc(X0_47) != iProver_top ),
% 2.35/0.98      inference(superposition,[status(thm)],[c_7043,c_7044]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_11,plain,
% 2.35/0.98      ( v1_tex_2(X0,X1)
% 2.35/0.98      | ~ m1_pre_topc(X0,X1)
% 2.35/0.98      | ~ v1_subset_1(sK1(X1,X0),u1_struct_0(X1))
% 2.35/0.98      | ~ l1_pre_topc(X1) ),
% 2.35/0.98      inference(cnf_transformation,[],[f78]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_6346,plain,
% 2.35/0.98      ( v1_tex_2(X0_47,X1_47)
% 2.35/0.98      | ~ m1_pre_topc(X0_47,X1_47)
% 2.35/0.98      | ~ v1_subset_1(sK1(X1_47,X0_47),u1_struct_0(X1_47))
% 2.35/0.98      | ~ l1_pre_topc(X1_47) ),
% 2.35/0.98      inference(subtyping,[status(esa)],[c_11]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_7041,plain,
% 2.35/0.98      ( v1_tex_2(X0_47,X1_47) = iProver_top
% 2.35/0.98      | m1_pre_topc(X0_47,X1_47) != iProver_top
% 2.35/0.98      | v1_subset_1(sK1(X1_47,X0_47),u1_struct_0(X1_47)) != iProver_top
% 2.35/0.98      | l1_pre_topc(X1_47) != iProver_top ),
% 2.35/0.98      inference(predicate_to_equality,[status(thm)],[c_6346]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_9209,plain,
% 2.35/0.98      ( sK1(X0_47,X1_47) = u1_struct_0(X0_47)
% 2.35/0.98      | v1_tex_2(X1_47,X0_47) = iProver_top
% 2.35/0.98      | m1_pre_topc(X1_47,X0_47) != iProver_top
% 2.35/0.98      | l1_pre_topc(X0_47) != iProver_top ),
% 2.35/0.98      inference(forward_subsumption_resolution,
% 2.35/0.98                [status(thm)],
% 2.35/0.98                [c_8399,c_7041]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_9211,plain,
% 2.35/0.98      ( sK1(X0_47,k1_tex_2(X0_47,X0_46)) = u1_struct_0(X0_47)
% 2.35/0.98      | v1_tex_2(k1_tex_2(X0_47,X0_46),X0_47) = iProver_top
% 2.35/0.98      | m1_subset_1(X0_46,u1_struct_0(X0_47)) != iProver_top
% 2.35/0.98      | v2_struct_0(X0_47) = iProver_top
% 2.35/0.98      | l1_pre_topc(X0_47) != iProver_top ),
% 2.35/0.98      inference(superposition,[status(thm)],[c_7046,c_9209]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_9288,plain,
% 2.35/0.98      ( sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(sK2)
% 2.35/0.98      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 2.35/0.98      | v2_struct_0(sK2) = iProver_top
% 2.35/0.98      | l1_pre_topc(sK2) != iProver_top ),
% 2.35/0.98      inference(superposition,[status(thm)],[c_9211,c_8886]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_232,plain,
% 2.35/0.98      ( ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2)
% 2.35/0.98      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) ),
% 2.35/0.98      inference(prop_impl,[status(thm)],[c_24]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_679,plain,
% 2.35/0.98      ( ~ m1_pre_topc(X0,X1)
% 2.35/0.98      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 2.35/0.98      | m1_subset_1(sK1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.35/0.98      | ~ l1_pre_topc(X1)
% 2.35/0.98      | k1_tex_2(sK2,sK3) != X0
% 2.35/0.98      | sK2 != X1 ),
% 2.35/0.98      inference(resolution_lifted,[status(thm)],[c_13,c_232]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_680,plain,
% 2.35/0.98      ( ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
% 2.35/0.98      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 2.35/0.98      | m1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.35/0.98      | ~ l1_pre_topc(sK2) ),
% 2.35/0.98      inference(unflattening,[status(thm)],[c_679]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_681,plain,
% 2.35/0.98      ( m1_pre_topc(k1_tex_2(sK2,sK3),sK2) != iProver_top
% 2.35/0.98      | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) != iProver_top
% 2.35/0.98      | m1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 2.35/0.98      | l1_pre_topc(sK2) != iProver_top ),
% 2.35/0.98      inference(predicate_to_equality,[status(thm)],[c_680]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_713,plain,
% 2.35/0.98      ( ~ m1_pre_topc(X0,X1)
% 2.35/0.98      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 2.35/0.98      | ~ v1_subset_1(sK1(X1,X0),u1_struct_0(X1))
% 2.35/0.98      | ~ l1_pre_topc(X1)
% 2.35/0.98      | k1_tex_2(sK2,sK3) != X0
% 2.35/0.98      | sK2 != X1 ),
% 2.35/0.98      inference(resolution_lifted,[status(thm)],[c_11,c_232]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_714,plain,
% 2.35/0.98      ( ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
% 2.35/0.98      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 2.35/0.98      | ~ v1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),u1_struct_0(sK2))
% 2.35/0.98      | ~ l1_pre_topc(sK2) ),
% 2.35/0.98      inference(unflattening,[status(thm)],[c_713]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_715,plain,
% 2.35/0.98      ( m1_pre_topc(k1_tex_2(sK2,sK3),sK2) != iProver_top
% 2.35/0.98      | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) != iProver_top
% 2.35/0.98      | v1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),u1_struct_0(sK2)) != iProver_top
% 2.35/0.98      | l1_pre_topc(sK2) != iProver_top ),
% 2.35/0.98      inference(predicate_to_equality,[status(thm)],[c_714]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_2193,plain,
% 2.35/0.98      ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) = iProver_top
% 2.35/0.98      | v1_zfmisc_1(u1_struct_0(sK2)) = iProver_top ),
% 2.35/0.98      inference(predicate_to_equality,[status(thm)],[c_2192]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_7383,plain,
% 2.35/0.98      ( v1_subset_1(X0_46,u1_struct_0(sK2))
% 2.35/0.98      | ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.35/0.98      | X0_46 = u1_struct_0(sK2) ),
% 2.35/0.98      inference(instantiation,[status(thm)],[c_6343]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_7933,plain,
% 2.35/0.98      ( v1_subset_1(sK1(sK2,k1_tex_2(sK2,X0_46)),u1_struct_0(sK2))
% 2.35/0.98      | ~ m1_subset_1(sK1(sK2,k1_tex_2(sK2,X0_46)),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.35/0.98      | sK1(sK2,k1_tex_2(sK2,X0_46)) = u1_struct_0(sK2) ),
% 2.35/0.98      inference(instantiation,[status(thm)],[c_7383]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_7936,plain,
% 2.35/0.98      ( sK1(sK2,k1_tex_2(sK2,X0_46)) = u1_struct_0(sK2)
% 2.35/0.98      | v1_subset_1(sK1(sK2,k1_tex_2(sK2,X0_46)),u1_struct_0(sK2)) = iProver_top
% 2.35/0.98      | m1_subset_1(sK1(sK2,k1_tex_2(sK2,X0_46)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 2.35/0.98      inference(predicate_to_equality,[status(thm)],[c_7933]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_7938,plain,
% 2.35/0.98      ( sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(sK2)
% 2.35/0.98      | v1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),u1_struct_0(sK2)) = iProver_top
% 2.35/0.98      | m1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 2.35/0.98      inference(instantiation,[status(thm)],[c_7936]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_9316,plain,
% 2.35/0.98      ( sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(sK2) ),
% 2.35/0.98      inference(global_propositional_subsumption,
% 2.35/0.98                [status(thm)],
% 2.35/0.98                [c_9288,c_29,c_30,c_31,c_86,c_90,c_681,c_715,c_732,
% 2.35/0.98                 c_2193,c_2203,c_6407,c_6410,c_7306,c_7573,c_7938,c_8004,
% 2.35/0.98                 c_8055]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_9435,plain,
% 2.35/0.98      ( u1_struct_0(k1_tex_2(sK2,sK3)) = u1_struct_0(sK2) ),
% 2.35/0.98      inference(light_normalisation,[status(thm)],[c_9433,c_9316]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_6357,plain,
% 2.35/0.98      ( X0_46 != X1_46 | X2_46 != X1_46 | X2_46 = X0_46 ),
% 2.35/0.98      theory(equality) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_7439,plain,
% 2.35/0.98      ( X0_46 != X1_46
% 2.35/0.98      | X0_46 = u1_struct_0(k1_tex_2(X0_47,X2_46))
% 2.35/0.98      | u1_struct_0(k1_tex_2(X0_47,X2_46)) != X1_46 ),
% 2.35/0.98      inference(instantiation,[status(thm)],[c_6357]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_7765,plain,
% 2.35/0.98      ( X0_46 != u1_struct_0(X0_47)
% 2.35/0.98      | X0_46 = u1_struct_0(k1_tex_2(X1_47,X1_46))
% 2.35/0.98      | u1_struct_0(k1_tex_2(X1_47,X1_46)) != u1_struct_0(X0_47) ),
% 2.35/0.98      inference(instantiation,[status(thm)],[c_7439]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_8731,plain,
% 2.35/0.98      ( u1_struct_0(X0_47) != u1_struct_0(X1_47)
% 2.35/0.98      | u1_struct_0(X0_47) = u1_struct_0(k1_tex_2(X2_47,X0_46))
% 2.35/0.98      | u1_struct_0(k1_tex_2(X2_47,X0_46)) != u1_struct_0(X1_47) ),
% 2.35/0.98      inference(instantiation,[status(thm)],[c_7765]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_8732,plain,
% 2.35/0.98      ( u1_struct_0(k1_tex_2(sK2,sK3)) != u1_struct_0(sK2)
% 2.35/0.98      | u1_struct_0(sK2) = u1_struct_0(k1_tex_2(sK2,sK3))
% 2.35/0.98      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.35/0.98      inference(instantiation,[status(thm)],[c_8731]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_6358,plain,
% 2.35/0.98      ( ~ v1_zfmisc_1(X0_46) | v1_zfmisc_1(X1_46) | X1_46 != X0_46 ),
% 2.35/0.98      theory(equality) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_7356,plain,
% 2.35/0.98      ( v1_zfmisc_1(X0_46)
% 2.35/0.98      | ~ v1_zfmisc_1(u1_struct_0(k1_tex_2(X0_47,X1_46)))
% 2.35/0.98      | X0_46 != u1_struct_0(k1_tex_2(X0_47,X1_46)) ),
% 2.35/0.98      inference(instantiation,[status(thm)],[c_6358]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_7426,plain,
% 2.35/0.98      ( v1_zfmisc_1(u1_struct_0(X0_47))
% 2.35/0.98      | ~ v1_zfmisc_1(u1_struct_0(k1_tex_2(X1_47,X0_46)))
% 2.35/0.98      | u1_struct_0(X0_47) != u1_struct_0(k1_tex_2(X1_47,X0_46)) ),
% 2.35/0.98      inference(instantiation,[status(thm)],[c_7356]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_7428,plain,
% 2.35/0.98      ( u1_struct_0(X0_47) != u1_struct_0(k1_tex_2(X1_47,X0_46))
% 2.35/0.98      | v1_zfmisc_1(u1_struct_0(X0_47)) = iProver_top
% 2.35/0.98      | v1_zfmisc_1(u1_struct_0(k1_tex_2(X1_47,X0_46))) != iProver_top ),
% 2.35/0.98      inference(predicate_to_equality,[status(thm)],[c_7426]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_7430,plain,
% 2.35/0.98      ( u1_struct_0(sK2) != u1_struct_0(k1_tex_2(sK2,sK3))
% 2.35/0.98      | v1_zfmisc_1(u1_struct_0(k1_tex_2(sK2,sK3))) != iProver_top
% 2.35/0.98      | v1_zfmisc_1(u1_struct_0(sK2)) = iProver_top ),
% 2.35/0.98      inference(instantiation,[status(thm)],[c_7428]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_6,plain,
% 2.35/0.98      ( ~ v7_struct_0(X0)
% 2.35/0.98      | ~ l1_struct_0(X0)
% 2.35/0.98      | v1_zfmisc_1(u1_struct_0(X0)) ),
% 2.35/0.98      inference(cnf_transformation,[],[f70]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_412,plain,
% 2.35/0.98      ( ~ v7_struct_0(X0)
% 2.35/0.98      | ~ l1_pre_topc(X0)
% 2.35/0.98      | v1_zfmisc_1(u1_struct_0(X0)) ),
% 2.35/0.98      inference(resolution,[status(thm)],[c_3,c_6]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_19,plain,
% 2.35/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.35/0.98      | v7_struct_0(k1_tex_2(X1,X0))
% 2.35/0.98      | v2_struct_0(X1)
% 2.35/0.98      | ~ l1_pre_topc(X1) ),
% 2.35/0.98      inference(cnf_transformation,[],[f84]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_2594,plain,
% 2.35/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.35/0.98      | v2_struct_0(X1)
% 2.35/0.98      | ~ l1_pre_topc(X2)
% 2.35/0.98      | ~ l1_pre_topc(X1)
% 2.35/0.98      | v1_zfmisc_1(u1_struct_0(X2))
% 2.35/0.98      | k1_tex_2(X1,X0) != X2 ),
% 2.35/0.98      inference(resolution_lifted,[status(thm)],[c_412,c_19]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_2595,plain,
% 2.35/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.35/0.98      | v2_struct_0(X1)
% 2.35/0.98      | ~ l1_pre_topc(X1)
% 2.35/0.98      | ~ l1_pre_topc(k1_tex_2(X1,X0))
% 2.35/0.98      | v1_zfmisc_1(u1_struct_0(k1_tex_2(X1,X0))) ),
% 2.35/0.98      inference(unflattening,[status(thm)],[c_2594]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_448,plain,
% 2.35/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.35/0.98      | v2_struct_0(X1)
% 2.35/0.98      | ~ l1_pre_topc(X2)
% 2.35/0.98      | ~ l1_pre_topc(X1)
% 2.35/0.98      | v1_zfmisc_1(u1_struct_0(X2))
% 2.35/0.98      | k1_tex_2(X1,X0) != X2 ),
% 2.35/0.98      inference(resolution_lifted,[status(thm)],[c_412,c_19]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_449,plain,
% 2.35/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.35/0.98      | v2_struct_0(X1)
% 2.35/0.98      | ~ l1_pre_topc(X1)
% 2.35/0.98      | ~ l1_pre_topc(k1_tex_2(X1,X0))
% 2.35/0.98      | v1_zfmisc_1(u1_struct_0(k1_tex_2(X1,X0))) ),
% 2.35/0.98      inference(unflattening,[status(thm)],[c_448]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_1046,plain,
% 2.35/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.35/0.98      | v2_struct_0(X1)
% 2.35/0.98      | ~ l1_pre_topc(X2)
% 2.35/0.98      | ~ l1_pre_topc(X1)
% 2.35/0.98      | l1_pre_topc(X3)
% 2.35/0.98      | X1 != X2
% 2.35/0.98      | k1_tex_2(X1,X0) != X3 ),
% 2.35/0.98      inference(resolution_lifted,[status(thm)],[c_4,c_17]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_1047,plain,
% 2.35/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.35/0.98      | v2_struct_0(X1)
% 2.35/0.98      | ~ l1_pre_topc(X1)
% 2.35/0.98      | l1_pre_topc(k1_tex_2(X1,X0)) ),
% 2.35/0.98      inference(unflattening,[status(thm)],[c_1046]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_2597,plain,
% 2.35/0.98      ( ~ l1_pre_topc(X1)
% 2.35/0.98      | v2_struct_0(X1)
% 2.35/0.98      | ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.35/0.98      | v1_zfmisc_1(u1_struct_0(k1_tex_2(X1,X0))) ),
% 2.35/0.98      inference(global_propositional_subsumption,
% 2.35/0.98                [status(thm)],
% 2.35/0.98                [c_2595,c_449,c_1047]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_2598,plain,
% 2.35/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.35/0.98      | v2_struct_0(X1)
% 2.35/0.98      | ~ l1_pre_topc(X1)
% 2.35/0.98      | v1_zfmisc_1(u1_struct_0(k1_tex_2(X1,X0))) ),
% 2.35/0.98      inference(renaming,[status(thm)],[c_2597]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_6328,plain,
% 2.35/0.98      ( ~ m1_subset_1(X0_46,u1_struct_0(X0_47))
% 2.35/0.98      | v2_struct_0(X0_47)
% 2.35/0.98      | ~ l1_pre_topc(X0_47)
% 2.35/0.98      | v1_zfmisc_1(u1_struct_0(k1_tex_2(X0_47,X0_46))) ),
% 2.35/0.98      inference(subtyping,[status(esa)],[c_2598]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_6430,plain,
% 2.35/0.98      ( m1_subset_1(X0_46,u1_struct_0(X0_47)) != iProver_top
% 2.35/0.98      | v2_struct_0(X0_47) = iProver_top
% 2.35/0.98      | l1_pre_topc(X0_47) != iProver_top
% 2.35/0.98      | v1_zfmisc_1(u1_struct_0(k1_tex_2(X0_47,X0_46))) = iProver_top ),
% 2.35/0.98      inference(predicate_to_equality,[status(thm)],[c_6328]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_6432,plain,
% 2.35/0.98      ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 2.35/0.98      | v2_struct_0(sK2) = iProver_top
% 2.35/0.98      | l1_pre_topc(sK2) != iProver_top
% 2.35/0.98      | v1_zfmisc_1(u1_struct_0(k1_tex_2(sK2,sK3))) = iProver_top ),
% 2.35/0.98      inference(instantiation,[status(thm)],[c_6430]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_6356,plain,( X0_47 = X0_47 ),theory(equality) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_6384,plain,
% 2.35/0.98      ( sK2 = sK2 ),
% 2.35/0.98      inference(instantiation,[status(thm)],[c_6356]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_6365,plain,
% 2.35/0.98      ( X0_47 != X1_47 | u1_struct_0(X0_47) = u1_struct_0(X1_47) ),
% 2.35/0.98      theory(equality) ).
% 2.35/0.98  
% 2.35/0.98  cnf(c_6377,plain,
% 2.35/0.98      ( sK2 != sK2 | u1_struct_0(sK2) = u1_struct_0(sK2) ),
% 2.35/0.98      inference(instantiation,[status(thm)],[c_6365]) ).
% 2.35/0.98  
% 2.35/0.98  cnf(contradiction,plain,
% 2.35/0.98      ( $false ),
% 2.35/0.98      inference(minisat,
% 2.35/0.98                [status(thm)],
% 2.35/0.98                [c_9435,c_8732,c_8086,c_7430,c_6432,c_6384,c_6377,c_31,
% 2.35/0.98                 c_30,c_29]) ).
% 2.35/0.98  
% 2.35/0.98  
% 2.35/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.35/0.98  
% 2.35/0.98  ------                               Statistics
% 2.35/0.98  
% 2.35/0.98  ------ General
% 2.35/0.98  
% 2.35/0.98  abstr_ref_over_cycles:                  0
% 2.35/0.98  abstr_ref_under_cycles:                 0
% 2.35/0.98  gc_basic_clause_elim:                   0
% 2.35/0.98  forced_gc_time:                         0
% 2.35/0.98  parsing_time:                           0.01
% 2.35/0.98  unif_index_cands_time:                  0.
% 2.35/0.98  unif_index_add_time:                    0.
% 2.35/0.98  orderings_time:                         0.
% 2.35/0.98  out_proof_time:                         0.012
% 2.35/0.98  total_time:                             0.209
% 2.35/0.98  num_of_symbols:                         51
% 2.35/0.98  num_of_terms:                           3965
% 2.35/0.98  
% 2.35/0.98  ------ Preprocessing
% 2.35/0.98  
% 2.35/0.98  num_of_splits:                          0
% 2.35/0.98  num_of_split_atoms:                     0
% 2.35/0.98  num_of_reused_defs:                     0
% 2.35/0.98  num_eq_ax_congr_red:                    17
% 2.35/0.98  num_of_sem_filtered_clauses:            1
% 2.35/0.98  num_of_subtypes:                        2
% 2.35/0.98  monotx_restored_types:                  1
% 2.35/0.98  sat_num_of_epr_types:                   0
% 2.35/0.98  sat_num_of_non_cyclic_types:            0
% 2.35/0.98  sat_guarded_non_collapsed_types:        0
% 2.35/0.98  num_pure_diseq_elim:                    0
% 2.35/0.98  simp_replaced_by:                       0
% 2.35/0.98  res_preprocessed:                       164
% 2.35/0.98  prep_upred:                             0
% 2.35/0.98  prep_unflattend:                        318
% 2.35/0.98  smt_new_axioms:                         0
% 2.35/0.98  pred_elim_cands:                        8
% 2.35/0.98  pred_elim:                              2
% 2.35/0.98  pred_elim_cl:                           2
% 2.35/0.98  pred_elim_cycles:                       19
% 2.35/0.98  merged_defs:                            10
% 2.35/0.98  merged_defs_ncl:                        0
% 2.35/0.98  bin_hyper_res:                          10
% 2.35/0.98  prep_cycles:                            5
% 2.35/0.98  pred_elim_time:                         0.083
% 2.35/0.98  splitting_time:                         0.
% 2.35/0.98  sem_filter_time:                        0.
% 2.35/0.98  monotx_time:                            0.001
% 2.35/0.98  subtype_inf_time:                       0.001
% 2.35/0.98  
% 2.35/0.98  ------ Problem properties
% 2.35/0.98  
% 2.35/0.98  clauses:                                26
% 2.35/0.98  conjectures:                            5
% 2.35/0.98  epr:                                    4
% 2.35/0.98  horn:                                   18
% 2.35/0.98  ground:                                 5
% 2.35/0.98  unary:                                  3
% 2.35/0.98  binary:                                 4
% 2.35/0.98  lits:                                   78
% 2.35/0.98  lits_eq:                                3
% 2.35/0.98  fd_pure:                                0
% 2.35/0.98  fd_pseudo:                              0
% 2.35/0.98  fd_cond:                                0
% 2.35/0.98  fd_pseudo_cond:                         1
% 2.35/0.98  ac_symbols:                             0
% 2.35/0.98  
% 2.35/0.98  ------ Propositional Solver
% 2.35/0.98  
% 2.35/0.98  prop_solver_calls:                      32
% 2.35/0.98  prop_fast_solver_calls:                 2450
% 2.35/0.98  smt_solver_calls:                       0
% 2.35/0.98  smt_fast_solver_calls:                  0
% 2.35/0.98  prop_num_of_clauses:                    1411
% 2.35/0.98  prop_preprocess_simplified:             7287
% 2.35/0.98  prop_fo_subsumed:                       74
% 2.35/0.98  prop_solver_time:                       0.
% 2.35/0.98  smt_solver_time:                        0.
% 2.35/0.98  smt_fast_solver_time:                   0.
% 2.35/0.98  prop_fast_solver_time:                  0.
% 2.35/0.98  prop_unsat_core_time:                   0.
% 2.35/0.98  
% 2.35/0.98  ------ QBF
% 2.35/0.98  
% 2.35/0.98  qbf_q_res:                              0
% 2.35/0.98  qbf_num_tautologies:                    0
% 2.35/0.98  qbf_prep_cycles:                        0
% 2.35/0.98  
% 2.35/0.98  ------ BMC1
% 2.35/0.98  
% 2.35/0.98  bmc1_current_bound:                     -1
% 2.35/0.98  bmc1_last_solved_bound:                 -1
% 2.35/0.98  bmc1_unsat_core_size:                   -1
% 2.35/0.98  bmc1_unsat_core_parents_size:           -1
% 2.35/0.98  bmc1_merge_next_fun:                    0
% 2.35/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.35/0.98  
% 2.35/0.98  ------ Instantiation
% 2.35/0.98  
% 2.35/0.98  inst_num_of_clauses:                    336
% 2.35/0.98  inst_num_in_passive:                    106
% 2.35/0.98  inst_num_in_active:                     195
% 2.35/0.98  inst_num_in_unprocessed:                35
% 2.35/0.98  inst_num_of_loops:                      270
% 2.35/0.98  inst_num_of_learning_restarts:          0
% 2.35/0.98  inst_num_moves_active_passive:          71
% 2.35/0.98  inst_lit_activity:                      0
% 2.35/0.98  inst_lit_activity_moves:                0
% 2.35/0.98  inst_num_tautologies:                   0
% 2.35/0.98  inst_num_prop_implied:                  0
% 2.35/0.98  inst_num_existing_simplified:           0
% 2.35/0.98  inst_num_eq_res_simplified:             0
% 2.35/0.98  inst_num_child_elim:                    0
% 2.35/0.98  inst_num_of_dismatching_blockings:      188
% 2.35/0.98  inst_num_of_non_proper_insts:           382
% 2.35/0.98  inst_num_of_duplicates:                 0
% 2.35/0.98  inst_inst_num_from_inst_to_res:         0
% 2.35/0.98  inst_dismatching_checking_time:         0.
% 2.35/0.98  
% 2.35/0.98  ------ Resolution
% 2.35/0.98  
% 2.35/0.98  res_num_of_clauses:                     0
% 2.35/0.98  res_num_in_passive:                     0
% 2.35/0.98  res_num_in_active:                      0
% 2.35/0.98  res_num_of_loops:                       169
% 2.35/0.98  res_forward_subset_subsumed:            19
% 2.35/0.98  res_backward_subset_subsumed:           0
% 2.35/0.98  res_forward_subsumed:                   5
% 2.35/0.98  res_backward_subsumed:                  0
% 2.35/0.98  res_forward_subsumption_resolution:     1
% 2.35/0.98  res_backward_subsumption_resolution:    0
% 2.35/0.98  res_clause_to_clause_subsumption:       293
% 2.35/0.98  res_orphan_elimination:                 0
% 2.35/0.98  res_tautology_del:                      83
% 2.35/0.98  res_num_eq_res_simplified:              0
% 2.35/0.98  res_num_sel_changes:                    0
% 2.35/0.98  res_moves_from_active_to_pass:          0
% 2.35/0.98  
% 2.35/0.98  ------ Superposition
% 2.35/0.98  
% 2.35/0.98  sup_time_total:                         0.
% 2.35/0.98  sup_time_generating:                    0.
% 2.35/0.98  sup_time_sim_full:                      0.
% 2.35/0.98  sup_time_sim_immed:                     0.
% 2.35/0.98  
% 2.35/0.98  sup_num_of_clauses:                     60
% 2.35/0.98  sup_num_in_active:                      51
% 2.35/0.98  sup_num_in_passive:                     9
% 2.35/0.98  sup_num_of_loops:                       52
% 2.35/0.98  sup_fw_superposition:                   15
% 2.35/0.98  sup_bw_superposition:                   36
% 2.35/0.98  sup_immediate_simplified:               11
% 2.35/0.98  sup_given_eliminated:                   0
% 2.35/0.98  comparisons_done:                       0
% 2.35/0.98  comparisons_avoided:                    0
% 2.35/0.98  
% 2.35/0.98  ------ Simplifications
% 2.35/0.98  
% 2.35/0.98  
% 2.35/0.98  sim_fw_subset_subsumed:                 10
% 2.35/0.98  sim_bw_subset_subsumed:                 2
% 2.35/0.98  sim_fw_subsumed:                        1
% 2.35/0.98  sim_bw_subsumed:                        0
% 2.35/0.98  sim_fw_subsumption_res:                 1
% 2.35/0.98  sim_bw_subsumption_res:                 0
% 2.35/0.98  sim_tautology_del:                      3
% 2.35/0.98  sim_eq_tautology_del:                   1
% 2.35/0.98  sim_eq_res_simp:                        0
% 2.35/0.98  sim_fw_demodulated:                     0
% 2.35/0.98  sim_bw_demodulated:                     0
% 2.35/0.98  sim_light_normalised:                   1
% 2.35/0.98  sim_joinable_taut:                      0
% 2.35/0.98  sim_joinable_simp:                      0
% 2.35/0.98  sim_ac_normalised:                      0
% 2.35/0.98  sim_smt_subsumption:                    0
% 2.35/0.98  
%------------------------------------------------------------------------------
