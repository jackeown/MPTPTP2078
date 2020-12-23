%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:25:41 EST 2020

% Result     : Theorem 2.77s
% Output     : CNFRefutation 2.77s
% Verified   : 
% Statistics : Number of formulae       :  187 (3608 expanded)
%              Number of clauses        :  106 (1259 expanded)
%              Number of leaves         :   20 ( 646 expanded)
%              Depth                    :   22
%              Number of atoms          :  751 (17108 expanded)
%              Number of equality atoms :  226 (2670 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   4 average)
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

fof(f21,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f83,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

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

fof(f35,plain,(
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

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

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
    inference(nnf_transformation,[],[f36])).

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

fof(f78,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | u1_struct_0(X1) = sK1(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f37])).

fof(f81,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f58])).

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

fof(f48,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f49,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f48])).

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
    inference(nnf_transformation,[],[f49])).

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

fof(f93,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2) ),
    inference(cnf_transformation,[],[f63])).

fof(f89,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f63])).

fof(f90,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f63])).

fof(f91,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
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

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f66,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | ~ v1_subset_1(sK1(X0,X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f57])).

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

fof(f40,plain,(
    ! [X0,X1] :
      ( ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f10,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f50,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ? [X1] :
              ( k6_domain_1(X0,X1) = X0
              & m1_subset_1(X1,X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f51,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ? [X2] :
              ( k6_domain_1(X0,X2) = X0
              & m1_subset_1(X2,X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(rectify,[],[f50])).

fof(f52,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k6_domain_1(X0,X2) = X0
          & m1_subset_1(X2,X0) )
     => ( k6_domain_1(X0,sK0(X0)) = X0
        & m1_subset_1(sK0(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ( k6_domain_1(X0,sK0(X0)) = X0
            & m1_subset_1(sK0(X0),X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f51,f52])).

fof(f75,plain,(
    ! [X0,X1] :
      ( v1_zfmisc_1(X0)
      | k6_domain_1(X0,X1) != X0
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ~ ( v1_tex_2(X1,X0)
              & u1_struct_0(X0) = u1_struct_0(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_tex_2(X1,X0)
          | u1_struct_0(X0) != u1_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_tex_2(X1,X0)
          | u1_struct_0(X0) != u1_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f42])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ v1_tex_2(X1,X0)
      | u1_struct_0(X0) != u1_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f67,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f16,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f87,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X0,X1)
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f71,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ~ ( v7_struct_0(X0)
              & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v7_struct_0(X0)
          | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v7_struct_0(X0)
          | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ v7_struct_0(X0)
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f85,plain,(
    ! [X0,X1] :
      ( v7_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f92,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | v1_tex_2(k1_tex_2(sK2,sK3),sK2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_18,plain,
    ( m1_pre_topc(k1_tex_2(X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2402,plain,
    ( m1_pre_topc(k1_tex_2(X0_47,X0_48),X0_47)
    | ~ m1_subset_1(X0_48,u1_struct_0(X0_47))
    | v2_struct_0(X0_47)
    | ~ l1_pre_topc(X0_47) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_3156,plain,
    ( m1_pre_topc(k1_tex_2(X0_47,X0_48),X0_47) = iProver_top
    | m1_subset_1(X0_48,u1_struct_0(X0_47)) != iProver_top
    | v2_struct_0(X0_47) = iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2402])).

cnf(c_13,plain,
    ( v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK1(X1,X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2406,plain,
    ( v1_tex_2(X0_47,X1_47)
    | ~ m1_pre_topc(X0_47,X1_47)
    | ~ l1_pre_topc(X1_47)
    | sK1(X1_47,X0_47) = u1_struct_0(X0_47) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_3152,plain,
    ( sK1(X0_47,X1_47) = u1_struct_0(X1_47)
    | v1_tex_2(X1_47,X0_47) = iProver_top
    | m1_pre_topc(X1_47,X0_47) != iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2406])).

cnf(c_4127,plain,
    ( sK1(X0_47,k1_tex_2(X0_47,X0_48)) = u1_struct_0(k1_tex_2(X0_47,X0_48))
    | v1_tex_2(k1_tex_2(X0_47,X0_48),X0_47) = iProver_top
    | m1_subset_1(X0_48,u1_struct_0(X0_47)) != iProver_top
    | v2_struct_0(X0_47) = iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(superposition,[status(thm)],[c_3156,c_3152])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2412,plain,
    ( ~ m1_subset_1(X0_48,X1_48)
    | m1_subset_1(k6_domain_1(X1_48,X0_48),k1_zfmisc_1(X1_48))
    | v1_xboole_0(X1_48) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_3146,plain,
    ( m1_subset_1(X0_48,X1_48) != iProver_top
    | m1_subset_1(k6_domain_1(X1_48,X0_48),k1_zfmisc_1(X1_48)) = iProver_top
    | v1_xboole_0(X1_48) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2412])).

cnf(c_16,plain,
    ( v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2404,plain,
    ( v1_subset_1(X0_48,X1_48)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(X1_48))
    | X0_48 = X1_48 ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_3154,plain,
    ( X0_48 = X1_48
    | v1_subset_1(X0_48,X1_48) = iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(X1_48)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2404])).

cnf(c_3998,plain,
    ( k6_domain_1(X0_48,X1_48) = X0_48
    | v1_subset_1(k6_domain_1(X0_48,X1_48),X0_48) = iProver_top
    | m1_subset_1(X1_48,X0_48) != iProver_top
    | v1_xboole_0(X0_48) = iProver_top ),
    inference(superposition,[status(thm)],[c_3146,c_3154])).

cnf(c_25,negated_conjecture,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_2398,negated_conjecture,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_3160,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) != iProver_top
    | v1_tex_2(k1_tex_2(sK2,sK3),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2398])).

cnf(c_4759,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK3) = u1_struct_0(sK2)
    | v1_tex_2(k1_tex_2(sK2,sK3),sK2) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3998,c_3160])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_30,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_28,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_31,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_32,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_5,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_90,plain,
    ( v2_struct_0(X0) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_92,plain,
    ( v2_struct_0(sK2) = iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_90])).

cnf(c_2,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_95,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_97,plain,
    ( l1_pre_topc(sK2) != iProver_top
    | l1_struct_0(sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_95])).

cnf(c_5001,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK3) = u1_struct_0(sK2)
    | v1_tex_2(k1_tex_2(sK2,sK3),sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4759,c_30,c_31,c_32,c_92,c_97])).

cnf(c_5756,plain,
    ( sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(k1_tex_2(sK2,sK3))
    | k6_domain_1(u1_struct_0(sK2),sK3) = u1_struct_0(sK2)
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4127,c_5001])).

cnf(c_14,plain,
    ( v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | m1_subset_1(sK1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2405,plain,
    ( v1_tex_2(X0_47,X1_47)
    | ~ m1_pre_topc(X0_47,X1_47)
    | m1_subset_1(sK1(X1_47,X0_47),k1_zfmisc_1(u1_struct_0(X1_47)))
    | ~ l1_pre_topc(X1_47) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_3153,plain,
    ( v1_tex_2(X0_47,X1_47) = iProver_top
    | m1_pre_topc(X0_47,X1_47) != iProver_top
    | m1_subset_1(sK1(X1_47,X0_47),k1_zfmisc_1(u1_struct_0(X1_47))) = iProver_top
    | l1_pre_topc(X1_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2405])).

cnf(c_4607,plain,
    ( sK1(X0_47,X1_47) = u1_struct_0(X0_47)
    | v1_subset_1(sK1(X0_47,X1_47),u1_struct_0(X0_47)) = iProver_top
    | v1_tex_2(X1_47,X0_47) = iProver_top
    | m1_pre_topc(X1_47,X0_47) != iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(superposition,[status(thm)],[c_3153,c_3154])).

cnf(c_12,plain,
    ( ~ v1_subset_1(sK1(X0,X1),u1_struct_0(X0))
    | v1_tex_2(X1,X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2407,plain,
    ( ~ v1_subset_1(sK1(X0_47,X1_47),u1_struct_0(X0_47))
    | v1_tex_2(X1_47,X0_47)
    | ~ m1_pre_topc(X1_47,X0_47)
    | ~ l1_pre_topc(X0_47) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_2467,plain,
    ( v1_subset_1(sK1(X0_47,X1_47),u1_struct_0(X0_47)) != iProver_top
    | v1_tex_2(X1_47,X0_47) = iProver_top
    | m1_pre_topc(X1_47,X0_47) != iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2407])).

cnf(c_5548,plain,
    ( sK1(X0_47,X1_47) = u1_struct_0(X0_47)
    | v1_tex_2(X1_47,X0_47) = iProver_top
    | m1_pre_topc(X1_47,X0_47) != iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4607,c_2467])).

cnf(c_5556,plain,
    ( sK1(X0_47,k1_tex_2(X0_47,X0_48)) = u1_struct_0(X0_47)
    | v1_tex_2(k1_tex_2(X0_47,X0_48),X0_47) = iProver_top
    | m1_subset_1(X0_48,u1_struct_0(X0_47)) != iProver_top
    | v2_struct_0(X0_47) = iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(superposition,[status(thm)],[c_3156,c_5548])).

cnf(c_5566,plain,
    ( sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(sK2)
    | k6_domain_1(u1_struct_0(sK2),sK3) = u1_struct_0(sK2)
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5556,c_5001])).

cnf(c_91,plain,
    ( v2_struct_0(sK2)
    | ~ l1_struct_0(sK2)
    | ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_96,plain,
    ( ~ l1_pre_topc(sK2)
    | l1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2477,plain,
    ( m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_2402])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k1_tex_2(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2401,plain,
    ( ~ m1_subset_1(X0_48,u1_struct_0(X0_47))
    | v2_struct_0(X0_47)
    | ~ v2_struct_0(k1_tex_2(X0_47,X0_48))
    | ~ l1_pre_topc(X0_47) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_2480,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ v2_struct_0(k1_tex_2(sK2,sK3))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_2401])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | v1_zfmisc_1(X1)
    | k6_domain_1(X1,X0) != X1 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2410,plain,
    ( ~ m1_subset_1(X0_48,X1_48)
    | v1_xboole_0(X1_48)
    | v1_zfmisc_1(X1_48)
    | k6_domain_1(X1_48,X0_48) != X1_48 ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_3422,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2))
    | v1_zfmisc_1(u1_struct_0(sK2))
    | k6_domain_1(u1_struct_0(sK2),sK3) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_2410])).

cnf(c_22,plain,
    ( ~ v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X0) != u1_struct_0(X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_2399,plain,
    ( ~ v1_tex_2(X0_47,X1_47)
    | ~ m1_pre_topc(X0_47,X1_47)
    | ~ l1_pre_topc(X1_47)
    | u1_struct_0(X0_47) != u1_struct_0(X1_47) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_3512,plain,
    ( ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2)
    | ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
    | ~ l1_pre_topc(sK2)
    | u1_struct_0(k1_tex_2(sK2,sK3)) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_2399])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2413,plain,
    ( ~ m1_pre_topc(X0_47,X1_47)
    | ~ l1_pre_topc(X1_47)
    | l1_pre_topc(X0_47) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_3568,plain,
    ( ~ m1_pre_topc(k1_tex_2(X0_47,X0_48),X1_47)
    | ~ l1_pre_topc(X1_47)
    | l1_pre_topc(k1_tex_2(X0_47,X0_48)) ),
    inference(instantiation,[status(thm)],[c_2413])).

cnf(c_3570,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
    | l1_pre_topc(k1_tex_2(sK2,sK3))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_3568])).

cnf(c_483,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_2,c_5])).

cnf(c_2390,plain,
    ( v2_struct_0(X0_47)
    | ~ l1_pre_topc(X0_47)
    | ~ v1_xboole_0(u1_struct_0(X0_47)) ),
    inference(subtyping,[status(esa)],[c_483])).

cnf(c_3943,plain,
    ( v2_struct_0(k1_tex_2(sK2,sK3))
    | ~ l1_pre_topc(k1_tex_2(sK2,sK3))
    | ~ v1_xboole_0(u1_struct_0(k1_tex_2(sK2,sK3))) ),
    inference(instantiation,[status(thm)],[c_2390])).

cnf(c_8,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_23,plain,
    ( ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | ~ v1_zfmisc_1(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_397,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ v1_zfmisc_1(X3)
    | X3 = X2
    | u1_struct_0(X0) != X2
    | u1_struct_0(X1) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_23])).

cnf(c_398,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(u1_struct_0(X0))
    | v1_xboole_0(u1_struct_0(X1))
    | ~ v1_zfmisc_1(u1_struct_0(X1))
    | u1_struct_0(X1) = u1_struct_0(X0) ),
    inference(unflattening,[status(thm)],[c_397])).

cnf(c_2392,plain,
    ( ~ m1_pre_topc(X0_47,X1_47)
    | ~ l1_pre_topc(X1_47)
    | v1_xboole_0(u1_struct_0(X0_47))
    | v1_xboole_0(u1_struct_0(X1_47))
    | ~ v1_zfmisc_1(u1_struct_0(X1_47))
    | u1_struct_0(X1_47) = u1_struct_0(X0_47) ),
    inference(subtyping,[status(esa)],[c_398])).

cnf(c_3166,plain,
    ( u1_struct_0(X0_47) = u1_struct_0(X1_47)
    | m1_pre_topc(X1_47,X0_47) != iProver_top
    | l1_pre_topc(X0_47) != iProver_top
    | v1_xboole_0(u1_struct_0(X1_47)) = iProver_top
    | v1_xboole_0(u1_struct_0(X0_47)) = iProver_top
    | v1_zfmisc_1(u1_struct_0(X0_47)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2392])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2411,plain,
    ( ~ m1_pre_topc(X0_47,X1_47)
    | m1_subset_1(u1_struct_0(X0_47),k1_zfmisc_1(u1_struct_0(X1_47)))
    | ~ l1_pre_topc(X1_47) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_3147,plain,
    ( m1_pre_topc(X0_47,X1_47) != iProver_top
    | m1_subset_1(u1_struct_0(X0_47),k1_zfmisc_1(u1_struct_0(X1_47))) = iProver_top
    | l1_pre_topc(X1_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2411])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2414,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(X1_48))
    | ~ v1_xboole_0(X1_48)
    | v1_xboole_0(X0_48) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_3144,plain,
    ( m1_subset_1(X0_48,k1_zfmisc_1(X1_48)) != iProver_top
    | v1_xboole_0(X1_48) != iProver_top
    | v1_xboole_0(X0_48) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2414])).

cnf(c_3821,plain,
    ( m1_pre_topc(X0_47,X1_47) != iProver_top
    | l1_pre_topc(X1_47) != iProver_top
    | v1_xboole_0(u1_struct_0(X1_47)) != iProver_top
    | v1_xboole_0(u1_struct_0(X0_47)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3147,c_3144])).

cnf(c_5380,plain,
    ( u1_struct_0(X0_47) = u1_struct_0(X1_47)
    | m1_pre_topc(X0_47,X1_47) != iProver_top
    | l1_pre_topc(X1_47) != iProver_top
    | v1_xboole_0(u1_struct_0(X0_47)) = iProver_top
    | v1_zfmisc_1(u1_struct_0(X1_47)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3166,c_3821])).

cnf(c_5382,plain,
    ( u1_struct_0(k1_tex_2(X0_47,X0_48)) = u1_struct_0(X0_47)
    | m1_subset_1(X0_48,u1_struct_0(X0_47)) != iProver_top
    | v2_struct_0(X0_47) = iProver_top
    | l1_pre_topc(X0_47) != iProver_top
    | v1_xboole_0(u1_struct_0(k1_tex_2(X0_47,X0_48))) = iProver_top
    | v1_zfmisc_1(u1_struct_0(X0_47)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3156,c_5380])).

cnf(c_5383,plain,
    ( ~ m1_subset_1(X0_48,u1_struct_0(X0_47))
    | v2_struct_0(X0_47)
    | ~ l1_pre_topc(X0_47)
    | v1_xboole_0(u1_struct_0(k1_tex_2(X0_47,X0_48)))
    | ~ v1_zfmisc_1(u1_struct_0(X0_47))
    | u1_struct_0(k1_tex_2(X0_47,X0_48)) = u1_struct_0(X0_47) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5382])).

cnf(c_5385,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | v1_xboole_0(u1_struct_0(k1_tex_2(sK2,sK3)))
    | ~ v1_zfmisc_1(u1_struct_0(sK2))
    | u1_struct_0(k1_tex_2(sK2,sK3)) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_5383])).

cnf(c_5557,plain,
    ( v1_tex_2(k1_tex_2(X0_47,X0_48),X0_47)
    | ~ m1_subset_1(X0_48,u1_struct_0(X0_47))
    | v2_struct_0(X0_47)
    | ~ l1_pre_topc(X0_47)
    | sK1(X0_47,k1_tex_2(X0_47,X0_48)) = u1_struct_0(X0_47) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5556])).

cnf(c_5559,plain,
    ( v1_tex_2(k1_tex_2(sK2,sK3),sK2)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_5557])).

cnf(c_5567,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(sK2)
    | k6_domain_1(u1_struct_0(sK2),sK3) = u1_struct_0(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5566])).

cnf(c_5584,plain,
    ( sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5566,c_29,c_28,c_27,c_91,c_96,c_2477,c_2480,c_3422,c_3512,c_3570,c_3943,c_5385,c_5559,c_5567])).

cnf(c_5757,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK3) = u1_struct_0(sK2)
    | u1_struct_0(k1_tex_2(sK2,sK3)) = u1_struct_0(sK2)
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5756,c_5584])).

cnf(c_5758,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | k6_domain_1(u1_struct_0(sK2),sK3) = u1_struct_0(sK2)
    | u1_struct_0(k1_tex_2(sK2,sK3)) = u1_struct_0(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5757])).

cnf(c_5860,plain,
    ( u1_struct_0(k1_tex_2(sK2,sK3)) = u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5757,c_29,c_28,c_27,c_91,c_96,c_2477,c_2480,c_3422,c_3570,c_3943,c_5385,c_5758])).

cnf(c_24,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v7_struct_0(X0)
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_463,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v7_struct_0(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_2,c_24])).

cnf(c_2391,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0_47),X0_48),u1_struct_0(X0_47))
    | ~ m1_subset_1(X0_48,u1_struct_0(X0_47))
    | ~ v7_struct_0(X0_47)
    | v2_struct_0(X0_47)
    | ~ l1_pre_topc(X0_47) ),
    inference(subtyping,[status(esa)],[c_463])).

cnf(c_3167,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(X0_47),X0_48),u1_struct_0(X0_47)) != iProver_top
    | m1_subset_1(X0_48,u1_struct_0(X0_47)) != iProver_top
    | v7_struct_0(X0_47) != iProver_top
    | v2_struct_0(X0_47) = iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2391])).

cnf(c_5868,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),X0_48),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_48,u1_struct_0(k1_tex_2(sK2,sK3))) != iProver_top
    | v7_struct_0(k1_tex_2(sK2,sK3)) != iProver_top
    | v2_struct_0(k1_tex_2(sK2,sK3)) = iProver_top
    | l1_pre_topc(k1_tex_2(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5860,c_3167])).

cnf(c_5982,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),X0_48),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top
    | v7_struct_0(k1_tex_2(sK2,sK3)) != iProver_top
    | v2_struct_0(k1_tex_2(sK2,sK3)) = iProver_top
    | l1_pre_topc(k1_tex_2(sK2,sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5868,c_5860])).

cnf(c_6064,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | v7_struct_0(k1_tex_2(sK2,sK3)) != iProver_top
    | v2_struct_0(k1_tex_2(sK2,sK3)) = iProver_top
    | l1_pre_topc(k1_tex_2(sK2,sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5982])).

cnf(c_3569,plain,
    ( m1_pre_topc(k1_tex_2(X0_47,X0_48),X1_47) != iProver_top
    | l1_pre_topc(X1_47) != iProver_top
    | l1_pre_topc(k1_tex_2(X0_47,X0_48)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3568])).

cnf(c_3571,plain,
    ( m1_pre_topc(k1_tex_2(sK2,sK3),sK2) != iProver_top
    | l1_pre_topc(k1_tex_2(sK2,sK3)) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3569])).

cnf(c_3516,plain,
    ( u1_struct_0(k1_tex_2(sK2,sK3)) != u1_struct_0(sK2)
    | v1_tex_2(k1_tex_2(sK2,sK3),sK2) != iProver_top
    | m1_pre_topc(k1_tex_2(sK2,sK3),sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3512])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v7_struct_0(k1_tex_2(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_2400,plain,
    ( ~ m1_subset_1(X0_48,u1_struct_0(X0_47))
    | v7_struct_0(k1_tex_2(X0_47,X0_48))
    | v2_struct_0(X0_47)
    | ~ l1_pre_topc(X0_47) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_2482,plain,
    ( m1_subset_1(X0_48,u1_struct_0(X0_47)) != iProver_top
    | v7_struct_0(k1_tex_2(X0_47,X0_48)) = iProver_top
    | v2_struct_0(X0_47) = iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2400])).

cnf(c_2484,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | v7_struct_0(k1_tex_2(sK2,sK3)) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2482])).

cnf(c_2479,plain,
    ( m1_subset_1(X0_48,u1_struct_0(X0_47)) != iProver_top
    | v2_struct_0(X0_47) = iProver_top
    | v2_struct_0(k1_tex_2(X0_47,X0_48)) != iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2401])).

cnf(c_2481,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | v2_struct_0(k1_tex_2(sK2,sK3)) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2479])).

cnf(c_2476,plain,
    ( m1_pre_topc(k1_tex_2(X0_47,X0_48),X0_47) = iProver_top
    | m1_subset_1(X0_48,u1_struct_0(X0_47)) != iProver_top
    | v2_struct_0(X0_47) = iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2402])).

cnf(c_2478,plain,
    ( m1_pre_topc(k1_tex_2(sK2,sK3),sK2) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2476])).

cnf(c_26,negated_conjecture,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | v1_tex_2(k1_tex_2(sK2,sK3),sK2) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_33,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) = iProver_top
    | v1_tex_2(k1_tex_2(sK2,sK3),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6064,c_5860,c_3571,c_3516,c_2484,c_2481,c_2478,c_33,c_32,c_31,c_30])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:00:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.77/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.00  
% 2.77/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.77/1.00  
% 2.77/1.00  ------  iProver source info
% 2.77/1.00  
% 2.77/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.77/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.77/1.00  git: non_committed_changes: false
% 2.77/1.00  git: last_make_outside_of_git: false
% 2.77/1.00  
% 2.77/1.00  ------ 
% 2.77/1.00  
% 2.77/1.00  ------ Input Options
% 2.77/1.00  
% 2.77/1.00  --out_options                           all
% 2.77/1.00  --tptp_safe_out                         true
% 2.77/1.00  --problem_path                          ""
% 2.77/1.00  --include_path                          ""
% 2.77/1.00  --clausifier                            res/vclausify_rel
% 2.77/1.00  --clausifier_options                    --mode clausify
% 2.77/1.00  --stdin                                 false
% 2.77/1.00  --stats_out                             all
% 2.77/1.00  
% 2.77/1.00  ------ General Options
% 2.77/1.00  
% 2.77/1.00  --fof                                   false
% 2.77/1.00  --time_out_real                         305.
% 2.77/1.00  --time_out_virtual                      -1.
% 2.77/1.00  --symbol_type_check                     false
% 2.77/1.00  --clausify_out                          false
% 2.77/1.00  --sig_cnt_out                           false
% 2.77/1.00  --trig_cnt_out                          false
% 2.77/1.00  --trig_cnt_out_tolerance                1.
% 2.77/1.00  --trig_cnt_out_sk_spl                   false
% 2.77/1.00  --abstr_cl_out                          false
% 2.77/1.00  
% 2.77/1.00  ------ Global Options
% 2.77/1.00  
% 2.77/1.00  --schedule                              default
% 2.77/1.00  --add_important_lit                     false
% 2.77/1.00  --prop_solver_per_cl                    1000
% 2.77/1.00  --min_unsat_core                        false
% 2.77/1.00  --soft_assumptions                      false
% 2.77/1.00  --soft_lemma_size                       3
% 2.77/1.00  --prop_impl_unit_size                   0
% 2.77/1.00  --prop_impl_unit                        []
% 2.77/1.00  --share_sel_clauses                     true
% 2.77/1.00  --reset_solvers                         false
% 2.77/1.00  --bc_imp_inh                            [conj_cone]
% 2.77/1.00  --conj_cone_tolerance                   3.
% 2.77/1.00  --extra_neg_conj                        none
% 2.77/1.00  --large_theory_mode                     true
% 2.77/1.00  --prolific_symb_bound                   200
% 2.77/1.00  --lt_threshold                          2000
% 2.77/1.00  --clause_weak_htbl                      true
% 2.77/1.00  --gc_record_bc_elim                     false
% 2.77/1.00  
% 2.77/1.00  ------ Preprocessing Options
% 2.77/1.00  
% 2.77/1.00  --preprocessing_flag                    true
% 2.77/1.00  --time_out_prep_mult                    0.1
% 2.77/1.00  --splitting_mode                        input
% 2.77/1.00  --splitting_grd                         true
% 2.77/1.00  --splitting_cvd                         false
% 2.77/1.00  --splitting_cvd_svl                     false
% 2.77/1.00  --splitting_nvd                         32
% 2.77/1.00  --sub_typing                            true
% 2.77/1.00  --prep_gs_sim                           true
% 2.77/1.00  --prep_unflatten                        true
% 2.77/1.00  --prep_res_sim                          true
% 2.77/1.00  --prep_upred                            true
% 2.77/1.00  --prep_sem_filter                       exhaustive
% 2.77/1.00  --prep_sem_filter_out                   false
% 2.77/1.00  --pred_elim                             true
% 2.77/1.00  --res_sim_input                         true
% 2.77/1.00  --eq_ax_congr_red                       true
% 2.77/1.00  --pure_diseq_elim                       true
% 2.77/1.00  --brand_transform                       false
% 2.77/1.00  --non_eq_to_eq                          false
% 2.77/1.00  --prep_def_merge                        true
% 2.77/1.00  --prep_def_merge_prop_impl              false
% 2.77/1.00  --prep_def_merge_mbd                    true
% 2.77/1.00  --prep_def_merge_tr_red                 false
% 2.77/1.00  --prep_def_merge_tr_cl                  false
% 2.77/1.00  --smt_preprocessing                     true
% 2.77/1.00  --smt_ac_axioms                         fast
% 2.77/1.00  --preprocessed_out                      false
% 2.77/1.00  --preprocessed_stats                    false
% 2.77/1.00  
% 2.77/1.00  ------ Abstraction refinement Options
% 2.77/1.00  
% 2.77/1.00  --abstr_ref                             []
% 2.77/1.00  --abstr_ref_prep                        false
% 2.77/1.00  --abstr_ref_until_sat                   false
% 2.77/1.00  --abstr_ref_sig_restrict                funpre
% 2.77/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.77/1.00  --abstr_ref_under                       []
% 2.77/1.00  
% 2.77/1.00  ------ SAT Options
% 2.77/1.00  
% 2.77/1.00  --sat_mode                              false
% 2.77/1.00  --sat_fm_restart_options                ""
% 2.77/1.00  --sat_gr_def                            false
% 2.77/1.00  --sat_epr_types                         true
% 2.77/1.00  --sat_non_cyclic_types                  false
% 2.77/1.00  --sat_finite_models                     false
% 2.77/1.00  --sat_fm_lemmas                         false
% 2.77/1.00  --sat_fm_prep                           false
% 2.77/1.00  --sat_fm_uc_incr                        true
% 2.77/1.00  --sat_out_model                         small
% 2.77/1.00  --sat_out_clauses                       false
% 2.77/1.00  
% 2.77/1.00  ------ QBF Options
% 2.77/1.00  
% 2.77/1.00  --qbf_mode                              false
% 2.77/1.00  --qbf_elim_univ                         false
% 2.77/1.00  --qbf_dom_inst                          none
% 2.77/1.00  --qbf_dom_pre_inst                      false
% 2.77/1.00  --qbf_sk_in                             false
% 2.77/1.00  --qbf_pred_elim                         true
% 2.77/1.00  --qbf_split                             512
% 2.77/1.00  
% 2.77/1.00  ------ BMC1 Options
% 2.77/1.00  
% 2.77/1.00  --bmc1_incremental                      false
% 2.77/1.00  --bmc1_axioms                           reachable_all
% 2.77/1.00  --bmc1_min_bound                        0
% 2.77/1.00  --bmc1_max_bound                        -1
% 2.77/1.00  --bmc1_max_bound_default                -1
% 2.77/1.00  --bmc1_symbol_reachability              true
% 2.77/1.00  --bmc1_property_lemmas                  false
% 2.77/1.00  --bmc1_k_induction                      false
% 2.77/1.00  --bmc1_non_equiv_states                 false
% 2.77/1.00  --bmc1_deadlock                         false
% 2.77/1.00  --bmc1_ucm                              false
% 2.77/1.00  --bmc1_add_unsat_core                   none
% 2.77/1.00  --bmc1_unsat_core_children              false
% 2.77/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.77/1.00  --bmc1_out_stat                         full
% 2.77/1.00  --bmc1_ground_init                      false
% 2.77/1.00  --bmc1_pre_inst_next_state              false
% 2.77/1.00  --bmc1_pre_inst_state                   false
% 2.77/1.00  --bmc1_pre_inst_reach_state             false
% 2.77/1.00  --bmc1_out_unsat_core                   false
% 2.77/1.00  --bmc1_aig_witness_out                  false
% 2.77/1.00  --bmc1_verbose                          false
% 2.77/1.00  --bmc1_dump_clauses_tptp                false
% 2.77/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.77/1.00  --bmc1_dump_file                        -
% 2.77/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.77/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.77/1.00  --bmc1_ucm_extend_mode                  1
% 2.77/1.00  --bmc1_ucm_init_mode                    2
% 2.77/1.00  --bmc1_ucm_cone_mode                    none
% 2.77/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.77/1.00  --bmc1_ucm_relax_model                  4
% 2.77/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.77/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.77/1.00  --bmc1_ucm_layered_model                none
% 2.77/1.00  --bmc1_ucm_max_lemma_size               10
% 2.77/1.00  
% 2.77/1.00  ------ AIG Options
% 2.77/1.00  
% 2.77/1.00  --aig_mode                              false
% 2.77/1.00  
% 2.77/1.00  ------ Instantiation Options
% 2.77/1.00  
% 2.77/1.00  --instantiation_flag                    true
% 2.77/1.00  --inst_sos_flag                         false
% 2.77/1.00  --inst_sos_phase                        true
% 2.77/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.77/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.77/1.00  --inst_lit_sel_side                     num_symb
% 2.77/1.00  --inst_solver_per_active                1400
% 2.77/1.00  --inst_solver_calls_frac                1.
% 2.77/1.00  --inst_passive_queue_type               priority_queues
% 2.77/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.77/1.00  --inst_passive_queues_freq              [25;2]
% 2.77/1.00  --inst_dismatching                      true
% 2.77/1.00  --inst_eager_unprocessed_to_passive     true
% 2.77/1.00  --inst_prop_sim_given                   true
% 2.77/1.00  --inst_prop_sim_new                     false
% 2.77/1.00  --inst_subs_new                         false
% 2.77/1.00  --inst_eq_res_simp                      false
% 2.77/1.00  --inst_subs_given                       false
% 2.77/1.00  --inst_orphan_elimination               true
% 2.77/1.00  --inst_learning_loop_flag               true
% 2.77/1.00  --inst_learning_start                   3000
% 2.77/1.00  --inst_learning_factor                  2
% 2.77/1.00  --inst_start_prop_sim_after_learn       3
% 2.77/1.00  --inst_sel_renew                        solver
% 2.77/1.00  --inst_lit_activity_flag                true
% 2.77/1.00  --inst_restr_to_given                   false
% 2.77/1.00  --inst_activity_threshold               500
% 2.77/1.00  --inst_out_proof                        true
% 2.77/1.00  
% 2.77/1.00  ------ Resolution Options
% 2.77/1.00  
% 2.77/1.00  --resolution_flag                       true
% 2.77/1.00  --res_lit_sel                           adaptive
% 2.77/1.00  --res_lit_sel_side                      none
% 2.77/1.00  --res_ordering                          kbo
% 2.77/1.00  --res_to_prop_solver                    active
% 2.77/1.00  --res_prop_simpl_new                    false
% 2.77/1.00  --res_prop_simpl_given                  true
% 2.77/1.00  --res_passive_queue_type                priority_queues
% 2.77/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.77/1.00  --res_passive_queues_freq               [15;5]
% 2.77/1.00  --res_forward_subs                      full
% 2.77/1.00  --res_backward_subs                     full
% 2.77/1.00  --res_forward_subs_resolution           true
% 2.77/1.00  --res_backward_subs_resolution          true
% 2.77/1.00  --res_orphan_elimination                true
% 2.77/1.00  --res_time_limit                        2.
% 2.77/1.00  --res_out_proof                         true
% 2.77/1.00  
% 2.77/1.00  ------ Superposition Options
% 2.77/1.00  
% 2.77/1.00  --superposition_flag                    true
% 2.77/1.00  --sup_passive_queue_type                priority_queues
% 2.77/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.77/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.77/1.00  --demod_completeness_check              fast
% 2.77/1.00  --demod_use_ground                      true
% 2.77/1.00  --sup_to_prop_solver                    passive
% 2.77/1.00  --sup_prop_simpl_new                    true
% 2.77/1.00  --sup_prop_simpl_given                  true
% 2.77/1.00  --sup_fun_splitting                     false
% 2.77/1.00  --sup_smt_interval                      50000
% 2.77/1.00  
% 2.77/1.00  ------ Superposition Simplification Setup
% 2.77/1.00  
% 2.77/1.00  --sup_indices_passive                   []
% 2.77/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.77/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.77/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.77/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.77/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.77/1.00  --sup_full_bw                           [BwDemod]
% 2.77/1.00  --sup_immed_triv                        [TrivRules]
% 2.77/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.77/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.77/1.00  --sup_immed_bw_main                     []
% 2.77/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.77/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.77/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.77/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.77/1.00  
% 2.77/1.00  ------ Combination Options
% 2.77/1.00  
% 2.77/1.00  --comb_res_mult                         3
% 2.77/1.00  --comb_sup_mult                         2
% 2.77/1.00  --comb_inst_mult                        10
% 2.77/1.00  
% 2.77/1.00  ------ Debug Options
% 2.77/1.00  
% 2.77/1.00  --dbg_backtrace                         false
% 2.77/1.00  --dbg_dump_prop_clauses                 false
% 2.77/1.00  --dbg_dump_prop_clauses_file            -
% 2.77/1.00  --dbg_out_stat                          false
% 2.77/1.00  ------ Parsing...
% 2.77/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.77/1.00  
% 2.77/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.77/1.00  
% 2.77/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.77/1.00  
% 2.77/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.77/1.00  ------ Proving...
% 2.77/1.00  ------ Problem Properties 
% 2.77/1.00  
% 2.77/1.00  
% 2.77/1.00  clauses                                 27
% 2.77/1.00  conjectures                             5
% 2.77/1.00  EPR                                     4
% 2.77/1.00  Horn                                    16
% 2.77/1.00  unary                                   3
% 2.77/1.00  binary                                  4
% 2.77/1.00  lits                                    85
% 2.77/1.00  lits eq                                 6
% 2.77/1.00  fd_pure                                 0
% 2.77/1.00  fd_pseudo                               0
% 2.77/1.00  fd_cond                                 0
% 2.77/1.00  fd_pseudo_cond                          1
% 2.77/1.00  AC symbols                              0
% 2.77/1.00  
% 2.77/1.00  ------ Schedule dynamic 5 is on 
% 2.77/1.00  
% 2.77/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.77/1.00  
% 2.77/1.00  
% 2.77/1.00  ------ 
% 2.77/1.00  Current options:
% 2.77/1.00  ------ 
% 2.77/1.00  
% 2.77/1.00  ------ Input Options
% 2.77/1.00  
% 2.77/1.00  --out_options                           all
% 2.77/1.00  --tptp_safe_out                         true
% 2.77/1.00  --problem_path                          ""
% 2.77/1.00  --include_path                          ""
% 2.77/1.00  --clausifier                            res/vclausify_rel
% 2.77/1.00  --clausifier_options                    --mode clausify
% 2.77/1.00  --stdin                                 false
% 2.77/1.00  --stats_out                             all
% 2.77/1.00  
% 2.77/1.00  ------ General Options
% 2.77/1.00  
% 2.77/1.00  --fof                                   false
% 2.77/1.00  --time_out_real                         305.
% 2.77/1.00  --time_out_virtual                      -1.
% 2.77/1.00  --symbol_type_check                     false
% 2.77/1.00  --clausify_out                          false
% 2.77/1.00  --sig_cnt_out                           false
% 2.77/1.00  --trig_cnt_out                          false
% 2.77/1.00  --trig_cnt_out_tolerance                1.
% 2.77/1.00  --trig_cnt_out_sk_spl                   false
% 2.77/1.00  --abstr_cl_out                          false
% 2.77/1.00  
% 2.77/1.00  ------ Global Options
% 2.77/1.00  
% 2.77/1.00  --schedule                              default
% 2.77/1.00  --add_important_lit                     false
% 2.77/1.00  --prop_solver_per_cl                    1000
% 2.77/1.00  --min_unsat_core                        false
% 2.77/1.00  --soft_assumptions                      false
% 2.77/1.00  --soft_lemma_size                       3
% 2.77/1.00  --prop_impl_unit_size                   0
% 2.77/1.00  --prop_impl_unit                        []
% 2.77/1.00  --share_sel_clauses                     true
% 2.77/1.00  --reset_solvers                         false
% 2.77/1.00  --bc_imp_inh                            [conj_cone]
% 2.77/1.00  --conj_cone_tolerance                   3.
% 2.77/1.00  --extra_neg_conj                        none
% 2.77/1.00  --large_theory_mode                     true
% 2.77/1.00  --prolific_symb_bound                   200
% 2.77/1.00  --lt_threshold                          2000
% 2.77/1.00  --clause_weak_htbl                      true
% 2.77/1.00  --gc_record_bc_elim                     false
% 2.77/1.00  
% 2.77/1.00  ------ Preprocessing Options
% 2.77/1.00  
% 2.77/1.00  --preprocessing_flag                    true
% 2.77/1.00  --time_out_prep_mult                    0.1
% 2.77/1.00  --splitting_mode                        input
% 2.77/1.00  --splitting_grd                         true
% 2.77/1.00  --splitting_cvd                         false
% 2.77/1.00  --splitting_cvd_svl                     false
% 2.77/1.00  --splitting_nvd                         32
% 2.77/1.00  --sub_typing                            true
% 2.77/1.00  --prep_gs_sim                           true
% 2.77/1.00  --prep_unflatten                        true
% 2.77/1.00  --prep_res_sim                          true
% 2.77/1.00  --prep_upred                            true
% 2.77/1.00  --prep_sem_filter                       exhaustive
% 2.77/1.00  --prep_sem_filter_out                   false
% 2.77/1.00  --pred_elim                             true
% 2.77/1.00  --res_sim_input                         true
% 2.77/1.00  --eq_ax_congr_red                       true
% 2.77/1.00  --pure_diseq_elim                       true
% 2.77/1.00  --brand_transform                       false
% 2.77/1.00  --non_eq_to_eq                          false
% 2.77/1.00  --prep_def_merge                        true
% 2.77/1.00  --prep_def_merge_prop_impl              false
% 2.77/1.00  --prep_def_merge_mbd                    true
% 2.77/1.00  --prep_def_merge_tr_red                 false
% 2.77/1.00  --prep_def_merge_tr_cl                  false
% 2.77/1.00  --smt_preprocessing                     true
% 2.77/1.00  --smt_ac_axioms                         fast
% 2.77/1.00  --preprocessed_out                      false
% 2.77/1.00  --preprocessed_stats                    false
% 2.77/1.00  
% 2.77/1.00  ------ Abstraction refinement Options
% 2.77/1.00  
% 2.77/1.00  --abstr_ref                             []
% 2.77/1.00  --abstr_ref_prep                        false
% 2.77/1.00  --abstr_ref_until_sat                   false
% 2.77/1.00  --abstr_ref_sig_restrict                funpre
% 2.77/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.77/1.00  --abstr_ref_under                       []
% 2.77/1.00  
% 2.77/1.00  ------ SAT Options
% 2.77/1.00  
% 2.77/1.00  --sat_mode                              false
% 2.77/1.00  --sat_fm_restart_options                ""
% 2.77/1.00  --sat_gr_def                            false
% 2.77/1.00  --sat_epr_types                         true
% 2.77/1.00  --sat_non_cyclic_types                  false
% 2.77/1.00  --sat_finite_models                     false
% 2.77/1.00  --sat_fm_lemmas                         false
% 2.77/1.00  --sat_fm_prep                           false
% 2.77/1.00  --sat_fm_uc_incr                        true
% 2.77/1.00  --sat_out_model                         small
% 2.77/1.00  --sat_out_clauses                       false
% 2.77/1.00  
% 2.77/1.00  ------ QBF Options
% 2.77/1.00  
% 2.77/1.00  --qbf_mode                              false
% 2.77/1.00  --qbf_elim_univ                         false
% 2.77/1.00  --qbf_dom_inst                          none
% 2.77/1.00  --qbf_dom_pre_inst                      false
% 2.77/1.00  --qbf_sk_in                             false
% 2.77/1.00  --qbf_pred_elim                         true
% 2.77/1.00  --qbf_split                             512
% 2.77/1.00  
% 2.77/1.00  ------ BMC1 Options
% 2.77/1.00  
% 2.77/1.00  --bmc1_incremental                      false
% 2.77/1.00  --bmc1_axioms                           reachable_all
% 2.77/1.00  --bmc1_min_bound                        0
% 2.77/1.00  --bmc1_max_bound                        -1
% 2.77/1.00  --bmc1_max_bound_default                -1
% 2.77/1.00  --bmc1_symbol_reachability              true
% 2.77/1.00  --bmc1_property_lemmas                  false
% 2.77/1.00  --bmc1_k_induction                      false
% 2.77/1.00  --bmc1_non_equiv_states                 false
% 2.77/1.00  --bmc1_deadlock                         false
% 2.77/1.00  --bmc1_ucm                              false
% 2.77/1.00  --bmc1_add_unsat_core                   none
% 2.77/1.00  --bmc1_unsat_core_children              false
% 2.77/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.77/1.00  --bmc1_out_stat                         full
% 2.77/1.00  --bmc1_ground_init                      false
% 2.77/1.00  --bmc1_pre_inst_next_state              false
% 2.77/1.00  --bmc1_pre_inst_state                   false
% 2.77/1.00  --bmc1_pre_inst_reach_state             false
% 2.77/1.00  --bmc1_out_unsat_core                   false
% 2.77/1.00  --bmc1_aig_witness_out                  false
% 2.77/1.00  --bmc1_verbose                          false
% 2.77/1.00  --bmc1_dump_clauses_tptp                false
% 2.77/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.77/1.00  --bmc1_dump_file                        -
% 2.77/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.77/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.77/1.00  --bmc1_ucm_extend_mode                  1
% 2.77/1.00  --bmc1_ucm_init_mode                    2
% 2.77/1.00  --bmc1_ucm_cone_mode                    none
% 2.77/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.77/1.00  --bmc1_ucm_relax_model                  4
% 2.77/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.77/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.77/1.00  --bmc1_ucm_layered_model                none
% 2.77/1.00  --bmc1_ucm_max_lemma_size               10
% 2.77/1.00  
% 2.77/1.00  ------ AIG Options
% 2.77/1.00  
% 2.77/1.00  --aig_mode                              false
% 2.77/1.00  
% 2.77/1.00  ------ Instantiation Options
% 2.77/1.00  
% 2.77/1.00  --instantiation_flag                    true
% 2.77/1.00  --inst_sos_flag                         false
% 2.77/1.00  --inst_sos_phase                        true
% 2.77/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.77/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.77/1.00  --inst_lit_sel_side                     none
% 2.77/1.00  --inst_solver_per_active                1400
% 2.77/1.00  --inst_solver_calls_frac                1.
% 2.77/1.00  --inst_passive_queue_type               priority_queues
% 2.77/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.77/1.00  --inst_passive_queues_freq              [25;2]
% 2.77/1.00  --inst_dismatching                      true
% 2.77/1.00  --inst_eager_unprocessed_to_passive     true
% 2.77/1.00  --inst_prop_sim_given                   true
% 2.77/1.00  --inst_prop_sim_new                     false
% 2.77/1.00  --inst_subs_new                         false
% 2.77/1.00  --inst_eq_res_simp                      false
% 2.77/1.00  --inst_subs_given                       false
% 2.77/1.00  --inst_orphan_elimination               true
% 2.77/1.00  --inst_learning_loop_flag               true
% 2.77/1.00  --inst_learning_start                   3000
% 2.77/1.00  --inst_learning_factor                  2
% 2.77/1.00  --inst_start_prop_sim_after_learn       3
% 2.77/1.00  --inst_sel_renew                        solver
% 2.77/1.00  --inst_lit_activity_flag                true
% 2.77/1.00  --inst_restr_to_given                   false
% 2.77/1.00  --inst_activity_threshold               500
% 2.77/1.00  --inst_out_proof                        true
% 2.77/1.00  
% 2.77/1.00  ------ Resolution Options
% 2.77/1.00  
% 2.77/1.00  --resolution_flag                       false
% 2.77/1.00  --res_lit_sel                           adaptive
% 2.77/1.00  --res_lit_sel_side                      none
% 2.77/1.00  --res_ordering                          kbo
% 2.77/1.00  --res_to_prop_solver                    active
% 2.77/1.00  --res_prop_simpl_new                    false
% 2.77/1.00  --res_prop_simpl_given                  true
% 2.77/1.00  --res_passive_queue_type                priority_queues
% 2.77/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.77/1.00  --res_passive_queues_freq               [15;5]
% 2.77/1.00  --res_forward_subs                      full
% 2.77/1.00  --res_backward_subs                     full
% 2.77/1.00  --res_forward_subs_resolution           true
% 2.77/1.00  --res_backward_subs_resolution          true
% 2.77/1.00  --res_orphan_elimination                true
% 2.77/1.00  --res_time_limit                        2.
% 2.77/1.00  --res_out_proof                         true
% 2.77/1.00  
% 2.77/1.00  ------ Superposition Options
% 2.77/1.00  
% 2.77/1.00  --superposition_flag                    true
% 2.77/1.00  --sup_passive_queue_type                priority_queues
% 2.77/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.77/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.77/1.00  --demod_completeness_check              fast
% 2.77/1.00  --demod_use_ground                      true
% 2.77/1.00  --sup_to_prop_solver                    passive
% 2.77/1.00  --sup_prop_simpl_new                    true
% 2.77/1.00  --sup_prop_simpl_given                  true
% 2.77/1.00  --sup_fun_splitting                     false
% 2.77/1.00  --sup_smt_interval                      50000
% 2.77/1.00  
% 2.77/1.00  ------ Superposition Simplification Setup
% 2.77/1.00  
% 2.77/1.00  --sup_indices_passive                   []
% 2.77/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.77/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.77/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.77/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.77/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.77/1.00  --sup_full_bw                           [BwDemod]
% 2.77/1.00  --sup_immed_triv                        [TrivRules]
% 2.77/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.77/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.77/1.00  --sup_immed_bw_main                     []
% 2.77/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.77/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.77/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.77/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.77/1.00  
% 2.77/1.00  ------ Combination Options
% 2.77/1.00  
% 2.77/1.00  --comb_res_mult                         3
% 2.77/1.00  --comb_sup_mult                         2
% 2.77/1.00  --comb_inst_mult                        10
% 2.77/1.00  
% 2.77/1.00  ------ Debug Options
% 2.77/1.00  
% 2.77/1.00  --dbg_backtrace                         false
% 2.77/1.00  --dbg_dump_prop_clauses                 false
% 2.77/1.00  --dbg_dump_prop_clauses_file            -
% 2.77/1.00  --dbg_out_stat                          false
% 2.77/1.00  
% 2.77/1.00  
% 2.77/1.00  
% 2.77/1.00  
% 2.77/1.00  ------ Proving...
% 2.77/1.00  
% 2.77/1.00  
% 2.77/1.00  % SZS status Theorem for theBenchmark.p
% 2.77/1.00  
% 2.77/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.77/1.00  
% 2.77/1.00  fof(f13,axiom,(
% 2.77/1.00    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 2.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.77/1.00  
% 2.77/1.00  fof(f21,plain,(
% 2.77/1.00    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 2.77/1.00    inference(pure_predicate_removal,[],[f13])).
% 2.77/1.00  
% 2.77/1.00  fof(f38,plain,(
% 2.77/1.00    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.77/1.00    inference(ennf_transformation,[],[f21])).
% 2.77/1.00  
% 2.77/1.00  fof(f39,plain,(
% 2.77/1.00    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.77/1.00    inference(flattening,[],[f38])).
% 2.77/1.00  
% 2.77/1.00  fof(f83,plain,(
% 2.77/1.00    ( ! [X0,X1] : (m1_pre_topc(k1_tex_2(X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.77/1.00    inference(cnf_transformation,[],[f39])).
% 2.77/1.00  
% 2.77/1.00  fof(f11,axiom,(
% 2.77/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v1_subset_1(X2,u1_struct_0(X0)))))))),
% 2.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.77/1.00  
% 2.77/1.00  fof(f35,plain,(
% 2.77/1.00    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : ((v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.77/1.00    inference(ennf_transformation,[],[f11])).
% 2.77/1.00  
% 2.77/1.00  fof(f36,plain,(
% 2.77/1.00    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.77/1.00    inference(flattening,[],[f35])).
% 2.77/1.00  
% 2.77/1.00  fof(f54,plain,(
% 2.77/1.00    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.77/1.00    inference(nnf_transformation,[],[f36])).
% 2.77/1.00  
% 2.77/1.00  fof(f55,plain,(
% 2.77/1.00    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.77/1.00    inference(rectify,[],[f54])).
% 2.77/1.00  
% 2.77/1.00  fof(f56,plain,(
% 2.77/1.00    ! [X1,X0] : (? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_subset_1(sK1(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK1(X0,X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.77/1.00    introduced(choice_axiom,[])).
% 2.77/1.00  
% 2.77/1.00  fof(f57,plain,(
% 2.77/1.00    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | (~v1_subset_1(sK1(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK1(X0,X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.77/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f55,f56])).
% 2.77/1.00  
% 2.77/1.00  fof(f78,plain,(
% 2.77/1.00    ( ! [X0,X1] : (v1_tex_2(X1,X0) | u1_struct_0(X1) = sK1(X0,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.77/1.00    inference(cnf_transformation,[],[f57])).
% 2.77/1.00  
% 2.77/1.00  fof(f7,axiom,(
% 2.77/1.00    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.77/1.00  
% 2.77/1.00  fof(f30,plain,(
% 2.77/1.00    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.77/1.00    inference(ennf_transformation,[],[f7])).
% 2.77/1.00  
% 2.77/1.00  fof(f31,plain,(
% 2.77/1.00    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.77/1.00    inference(flattening,[],[f30])).
% 2.77/1.00  
% 2.77/1.00  fof(f70,plain,(
% 2.77/1.00    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.77/1.00    inference(cnf_transformation,[],[f31])).
% 2.77/1.00  
% 2.77/1.00  fof(f12,axiom,(
% 2.77/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 2.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.77/1.00  
% 2.77/1.00  fof(f37,plain,(
% 2.77/1.00    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.77/1.00    inference(ennf_transformation,[],[f12])).
% 2.77/1.00  
% 2.77/1.00  fof(f58,plain,(
% 2.77/1.00    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.77/1.00    inference(nnf_transformation,[],[f37])).
% 2.77/1.00  
% 2.77/1.00  fof(f81,plain,(
% 2.77/1.00    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.77/1.00    inference(cnf_transformation,[],[f58])).
% 2.77/1.00  
% 2.77/1.00  fof(f18,conjecture,(
% 2.77/1.00    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 2.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.77/1.00  
% 2.77/1.00  fof(f19,negated_conjecture,(
% 2.77/1.00    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 2.77/1.00    inference(negated_conjecture,[],[f18])).
% 2.77/1.00  
% 2.77/1.00  fof(f48,plain,(
% 2.77/1.00    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.77/1.00    inference(ennf_transformation,[],[f19])).
% 2.77/1.00  
% 2.77/1.00  fof(f49,plain,(
% 2.77/1.00    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.77/1.00    inference(flattening,[],[f48])).
% 2.77/1.00  
% 2.77/1.00  fof(f59,plain,(
% 2.77/1.00    ? [X0] : (? [X1] : (((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.77/1.00    inference(nnf_transformation,[],[f49])).
% 2.77/1.00  
% 2.77/1.00  fof(f60,plain,(
% 2.77/1.00    ? [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.77/1.00    inference(flattening,[],[f59])).
% 2.77/1.00  
% 2.77/1.00  fof(f62,plain,(
% 2.77/1.00    ( ! [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) => ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),sK3),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,sK3),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),sK3),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,sK3),X0)) & m1_subset_1(sK3,u1_struct_0(X0)))) )),
% 2.77/1.00    introduced(choice_axiom,[])).
% 2.77/1.00  
% 2.77/1.00  fof(f61,plain,(
% 2.77/1.00    ? [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(sK2),X1),u1_struct_0(sK2)) | ~v1_tex_2(k1_tex_2(sK2,X1),sK2)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK2),X1),u1_struct_0(sK2)) | v1_tex_2(k1_tex_2(sK2,X1),sK2)) & m1_subset_1(X1,u1_struct_0(sK2))) & l1_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 2.77/1.00    introduced(choice_axiom,[])).
% 2.77/1.00  
% 2.77/1.00  fof(f63,plain,(
% 2.77/1.00    ((~v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) | ~v1_tex_2(k1_tex_2(sK2,sK3),sK2)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) | v1_tex_2(k1_tex_2(sK2,sK3),sK2)) & m1_subset_1(sK3,u1_struct_0(sK2))) & l1_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 2.77/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f60,f62,f61])).
% 2.77/1.00  
% 2.77/1.00  fof(f93,plain,(
% 2.77/1.00    ~v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) | ~v1_tex_2(k1_tex_2(sK2,sK3),sK2)),
% 2.77/1.00    inference(cnf_transformation,[],[f63])).
% 2.77/1.00  
% 2.77/1.00  fof(f89,plain,(
% 2.77/1.00    ~v2_struct_0(sK2)),
% 2.77/1.00    inference(cnf_transformation,[],[f63])).
% 2.77/1.00  
% 2.77/1.00  fof(f90,plain,(
% 2.77/1.00    l1_pre_topc(sK2)),
% 2.77/1.00    inference(cnf_transformation,[],[f63])).
% 2.77/1.00  
% 2.77/1.00  fof(f91,plain,(
% 2.77/1.00    m1_subset_1(sK3,u1_struct_0(sK2))),
% 2.77/1.00    inference(cnf_transformation,[],[f63])).
% 2.77/1.00  
% 2.77/1.00  fof(f6,axiom,(
% 2.77/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.77/1.00  
% 2.77/1.00  fof(f28,plain,(
% 2.77/1.00    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.77/1.00    inference(ennf_transformation,[],[f6])).
% 2.77/1.00  
% 2.77/1.00  fof(f29,plain,(
% 2.77/1.00    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.77/1.00    inference(flattening,[],[f28])).
% 2.77/1.00  
% 2.77/1.00  fof(f69,plain,(
% 2.77/1.00    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.77/1.00    inference(cnf_transformation,[],[f29])).
% 2.77/1.00  
% 2.77/1.00  fof(f3,axiom,(
% 2.77/1.00    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.77/1.00  
% 2.77/1.00  fof(f24,plain,(
% 2.77/1.00    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.77/1.00    inference(ennf_transformation,[],[f3])).
% 2.77/1.00  
% 2.77/1.00  fof(f66,plain,(
% 2.77/1.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.77/1.00    inference(cnf_transformation,[],[f24])).
% 2.77/1.00  
% 2.77/1.00  fof(f77,plain,(
% 2.77/1.00    ( ! [X0,X1] : (v1_tex_2(X1,X0) | m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.77/1.00    inference(cnf_transformation,[],[f57])).
% 2.77/1.00  
% 2.77/1.00  fof(f79,plain,(
% 2.77/1.00    ( ! [X0,X1] : (v1_tex_2(X1,X0) | ~v1_subset_1(sK1(X0,X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.77/1.00    inference(cnf_transformation,[],[f57])).
% 2.77/1.00  
% 2.77/1.00  fof(f14,axiom,(
% 2.77/1.00    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 2.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.77/1.00  
% 2.77/1.00  fof(f20,plain,(
% 2.77/1.00    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 2.77/1.00    inference(pure_predicate_removal,[],[f14])).
% 2.77/1.00  
% 2.77/1.00  fof(f40,plain,(
% 2.77/1.00    ! [X0,X1] : ((v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.77/1.00    inference(ennf_transformation,[],[f20])).
% 2.77/1.00  
% 2.77/1.00  fof(f41,plain,(
% 2.77/1.00    ! [X0,X1] : ((v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.77/1.00    inference(flattening,[],[f40])).
% 2.77/1.00  
% 2.77/1.00  fof(f84,plain,(
% 2.77/1.00    ( ! [X0,X1] : (~v2_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.77/1.00    inference(cnf_transformation,[],[f41])).
% 2.77/1.00  
% 2.77/1.00  fof(f10,axiom,(
% 2.77/1.00    ! [X0] : (~v1_xboole_0(X0) => (v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))))),
% 2.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.77/1.00  
% 2.77/1.00  fof(f34,plain,(
% 2.77/1.00    ! [X0] : ((v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))) | v1_xboole_0(X0))),
% 2.77/1.00    inference(ennf_transformation,[],[f10])).
% 2.77/1.00  
% 2.77/1.00  fof(f50,plain,(
% 2.77/1.00    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 2.77/1.00    inference(nnf_transformation,[],[f34])).
% 2.77/1.00  
% 2.77/1.00  fof(f51,plain,(
% 2.77/1.00    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 2.77/1.00    inference(rectify,[],[f50])).
% 2.77/1.00  
% 2.77/1.00  fof(f52,plain,(
% 2.77/1.00    ! [X0] : (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) => (k6_domain_1(X0,sK0(X0)) = X0 & m1_subset_1(sK0(X0),X0)))),
% 2.77/1.00    introduced(choice_axiom,[])).
% 2.77/1.00  
% 2.77/1.00  fof(f53,plain,(
% 2.77/1.00    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & ((k6_domain_1(X0,sK0(X0)) = X0 & m1_subset_1(sK0(X0),X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 2.77/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f51,f52])).
% 2.77/1.00  
% 2.77/1.00  fof(f75,plain,(
% 2.77/1.00    ( ! [X0,X1] : (v1_zfmisc_1(X0) | k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.77/1.00    inference(cnf_transformation,[],[f53])).
% 2.77/1.00  
% 2.77/1.00  fof(f15,axiom,(
% 2.77/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ~(v1_tex_2(X1,X0) & u1_struct_0(X0) = u1_struct_0(X1))))),
% 2.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.77/1.00  
% 2.77/1.00  fof(f42,plain,(
% 2.77/1.00    ! [X0] : (! [X1] : ((~v1_tex_2(X1,X0) | u1_struct_0(X0) != u1_struct_0(X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.77/1.00    inference(ennf_transformation,[],[f15])).
% 2.77/1.00  
% 2.77/1.00  fof(f43,plain,(
% 2.77/1.00    ! [X0] : (! [X1] : (~v1_tex_2(X1,X0) | u1_struct_0(X0) != u1_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.77/1.00    inference(flattening,[],[f42])).
% 2.77/1.00  
% 2.77/1.00  fof(f86,plain,(
% 2.77/1.00    ( ! [X0,X1] : (~v1_tex_2(X1,X0) | u1_struct_0(X0) != u1_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.77/1.00    inference(cnf_transformation,[],[f43])).
% 2.77/1.00  
% 2.77/1.00  fof(f4,axiom,(
% 2.77/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.77/1.00  
% 2.77/1.00  fof(f25,plain,(
% 2.77/1.00    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.77/1.00    inference(ennf_transformation,[],[f4])).
% 2.77/1.00  
% 2.77/1.00  fof(f67,plain,(
% 2.77/1.00    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.77/1.00    inference(cnf_transformation,[],[f25])).
% 2.77/1.00  
% 2.77/1.00  fof(f9,axiom,(
% 2.77/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))),
% 2.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.77/1.00  
% 2.77/1.00  fof(f33,plain,(
% 2.77/1.00    ! [X0] : (! [X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.77/1.00    inference(ennf_transformation,[],[f9])).
% 2.77/1.00  
% 2.77/1.00  fof(f72,plain,(
% 2.77/1.00    ( ! [X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.77/1.00    inference(cnf_transformation,[],[f33])).
% 2.77/1.00  
% 2.77/1.00  fof(f16,axiom,(
% 2.77/1.00    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 2.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.77/1.00  
% 2.77/1.00  fof(f44,plain,(
% 2.77/1.00    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 2.77/1.00    inference(ennf_transformation,[],[f16])).
% 2.77/1.00  
% 2.77/1.00  fof(f45,plain,(
% 2.77/1.00    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.77/1.00    inference(flattening,[],[f44])).
% 2.77/1.00  
% 2.77/1.00  fof(f87,plain,(
% 2.77/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.77/1.00    inference(cnf_transformation,[],[f45])).
% 2.77/1.00  
% 2.77/1.00  fof(f8,axiom,(
% 2.77/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.77/1.00  
% 2.77/1.00  fof(f32,plain,(
% 2.77/1.00    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.77/1.00    inference(ennf_transformation,[],[f8])).
% 2.77/1.00  
% 2.77/1.00  fof(f71,plain,(
% 2.77/1.00    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.77/1.00    inference(cnf_transformation,[],[f32])).
% 2.77/1.00  
% 2.77/1.00  fof(f2,axiom,(
% 2.77/1.00    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 2.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.77/1.00  
% 2.77/1.00  fof(f23,plain,(
% 2.77/1.00    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 2.77/1.00    inference(ennf_transformation,[],[f2])).
% 2.77/1.00  
% 2.77/1.00  fof(f65,plain,(
% 2.77/1.00    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 2.77/1.00    inference(cnf_transformation,[],[f23])).
% 2.77/1.00  
% 2.77/1.00  fof(f17,axiom,(
% 2.77/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~(v7_struct_0(X0) & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 2.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.77/1.00  
% 2.77/1.00  fof(f46,plain,(
% 2.77/1.00    ! [X0] : (! [X1] : ((~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.77/1.00    inference(ennf_transformation,[],[f17])).
% 2.77/1.00  
% 2.77/1.00  fof(f47,plain,(
% 2.77/1.00    ! [X0] : (! [X1] : (~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.77/1.00    inference(flattening,[],[f46])).
% 2.77/1.00  
% 2.77/1.00  fof(f88,plain,(
% 2.77/1.00    ( ! [X0,X1] : (~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.77/1.00    inference(cnf_transformation,[],[f47])).
% 2.77/1.00  
% 2.77/1.00  fof(f85,plain,(
% 2.77/1.00    ( ! [X0,X1] : (v7_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.77/1.00    inference(cnf_transformation,[],[f41])).
% 2.77/1.00  
% 2.77/1.00  fof(f92,plain,(
% 2.77/1.00    v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) | v1_tex_2(k1_tex_2(sK2,sK3),sK2)),
% 2.77/1.00    inference(cnf_transformation,[],[f63])).
% 2.77/1.00  
% 2.77/1.00  cnf(c_18,plain,
% 2.77/1.00      ( m1_pre_topc(k1_tex_2(X0,X1),X0)
% 2.77/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.77/1.00      | v2_struct_0(X0)
% 2.77/1.00      | ~ l1_pre_topc(X0) ),
% 2.77/1.00      inference(cnf_transformation,[],[f83]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_2402,plain,
% 2.77/1.00      ( m1_pre_topc(k1_tex_2(X0_47,X0_48),X0_47)
% 2.77/1.00      | ~ m1_subset_1(X0_48,u1_struct_0(X0_47))
% 2.77/1.00      | v2_struct_0(X0_47)
% 2.77/1.00      | ~ l1_pre_topc(X0_47) ),
% 2.77/1.00      inference(subtyping,[status(esa)],[c_18]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_3156,plain,
% 2.77/1.00      ( m1_pre_topc(k1_tex_2(X0_47,X0_48),X0_47) = iProver_top
% 2.77/1.00      | m1_subset_1(X0_48,u1_struct_0(X0_47)) != iProver_top
% 2.77/1.00      | v2_struct_0(X0_47) = iProver_top
% 2.77/1.00      | l1_pre_topc(X0_47) != iProver_top ),
% 2.77/1.00      inference(predicate_to_equality,[status(thm)],[c_2402]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_13,plain,
% 2.77/1.00      ( v1_tex_2(X0,X1)
% 2.77/1.00      | ~ m1_pre_topc(X0,X1)
% 2.77/1.00      | ~ l1_pre_topc(X1)
% 2.77/1.00      | sK1(X1,X0) = u1_struct_0(X0) ),
% 2.77/1.00      inference(cnf_transformation,[],[f78]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_2406,plain,
% 2.77/1.00      ( v1_tex_2(X0_47,X1_47)
% 2.77/1.00      | ~ m1_pre_topc(X0_47,X1_47)
% 2.77/1.00      | ~ l1_pre_topc(X1_47)
% 2.77/1.00      | sK1(X1_47,X0_47) = u1_struct_0(X0_47) ),
% 2.77/1.00      inference(subtyping,[status(esa)],[c_13]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_3152,plain,
% 2.77/1.00      ( sK1(X0_47,X1_47) = u1_struct_0(X1_47)
% 2.77/1.00      | v1_tex_2(X1_47,X0_47) = iProver_top
% 2.77/1.00      | m1_pre_topc(X1_47,X0_47) != iProver_top
% 2.77/1.00      | l1_pre_topc(X0_47) != iProver_top ),
% 2.77/1.00      inference(predicate_to_equality,[status(thm)],[c_2406]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_4127,plain,
% 2.77/1.00      ( sK1(X0_47,k1_tex_2(X0_47,X0_48)) = u1_struct_0(k1_tex_2(X0_47,X0_48))
% 2.77/1.00      | v1_tex_2(k1_tex_2(X0_47,X0_48),X0_47) = iProver_top
% 2.77/1.00      | m1_subset_1(X0_48,u1_struct_0(X0_47)) != iProver_top
% 2.77/1.00      | v2_struct_0(X0_47) = iProver_top
% 2.77/1.00      | l1_pre_topc(X0_47) != iProver_top ),
% 2.77/1.00      inference(superposition,[status(thm)],[c_3156,c_3152]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_6,plain,
% 2.77/1.00      ( ~ m1_subset_1(X0,X1)
% 2.77/1.00      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
% 2.77/1.00      | v1_xboole_0(X1) ),
% 2.77/1.00      inference(cnf_transformation,[],[f70]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_2412,plain,
% 2.77/1.00      ( ~ m1_subset_1(X0_48,X1_48)
% 2.77/1.00      | m1_subset_1(k6_domain_1(X1_48,X0_48),k1_zfmisc_1(X1_48))
% 2.77/1.00      | v1_xboole_0(X1_48) ),
% 2.77/1.00      inference(subtyping,[status(esa)],[c_6]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_3146,plain,
% 2.77/1.00      ( m1_subset_1(X0_48,X1_48) != iProver_top
% 2.77/1.00      | m1_subset_1(k6_domain_1(X1_48,X0_48),k1_zfmisc_1(X1_48)) = iProver_top
% 2.77/1.00      | v1_xboole_0(X1_48) = iProver_top ),
% 2.77/1.00      inference(predicate_to_equality,[status(thm)],[c_2412]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_16,plain,
% 2.77/1.00      ( v1_subset_1(X0,X1)
% 2.77/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.77/1.00      | X0 = X1 ),
% 2.77/1.00      inference(cnf_transformation,[],[f81]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_2404,plain,
% 2.77/1.00      ( v1_subset_1(X0_48,X1_48)
% 2.77/1.00      | ~ m1_subset_1(X0_48,k1_zfmisc_1(X1_48))
% 2.77/1.00      | X0_48 = X1_48 ),
% 2.77/1.00      inference(subtyping,[status(esa)],[c_16]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_3154,plain,
% 2.77/1.00      ( X0_48 = X1_48
% 2.77/1.00      | v1_subset_1(X0_48,X1_48) = iProver_top
% 2.77/1.00      | m1_subset_1(X0_48,k1_zfmisc_1(X1_48)) != iProver_top ),
% 2.77/1.00      inference(predicate_to_equality,[status(thm)],[c_2404]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_3998,plain,
% 2.77/1.00      ( k6_domain_1(X0_48,X1_48) = X0_48
% 2.77/1.00      | v1_subset_1(k6_domain_1(X0_48,X1_48),X0_48) = iProver_top
% 2.77/1.00      | m1_subset_1(X1_48,X0_48) != iProver_top
% 2.77/1.00      | v1_xboole_0(X0_48) = iProver_top ),
% 2.77/1.00      inference(superposition,[status(thm)],[c_3146,c_3154]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_25,negated_conjecture,
% 2.77/1.00      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 2.77/1.00      | ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2) ),
% 2.77/1.00      inference(cnf_transformation,[],[f93]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_2398,negated_conjecture,
% 2.77/1.00      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 2.77/1.00      | ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2) ),
% 2.77/1.00      inference(subtyping,[status(esa)],[c_25]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_3160,plain,
% 2.77/1.00      ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) != iProver_top
% 2.77/1.00      | v1_tex_2(k1_tex_2(sK2,sK3),sK2) != iProver_top ),
% 2.77/1.00      inference(predicate_to_equality,[status(thm)],[c_2398]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_4759,plain,
% 2.77/1.00      ( k6_domain_1(u1_struct_0(sK2),sK3) = u1_struct_0(sK2)
% 2.77/1.00      | v1_tex_2(k1_tex_2(sK2,sK3),sK2) != iProver_top
% 2.77/1.00      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 2.77/1.00      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 2.77/1.00      inference(superposition,[status(thm)],[c_3998,c_3160]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_29,negated_conjecture,
% 2.77/1.00      ( ~ v2_struct_0(sK2) ),
% 2.77/1.00      inference(cnf_transformation,[],[f89]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_30,plain,
% 2.77/1.00      ( v2_struct_0(sK2) != iProver_top ),
% 2.77/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_28,negated_conjecture,
% 2.77/1.00      ( l1_pre_topc(sK2) ),
% 2.77/1.00      inference(cnf_transformation,[],[f90]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_31,plain,
% 2.77/1.00      ( l1_pre_topc(sK2) = iProver_top ),
% 2.77/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_27,negated_conjecture,
% 2.77/1.00      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 2.77/1.00      inference(cnf_transformation,[],[f91]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_32,plain,
% 2.77/1.00      ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
% 2.77/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_5,plain,
% 2.77/1.00      ( v2_struct_0(X0)
% 2.77/1.00      | ~ l1_struct_0(X0)
% 2.77/1.00      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.77/1.00      inference(cnf_transformation,[],[f69]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_90,plain,
% 2.77/1.00      ( v2_struct_0(X0) = iProver_top
% 2.77/1.00      | l1_struct_0(X0) != iProver_top
% 2.77/1.00      | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
% 2.77/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_92,plain,
% 2.77/1.00      ( v2_struct_0(sK2) = iProver_top
% 2.77/1.00      | l1_struct_0(sK2) != iProver_top
% 2.77/1.00      | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 2.77/1.00      inference(instantiation,[status(thm)],[c_90]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_2,plain,
% 2.77/1.00      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 2.77/1.00      inference(cnf_transformation,[],[f66]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_95,plain,
% 2.77/1.00      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 2.77/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_97,plain,
% 2.77/1.00      ( l1_pre_topc(sK2) != iProver_top
% 2.77/1.00      | l1_struct_0(sK2) = iProver_top ),
% 2.77/1.00      inference(instantiation,[status(thm)],[c_95]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_5001,plain,
% 2.77/1.00      ( k6_domain_1(u1_struct_0(sK2),sK3) = u1_struct_0(sK2)
% 2.77/1.00      | v1_tex_2(k1_tex_2(sK2,sK3),sK2) != iProver_top ),
% 2.77/1.00      inference(global_propositional_subsumption,
% 2.77/1.00                [status(thm)],
% 2.77/1.00                [c_4759,c_30,c_31,c_32,c_92,c_97]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_5756,plain,
% 2.77/1.00      ( sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(k1_tex_2(sK2,sK3))
% 2.77/1.00      | k6_domain_1(u1_struct_0(sK2),sK3) = u1_struct_0(sK2)
% 2.77/1.00      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 2.77/1.00      | v2_struct_0(sK2) = iProver_top
% 2.77/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 2.77/1.00      inference(superposition,[status(thm)],[c_4127,c_5001]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_14,plain,
% 2.77/1.00      ( v1_tex_2(X0,X1)
% 2.77/1.00      | ~ m1_pre_topc(X0,X1)
% 2.77/1.00      | m1_subset_1(sK1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.77/1.00      | ~ l1_pre_topc(X1) ),
% 2.77/1.00      inference(cnf_transformation,[],[f77]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_2405,plain,
% 2.77/1.00      ( v1_tex_2(X0_47,X1_47)
% 2.77/1.00      | ~ m1_pre_topc(X0_47,X1_47)
% 2.77/1.00      | m1_subset_1(sK1(X1_47,X0_47),k1_zfmisc_1(u1_struct_0(X1_47)))
% 2.77/1.00      | ~ l1_pre_topc(X1_47) ),
% 2.77/1.00      inference(subtyping,[status(esa)],[c_14]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_3153,plain,
% 2.77/1.00      ( v1_tex_2(X0_47,X1_47) = iProver_top
% 2.77/1.00      | m1_pre_topc(X0_47,X1_47) != iProver_top
% 2.77/1.00      | m1_subset_1(sK1(X1_47,X0_47),k1_zfmisc_1(u1_struct_0(X1_47))) = iProver_top
% 2.77/1.00      | l1_pre_topc(X1_47) != iProver_top ),
% 2.77/1.00      inference(predicate_to_equality,[status(thm)],[c_2405]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_4607,plain,
% 2.77/1.00      ( sK1(X0_47,X1_47) = u1_struct_0(X0_47)
% 2.77/1.00      | v1_subset_1(sK1(X0_47,X1_47),u1_struct_0(X0_47)) = iProver_top
% 2.77/1.00      | v1_tex_2(X1_47,X0_47) = iProver_top
% 2.77/1.00      | m1_pre_topc(X1_47,X0_47) != iProver_top
% 2.77/1.00      | l1_pre_topc(X0_47) != iProver_top ),
% 2.77/1.00      inference(superposition,[status(thm)],[c_3153,c_3154]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_12,plain,
% 2.77/1.00      ( ~ v1_subset_1(sK1(X0,X1),u1_struct_0(X0))
% 2.77/1.00      | v1_tex_2(X1,X0)
% 2.77/1.00      | ~ m1_pre_topc(X1,X0)
% 2.77/1.00      | ~ l1_pre_topc(X0) ),
% 2.77/1.00      inference(cnf_transformation,[],[f79]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_2407,plain,
% 2.77/1.00      ( ~ v1_subset_1(sK1(X0_47,X1_47),u1_struct_0(X0_47))
% 2.77/1.00      | v1_tex_2(X1_47,X0_47)
% 2.77/1.00      | ~ m1_pre_topc(X1_47,X0_47)
% 2.77/1.00      | ~ l1_pre_topc(X0_47) ),
% 2.77/1.00      inference(subtyping,[status(esa)],[c_12]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_2467,plain,
% 2.77/1.00      ( v1_subset_1(sK1(X0_47,X1_47),u1_struct_0(X0_47)) != iProver_top
% 2.77/1.00      | v1_tex_2(X1_47,X0_47) = iProver_top
% 2.77/1.00      | m1_pre_topc(X1_47,X0_47) != iProver_top
% 2.77/1.00      | l1_pre_topc(X0_47) != iProver_top ),
% 2.77/1.00      inference(predicate_to_equality,[status(thm)],[c_2407]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_5548,plain,
% 2.77/1.00      ( sK1(X0_47,X1_47) = u1_struct_0(X0_47)
% 2.77/1.00      | v1_tex_2(X1_47,X0_47) = iProver_top
% 2.77/1.00      | m1_pre_topc(X1_47,X0_47) != iProver_top
% 2.77/1.00      | l1_pre_topc(X0_47) != iProver_top ),
% 2.77/1.00      inference(global_propositional_subsumption,
% 2.77/1.00                [status(thm)],
% 2.77/1.00                [c_4607,c_2467]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_5556,plain,
% 2.77/1.00      ( sK1(X0_47,k1_tex_2(X0_47,X0_48)) = u1_struct_0(X0_47)
% 2.77/1.00      | v1_tex_2(k1_tex_2(X0_47,X0_48),X0_47) = iProver_top
% 2.77/1.00      | m1_subset_1(X0_48,u1_struct_0(X0_47)) != iProver_top
% 2.77/1.00      | v2_struct_0(X0_47) = iProver_top
% 2.77/1.00      | l1_pre_topc(X0_47) != iProver_top ),
% 2.77/1.00      inference(superposition,[status(thm)],[c_3156,c_5548]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_5566,plain,
% 2.77/1.00      ( sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(sK2)
% 2.77/1.00      | k6_domain_1(u1_struct_0(sK2),sK3) = u1_struct_0(sK2)
% 2.77/1.00      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 2.77/1.00      | v2_struct_0(sK2) = iProver_top
% 2.77/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 2.77/1.00      inference(superposition,[status(thm)],[c_5556,c_5001]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_91,plain,
% 2.77/1.00      ( v2_struct_0(sK2)
% 2.77/1.00      | ~ l1_struct_0(sK2)
% 2.77/1.00      | ~ v1_xboole_0(u1_struct_0(sK2)) ),
% 2.77/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_96,plain,
% 2.77/1.00      ( ~ l1_pre_topc(sK2) | l1_struct_0(sK2) ),
% 2.77/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_2477,plain,
% 2.77/1.00      ( m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
% 2.77/1.00      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 2.77/1.00      | v2_struct_0(sK2)
% 2.77/1.00      | ~ l1_pre_topc(sK2) ),
% 2.77/1.00      inference(instantiation,[status(thm)],[c_2402]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_21,plain,
% 2.77/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.77/1.00      | v2_struct_0(X1)
% 2.77/1.00      | ~ v2_struct_0(k1_tex_2(X1,X0))
% 2.77/1.00      | ~ l1_pre_topc(X1) ),
% 2.77/1.00      inference(cnf_transformation,[],[f84]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_2401,plain,
% 2.77/1.00      ( ~ m1_subset_1(X0_48,u1_struct_0(X0_47))
% 2.77/1.00      | v2_struct_0(X0_47)
% 2.77/1.00      | ~ v2_struct_0(k1_tex_2(X0_47,X0_48))
% 2.77/1.00      | ~ l1_pre_topc(X0_47) ),
% 2.77/1.00      inference(subtyping,[status(esa)],[c_21]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_2480,plain,
% 2.77/1.00      ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 2.77/1.00      | ~ v2_struct_0(k1_tex_2(sK2,sK3))
% 2.77/1.00      | v2_struct_0(sK2)
% 2.77/1.00      | ~ l1_pre_topc(sK2) ),
% 2.77/1.00      inference(instantiation,[status(thm)],[c_2401]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_9,plain,
% 2.77/1.00      ( ~ m1_subset_1(X0,X1)
% 2.77/1.00      | v1_xboole_0(X1)
% 2.77/1.00      | v1_zfmisc_1(X1)
% 2.77/1.00      | k6_domain_1(X1,X0) != X1 ),
% 2.77/1.00      inference(cnf_transformation,[],[f75]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_2410,plain,
% 2.77/1.00      ( ~ m1_subset_1(X0_48,X1_48)
% 2.77/1.00      | v1_xboole_0(X1_48)
% 2.77/1.00      | v1_zfmisc_1(X1_48)
% 2.77/1.00      | k6_domain_1(X1_48,X0_48) != X1_48 ),
% 2.77/1.00      inference(subtyping,[status(esa)],[c_9]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_3422,plain,
% 2.77/1.00      ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 2.77/1.00      | v1_xboole_0(u1_struct_0(sK2))
% 2.77/1.00      | v1_zfmisc_1(u1_struct_0(sK2))
% 2.77/1.00      | k6_domain_1(u1_struct_0(sK2),sK3) != u1_struct_0(sK2) ),
% 2.77/1.00      inference(instantiation,[status(thm)],[c_2410]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_22,plain,
% 2.77/1.00      ( ~ v1_tex_2(X0,X1)
% 2.77/1.00      | ~ m1_pre_topc(X0,X1)
% 2.77/1.00      | ~ l1_pre_topc(X1)
% 2.77/1.00      | u1_struct_0(X0) != u1_struct_0(X1) ),
% 2.77/1.00      inference(cnf_transformation,[],[f86]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_2399,plain,
% 2.77/1.00      ( ~ v1_tex_2(X0_47,X1_47)
% 2.77/1.00      | ~ m1_pre_topc(X0_47,X1_47)
% 2.77/1.00      | ~ l1_pre_topc(X1_47)
% 2.77/1.00      | u1_struct_0(X0_47) != u1_struct_0(X1_47) ),
% 2.77/1.00      inference(subtyping,[status(esa)],[c_22]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_3512,plain,
% 2.77/1.00      ( ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2)
% 2.77/1.00      | ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
% 2.77/1.00      | ~ l1_pre_topc(sK2)
% 2.77/1.00      | u1_struct_0(k1_tex_2(sK2,sK3)) != u1_struct_0(sK2) ),
% 2.77/1.00      inference(instantiation,[status(thm)],[c_2399]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_3,plain,
% 2.77/1.00      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.77/1.00      inference(cnf_transformation,[],[f67]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_2413,plain,
% 2.77/1.00      ( ~ m1_pre_topc(X0_47,X1_47)
% 2.77/1.00      | ~ l1_pre_topc(X1_47)
% 2.77/1.00      | l1_pre_topc(X0_47) ),
% 2.77/1.00      inference(subtyping,[status(esa)],[c_3]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_3568,plain,
% 2.77/1.00      ( ~ m1_pre_topc(k1_tex_2(X0_47,X0_48),X1_47)
% 2.77/1.00      | ~ l1_pre_topc(X1_47)
% 2.77/1.00      | l1_pre_topc(k1_tex_2(X0_47,X0_48)) ),
% 2.77/1.00      inference(instantiation,[status(thm)],[c_2413]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_3570,plain,
% 2.77/1.00      ( ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
% 2.77/1.00      | l1_pre_topc(k1_tex_2(sK2,sK3))
% 2.77/1.00      | ~ l1_pre_topc(sK2) ),
% 2.77/1.00      inference(instantiation,[status(thm)],[c_3568]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_483,plain,
% 2.77/1.00      ( v2_struct_0(X0)
% 2.77/1.00      | ~ l1_pre_topc(X0)
% 2.77/1.00      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.77/1.00      inference(resolution,[status(thm)],[c_2,c_5]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_2390,plain,
% 2.77/1.00      ( v2_struct_0(X0_47)
% 2.77/1.00      | ~ l1_pre_topc(X0_47)
% 2.77/1.00      | ~ v1_xboole_0(u1_struct_0(X0_47)) ),
% 2.77/1.00      inference(subtyping,[status(esa)],[c_483]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_3943,plain,
% 2.77/1.00      ( v2_struct_0(k1_tex_2(sK2,sK3))
% 2.77/1.00      | ~ l1_pre_topc(k1_tex_2(sK2,sK3))
% 2.77/1.00      | ~ v1_xboole_0(u1_struct_0(k1_tex_2(sK2,sK3))) ),
% 2.77/1.00      inference(instantiation,[status(thm)],[c_2390]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_8,plain,
% 2.77/1.00      ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 2.77/1.00      | ~ m1_pre_topc(X0,X1)
% 2.77/1.00      | ~ l1_pre_topc(X1) ),
% 2.77/1.00      inference(cnf_transformation,[],[f72]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_23,plain,
% 2.77/1.00      ( ~ r1_tarski(X0,X1)
% 2.77/1.00      | v1_xboole_0(X0)
% 2.77/1.00      | v1_xboole_0(X1)
% 2.77/1.00      | ~ v1_zfmisc_1(X1)
% 2.77/1.00      | X1 = X0 ),
% 2.77/1.00      inference(cnf_transformation,[],[f87]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_397,plain,
% 2.77/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.77/1.00      | ~ l1_pre_topc(X1)
% 2.77/1.00      | v1_xboole_0(X2)
% 2.77/1.00      | v1_xboole_0(X3)
% 2.77/1.00      | ~ v1_zfmisc_1(X3)
% 2.77/1.00      | X3 = X2
% 2.77/1.00      | u1_struct_0(X0) != X2
% 2.77/1.00      | u1_struct_0(X1) != X3 ),
% 2.77/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_23]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_398,plain,
% 2.77/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.77/1.00      | ~ l1_pre_topc(X1)
% 2.77/1.00      | v1_xboole_0(u1_struct_0(X0))
% 2.77/1.00      | v1_xboole_0(u1_struct_0(X1))
% 2.77/1.00      | ~ v1_zfmisc_1(u1_struct_0(X1))
% 2.77/1.00      | u1_struct_0(X1) = u1_struct_0(X0) ),
% 2.77/1.00      inference(unflattening,[status(thm)],[c_397]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_2392,plain,
% 2.77/1.00      ( ~ m1_pre_topc(X0_47,X1_47)
% 2.77/1.00      | ~ l1_pre_topc(X1_47)
% 2.77/1.00      | v1_xboole_0(u1_struct_0(X0_47))
% 2.77/1.00      | v1_xboole_0(u1_struct_0(X1_47))
% 2.77/1.00      | ~ v1_zfmisc_1(u1_struct_0(X1_47))
% 2.77/1.00      | u1_struct_0(X1_47) = u1_struct_0(X0_47) ),
% 2.77/1.00      inference(subtyping,[status(esa)],[c_398]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_3166,plain,
% 2.77/1.00      ( u1_struct_0(X0_47) = u1_struct_0(X1_47)
% 2.77/1.00      | m1_pre_topc(X1_47,X0_47) != iProver_top
% 2.77/1.00      | l1_pre_topc(X0_47) != iProver_top
% 2.77/1.00      | v1_xboole_0(u1_struct_0(X1_47)) = iProver_top
% 2.77/1.00      | v1_xboole_0(u1_struct_0(X0_47)) = iProver_top
% 2.77/1.00      | v1_zfmisc_1(u1_struct_0(X0_47)) != iProver_top ),
% 2.77/1.00      inference(predicate_to_equality,[status(thm)],[c_2392]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_7,plain,
% 2.77/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.77/1.00      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.77/1.00      | ~ l1_pre_topc(X1) ),
% 2.77/1.00      inference(cnf_transformation,[],[f71]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_2411,plain,
% 2.77/1.00      ( ~ m1_pre_topc(X0_47,X1_47)
% 2.77/1.00      | m1_subset_1(u1_struct_0(X0_47),k1_zfmisc_1(u1_struct_0(X1_47)))
% 2.77/1.00      | ~ l1_pre_topc(X1_47) ),
% 2.77/1.00      inference(subtyping,[status(esa)],[c_7]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_3147,plain,
% 2.77/1.00      ( m1_pre_topc(X0_47,X1_47) != iProver_top
% 2.77/1.00      | m1_subset_1(u1_struct_0(X0_47),k1_zfmisc_1(u1_struct_0(X1_47))) = iProver_top
% 2.77/1.00      | l1_pre_topc(X1_47) != iProver_top ),
% 2.77/1.00      inference(predicate_to_equality,[status(thm)],[c_2411]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_1,plain,
% 2.77/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.77/1.00      | ~ v1_xboole_0(X1)
% 2.77/1.00      | v1_xboole_0(X0) ),
% 2.77/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_2414,plain,
% 2.77/1.00      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(X1_48))
% 2.77/1.00      | ~ v1_xboole_0(X1_48)
% 2.77/1.00      | v1_xboole_0(X0_48) ),
% 2.77/1.00      inference(subtyping,[status(esa)],[c_1]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_3144,plain,
% 2.77/1.00      ( m1_subset_1(X0_48,k1_zfmisc_1(X1_48)) != iProver_top
% 2.77/1.00      | v1_xboole_0(X1_48) != iProver_top
% 2.77/1.00      | v1_xboole_0(X0_48) = iProver_top ),
% 2.77/1.00      inference(predicate_to_equality,[status(thm)],[c_2414]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_3821,plain,
% 2.77/1.00      ( m1_pre_topc(X0_47,X1_47) != iProver_top
% 2.77/1.00      | l1_pre_topc(X1_47) != iProver_top
% 2.77/1.00      | v1_xboole_0(u1_struct_0(X1_47)) != iProver_top
% 2.77/1.00      | v1_xboole_0(u1_struct_0(X0_47)) = iProver_top ),
% 2.77/1.00      inference(superposition,[status(thm)],[c_3147,c_3144]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_5380,plain,
% 2.77/1.00      ( u1_struct_0(X0_47) = u1_struct_0(X1_47)
% 2.77/1.00      | m1_pre_topc(X0_47,X1_47) != iProver_top
% 2.77/1.00      | l1_pre_topc(X1_47) != iProver_top
% 2.77/1.00      | v1_xboole_0(u1_struct_0(X0_47)) = iProver_top
% 2.77/1.00      | v1_zfmisc_1(u1_struct_0(X1_47)) != iProver_top ),
% 2.77/1.00      inference(forward_subsumption_resolution,
% 2.77/1.00                [status(thm)],
% 2.77/1.00                [c_3166,c_3821]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_5382,plain,
% 2.77/1.00      ( u1_struct_0(k1_tex_2(X0_47,X0_48)) = u1_struct_0(X0_47)
% 2.77/1.00      | m1_subset_1(X0_48,u1_struct_0(X0_47)) != iProver_top
% 2.77/1.00      | v2_struct_0(X0_47) = iProver_top
% 2.77/1.00      | l1_pre_topc(X0_47) != iProver_top
% 2.77/1.00      | v1_xboole_0(u1_struct_0(k1_tex_2(X0_47,X0_48))) = iProver_top
% 2.77/1.00      | v1_zfmisc_1(u1_struct_0(X0_47)) != iProver_top ),
% 2.77/1.00      inference(superposition,[status(thm)],[c_3156,c_5380]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_5383,plain,
% 2.77/1.00      ( ~ m1_subset_1(X0_48,u1_struct_0(X0_47))
% 2.77/1.00      | v2_struct_0(X0_47)
% 2.77/1.00      | ~ l1_pre_topc(X0_47)
% 2.77/1.00      | v1_xboole_0(u1_struct_0(k1_tex_2(X0_47,X0_48)))
% 2.77/1.00      | ~ v1_zfmisc_1(u1_struct_0(X0_47))
% 2.77/1.00      | u1_struct_0(k1_tex_2(X0_47,X0_48)) = u1_struct_0(X0_47) ),
% 2.77/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_5382]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_5385,plain,
% 2.77/1.00      ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 2.77/1.00      | v2_struct_0(sK2)
% 2.77/1.00      | ~ l1_pre_topc(sK2)
% 2.77/1.00      | v1_xboole_0(u1_struct_0(k1_tex_2(sK2,sK3)))
% 2.77/1.00      | ~ v1_zfmisc_1(u1_struct_0(sK2))
% 2.77/1.00      | u1_struct_0(k1_tex_2(sK2,sK3)) = u1_struct_0(sK2) ),
% 2.77/1.00      inference(instantiation,[status(thm)],[c_5383]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_5557,plain,
% 2.77/1.00      ( v1_tex_2(k1_tex_2(X0_47,X0_48),X0_47)
% 2.77/1.00      | ~ m1_subset_1(X0_48,u1_struct_0(X0_47))
% 2.77/1.00      | v2_struct_0(X0_47)
% 2.77/1.00      | ~ l1_pre_topc(X0_47)
% 2.77/1.00      | sK1(X0_47,k1_tex_2(X0_47,X0_48)) = u1_struct_0(X0_47) ),
% 2.77/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_5556]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_5559,plain,
% 2.77/1.00      ( v1_tex_2(k1_tex_2(sK2,sK3),sK2)
% 2.77/1.00      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 2.77/1.00      | v2_struct_0(sK2)
% 2.77/1.00      | ~ l1_pre_topc(sK2)
% 2.77/1.00      | sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(sK2) ),
% 2.77/1.00      inference(instantiation,[status(thm)],[c_5557]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_5567,plain,
% 2.77/1.00      ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 2.77/1.00      | v2_struct_0(sK2)
% 2.77/1.00      | ~ l1_pre_topc(sK2)
% 2.77/1.00      | sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(sK2)
% 2.77/1.00      | k6_domain_1(u1_struct_0(sK2),sK3) = u1_struct_0(sK2) ),
% 2.77/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_5566]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_5584,plain,
% 2.77/1.00      ( sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(sK2) ),
% 2.77/1.00      inference(global_propositional_subsumption,
% 2.77/1.00                [status(thm)],
% 2.77/1.00                [c_5566,c_29,c_28,c_27,c_91,c_96,c_2477,c_2480,c_3422,
% 2.77/1.00                 c_3512,c_3570,c_3943,c_5385,c_5559,c_5567]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_5757,plain,
% 2.77/1.00      ( k6_domain_1(u1_struct_0(sK2),sK3) = u1_struct_0(sK2)
% 2.77/1.00      | u1_struct_0(k1_tex_2(sK2,sK3)) = u1_struct_0(sK2)
% 2.77/1.00      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 2.77/1.00      | v2_struct_0(sK2) = iProver_top
% 2.77/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 2.77/1.00      inference(light_normalisation,[status(thm)],[c_5756,c_5584]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_5758,plain,
% 2.77/1.00      ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 2.77/1.00      | v2_struct_0(sK2)
% 2.77/1.00      | ~ l1_pre_topc(sK2)
% 2.77/1.00      | k6_domain_1(u1_struct_0(sK2),sK3) = u1_struct_0(sK2)
% 2.77/1.00      | u1_struct_0(k1_tex_2(sK2,sK3)) = u1_struct_0(sK2) ),
% 2.77/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_5757]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_5860,plain,
% 2.77/1.00      ( u1_struct_0(k1_tex_2(sK2,sK3)) = u1_struct_0(sK2) ),
% 2.77/1.00      inference(global_propositional_subsumption,
% 2.77/1.00                [status(thm)],
% 2.77/1.00                [c_5757,c_29,c_28,c_27,c_91,c_96,c_2477,c_2480,c_3422,
% 2.77/1.00                 c_3570,c_3943,c_5385,c_5758]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_24,plain,
% 2.77/1.00      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
% 2.77/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.77/1.00      | ~ v7_struct_0(X0)
% 2.77/1.00      | v2_struct_0(X0)
% 2.77/1.00      | ~ l1_struct_0(X0) ),
% 2.77/1.00      inference(cnf_transformation,[],[f88]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_463,plain,
% 2.77/1.00      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
% 2.77/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.77/1.00      | ~ v7_struct_0(X0)
% 2.77/1.00      | v2_struct_0(X0)
% 2.77/1.00      | ~ l1_pre_topc(X0) ),
% 2.77/1.00      inference(resolution,[status(thm)],[c_2,c_24]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_2391,plain,
% 2.77/1.00      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0_47),X0_48),u1_struct_0(X0_47))
% 2.77/1.00      | ~ m1_subset_1(X0_48,u1_struct_0(X0_47))
% 2.77/1.00      | ~ v7_struct_0(X0_47)
% 2.77/1.00      | v2_struct_0(X0_47)
% 2.77/1.00      | ~ l1_pre_topc(X0_47) ),
% 2.77/1.00      inference(subtyping,[status(esa)],[c_463]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_3167,plain,
% 2.77/1.00      ( v1_subset_1(k6_domain_1(u1_struct_0(X0_47),X0_48),u1_struct_0(X0_47)) != iProver_top
% 2.77/1.00      | m1_subset_1(X0_48,u1_struct_0(X0_47)) != iProver_top
% 2.77/1.00      | v7_struct_0(X0_47) != iProver_top
% 2.77/1.00      | v2_struct_0(X0_47) = iProver_top
% 2.77/1.00      | l1_pre_topc(X0_47) != iProver_top ),
% 2.77/1.00      inference(predicate_to_equality,[status(thm)],[c_2391]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_5868,plain,
% 2.77/1.00      ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),X0_48),u1_struct_0(sK2)) != iProver_top
% 2.77/1.00      | m1_subset_1(X0_48,u1_struct_0(k1_tex_2(sK2,sK3))) != iProver_top
% 2.77/1.00      | v7_struct_0(k1_tex_2(sK2,sK3)) != iProver_top
% 2.77/1.00      | v2_struct_0(k1_tex_2(sK2,sK3)) = iProver_top
% 2.77/1.00      | l1_pre_topc(k1_tex_2(sK2,sK3)) != iProver_top ),
% 2.77/1.00      inference(superposition,[status(thm)],[c_5860,c_3167]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_5982,plain,
% 2.77/1.00      ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),X0_48),u1_struct_0(sK2)) != iProver_top
% 2.77/1.00      | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top
% 2.77/1.00      | v7_struct_0(k1_tex_2(sK2,sK3)) != iProver_top
% 2.77/1.00      | v2_struct_0(k1_tex_2(sK2,sK3)) = iProver_top
% 2.77/1.00      | l1_pre_topc(k1_tex_2(sK2,sK3)) != iProver_top ),
% 2.77/1.00      inference(light_normalisation,[status(thm)],[c_5868,c_5860]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_6064,plain,
% 2.77/1.00      ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) != iProver_top
% 2.77/1.00      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 2.77/1.00      | v7_struct_0(k1_tex_2(sK2,sK3)) != iProver_top
% 2.77/1.00      | v2_struct_0(k1_tex_2(sK2,sK3)) = iProver_top
% 2.77/1.00      | l1_pre_topc(k1_tex_2(sK2,sK3)) != iProver_top ),
% 2.77/1.00      inference(instantiation,[status(thm)],[c_5982]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_3569,plain,
% 2.77/1.00      ( m1_pre_topc(k1_tex_2(X0_47,X0_48),X1_47) != iProver_top
% 2.77/1.00      | l1_pre_topc(X1_47) != iProver_top
% 2.77/1.00      | l1_pre_topc(k1_tex_2(X0_47,X0_48)) = iProver_top ),
% 2.77/1.00      inference(predicate_to_equality,[status(thm)],[c_3568]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_3571,plain,
% 2.77/1.00      ( m1_pre_topc(k1_tex_2(sK2,sK3),sK2) != iProver_top
% 2.77/1.00      | l1_pre_topc(k1_tex_2(sK2,sK3)) = iProver_top
% 2.77/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 2.77/1.00      inference(instantiation,[status(thm)],[c_3569]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_3516,plain,
% 2.77/1.00      ( u1_struct_0(k1_tex_2(sK2,sK3)) != u1_struct_0(sK2)
% 2.77/1.00      | v1_tex_2(k1_tex_2(sK2,sK3),sK2) != iProver_top
% 2.77/1.00      | m1_pre_topc(k1_tex_2(sK2,sK3),sK2) != iProver_top
% 2.77/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 2.77/1.00      inference(predicate_to_equality,[status(thm)],[c_3512]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_20,plain,
% 2.77/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.77/1.00      | v7_struct_0(k1_tex_2(X1,X0))
% 2.77/1.00      | v2_struct_0(X1)
% 2.77/1.00      | ~ l1_pre_topc(X1) ),
% 2.77/1.00      inference(cnf_transformation,[],[f85]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_2400,plain,
% 2.77/1.00      ( ~ m1_subset_1(X0_48,u1_struct_0(X0_47))
% 2.77/1.00      | v7_struct_0(k1_tex_2(X0_47,X0_48))
% 2.77/1.00      | v2_struct_0(X0_47)
% 2.77/1.00      | ~ l1_pre_topc(X0_47) ),
% 2.77/1.00      inference(subtyping,[status(esa)],[c_20]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_2482,plain,
% 2.77/1.00      ( m1_subset_1(X0_48,u1_struct_0(X0_47)) != iProver_top
% 2.77/1.00      | v7_struct_0(k1_tex_2(X0_47,X0_48)) = iProver_top
% 2.77/1.00      | v2_struct_0(X0_47) = iProver_top
% 2.77/1.00      | l1_pre_topc(X0_47) != iProver_top ),
% 2.77/1.00      inference(predicate_to_equality,[status(thm)],[c_2400]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_2484,plain,
% 2.77/1.00      ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 2.77/1.00      | v7_struct_0(k1_tex_2(sK2,sK3)) = iProver_top
% 2.77/1.00      | v2_struct_0(sK2) = iProver_top
% 2.77/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 2.77/1.00      inference(instantiation,[status(thm)],[c_2482]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_2479,plain,
% 2.77/1.00      ( m1_subset_1(X0_48,u1_struct_0(X0_47)) != iProver_top
% 2.77/1.00      | v2_struct_0(X0_47) = iProver_top
% 2.77/1.00      | v2_struct_0(k1_tex_2(X0_47,X0_48)) != iProver_top
% 2.77/1.00      | l1_pre_topc(X0_47) != iProver_top ),
% 2.77/1.00      inference(predicate_to_equality,[status(thm)],[c_2401]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_2481,plain,
% 2.77/1.00      ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 2.77/1.00      | v2_struct_0(k1_tex_2(sK2,sK3)) != iProver_top
% 2.77/1.00      | v2_struct_0(sK2) = iProver_top
% 2.77/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 2.77/1.00      inference(instantiation,[status(thm)],[c_2479]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_2476,plain,
% 2.77/1.00      ( m1_pre_topc(k1_tex_2(X0_47,X0_48),X0_47) = iProver_top
% 2.77/1.00      | m1_subset_1(X0_48,u1_struct_0(X0_47)) != iProver_top
% 2.77/1.00      | v2_struct_0(X0_47) = iProver_top
% 2.77/1.00      | l1_pre_topc(X0_47) != iProver_top ),
% 2.77/1.00      inference(predicate_to_equality,[status(thm)],[c_2402]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_2478,plain,
% 2.77/1.00      ( m1_pre_topc(k1_tex_2(sK2,sK3),sK2) = iProver_top
% 2.77/1.00      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 2.77/1.00      | v2_struct_0(sK2) = iProver_top
% 2.77/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 2.77/1.00      inference(instantiation,[status(thm)],[c_2476]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_26,negated_conjecture,
% 2.77/1.00      ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 2.77/1.00      | v1_tex_2(k1_tex_2(sK2,sK3),sK2) ),
% 2.77/1.00      inference(cnf_transformation,[],[f92]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_33,plain,
% 2.77/1.00      ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) = iProver_top
% 2.77/1.00      | v1_tex_2(k1_tex_2(sK2,sK3),sK2) = iProver_top ),
% 2.77/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(contradiction,plain,
% 2.77/1.00      ( $false ),
% 2.77/1.00      inference(minisat,
% 2.77/1.00                [status(thm)],
% 2.77/1.00                [c_6064,c_5860,c_3571,c_3516,c_2484,c_2481,c_2478,c_33,
% 2.77/1.00                 c_32,c_31,c_30]) ).
% 2.77/1.00  
% 2.77/1.00  
% 2.77/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.77/1.00  
% 2.77/1.00  ------                               Statistics
% 2.77/1.00  
% 2.77/1.00  ------ General
% 2.77/1.00  
% 2.77/1.00  abstr_ref_over_cycles:                  0
% 2.77/1.00  abstr_ref_under_cycles:                 0
% 2.77/1.00  gc_basic_clause_elim:                   0
% 2.77/1.00  forced_gc_time:                         0
% 2.77/1.00  parsing_time:                           0.028
% 2.77/1.00  unif_index_cands_time:                  0.
% 2.77/1.00  unif_index_add_time:                    0.
% 2.77/1.00  orderings_time:                         0.
% 2.77/1.00  out_proof_time:                         0.021
% 2.77/1.00  total_time:                             0.276
% 2.77/1.00  num_of_symbols:                         52
% 2.77/1.00  num_of_terms:                           3484
% 2.77/1.00  
% 2.77/1.00  ------ Preprocessing
% 2.77/1.00  
% 2.77/1.00  num_of_splits:                          0
% 2.77/1.00  num_of_split_atoms:                     0
% 2.77/1.00  num_of_reused_defs:                     0
% 2.77/1.00  num_eq_ax_congr_red:                    14
% 2.77/1.00  num_of_sem_filtered_clauses:            1
% 2.77/1.00  num_of_subtypes:                        2
% 2.77/1.00  monotx_restored_types:                  1
% 2.77/1.00  sat_num_of_epr_types:                   0
% 2.77/1.00  sat_num_of_non_cyclic_types:            0
% 2.77/1.01  sat_guarded_non_collapsed_types:        0
% 2.77/1.01  num_pure_diseq_elim:                    0
% 2.77/1.01  simp_replaced_by:                       0
% 2.77/1.01  res_preprocessed:                       143
% 2.77/1.01  prep_upred:                             0
% 2.77/1.01  prep_unflattend:                        93
% 2.77/1.01  smt_new_axioms:                         0
% 2.77/1.01  pred_elim_cands:                        9
% 2.77/1.01  pred_elim:                              2
% 2.77/1.01  pred_elim_cl:                           2
% 2.77/1.01  pred_elim_cycles:                       13
% 2.77/1.01  merged_defs:                            8
% 2.77/1.01  merged_defs_ncl:                        0
% 2.77/1.01  bin_hyper_res:                          8
% 2.77/1.01  prep_cycles:                            4
% 2.77/1.01  pred_elim_time:                         0.053
% 2.77/1.01  splitting_time:                         0.
% 2.77/1.01  sem_filter_time:                        0.
% 2.77/1.01  monotx_time:                            0.001
% 2.77/1.01  subtype_inf_time:                       0.002
% 2.77/1.01  
% 2.77/1.01  ------ Problem properties
% 2.77/1.01  
% 2.77/1.01  clauses:                                27
% 2.77/1.01  conjectures:                            5
% 2.77/1.01  epr:                                    4
% 2.77/1.01  horn:                                   16
% 2.77/1.01  ground:                                 5
% 2.77/1.01  unary:                                  3
% 2.77/1.01  binary:                                 4
% 2.77/1.01  lits:                                   85
% 2.77/1.01  lits_eq:                                6
% 2.77/1.01  fd_pure:                                0
% 2.77/1.01  fd_pseudo:                              0
% 2.77/1.01  fd_cond:                                0
% 2.77/1.01  fd_pseudo_cond:                         1
% 2.77/1.01  ac_symbols:                             0
% 2.77/1.01  
% 2.77/1.01  ------ Propositional Solver
% 2.77/1.01  
% 2.77/1.01  prop_solver_calls:                      28
% 2.77/1.01  prop_fast_solver_calls:                 1512
% 2.77/1.01  smt_solver_calls:                       0
% 2.77/1.01  smt_fast_solver_calls:                  0
% 2.77/1.01  prop_num_of_clauses:                    1447
% 2.77/1.01  prop_preprocess_simplified:             6047
% 2.77/1.01  prop_fo_subsumed:                       44
% 2.77/1.01  prop_solver_time:                       0.
% 2.77/1.01  smt_solver_time:                        0.
% 2.77/1.01  smt_fast_solver_time:                   0.
% 2.77/1.01  prop_fast_solver_time:                  0.
% 2.77/1.01  prop_unsat_core_time:                   0.
% 2.77/1.01  
% 2.77/1.01  ------ QBF
% 2.77/1.01  
% 2.77/1.01  qbf_q_res:                              0
% 2.77/1.01  qbf_num_tautologies:                    0
% 2.77/1.01  qbf_prep_cycles:                        0
% 2.77/1.01  
% 2.77/1.01  ------ BMC1
% 2.77/1.01  
% 2.77/1.01  bmc1_current_bound:                     -1
% 2.77/1.01  bmc1_last_solved_bound:                 -1
% 2.77/1.01  bmc1_unsat_core_size:                   -1
% 2.77/1.01  bmc1_unsat_core_parents_size:           -1
% 2.77/1.01  bmc1_merge_next_fun:                    0
% 2.77/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.77/1.01  
% 2.77/1.01  ------ Instantiation
% 2.77/1.01  
% 2.77/1.01  inst_num_of_clauses:                    403
% 2.77/1.01  inst_num_in_passive:                    161
% 2.77/1.01  inst_num_in_active:                     203
% 2.77/1.01  inst_num_in_unprocessed:                39
% 2.77/1.01  inst_num_of_loops:                      280
% 2.77/1.01  inst_num_of_learning_restarts:          0
% 2.77/1.01  inst_num_moves_active_passive:          73
% 2.77/1.01  inst_lit_activity:                      0
% 2.77/1.01  inst_lit_activity_moves:                0
% 2.77/1.01  inst_num_tautologies:                   0
% 2.77/1.01  inst_num_prop_implied:                  0
% 2.77/1.01  inst_num_existing_simplified:           0
% 2.77/1.01  inst_num_eq_res_simplified:             0
% 2.77/1.01  inst_num_child_elim:                    0
% 2.77/1.01  inst_num_of_dismatching_blockings:      162
% 2.77/1.01  inst_num_of_non_proper_insts:           426
% 2.77/1.01  inst_num_of_duplicates:                 0
% 2.77/1.01  inst_inst_num_from_inst_to_res:         0
% 2.77/1.01  inst_dismatching_checking_time:         0.
% 2.77/1.01  
% 2.77/1.01  ------ Resolution
% 2.77/1.01  
% 2.77/1.01  res_num_of_clauses:                     0
% 2.77/1.01  res_num_in_passive:                     0
% 2.77/1.01  res_num_in_active:                      0
% 2.77/1.01  res_num_of_loops:                       147
% 2.77/1.01  res_forward_subset_subsumed:            35
% 2.77/1.01  res_backward_subset_subsumed:           0
% 2.77/1.01  res_forward_subsumed:                   0
% 2.77/1.01  res_backward_subsumed:                  0
% 2.77/1.01  res_forward_subsumption_resolution:     3
% 2.77/1.01  res_backward_subsumption_resolution:    0
% 2.77/1.01  res_clause_to_clause_subsumption:       216
% 2.77/1.01  res_orphan_elimination:                 0
% 2.77/1.01  res_tautology_del:                      83
% 2.77/1.01  res_num_eq_res_simplified:              0
% 2.77/1.01  res_num_sel_changes:                    0
% 2.77/1.01  res_moves_from_active_to_pass:          0
% 2.77/1.01  
% 2.77/1.01  ------ Superposition
% 2.77/1.01  
% 2.77/1.01  sup_time_total:                         0.
% 2.77/1.01  sup_time_generating:                    0.
% 2.77/1.01  sup_time_sim_full:                      0.
% 2.77/1.01  sup_time_sim_immed:                     0.
% 2.77/1.01  
% 2.77/1.01  sup_num_of_clauses:                     73
% 2.77/1.01  sup_num_in_active:                      55
% 2.77/1.01  sup_num_in_passive:                     18
% 2.77/1.01  sup_num_of_loops:                       54
% 2.77/1.01  sup_fw_superposition:                   13
% 2.77/1.01  sup_bw_superposition:                   55
% 2.77/1.01  sup_immediate_simplified:               16
% 2.77/1.01  sup_given_eliminated:                   0
% 2.77/1.01  comparisons_done:                       0
% 2.77/1.01  comparisons_avoided:                    0
% 2.77/1.01  
% 2.77/1.01  ------ Simplifications
% 2.77/1.01  
% 2.77/1.01  
% 2.77/1.01  sim_fw_subset_subsumed:                 6
% 2.77/1.01  sim_bw_subset_subsumed:                 0
% 2.77/1.01  sim_fw_subsumed:                        3
% 2.77/1.01  sim_bw_subsumed:                        0
% 2.77/1.01  sim_fw_subsumption_res:                 2
% 2.77/1.01  sim_bw_subsumption_res:                 0
% 2.77/1.01  sim_tautology_del:                      5
% 2.77/1.01  sim_eq_tautology_del:                   3
% 2.77/1.01  sim_eq_res_simp:                        0
% 2.77/1.01  sim_fw_demodulated:                     2
% 2.77/1.01  sim_bw_demodulated:                     0
% 2.77/1.01  sim_light_normalised:                   5
% 2.77/1.01  sim_joinable_taut:                      0
% 2.77/1.01  sim_joinable_simp:                      0
% 2.77/1.01  sim_ac_normalised:                      0
% 2.77/1.01  sim_smt_subsumption:                    0
% 2.77/1.01  
%------------------------------------------------------------------------------
