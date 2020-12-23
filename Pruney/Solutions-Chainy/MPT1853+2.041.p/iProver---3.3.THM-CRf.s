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
% DateTime   : Thu Dec  3 12:25:43 EST 2020

% Result     : Theorem 2.26s
% Output     : CNFRefutation 2.26s
% Verified   : 
% Statistics : Number of formulae       :  221 (1048 expanded)
%              Number of clauses        :  142 ( 337 expanded)
%              Number of leaves         :   25 ( 206 expanded)
%              Depth                    :   20
%              Number of atoms          :  814 (5179 expanded)
%              Number of equality atoms :  219 ( 456 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
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

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f33])).

fof(f48,plain,(
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
    inference(rectify,[],[f47])).

fof(f49,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v1_subset_1(X2,u1_struct_0(X0))
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_subset_1(sK1(X0,X1),u1_struct_0(X0))
        & u1_struct_0(X1) = sK1(X0,X1)
        & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f48,f49])).

fof(f68,plain,(
    ! [X0,X3,X1] :
      ( v1_subset_1(X3,u1_struct_0(X0))
      | u1_struct_0(X1) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f84,plain,(
    ! [X0,X1] :
      ( v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f68])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( v1_tex_2(k1_tex_2(X0,X1),X0)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f52,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f53,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f52])).

fof(f55,plain,(
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

fof(f54,plain,
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

fof(f56,plain,
    ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
      | ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2) )
    & ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
      | v1_tex_2(k1_tex_2(sK2,sK3),sK2) )
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l1_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f53,f55,f54])).

fof(f82,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | v1_tex_2(k1_tex_2(sK2,sK3),sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f80,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f79,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f81,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f56])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f58,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f12,axiom,(
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
    inference(pure_predicate_removal,[],[f12])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f75,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f25,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f61,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v7_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f59,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f73,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f14,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_zfmisc_1(X0)
          | ~ v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_zfmisc_1(X0)
          | ~ v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(X0)
      | ~ v1_subset_1(k6_domain_1(X0,X1),X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( ~ v1_xboole_0(X1)
           => ~ v1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ~ v1_subset_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | u1_struct_0(X1) = sK1(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f83,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f9,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f44,plain,(
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
    inference(rectify,[],[f43])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k6_domain_1(X0,X2) = X0
          & m1_subset_1(X2,X0) )
     => ( k6_domain_1(X0,sK0(X0)) = X0
        & m1_subset_1(sK0(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ( k6_domain_1(X0,sK0(X0)) = X0
            & m1_subset_1(sK0(X0),X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f44,f45])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v1_zfmisc_1(X0)
      | k6_domain_1(X0,X1) != X0
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | ~ v1_subset_1(sK1(X0,X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_3168,plain,
    ( X0_46 != X1_46
    | X2_46 != X1_46
    | X2_46 = X0_46 ),
    theory(equality)).

cnf(c_4050,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK3) != X0_46
    | k6_domain_1(u1_struct_0(sK2),sK3) = u1_struct_0(sK2)
    | u1_struct_0(sK2) != X0_46 ),
    inference(instantiation,[status(thm)],[c_3168])).

cnf(c_6179,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK3) != k6_domain_1(u1_struct_0(sK2),sK3)
    | k6_domain_1(u1_struct_0(sK2),sK3) = u1_struct_0(sK2)
    | u1_struct_0(sK2) != k6_domain_1(u1_struct_0(sK2),sK3) ),
    inference(instantiation,[status(thm)],[c_4050])).

cnf(c_14,plain,
    ( ~ v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_157,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_tex_2(X0,X1)
    | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14,c_6])).

cnf(c_158,plain,
    ( ~ v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_157])).

cnf(c_23,negated_conjecture,
    ( v1_tex_2(k1_tex_2(sK2,sK3),sK2)
    | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_213,plain,
    ( v1_tex_2(k1_tex_2(sK2,sK3),sK2)
    | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) ),
    inference(prop_impl,[status(thm)],[c_23])).

cnf(c_698,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | k1_tex_2(sK2,sK3) != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_158,c_213])).

cnf(c_699,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
    | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | v1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_698])).

cnf(c_25,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_701,plain,
    ( v1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),u1_struct_0(sK2))
    | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_699,c_25])).

cnf(c_702,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
    | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | v1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_701])).

cnf(c_3141,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
    | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | v1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_702])).

cnf(c_3710,plain,
    ( m1_pre_topc(k1_tex_2(sK2,sK3),sK2) != iProver_top
    | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) = iProver_top
    | v1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3141])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_27,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_28,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_29,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_82,plain,
    ( v2_struct_0(X0) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_84,plain,
    ( v2_struct_0(sK2) = iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_82])).

cnf(c_1,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_86,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_88,plain,
    ( l1_pre_topc(sK2) != iProver_top
    | l1_struct_0(sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_86])).

cnf(c_17,plain,
    ( m1_pre_topc(k1_tex_2(X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_3155,plain,
    ( m1_pre_topc(k1_tex_2(X0_47,X0_46),X0_47)
    | ~ m1_subset_1(X0_46,u1_struct_0(X0_47))
    | v2_struct_0(X0_47)
    | ~ l1_pre_topc(X0_47) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_3217,plain,
    ( m1_pre_topc(k1_tex_2(X0_47,X0_46),X0_47) = iProver_top
    | m1_subset_1(X0_46,u1_struct_0(X0_47)) != iProver_top
    | v2_struct_0(X0_47) = iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3155])).

cnf(c_3219,plain,
    ( m1_pre_topc(k1_tex_2(sK2,sK3),sK2) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3217])).

cnf(c_4,plain,
    ( ~ v7_struct_0(X0)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_385,plain,
    ( ~ v7_struct_0(X0)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_1,c_4])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v7_struct_0(k1_tex_2(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1613,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v1_zfmisc_1(u1_struct_0(X2))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k1_tex_2(X1,X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_385,c_19])).

cnf(c_1614,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v1_zfmisc_1(u1_struct_0(k1_tex_2(X1,X0)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(k1_tex_2(X1,X0)) ),
    inference(unflattening,[status(thm)],[c_1613])).

cnf(c_421,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v1_zfmisc_1(u1_struct_0(X2))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k1_tex_2(X1,X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_385,c_19])).

cnf(c_422,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v1_zfmisc_1(u1_struct_0(k1_tex_2(X1,X0)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(k1_tex_2(X1,X0)) ),
    inference(unflattening,[status(thm)],[c_421])).

cnf(c_2,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_549,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X3)
    | X1 != X2
    | k1_tex_2(X1,X0) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_17])).

cnf(c_550,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k1_tex_2(X1,X0)) ),
    inference(unflattening,[status(thm)],[c_549])).

cnf(c_1616,plain,
    ( ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v1_zfmisc_1(u1_struct_0(k1_tex_2(X1,X0)))
    | ~ m1_subset_1(X0,u1_struct_0(X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1614,c_422,c_550])).

cnf(c_1617,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v1_zfmisc_1(u1_struct_0(k1_tex_2(X1,X0)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_1616])).

cnf(c_3140,plain,
    ( ~ m1_subset_1(X0_46,u1_struct_0(X0_47))
    | v1_zfmisc_1(u1_struct_0(k1_tex_2(X0_47,X0_46)))
    | v2_struct_0(X0_47)
    | ~ l1_pre_topc(X0_47) ),
    inference(subtyping,[status(esa)],[c_1617])).

cnf(c_3242,plain,
    ( m1_subset_1(X0_46,u1_struct_0(X0_47)) != iProver_top
    | v1_zfmisc_1(u1_struct_0(k1_tex_2(X0_47,X0_46))) = iProver_top
    | v2_struct_0(X0_47) = iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3140])).

cnf(c_3244,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | v1_zfmisc_1(u1_struct_0(k1_tex_2(sK2,sK3))) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3242])).

cnf(c_3218,plain,
    ( m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_3155])).

cnf(c_3320,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | v1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3141,c_26,c_25,c_24,c_699,c_3218])).

cnf(c_3322,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) = iProver_top
    | v1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3320])).

cnf(c_3161,plain,
    ( ~ m1_pre_topc(X0_47,X1_47)
    | m1_subset_1(u1_struct_0(X0_47),k1_zfmisc_1(u1_struct_0(X1_47)))
    | ~ l1_pre_topc(X1_47) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_3955,plain,
    ( ~ m1_pre_topc(k1_tex_2(X0_47,X0_46),X0_47)
    | m1_subset_1(u1_struct_0(k1_tex_2(X0_47,X0_46)),k1_zfmisc_1(u1_struct_0(X0_47)))
    | ~ l1_pre_topc(X0_47) ),
    inference(instantiation,[status(thm)],[c_3161])).

cnf(c_3956,plain,
    ( m1_pre_topc(k1_tex_2(X0_47,X0_46),X0_47) != iProver_top
    | m1_subset_1(u1_struct_0(k1_tex_2(X0_47,X0_46)),k1_zfmisc_1(u1_struct_0(X0_47))) = iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3955])).

cnf(c_3958,plain,
    ( m1_pre_topc(k1_tex_2(sK2,sK3),sK2) != iProver_top
    | m1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3956])).

cnf(c_3177,plain,
    ( ~ v1_zfmisc_1(X0_46)
    | v1_zfmisc_1(X1_46)
    | X1_46 != X0_46 ),
    theory(equality)).

cnf(c_3996,plain,
    ( v1_zfmisc_1(X0_46)
    | ~ v1_zfmisc_1(u1_struct_0(k1_tex_2(X0_47,X1_46)))
    | X0_46 != u1_struct_0(k1_tex_2(X0_47,X1_46)) ),
    inference(instantiation,[status(thm)],[c_3177])).

cnf(c_4081,plain,
    ( v1_zfmisc_1(u1_struct_0(X0_47))
    | ~ v1_zfmisc_1(u1_struct_0(k1_tex_2(X1_47,X0_46)))
    | u1_struct_0(X0_47) != u1_struct_0(k1_tex_2(X1_47,X0_46)) ),
    inference(instantiation,[status(thm)],[c_3996])).

cnf(c_4083,plain,
    ( u1_struct_0(X0_47) != u1_struct_0(k1_tex_2(X1_47,X0_46))
    | v1_zfmisc_1(u1_struct_0(X0_47)) = iProver_top
    | v1_zfmisc_1(u1_struct_0(k1_tex_2(X1_47,X0_46))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4081])).

cnf(c_4085,plain,
    ( u1_struct_0(sK2) != u1_struct_0(k1_tex_2(sK2,sK3))
    | v1_zfmisc_1(u1_struct_0(k1_tex_2(sK2,sK3))) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4083])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | v1_subset_1(X0,X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_3157,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(X1_46))
    | v1_subset_1(X0_46,X1_46)
    | X1_46 = X0_46 ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_4073,plain,
    ( ~ m1_subset_1(u1_struct_0(k1_tex_2(X0_47,X0_46)),k1_zfmisc_1(X1_46))
    | v1_subset_1(u1_struct_0(k1_tex_2(X0_47,X0_46)),X1_46)
    | X1_46 = u1_struct_0(k1_tex_2(X0_47,X0_46)) ),
    inference(instantiation,[status(thm)],[c_3157])).

cnf(c_4368,plain,
    ( ~ m1_subset_1(u1_struct_0(k1_tex_2(X0_47,X0_46)),k1_zfmisc_1(u1_struct_0(X0_47)))
    | v1_subset_1(u1_struct_0(k1_tex_2(X0_47,X0_46)),u1_struct_0(X0_47))
    | u1_struct_0(X0_47) = u1_struct_0(k1_tex_2(X0_47,X0_46)) ),
    inference(instantiation,[status(thm)],[c_4073])).

cnf(c_4369,plain,
    ( u1_struct_0(X0_47) = u1_struct_0(k1_tex_2(X0_47,X0_46))
    | m1_subset_1(u1_struct_0(k1_tex_2(X0_47,X0_46)),k1_zfmisc_1(u1_struct_0(X0_47))) != iProver_top
    | v1_subset_1(u1_struct_0(k1_tex_2(X0_47,X0_46)),u1_struct_0(X0_47)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4368])).

cnf(c_4371,plain,
    ( u1_struct_0(sK2) = u1_struct_0(k1_tex_2(sK2,sK3))
    | m1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),u1_struct_0(sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4369])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ v1_subset_1(k6_domain_1(X1,X0),X1)
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_3153,plain,
    ( ~ m1_subset_1(X0_46,X1_46)
    | ~ v1_subset_1(k6_domain_1(X1_46,X0_46),X1_46)
    | ~ v1_zfmisc_1(X1_46)
    | v1_xboole_0(X1_46) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_5704,plain,
    ( ~ m1_subset_1(X0_46,u1_struct_0(X0_47))
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0_47),X0_46),u1_struct_0(X0_47))
    | ~ v1_zfmisc_1(u1_struct_0(X0_47))
    | v1_xboole_0(u1_struct_0(X0_47)) ),
    inference(instantiation,[status(thm)],[c_3153])).

cnf(c_5710,plain,
    ( m1_subset_1(X0_46,u1_struct_0(X0_47)) != iProver_top
    | v1_subset_1(k6_domain_1(u1_struct_0(X0_47),X0_46),u1_struct_0(X0_47)) != iProver_top
    | v1_zfmisc_1(u1_struct_0(X0_47)) != iProver_top
    | v1_xboole_0(u1_struct_0(X0_47)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5704])).

cnf(c_5712,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK2)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_5710])).

cnf(c_6015,plain,
    ( v1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),u1_struct_0(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3710,c_27,c_28,c_29,c_84,c_88,c_3219,c_3244,c_3322,c_3958,c_4085,c_4371,c_5712])).

cnf(c_3690,plain,
    ( m1_pre_topc(X0_47,X1_47) != iProver_top
    | m1_subset_1(u1_struct_0(X0_47),k1_zfmisc_1(u1_struct_0(X1_47))) = iProver_top
    | l1_pre_topc(X1_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3161])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_subset_1(X0,X1)
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_subset_1(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_170,plain,
    ( ~ v1_zfmisc_1(X1)
    | ~ v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7,c_0])).

cnf(c_171,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_subset_1(X0,X1)
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_170])).

cnf(c_3149,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(X1_46))
    | ~ v1_subset_1(X0_46,X1_46)
    | ~ v1_zfmisc_1(X1_46)
    | v1_xboole_0(X0_46) ),
    inference(subtyping,[status(esa)],[c_171])).

cnf(c_3702,plain,
    ( m1_subset_1(X0_46,k1_zfmisc_1(X1_46)) != iProver_top
    | v1_subset_1(X0_46,X1_46) != iProver_top
    | v1_zfmisc_1(X1_46) != iProver_top
    | v1_xboole_0(X0_46) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3149])).

cnf(c_4397,plain,
    ( m1_pre_topc(X0_47,X1_47) != iProver_top
    | v1_subset_1(u1_struct_0(X0_47),u1_struct_0(X1_47)) != iProver_top
    | v1_zfmisc_1(u1_struct_0(X1_47)) != iProver_top
    | l1_pre_topc(X1_47) != iProver_top
    | v1_xboole_0(u1_struct_0(X0_47)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3690,c_3702])).

cnf(c_6020,plain,
    ( m1_pre_topc(k1_tex_2(sK2,sK3),sK2) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK2)) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_xboole_0(u1_struct_0(k1_tex_2(sK2,sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_6015,c_4397])).

cnf(c_3169,plain,
    ( ~ v1_subset_1(X0_46,X1_46)
    | v1_subset_1(X2_46,X3_46)
    | X2_46 != X0_46
    | X3_46 != X1_46 ),
    theory(equality)).

cnf(c_3986,plain,
    ( v1_subset_1(X0_46,X1_46)
    | ~ v1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),u1_struct_0(sK2))
    | X0_46 != u1_struct_0(k1_tex_2(sK2,sK3))
    | X1_46 != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_3169])).

cnf(c_4177,plain,
    ( v1_subset_1(X0_46,u1_struct_0(sK2))
    | ~ v1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),u1_struct_0(sK2))
    | X0_46 != u1_struct_0(k1_tex_2(sK2,sK3))
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_3986])).

cnf(c_5071,plain,
    ( v1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),u1_struct_0(sK2))
    | ~ v1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),u1_struct_0(sK2))
    | sK1(sK2,k1_tex_2(sK2,sK3)) != u1_struct_0(k1_tex_2(sK2,sK3))
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_4177])).

cnf(c_5072,plain,
    ( sK1(sK2,k1_tex_2(sK2,sK3)) != u1_struct_0(k1_tex_2(sK2,sK3))
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | v1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),u1_struct_0(sK2)) = iProver_top
    | v1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5071])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_3162,plain,
    ( ~ m1_subset_1(X0_46,X1_46)
    | m1_subset_1(k6_domain_1(X1_46,X0_46),k1_zfmisc_1(X1_46))
    | v1_xboole_0(X1_46) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_3689,plain,
    ( m1_subset_1(X0_46,X1_46) != iProver_top
    | m1_subset_1(k6_domain_1(X1_46,X0_46),k1_zfmisc_1(X1_46)) = iProver_top
    | v1_xboole_0(X1_46) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3162])).

cnf(c_3694,plain,
    ( X0_46 = X1_46
    | m1_subset_1(X1_46,k1_zfmisc_1(X0_46)) != iProver_top
    | v1_subset_1(X1_46,X0_46) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3157])).

cnf(c_4197,plain,
    ( k6_domain_1(X0_46,X1_46) = X0_46
    | m1_subset_1(X1_46,X0_46) != iProver_top
    | v1_subset_1(k6_domain_1(X0_46,X1_46),X0_46) = iProver_top
    | v1_xboole_0(X0_46) = iProver_top ),
    inference(superposition,[status(thm)],[c_3689,c_3694])).

cnf(c_12,plain,
    ( v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK1(X1,X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_22,negated_conjecture,
    ( ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_211,plain,
    ( ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) ),
    inference(prop_impl,[status(thm)],[c_22])).

cnf(c_664,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | ~ l1_pre_topc(X1)
    | k1_tex_2(sK2,sK3) != X0
    | sK1(X1,X0) = u1_struct_0(X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_211])).

cnf(c_665,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2)
    | sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(k1_tex_2(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_664])).

cnf(c_667,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
    | sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(k1_tex_2(sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_665,c_25])).

cnf(c_668,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(k1_tex_2(sK2,sK3)) ),
    inference(renaming,[status(thm)],[c_667])).

cnf(c_3143,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(k1_tex_2(sK2,sK3)) ),
    inference(subtyping,[status(esa)],[c_668])).

cnf(c_3708,plain,
    ( sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(k1_tex_2(sK2,sK3))
    | m1_pre_topc(k1_tex_2(sK2,sK3),sK2) != iProver_top
    | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3143])).

cnf(c_3310,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(k1_tex_2(sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3143,c_26,c_25,c_24,c_3218])).

cnf(c_3312,plain,
    ( sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(k1_tex_2(sK2,sK3))
    | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3310])).

cnf(c_5004,plain,
    ( sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(k1_tex_2(sK2,sK3))
    | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3708,c_3312])).

cnf(c_5010,plain,
    ( sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(k1_tex_2(sK2,sK3))
    | k6_domain_1(u1_struct_0(sK2),sK3) = u1_struct_0(sK2)
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4197,c_5004])).

cnf(c_5011,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2))
    | sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(k1_tex_2(sK2,sK3))
    | k6_domain_1(u1_struct_0(sK2),sK3) = u1_struct_0(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5010])).

cnf(c_3166,plain,
    ( X0_46 = X0_46 ),
    theory(equality)).

cnf(c_4613,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK3) = k6_domain_1(u1_struct_0(sK2),sK3) ),
    inference(instantiation,[status(thm)],[c_3166])).

cnf(c_4229,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_subset_1(X0_46,u1_struct_0(sK2))
    | u1_struct_0(sK2) = X0_46 ),
    inference(instantiation,[status(thm)],[c_3157])).

cnf(c_4565,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | u1_struct_0(sK2) = k6_domain_1(u1_struct_0(sK2),sK3) ),
    inference(instantiation,[status(thm)],[c_4229])).

cnf(c_4566,plain,
    ( u1_struct_0(sK2) = k6_domain_1(u1_struct_0(sK2),sK3)
    | m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4565])).

cnf(c_3163,plain,
    ( ~ m1_pre_topc(X0_47,X1_47)
    | ~ l1_pre_topc(X1_47)
    | l1_pre_topc(X0_47) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_4324,plain,
    ( ~ m1_pre_topc(k1_tex_2(X0_47,X0_46),X1_47)
    | ~ l1_pre_topc(X1_47)
    | l1_pre_topc(k1_tex_2(X0_47,X0_46)) ),
    inference(instantiation,[status(thm)],[c_3163])).

cnf(c_4325,plain,
    ( m1_pre_topc(k1_tex_2(X0_47,X0_46),X1_47) != iProver_top
    | l1_pre_topc(X1_47) != iProver_top
    | l1_pre_topc(k1_tex_2(X0_47,X0_46)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4324])).

cnf(c_4327,plain,
    ( m1_pre_topc(k1_tex_2(sK2,sK3),sK2) != iProver_top
    | l1_pre_topc(k1_tex_2(sK2,sK3)) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4325])).

cnf(c_399,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_1,c_3])).

cnf(c_3148,plain,
    ( v2_struct_0(X0_47)
    | ~ l1_pre_topc(X0_47)
    | ~ v1_xboole_0(u1_struct_0(X0_47)) ),
    inference(subtyping,[status(esa)],[c_399])).

cnf(c_4103,plain,
    ( v2_struct_0(k1_tex_2(X0_47,X0_46))
    | ~ l1_pre_topc(k1_tex_2(X0_47,X0_46))
    | ~ v1_xboole_0(u1_struct_0(k1_tex_2(X0_47,X0_46))) ),
    inference(instantiation,[status(thm)],[c_3148])).

cnf(c_4104,plain,
    ( v2_struct_0(k1_tex_2(X0_47,X0_46)) = iProver_top
    | l1_pre_topc(k1_tex_2(X0_47,X0_46)) != iProver_top
    | v1_xboole_0(u1_struct_0(k1_tex_2(X0_47,X0_46))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4103])).

cnf(c_4106,plain,
    ( v2_struct_0(k1_tex_2(sK2,sK3)) = iProver_top
    | l1_pre_topc(k1_tex_2(sK2,sK3)) != iProver_top
    | v1_xboole_0(u1_struct_0(k1_tex_2(sK2,sK3))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4104])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_zfmisc_1(X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) != X1 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_3160,plain,
    ( ~ m1_subset_1(X0_46,X1_46)
    | v1_zfmisc_1(X1_46)
    | v1_xboole_0(X1_46)
    | k6_domain_1(X1_46,X0_46) != X1_46 ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_3960,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | v1_zfmisc_1(u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2))
    | k6_domain_1(u1_struct_0(sK2),sK3) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_3160])).

cnf(c_3961,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK3) != u1_struct_0(sK2)
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK2)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3960])).

cnf(c_3947,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3162])).

cnf(c_3948,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3947])).

cnf(c_11,plain,
    ( v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v1_subset_1(sK1(X1,X0),u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_681,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_subset_1(sK1(X1,X0),u1_struct_0(X1))
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | ~ l1_pre_topc(X1)
    | k1_tex_2(sK2,sK3) != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_211])).

cnf(c_682,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
    | ~ v1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),u1_struct_0(sK2))
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_681])).

cnf(c_684,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | ~ v1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),u1_struct_0(sK2))
    | ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_682,c_25])).

cnf(c_685,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
    | ~ v1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),u1_struct_0(sK2))
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_684])).

cnf(c_3142,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
    | ~ v1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),u1_struct_0(sK2))
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_685])).

cnf(c_3315,plain,
    ( ~ v1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),u1_struct_0(sK2))
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3142,c_26,c_25,c_24,c_682,c_3218])).

cnf(c_3317,plain,
    ( v1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),u1_struct_0(sK2)) != iProver_top
    | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3315])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k1_tex_2(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_3154,plain,
    ( ~ m1_subset_1(X0_46,u1_struct_0(X0_47))
    | v2_struct_0(X0_47)
    | ~ v2_struct_0(k1_tex_2(X0_47,X0_46))
    | ~ l1_pre_topc(X0_47) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_3220,plain,
    ( m1_subset_1(X0_46,u1_struct_0(X0_47)) != iProver_top
    | v2_struct_0(X0_47) = iProver_top
    | v2_struct_0(k1_tex_2(X0_47,X0_46)) != iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3154])).

cnf(c_3222,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | v2_struct_0(k1_tex_2(sK2,sK3)) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3220])).

cnf(c_3167,plain,
    ( X0_47 = X0_47 ),
    theory(equality)).

cnf(c_3195,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_3167])).

cnf(c_3175,plain,
    ( X0_47 != X1_47
    | u1_struct_0(X0_47) = u1_struct_0(X1_47) ),
    theory(equality)).

cnf(c_3187,plain,
    ( sK2 != sK2
    | u1_struct_0(sK2) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_3175])).

cnf(c_87,plain,
    ( ~ l1_pre_topc(sK2)
    | l1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_83,plain,
    ( v2_struct_0(sK2)
    | ~ l1_struct_0(sK2)
    | ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6179,c_6020,c_6015,c_5072,c_5011,c_4613,c_4566,c_4327,c_4106,c_3961,c_3948,c_3317,c_3222,c_3219,c_3195,c_3187,c_88,c_87,c_84,c_83,c_29,c_24,c_28,c_25,c_27,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n016.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:14:04 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 2.26/0.94  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.26/0.94  
% 2.26/0.94  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.26/0.94  
% 2.26/0.94  ------  iProver source info
% 2.26/0.94  
% 2.26/0.94  git: date: 2020-06-30 10:37:57 +0100
% 2.26/0.94  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.26/0.94  git: non_committed_changes: false
% 2.26/0.94  git: last_make_outside_of_git: false
% 2.26/0.94  
% 2.26/0.94  ------ 
% 2.26/0.94  
% 2.26/0.94  ------ Input Options
% 2.26/0.94  
% 2.26/0.94  --out_options                           all
% 2.26/0.94  --tptp_safe_out                         true
% 2.26/0.94  --problem_path                          ""
% 2.26/0.94  --include_path                          ""
% 2.26/0.94  --clausifier                            res/vclausify_rel
% 2.26/0.94  --clausifier_options                    --mode clausify
% 2.26/0.94  --stdin                                 false
% 2.26/0.94  --stats_out                             all
% 2.26/0.94  
% 2.26/0.94  ------ General Options
% 2.26/0.94  
% 2.26/0.94  --fof                                   false
% 2.26/0.94  --time_out_real                         305.
% 2.26/0.94  --time_out_virtual                      -1.
% 2.26/0.94  --symbol_type_check                     false
% 2.26/0.94  --clausify_out                          false
% 2.26/0.94  --sig_cnt_out                           false
% 2.26/0.94  --trig_cnt_out                          false
% 2.26/0.94  --trig_cnt_out_tolerance                1.
% 2.26/0.94  --trig_cnt_out_sk_spl                   false
% 2.26/0.94  --abstr_cl_out                          false
% 2.26/0.94  
% 2.26/0.94  ------ Global Options
% 2.26/0.94  
% 2.26/0.94  --schedule                              default
% 2.26/0.94  --add_important_lit                     false
% 2.26/0.94  --prop_solver_per_cl                    1000
% 2.26/0.94  --min_unsat_core                        false
% 2.26/0.94  --soft_assumptions                      false
% 2.26/0.94  --soft_lemma_size                       3
% 2.26/0.94  --prop_impl_unit_size                   0
% 2.26/0.94  --prop_impl_unit                        []
% 2.26/0.94  --share_sel_clauses                     true
% 2.26/0.94  --reset_solvers                         false
% 2.26/0.94  --bc_imp_inh                            [conj_cone]
% 2.26/0.94  --conj_cone_tolerance                   3.
% 2.26/0.94  --extra_neg_conj                        none
% 2.26/0.94  --large_theory_mode                     true
% 2.26/0.94  --prolific_symb_bound                   200
% 2.26/0.94  --lt_threshold                          2000
% 2.26/0.94  --clause_weak_htbl                      true
% 2.26/0.94  --gc_record_bc_elim                     false
% 2.26/0.94  
% 2.26/0.94  ------ Preprocessing Options
% 2.26/0.94  
% 2.26/0.94  --preprocessing_flag                    true
% 2.26/0.94  --time_out_prep_mult                    0.1
% 2.26/0.94  --splitting_mode                        input
% 2.26/0.94  --splitting_grd                         true
% 2.26/0.94  --splitting_cvd                         false
% 2.26/0.94  --splitting_cvd_svl                     false
% 2.26/0.94  --splitting_nvd                         32
% 2.26/0.94  --sub_typing                            true
% 2.26/0.94  --prep_gs_sim                           true
% 2.26/0.94  --prep_unflatten                        true
% 2.26/0.94  --prep_res_sim                          true
% 2.26/0.94  --prep_upred                            true
% 2.26/0.94  --prep_sem_filter                       exhaustive
% 2.26/0.94  --prep_sem_filter_out                   false
% 2.26/0.94  --pred_elim                             true
% 2.26/0.94  --res_sim_input                         true
% 2.26/0.94  --eq_ax_congr_red                       true
% 2.26/0.94  --pure_diseq_elim                       true
% 2.26/0.94  --brand_transform                       false
% 2.26/0.94  --non_eq_to_eq                          false
% 2.26/0.94  --prep_def_merge                        true
% 2.26/0.94  --prep_def_merge_prop_impl              false
% 2.26/0.94  --prep_def_merge_mbd                    true
% 2.26/0.94  --prep_def_merge_tr_red                 false
% 2.26/0.94  --prep_def_merge_tr_cl                  false
% 2.26/0.94  --smt_preprocessing                     true
% 2.26/0.94  --smt_ac_axioms                         fast
% 2.26/0.94  --preprocessed_out                      false
% 2.26/0.94  --preprocessed_stats                    false
% 2.26/0.94  
% 2.26/0.94  ------ Abstraction refinement Options
% 2.26/0.94  
% 2.26/0.94  --abstr_ref                             []
% 2.26/0.94  --abstr_ref_prep                        false
% 2.26/0.94  --abstr_ref_until_sat                   false
% 2.26/0.94  --abstr_ref_sig_restrict                funpre
% 2.26/0.94  --abstr_ref_af_restrict_to_split_sk     false
% 2.26/0.94  --abstr_ref_under                       []
% 2.26/0.94  
% 2.26/0.94  ------ SAT Options
% 2.26/0.94  
% 2.26/0.94  --sat_mode                              false
% 2.26/0.94  --sat_fm_restart_options                ""
% 2.26/0.94  --sat_gr_def                            false
% 2.26/0.94  --sat_epr_types                         true
% 2.26/0.94  --sat_non_cyclic_types                  false
% 2.26/0.94  --sat_finite_models                     false
% 2.26/0.94  --sat_fm_lemmas                         false
% 2.26/0.94  --sat_fm_prep                           false
% 2.26/0.94  --sat_fm_uc_incr                        true
% 2.26/0.94  --sat_out_model                         small
% 2.26/0.94  --sat_out_clauses                       false
% 2.26/0.94  
% 2.26/0.94  ------ QBF Options
% 2.26/0.94  
% 2.26/0.94  --qbf_mode                              false
% 2.26/0.94  --qbf_elim_univ                         false
% 2.26/0.94  --qbf_dom_inst                          none
% 2.26/0.94  --qbf_dom_pre_inst                      false
% 2.26/0.94  --qbf_sk_in                             false
% 2.26/0.94  --qbf_pred_elim                         true
% 2.26/0.94  --qbf_split                             512
% 2.26/0.94  
% 2.26/0.94  ------ BMC1 Options
% 2.26/0.94  
% 2.26/0.94  --bmc1_incremental                      false
% 2.26/0.94  --bmc1_axioms                           reachable_all
% 2.26/0.94  --bmc1_min_bound                        0
% 2.26/0.94  --bmc1_max_bound                        -1
% 2.26/0.94  --bmc1_max_bound_default                -1
% 2.26/0.94  --bmc1_symbol_reachability              true
% 2.26/0.94  --bmc1_property_lemmas                  false
% 2.26/0.94  --bmc1_k_induction                      false
% 2.26/0.94  --bmc1_non_equiv_states                 false
% 2.26/0.94  --bmc1_deadlock                         false
% 2.26/0.94  --bmc1_ucm                              false
% 2.26/0.94  --bmc1_add_unsat_core                   none
% 2.26/0.94  --bmc1_unsat_core_children              false
% 2.26/0.94  --bmc1_unsat_core_extrapolate_axioms    false
% 2.26/0.94  --bmc1_out_stat                         full
% 2.26/0.94  --bmc1_ground_init                      false
% 2.26/0.94  --bmc1_pre_inst_next_state              false
% 2.26/0.94  --bmc1_pre_inst_state                   false
% 2.26/0.94  --bmc1_pre_inst_reach_state             false
% 2.26/0.94  --bmc1_out_unsat_core                   false
% 2.26/0.94  --bmc1_aig_witness_out                  false
% 2.26/0.94  --bmc1_verbose                          false
% 2.26/0.94  --bmc1_dump_clauses_tptp                false
% 2.26/0.94  --bmc1_dump_unsat_core_tptp             false
% 2.26/0.94  --bmc1_dump_file                        -
% 2.26/0.94  --bmc1_ucm_expand_uc_limit              128
% 2.26/0.94  --bmc1_ucm_n_expand_iterations          6
% 2.26/0.94  --bmc1_ucm_extend_mode                  1
% 2.26/0.94  --bmc1_ucm_init_mode                    2
% 2.26/0.94  --bmc1_ucm_cone_mode                    none
% 2.26/0.94  --bmc1_ucm_reduced_relation_type        0
% 2.26/0.94  --bmc1_ucm_relax_model                  4
% 2.26/0.94  --bmc1_ucm_full_tr_after_sat            true
% 2.26/0.94  --bmc1_ucm_expand_neg_assumptions       false
% 2.26/0.94  --bmc1_ucm_layered_model                none
% 2.26/0.94  --bmc1_ucm_max_lemma_size               10
% 2.26/0.94  
% 2.26/0.94  ------ AIG Options
% 2.26/0.94  
% 2.26/0.94  --aig_mode                              false
% 2.26/0.94  
% 2.26/0.94  ------ Instantiation Options
% 2.26/0.94  
% 2.26/0.94  --instantiation_flag                    true
% 2.26/0.94  --inst_sos_flag                         false
% 2.26/0.94  --inst_sos_phase                        true
% 2.26/0.94  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.26/0.94  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.26/0.94  --inst_lit_sel_side                     num_symb
% 2.26/0.94  --inst_solver_per_active                1400
% 2.26/0.94  --inst_solver_calls_frac                1.
% 2.26/0.94  --inst_passive_queue_type               priority_queues
% 2.26/0.94  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.26/0.94  --inst_passive_queues_freq              [25;2]
% 2.26/0.94  --inst_dismatching                      true
% 2.26/0.94  --inst_eager_unprocessed_to_passive     true
% 2.26/0.94  --inst_prop_sim_given                   true
% 2.26/0.94  --inst_prop_sim_new                     false
% 2.26/0.94  --inst_subs_new                         false
% 2.26/0.94  --inst_eq_res_simp                      false
% 2.26/0.94  --inst_subs_given                       false
% 2.26/0.94  --inst_orphan_elimination               true
% 2.26/0.94  --inst_learning_loop_flag               true
% 2.26/0.94  --inst_learning_start                   3000
% 2.26/0.94  --inst_learning_factor                  2
% 2.26/0.94  --inst_start_prop_sim_after_learn       3
% 2.26/0.94  --inst_sel_renew                        solver
% 2.26/0.94  --inst_lit_activity_flag                true
% 2.26/0.94  --inst_restr_to_given                   false
% 2.26/0.94  --inst_activity_threshold               500
% 2.26/0.94  --inst_out_proof                        true
% 2.26/0.94  
% 2.26/0.94  ------ Resolution Options
% 2.26/0.94  
% 2.26/0.94  --resolution_flag                       true
% 2.26/0.94  --res_lit_sel                           adaptive
% 2.26/0.94  --res_lit_sel_side                      none
% 2.26/0.94  --res_ordering                          kbo
% 2.26/0.94  --res_to_prop_solver                    active
% 2.26/0.94  --res_prop_simpl_new                    false
% 2.26/0.94  --res_prop_simpl_given                  true
% 2.26/0.94  --res_passive_queue_type                priority_queues
% 2.26/0.94  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.26/0.94  --res_passive_queues_freq               [15;5]
% 2.26/0.94  --res_forward_subs                      full
% 2.26/0.94  --res_backward_subs                     full
% 2.26/0.94  --res_forward_subs_resolution           true
% 2.26/0.94  --res_backward_subs_resolution          true
% 2.26/0.94  --res_orphan_elimination                true
% 2.26/0.94  --res_time_limit                        2.
% 2.26/0.94  --res_out_proof                         true
% 2.26/0.94  
% 2.26/0.94  ------ Superposition Options
% 2.26/0.94  
% 2.26/0.94  --superposition_flag                    true
% 2.26/0.94  --sup_passive_queue_type                priority_queues
% 2.26/0.94  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.26/0.94  --sup_passive_queues_freq               [8;1;4]
% 2.26/0.94  --demod_completeness_check              fast
% 2.26/0.94  --demod_use_ground                      true
% 2.26/0.94  --sup_to_prop_solver                    passive
% 2.26/0.94  --sup_prop_simpl_new                    true
% 2.26/0.94  --sup_prop_simpl_given                  true
% 2.26/0.94  --sup_fun_splitting                     false
% 2.26/0.94  --sup_smt_interval                      50000
% 2.26/0.94  
% 2.26/0.94  ------ Superposition Simplification Setup
% 2.26/0.94  
% 2.26/0.94  --sup_indices_passive                   []
% 2.26/0.94  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.26/0.94  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.26/0.94  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.26/0.94  --sup_full_triv                         [TrivRules;PropSubs]
% 2.26/0.94  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.26/0.94  --sup_full_bw                           [BwDemod]
% 2.26/0.94  --sup_immed_triv                        [TrivRules]
% 2.26/0.94  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.26/0.94  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.26/0.94  --sup_immed_bw_main                     []
% 2.26/0.94  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.26/0.94  --sup_input_triv                        [Unflattening;TrivRules]
% 2.26/0.94  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.26/0.94  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.26/0.94  
% 2.26/0.94  ------ Combination Options
% 2.26/0.94  
% 2.26/0.94  --comb_res_mult                         3
% 2.26/0.94  --comb_sup_mult                         2
% 2.26/0.94  --comb_inst_mult                        10
% 2.26/0.94  
% 2.26/0.94  ------ Debug Options
% 2.26/0.94  
% 2.26/0.94  --dbg_backtrace                         false
% 2.26/0.94  --dbg_dump_prop_clauses                 false
% 2.26/0.94  --dbg_dump_prop_clauses_file            -
% 2.26/0.94  --dbg_out_stat                          false
% 2.26/0.94  ------ Parsing...
% 2.26/0.94  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.26/0.94  
% 2.26/0.94  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.26/0.94  
% 2.26/0.94  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.26/0.94  
% 2.26/0.94  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.26/0.94  ------ Proving...
% 2.26/0.94  ------ Problem Properties 
% 2.26/0.94  
% 2.26/0.94  
% 2.26/0.94  clauses                                 25
% 2.26/0.94  conjectures                             3
% 2.26/0.94  EPR                                     3
% 2.26/0.94  Horn                                    15
% 2.26/0.94  unary                                   3
% 2.26/0.94  binary                                  1
% 2.26/0.94  lits                                    77
% 2.26/0.94  lits eq                                 5
% 2.26/0.94  fd_pure                                 0
% 2.26/0.94  fd_pseudo                               0
% 2.26/0.94  fd_cond                                 0
% 2.26/0.94  fd_pseudo_cond                          1
% 2.26/0.94  AC symbols                              0
% 2.26/0.94  
% 2.26/0.94  ------ Schedule dynamic 5 is on 
% 2.26/0.94  
% 2.26/0.94  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.26/0.94  
% 2.26/0.94  
% 2.26/0.94  ------ 
% 2.26/0.94  Current options:
% 2.26/0.94  ------ 
% 2.26/0.94  
% 2.26/0.94  ------ Input Options
% 2.26/0.94  
% 2.26/0.94  --out_options                           all
% 2.26/0.94  --tptp_safe_out                         true
% 2.26/0.94  --problem_path                          ""
% 2.26/0.94  --include_path                          ""
% 2.26/0.94  --clausifier                            res/vclausify_rel
% 2.26/0.94  --clausifier_options                    --mode clausify
% 2.26/0.94  --stdin                                 false
% 2.26/0.94  --stats_out                             all
% 2.26/0.94  
% 2.26/0.94  ------ General Options
% 2.26/0.94  
% 2.26/0.94  --fof                                   false
% 2.26/0.94  --time_out_real                         305.
% 2.26/0.94  --time_out_virtual                      -1.
% 2.26/0.94  --symbol_type_check                     false
% 2.26/0.94  --clausify_out                          false
% 2.26/0.94  --sig_cnt_out                           false
% 2.26/0.94  --trig_cnt_out                          false
% 2.26/0.94  --trig_cnt_out_tolerance                1.
% 2.26/0.94  --trig_cnt_out_sk_spl                   false
% 2.26/0.94  --abstr_cl_out                          false
% 2.26/0.94  
% 2.26/0.94  ------ Global Options
% 2.26/0.94  
% 2.26/0.94  --schedule                              default
% 2.26/0.94  --add_important_lit                     false
% 2.26/0.94  --prop_solver_per_cl                    1000
% 2.26/0.94  --min_unsat_core                        false
% 2.26/0.94  --soft_assumptions                      false
% 2.26/0.94  --soft_lemma_size                       3
% 2.26/0.94  --prop_impl_unit_size                   0
% 2.26/0.94  --prop_impl_unit                        []
% 2.26/0.94  --share_sel_clauses                     true
% 2.26/0.94  --reset_solvers                         false
% 2.26/0.94  --bc_imp_inh                            [conj_cone]
% 2.26/0.94  --conj_cone_tolerance                   3.
% 2.26/0.94  --extra_neg_conj                        none
% 2.26/0.94  --large_theory_mode                     true
% 2.26/0.94  --prolific_symb_bound                   200
% 2.26/0.94  --lt_threshold                          2000
% 2.26/0.94  --clause_weak_htbl                      true
% 2.26/0.94  --gc_record_bc_elim                     false
% 2.26/0.94  
% 2.26/0.94  ------ Preprocessing Options
% 2.26/0.94  
% 2.26/0.94  --preprocessing_flag                    true
% 2.26/0.94  --time_out_prep_mult                    0.1
% 2.26/0.94  --splitting_mode                        input
% 2.26/0.94  --splitting_grd                         true
% 2.26/0.94  --splitting_cvd                         false
% 2.26/0.94  --splitting_cvd_svl                     false
% 2.26/0.94  --splitting_nvd                         32
% 2.26/0.94  --sub_typing                            true
% 2.26/0.94  --prep_gs_sim                           true
% 2.26/0.94  --prep_unflatten                        true
% 2.26/0.94  --prep_res_sim                          true
% 2.26/0.94  --prep_upred                            true
% 2.26/0.94  --prep_sem_filter                       exhaustive
% 2.26/0.94  --prep_sem_filter_out                   false
% 2.26/0.94  --pred_elim                             true
% 2.26/0.94  --res_sim_input                         true
% 2.26/0.94  --eq_ax_congr_red                       true
% 2.26/0.94  --pure_diseq_elim                       true
% 2.26/0.94  --brand_transform                       false
% 2.26/0.94  --non_eq_to_eq                          false
% 2.26/0.94  --prep_def_merge                        true
% 2.26/0.94  --prep_def_merge_prop_impl              false
% 2.26/0.94  --prep_def_merge_mbd                    true
% 2.26/0.94  --prep_def_merge_tr_red                 false
% 2.26/0.94  --prep_def_merge_tr_cl                  false
% 2.26/0.94  --smt_preprocessing                     true
% 2.26/0.94  --smt_ac_axioms                         fast
% 2.26/0.94  --preprocessed_out                      false
% 2.26/0.94  --preprocessed_stats                    false
% 2.26/0.94  
% 2.26/0.94  ------ Abstraction refinement Options
% 2.26/0.94  
% 2.26/0.94  --abstr_ref                             []
% 2.26/0.94  --abstr_ref_prep                        false
% 2.26/0.94  --abstr_ref_until_sat                   false
% 2.26/0.94  --abstr_ref_sig_restrict                funpre
% 2.26/0.94  --abstr_ref_af_restrict_to_split_sk     false
% 2.26/0.94  --abstr_ref_under                       []
% 2.26/0.94  
% 2.26/0.94  ------ SAT Options
% 2.26/0.94  
% 2.26/0.94  --sat_mode                              false
% 2.26/0.94  --sat_fm_restart_options                ""
% 2.26/0.94  --sat_gr_def                            false
% 2.26/0.94  --sat_epr_types                         true
% 2.26/0.94  --sat_non_cyclic_types                  false
% 2.26/0.94  --sat_finite_models                     false
% 2.26/0.94  --sat_fm_lemmas                         false
% 2.26/0.94  --sat_fm_prep                           false
% 2.26/0.94  --sat_fm_uc_incr                        true
% 2.26/0.94  --sat_out_model                         small
% 2.26/0.94  --sat_out_clauses                       false
% 2.26/0.94  
% 2.26/0.94  ------ QBF Options
% 2.26/0.94  
% 2.26/0.94  --qbf_mode                              false
% 2.26/0.94  --qbf_elim_univ                         false
% 2.26/0.94  --qbf_dom_inst                          none
% 2.26/0.94  --qbf_dom_pre_inst                      false
% 2.26/0.94  --qbf_sk_in                             false
% 2.26/0.94  --qbf_pred_elim                         true
% 2.26/0.94  --qbf_split                             512
% 2.26/0.94  
% 2.26/0.94  ------ BMC1 Options
% 2.26/0.94  
% 2.26/0.94  --bmc1_incremental                      false
% 2.26/0.94  --bmc1_axioms                           reachable_all
% 2.26/0.94  --bmc1_min_bound                        0
% 2.26/0.94  --bmc1_max_bound                        -1
% 2.26/0.94  --bmc1_max_bound_default                -1
% 2.26/0.94  --bmc1_symbol_reachability              true
% 2.26/0.94  --bmc1_property_lemmas                  false
% 2.26/0.94  --bmc1_k_induction                      false
% 2.26/0.94  --bmc1_non_equiv_states                 false
% 2.26/0.94  --bmc1_deadlock                         false
% 2.26/0.94  --bmc1_ucm                              false
% 2.26/0.94  --bmc1_add_unsat_core                   none
% 2.26/0.94  --bmc1_unsat_core_children              false
% 2.26/0.94  --bmc1_unsat_core_extrapolate_axioms    false
% 2.26/0.94  --bmc1_out_stat                         full
% 2.26/0.94  --bmc1_ground_init                      false
% 2.26/0.94  --bmc1_pre_inst_next_state              false
% 2.26/0.94  --bmc1_pre_inst_state                   false
% 2.26/0.94  --bmc1_pre_inst_reach_state             false
% 2.26/0.94  --bmc1_out_unsat_core                   false
% 2.26/0.94  --bmc1_aig_witness_out                  false
% 2.26/0.94  --bmc1_verbose                          false
% 2.26/0.94  --bmc1_dump_clauses_tptp                false
% 2.26/0.94  --bmc1_dump_unsat_core_tptp             false
% 2.26/0.94  --bmc1_dump_file                        -
% 2.26/0.94  --bmc1_ucm_expand_uc_limit              128
% 2.26/0.94  --bmc1_ucm_n_expand_iterations          6
% 2.26/0.94  --bmc1_ucm_extend_mode                  1
% 2.26/0.94  --bmc1_ucm_init_mode                    2
% 2.26/0.94  --bmc1_ucm_cone_mode                    none
% 2.26/0.94  --bmc1_ucm_reduced_relation_type        0
% 2.26/0.94  --bmc1_ucm_relax_model                  4
% 2.26/0.94  --bmc1_ucm_full_tr_after_sat            true
% 2.26/0.94  --bmc1_ucm_expand_neg_assumptions       false
% 2.26/0.94  --bmc1_ucm_layered_model                none
% 2.26/0.94  --bmc1_ucm_max_lemma_size               10
% 2.26/0.94  
% 2.26/0.94  ------ AIG Options
% 2.26/0.94  
% 2.26/0.94  --aig_mode                              false
% 2.26/0.94  
% 2.26/0.94  ------ Instantiation Options
% 2.26/0.94  
% 2.26/0.94  --instantiation_flag                    true
% 2.26/0.94  --inst_sos_flag                         false
% 2.26/0.94  --inst_sos_phase                        true
% 2.26/0.94  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.26/0.94  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.26/0.94  --inst_lit_sel_side                     none
% 2.26/0.94  --inst_solver_per_active                1400
% 2.26/0.94  --inst_solver_calls_frac                1.
% 2.26/0.94  --inst_passive_queue_type               priority_queues
% 2.26/0.94  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.26/0.94  --inst_passive_queues_freq              [25;2]
% 2.26/0.94  --inst_dismatching                      true
% 2.26/0.94  --inst_eager_unprocessed_to_passive     true
% 2.26/0.94  --inst_prop_sim_given                   true
% 2.26/0.94  --inst_prop_sim_new                     false
% 2.26/0.94  --inst_subs_new                         false
% 2.26/0.94  --inst_eq_res_simp                      false
% 2.26/0.94  --inst_subs_given                       false
% 2.26/0.94  --inst_orphan_elimination               true
% 2.26/0.94  --inst_learning_loop_flag               true
% 2.26/0.94  --inst_learning_start                   3000
% 2.26/0.94  --inst_learning_factor                  2
% 2.26/0.94  --inst_start_prop_sim_after_learn       3
% 2.26/0.94  --inst_sel_renew                        solver
% 2.26/0.94  --inst_lit_activity_flag                true
% 2.26/0.94  --inst_restr_to_given                   false
% 2.26/0.94  --inst_activity_threshold               500
% 2.26/0.94  --inst_out_proof                        true
% 2.26/0.94  
% 2.26/0.94  ------ Resolution Options
% 2.26/0.94  
% 2.26/0.94  --resolution_flag                       false
% 2.26/0.94  --res_lit_sel                           adaptive
% 2.26/0.94  --res_lit_sel_side                      none
% 2.26/0.94  --res_ordering                          kbo
% 2.26/0.94  --res_to_prop_solver                    active
% 2.26/0.94  --res_prop_simpl_new                    false
% 2.26/0.94  --res_prop_simpl_given                  true
% 2.26/0.94  --res_passive_queue_type                priority_queues
% 2.26/0.94  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.26/0.94  --res_passive_queues_freq               [15;5]
% 2.26/0.94  --res_forward_subs                      full
% 2.26/0.94  --res_backward_subs                     full
% 2.26/0.94  --res_forward_subs_resolution           true
% 2.26/0.94  --res_backward_subs_resolution          true
% 2.26/0.94  --res_orphan_elimination                true
% 2.26/0.94  --res_time_limit                        2.
% 2.26/0.94  --res_out_proof                         true
% 2.26/0.94  
% 2.26/0.94  ------ Superposition Options
% 2.26/0.94  
% 2.26/0.94  --superposition_flag                    true
% 2.26/0.94  --sup_passive_queue_type                priority_queues
% 2.26/0.94  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.26/0.94  --sup_passive_queues_freq               [8;1;4]
% 2.26/0.94  --demod_completeness_check              fast
% 2.26/0.94  --demod_use_ground                      true
% 2.26/0.94  --sup_to_prop_solver                    passive
% 2.26/0.94  --sup_prop_simpl_new                    true
% 2.26/0.94  --sup_prop_simpl_given                  true
% 2.26/0.94  --sup_fun_splitting                     false
% 2.26/0.94  --sup_smt_interval                      50000
% 2.26/0.94  
% 2.26/0.94  ------ Superposition Simplification Setup
% 2.26/0.94  
% 2.26/0.94  --sup_indices_passive                   []
% 2.26/0.94  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.26/0.94  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.26/0.94  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.26/0.94  --sup_full_triv                         [TrivRules;PropSubs]
% 2.26/0.94  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.26/0.94  --sup_full_bw                           [BwDemod]
% 2.26/0.94  --sup_immed_triv                        [TrivRules]
% 2.26/0.94  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.26/0.94  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.26/0.94  --sup_immed_bw_main                     []
% 2.26/0.94  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.26/0.94  --sup_input_triv                        [Unflattening;TrivRules]
% 2.26/0.94  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.26/0.94  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.26/0.94  
% 2.26/0.94  ------ Combination Options
% 2.26/0.94  
% 2.26/0.94  --comb_res_mult                         3
% 2.26/0.94  --comb_sup_mult                         2
% 2.26/0.94  --comb_inst_mult                        10
% 2.26/0.94  
% 2.26/0.94  ------ Debug Options
% 2.26/0.94  
% 2.26/0.94  --dbg_backtrace                         false
% 2.26/0.94  --dbg_dump_prop_clauses                 false
% 2.26/0.94  --dbg_dump_prop_clauses_file            -
% 2.26/0.94  --dbg_out_stat                          false
% 2.26/0.94  
% 2.26/0.94  
% 2.26/0.94  
% 2.26/0.94  
% 2.26/0.94  ------ Proving...
% 2.26/0.94  
% 2.26/0.94  
% 2.26/0.94  % SZS status Theorem for theBenchmark.p
% 2.26/0.94  
% 2.26/0.94  % SZS output start CNFRefutation for theBenchmark.p
% 2.26/0.94  
% 2.26/0.94  fof(f10,axiom,(
% 2.26/0.94    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v1_subset_1(X2,u1_struct_0(X0)))))))),
% 2.26/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.26/0.94  
% 2.26/0.94  fof(f32,plain,(
% 2.26/0.94    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : ((v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.26/0.94    inference(ennf_transformation,[],[f10])).
% 2.26/0.94  
% 2.26/0.94  fof(f33,plain,(
% 2.26/0.94    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.26/0.94    inference(flattening,[],[f32])).
% 2.26/0.94  
% 2.26/0.94  fof(f47,plain,(
% 2.26/0.94    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.26/0.94    inference(nnf_transformation,[],[f33])).
% 2.26/0.94  
% 2.26/0.94  fof(f48,plain,(
% 2.26/0.94    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.26/0.94    inference(rectify,[],[f47])).
% 2.26/0.94  
% 2.26/0.94  fof(f49,plain,(
% 2.26/0.94    ! [X1,X0] : (? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_subset_1(sK1(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK1(X0,X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.26/0.94    introduced(choice_axiom,[])).
% 2.26/0.94  
% 2.26/0.94  fof(f50,plain,(
% 2.26/0.94    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | (~v1_subset_1(sK1(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK1(X0,X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.26/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f48,f49])).
% 2.26/0.94  
% 2.26/0.94  fof(f68,plain,(
% 2.26/0.94    ( ! [X0,X3,X1] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.26/0.94    inference(cnf_transformation,[],[f50])).
% 2.26/0.94  
% 2.26/0.94  fof(f84,plain,(
% 2.26/0.94    ( ! [X0,X1] : (v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.26/0.94    inference(equality_resolution,[],[f68])).
% 2.26/0.94  
% 2.26/0.94  fof(f7,axiom,(
% 2.26/0.94    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.26/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.26/0.94  
% 2.26/0.94  fof(f28,plain,(
% 2.26/0.94    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.26/0.94    inference(ennf_transformation,[],[f7])).
% 2.26/0.94  
% 2.26/0.94  fof(f63,plain,(
% 2.26/0.94    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.26/0.94    inference(cnf_transformation,[],[f28])).
% 2.26/0.94  
% 2.26/0.94  fof(f15,conjecture,(
% 2.26/0.94    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 2.26/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.26/0.94  
% 2.26/0.94  fof(f16,negated_conjecture,(
% 2.26/0.94    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 2.26/0.94    inference(negated_conjecture,[],[f15])).
% 2.26/0.94  
% 2.26/0.94  fof(f41,plain,(
% 2.26/0.94    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.26/0.94    inference(ennf_transformation,[],[f16])).
% 2.26/0.94  
% 2.26/0.94  fof(f42,plain,(
% 2.26/0.94    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.26/0.94    inference(flattening,[],[f41])).
% 2.26/0.94  
% 2.26/0.94  fof(f52,plain,(
% 2.26/0.94    ? [X0] : (? [X1] : (((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.26/0.94    inference(nnf_transformation,[],[f42])).
% 2.26/0.94  
% 2.26/0.94  fof(f53,plain,(
% 2.26/0.94    ? [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.26/0.94    inference(flattening,[],[f52])).
% 2.26/0.94  
% 2.26/0.94  fof(f55,plain,(
% 2.26/0.94    ( ! [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) => ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),sK3),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,sK3),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),sK3),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,sK3),X0)) & m1_subset_1(sK3,u1_struct_0(X0)))) )),
% 2.26/0.94    introduced(choice_axiom,[])).
% 2.26/0.94  
% 2.26/0.94  fof(f54,plain,(
% 2.26/0.94    ? [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(sK2),X1),u1_struct_0(sK2)) | ~v1_tex_2(k1_tex_2(sK2,X1),sK2)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK2),X1),u1_struct_0(sK2)) | v1_tex_2(k1_tex_2(sK2,X1),sK2)) & m1_subset_1(X1,u1_struct_0(sK2))) & l1_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 2.26/0.94    introduced(choice_axiom,[])).
% 2.26/0.94  
% 2.26/0.94  fof(f56,plain,(
% 2.26/0.94    ((~v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) | ~v1_tex_2(k1_tex_2(sK2,sK3),sK2)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) | v1_tex_2(k1_tex_2(sK2,sK3),sK2)) & m1_subset_1(sK3,u1_struct_0(sK2))) & l1_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 2.26/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f53,f55,f54])).
% 2.26/0.94  
% 2.26/0.94  fof(f82,plain,(
% 2.26/0.94    v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) | v1_tex_2(k1_tex_2(sK2,sK3),sK2)),
% 2.26/0.94    inference(cnf_transformation,[],[f56])).
% 2.26/0.94  
% 2.26/0.94  fof(f80,plain,(
% 2.26/0.94    l1_pre_topc(sK2)),
% 2.26/0.94    inference(cnf_transformation,[],[f56])).
% 2.26/0.94  
% 2.26/0.94  fof(f79,plain,(
% 2.26/0.94    ~v2_struct_0(sK2)),
% 2.26/0.94    inference(cnf_transformation,[],[f56])).
% 2.26/0.94  
% 2.26/0.94  fof(f81,plain,(
% 2.26/0.94    m1_subset_1(sK3,u1_struct_0(sK2))),
% 2.26/0.94    inference(cnf_transformation,[],[f56])).
% 2.26/0.94  
% 2.26/0.94  fof(f4,axiom,(
% 2.26/0.94    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.26/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.26/0.94  
% 2.26/0.94  fof(f22,plain,(
% 2.26/0.94    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.26/0.94    inference(ennf_transformation,[],[f4])).
% 2.26/0.94  
% 2.26/0.94  fof(f23,plain,(
% 2.26/0.94    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.26/0.94    inference(flattening,[],[f22])).
% 2.26/0.94  
% 2.26/0.94  fof(f60,plain,(
% 2.26/0.94    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.26/0.94    inference(cnf_transformation,[],[f23])).
% 2.26/0.94  
% 2.26/0.94  fof(f2,axiom,(
% 2.26/0.94    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.26/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.26/0.94  
% 2.26/0.94  fof(f20,plain,(
% 2.26/0.94    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.26/0.94    inference(ennf_transformation,[],[f2])).
% 2.26/0.94  
% 2.26/0.94  fof(f58,plain,(
% 2.26/0.94    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.26/0.94    inference(cnf_transformation,[],[f20])).
% 2.26/0.94  
% 2.26/0.94  fof(f12,axiom,(
% 2.26/0.94    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 2.26/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.26/0.94  
% 2.26/0.94  fof(f17,plain,(
% 2.26/0.94    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 2.26/0.94    inference(pure_predicate_removal,[],[f12])).
% 2.26/0.94  
% 2.26/0.94  fof(f35,plain,(
% 2.26/0.94    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.26/0.94    inference(ennf_transformation,[],[f17])).
% 2.26/0.94  
% 2.26/0.94  fof(f36,plain,(
% 2.26/0.94    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.26/0.94    inference(flattening,[],[f35])).
% 2.26/0.94  
% 2.26/0.94  fof(f75,plain,(
% 2.26/0.94    ( ! [X0,X1] : (m1_pre_topc(k1_tex_2(X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.26/0.94    inference(cnf_transformation,[],[f36])).
% 2.26/0.94  
% 2.26/0.94  fof(f5,axiom,(
% 2.26/0.94    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 2.26/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.26/0.94  
% 2.26/0.94  fof(f24,plain,(
% 2.26/0.94    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 2.26/0.94    inference(ennf_transformation,[],[f5])).
% 2.26/0.94  
% 2.26/0.94  fof(f25,plain,(
% 2.26/0.94    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 2.26/0.94    inference(flattening,[],[f24])).
% 2.26/0.94  
% 2.26/0.94  fof(f61,plain,(
% 2.26/0.94    ( ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0)) )),
% 2.26/0.94    inference(cnf_transformation,[],[f25])).
% 2.26/0.94  
% 2.26/0.94  fof(f13,axiom,(
% 2.26/0.94    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 2.26/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.26/0.94  
% 2.26/0.94  fof(f18,plain,(
% 2.26/0.94    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 2.26/0.94    inference(pure_predicate_removal,[],[f13])).
% 2.26/0.94  
% 2.26/0.94  fof(f37,plain,(
% 2.26/0.94    ! [X0,X1] : ((v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.26/0.94    inference(ennf_transformation,[],[f18])).
% 2.26/0.94  
% 2.26/0.94  fof(f38,plain,(
% 2.26/0.94    ! [X0,X1] : ((v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.26/0.94    inference(flattening,[],[f37])).
% 2.26/0.94  
% 2.26/0.94  fof(f77,plain,(
% 2.26/0.94    ( ! [X0,X1] : (v7_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.26/0.94    inference(cnf_transformation,[],[f38])).
% 2.26/0.94  
% 2.26/0.94  fof(f3,axiom,(
% 2.26/0.94    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.26/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.26/0.94  
% 2.26/0.94  fof(f21,plain,(
% 2.26/0.94    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.26/0.94    inference(ennf_transformation,[],[f3])).
% 2.26/0.94  
% 2.26/0.94  fof(f59,plain,(
% 2.26/0.94    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.26/0.94    inference(cnf_transformation,[],[f21])).
% 2.26/0.94  
% 2.26/0.94  fof(f11,axiom,(
% 2.26/0.94    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 2.26/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.26/0.94  
% 2.26/0.94  fof(f34,plain,(
% 2.26/0.94    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.26/0.94    inference(ennf_transformation,[],[f11])).
% 2.26/0.94  
% 2.26/0.94  fof(f51,plain,(
% 2.26/0.94    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.26/0.94    inference(nnf_transformation,[],[f34])).
% 2.26/0.94  
% 2.26/0.94  fof(f73,plain,(
% 2.26/0.94    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.26/0.94    inference(cnf_transformation,[],[f51])).
% 2.26/0.94  
% 2.26/0.94  fof(f14,axiom,(
% 2.26/0.94    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 2.26/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.26/0.94  
% 2.26/0.94  fof(f39,plain,(
% 2.26/0.94    ! [X0] : (! [X1] : ((~v1_zfmisc_1(X0) | ~v1_subset_1(k6_domain_1(X0,X1),X0)) | ~m1_subset_1(X1,X0)) | v1_xboole_0(X0))),
% 2.26/0.94    inference(ennf_transformation,[],[f14])).
% 2.26/0.94  
% 2.26/0.94  fof(f40,plain,(
% 2.26/0.94    ! [X0] : (! [X1] : (~v1_zfmisc_1(X0) | ~v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | v1_xboole_0(X0))),
% 2.26/0.94    inference(flattening,[],[f39])).
% 2.26/0.94  
% 2.26/0.94  fof(f78,plain,(
% 2.26/0.94    ( ! [X0,X1] : (~v1_zfmisc_1(X0) | ~v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.26/0.94    inference(cnf_transformation,[],[f40])).
% 2.26/0.94  
% 2.26/0.94  fof(f8,axiom,(
% 2.26/0.94    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (~v1_xboole_0(X1) => ~v1_subset_1(X1,X0))))),
% 2.26/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.26/0.94  
% 2.26/0.94  fof(f29,plain,(
% 2.26/0.94    ! [X0] : (! [X1] : ((~v1_subset_1(X1,X0) | v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | (~v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 2.26/0.94    inference(ennf_transformation,[],[f8])).
% 2.26/0.94  
% 2.26/0.94  fof(f30,plain,(
% 2.26/0.94    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 2.26/0.94    inference(flattening,[],[f29])).
% 2.26/0.94  
% 2.26/0.94  fof(f64,plain,(
% 2.26/0.94    ( ! [X0,X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 2.26/0.94    inference(cnf_transformation,[],[f30])).
% 2.26/0.94  
% 2.26/0.94  fof(f1,axiom,(
% 2.26/0.94    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~v1_subset_1(X1,X0)))),
% 2.26/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.26/0.94  
% 2.26/0.94  fof(f19,plain,(
% 2.26/0.94    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 2.26/0.94    inference(ennf_transformation,[],[f1])).
% 2.26/0.94  
% 2.26/0.94  fof(f57,plain,(
% 2.26/0.94    ( ! [X0,X1] : (~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 2.26/0.94    inference(cnf_transformation,[],[f19])).
% 2.26/0.94  
% 2.26/0.94  fof(f6,axiom,(
% 2.26/0.94    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.26/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.26/0.94  
% 2.26/0.94  fof(f26,plain,(
% 2.26/0.94    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.26/0.94    inference(ennf_transformation,[],[f6])).
% 2.26/0.94  
% 2.26/0.94  fof(f27,plain,(
% 2.26/0.94    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.26/0.94    inference(flattening,[],[f26])).
% 2.26/0.94  
% 2.26/0.94  fof(f62,plain,(
% 2.26/0.94    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.26/0.94    inference(cnf_transformation,[],[f27])).
% 2.26/0.94  
% 2.26/0.94  fof(f70,plain,(
% 2.26/0.94    ( ! [X0,X1] : (v1_tex_2(X1,X0) | u1_struct_0(X1) = sK1(X0,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.26/0.94    inference(cnf_transformation,[],[f50])).
% 2.26/0.94  
% 2.26/0.94  fof(f83,plain,(
% 2.26/0.94    ~v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) | ~v1_tex_2(k1_tex_2(sK2,sK3),sK2)),
% 2.26/0.94    inference(cnf_transformation,[],[f56])).
% 2.26/0.94  
% 2.26/0.94  fof(f9,axiom,(
% 2.26/0.94    ! [X0] : (~v1_xboole_0(X0) => (v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))))),
% 2.26/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.26/0.94  
% 2.26/0.94  fof(f31,plain,(
% 2.26/0.94    ! [X0] : ((v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))) | v1_xboole_0(X0))),
% 2.26/0.94    inference(ennf_transformation,[],[f9])).
% 2.26/0.94  
% 2.26/0.94  fof(f43,plain,(
% 2.26/0.94    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 2.26/0.94    inference(nnf_transformation,[],[f31])).
% 2.26/0.94  
% 2.26/0.94  fof(f44,plain,(
% 2.26/0.94    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 2.26/0.94    inference(rectify,[],[f43])).
% 2.26/0.94  
% 2.26/0.94  fof(f45,plain,(
% 2.26/0.94    ! [X0] : (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) => (k6_domain_1(X0,sK0(X0)) = X0 & m1_subset_1(sK0(X0),X0)))),
% 2.26/0.94    introduced(choice_axiom,[])).
% 2.26/0.94  
% 2.26/0.94  fof(f46,plain,(
% 2.26/0.94    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & ((k6_domain_1(X0,sK0(X0)) = X0 & m1_subset_1(sK0(X0),X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 2.26/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f44,f45])).
% 2.26/0.94  
% 2.26/0.94  fof(f67,plain,(
% 2.26/0.94    ( ! [X0,X1] : (v1_zfmisc_1(X0) | k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.26/0.94    inference(cnf_transformation,[],[f46])).
% 2.26/0.94  
% 2.26/0.94  fof(f71,plain,(
% 2.26/0.94    ( ! [X0,X1] : (v1_tex_2(X1,X0) | ~v1_subset_1(sK1(X0,X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.26/0.94    inference(cnf_transformation,[],[f50])).
% 2.26/0.94  
% 2.26/0.94  fof(f76,plain,(
% 2.26/0.94    ( ! [X0,X1] : (~v2_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.26/0.94    inference(cnf_transformation,[],[f38])).
% 2.26/0.94  
% 2.26/0.94  cnf(c_3168,plain,
% 2.26/0.94      ( X0_46 != X1_46 | X2_46 != X1_46 | X2_46 = X0_46 ),
% 2.26/0.94      theory(equality) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_4050,plain,
% 2.26/0.94      ( k6_domain_1(u1_struct_0(sK2),sK3) != X0_46
% 2.26/0.94      | k6_domain_1(u1_struct_0(sK2),sK3) = u1_struct_0(sK2)
% 2.26/0.94      | u1_struct_0(sK2) != X0_46 ),
% 2.26/0.94      inference(instantiation,[status(thm)],[c_3168]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_6179,plain,
% 2.26/0.94      ( k6_domain_1(u1_struct_0(sK2),sK3) != k6_domain_1(u1_struct_0(sK2),sK3)
% 2.26/0.94      | k6_domain_1(u1_struct_0(sK2),sK3) = u1_struct_0(sK2)
% 2.26/0.94      | u1_struct_0(sK2) != k6_domain_1(u1_struct_0(sK2),sK3) ),
% 2.26/0.94      inference(instantiation,[status(thm)],[c_4050]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_14,plain,
% 2.26/0.94      ( ~ v1_tex_2(X0,X1)
% 2.26/0.94      | ~ m1_pre_topc(X0,X1)
% 2.26/0.94      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.26/0.94      | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
% 2.26/0.94      | ~ l1_pre_topc(X1) ),
% 2.26/0.94      inference(cnf_transformation,[],[f84]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_6,plain,
% 2.26/0.94      ( ~ m1_pre_topc(X0,X1)
% 2.26/0.94      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.26/0.94      | ~ l1_pre_topc(X1) ),
% 2.26/0.94      inference(cnf_transformation,[],[f63]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_157,plain,
% 2.26/0.94      ( ~ m1_pre_topc(X0,X1)
% 2.26/0.94      | ~ v1_tex_2(X0,X1)
% 2.26/0.94      | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
% 2.26/0.94      | ~ l1_pre_topc(X1) ),
% 2.26/0.94      inference(global_propositional_subsumption,
% 2.26/0.94                [status(thm)],
% 2.26/0.94                [c_14,c_6]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_158,plain,
% 2.26/0.94      ( ~ v1_tex_2(X0,X1)
% 2.26/0.94      | ~ m1_pre_topc(X0,X1)
% 2.26/0.94      | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
% 2.26/0.94      | ~ l1_pre_topc(X1) ),
% 2.26/0.94      inference(renaming,[status(thm)],[c_157]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_23,negated_conjecture,
% 2.26/0.94      ( v1_tex_2(k1_tex_2(sK2,sK3),sK2)
% 2.26/0.94      | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) ),
% 2.26/0.94      inference(cnf_transformation,[],[f82]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_213,plain,
% 2.26/0.94      ( v1_tex_2(k1_tex_2(sK2,sK3),sK2)
% 2.26/0.94      | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) ),
% 2.26/0.94      inference(prop_impl,[status(thm)],[c_23]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_698,plain,
% 2.26/0.94      ( ~ m1_pre_topc(X0,X1)
% 2.26/0.94      | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 2.26/0.94      | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
% 2.26/0.94      | ~ l1_pre_topc(X1)
% 2.26/0.94      | k1_tex_2(sK2,sK3) != X0
% 2.26/0.94      | sK2 != X1 ),
% 2.26/0.94      inference(resolution_lifted,[status(thm)],[c_158,c_213]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_699,plain,
% 2.26/0.94      ( ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
% 2.26/0.94      | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 2.26/0.94      | v1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),u1_struct_0(sK2))
% 2.26/0.94      | ~ l1_pre_topc(sK2) ),
% 2.26/0.94      inference(unflattening,[status(thm)],[c_698]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_25,negated_conjecture,
% 2.26/0.94      ( l1_pre_topc(sK2) ),
% 2.26/0.94      inference(cnf_transformation,[],[f80]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_701,plain,
% 2.26/0.94      ( v1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),u1_struct_0(sK2))
% 2.26/0.94      | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 2.26/0.94      | ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2) ),
% 2.26/0.94      inference(global_propositional_subsumption,
% 2.26/0.94                [status(thm)],
% 2.26/0.94                [c_699,c_25]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_702,plain,
% 2.26/0.94      ( ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
% 2.26/0.94      | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 2.26/0.94      | v1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),u1_struct_0(sK2)) ),
% 2.26/0.94      inference(renaming,[status(thm)],[c_701]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_3141,plain,
% 2.26/0.94      ( ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
% 2.26/0.94      | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 2.26/0.94      | v1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),u1_struct_0(sK2)) ),
% 2.26/0.94      inference(subtyping,[status(esa)],[c_702]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_3710,plain,
% 2.26/0.94      ( m1_pre_topc(k1_tex_2(sK2,sK3),sK2) != iProver_top
% 2.26/0.94      | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) = iProver_top
% 2.26/0.94      | v1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),u1_struct_0(sK2)) = iProver_top ),
% 2.26/0.94      inference(predicate_to_equality,[status(thm)],[c_3141]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_26,negated_conjecture,
% 2.26/0.94      ( ~ v2_struct_0(sK2) ),
% 2.26/0.94      inference(cnf_transformation,[],[f79]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_27,plain,
% 2.26/0.94      ( v2_struct_0(sK2) != iProver_top ),
% 2.26/0.94      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_28,plain,
% 2.26/0.94      ( l1_pre_topc(sK2) = iProver_top ),
% 2.26/0.94      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_24,negated_conjecture,
% 2.26/0.94      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 2.26/0.94      inference(cnf_transformation,[],[f81]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_29,plain,
% 2.26/0.94      ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
% 2.26/0.94      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_3,plain,
% 2.26/0.94      ( v2_struct_0(X0)
% 2.26/0.94      | ~ l1_struct_0(X0)
% 2.26/0.94      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.26/0.94      inference(cnf_transformation,[],[f60]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_82,plain,
% 2.26/0.94      ( v2_struct_0(X0) = iProver_top
% 2.26/0.94      | l1_struct_0(X0) != iProver_top
% 2.26/0.94      | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
% 2.26/0.94      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_84,plain,
% 2.26/0.94      ( v2_struct_0(sK2) = iProver_top
% 2.26/0.94      | l1_struct_0(sK2) != iProver_top
% 2.26/0.94      | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 2.26/0.94      inference(instantiation,[status(thm)],[c_82]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_1,plain,
% 2.26/0.94      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 2.26/0.94      inference(cnf_transformation,[],[f58]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_86,plain,
% 2.26/0.94      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 2.26/0.94      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_88,plain,
% 2.26/0.94      ( l1_pre_topc(sK2) != iProver_top
% 2.26/0.94      | l1_struct_0(sK2) = iProver_top ),
% 2.26/0.94      inference(instantiation,[status(thm)],[c_86]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_17,plain,
% 2.26/0.94      ( m1_pre_topc(k1_tex_2(X0,X1),X0)
% 2.26/0.94      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.26/0.94      | v2_struct_0(X0)
% 2.26/0.94      | ~ l1_pre_topc(X0) ),
% 2.26/0.94      inference(cnf_transformation,[],[f75]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_3155,plain,
% 2.26/0.94      ( m1_pre_topc(k1_tex_2(X0_47,X0_46),X0_47)
% 2.26/0.94      | ~ m1_subset_1(X0_46,u1_struct_0(X0_47))
% 2.26/0.94      | v2_struct_0(X0_47)
% 2.26/0.94      | ~ l1_pre_topc(X0_47) ),
% 2.26/0.94      inference(subtyping,[status(esa)],[c_17]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_3217,plain,
% 2.26/0.94      ( m1_pre_topc(k1_tex_2(X0_47,X0_46),X0_47) = iProver_top
% 2.26/0.94      | m1_subset_1(X0_46,u1_struct_0(X0_47)) != iProver_top
% 2.26/0.94      | v2_struct_0(X0_47) = iProver_top
% 2.26/0.94      | l1_pre_topc(X0_47) != iProver_top ),
% 2.26/0.94      inference(predicate_to_equality,[status(thm)],[c_3155]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_3219,plain,
% 2.26/0.94      ( m1_pre_topc(k1_tex_2(sK2,sK3),sK2) = iProver_top
% 2.26/0.94      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 2.26/0.94      | v2_struct_0(sK2) = iProver_top
% 2.26/0.94      | l1_pre_topc(sK2) != iProver_top ),
% 2.26/0.94      inference(instantiation,[status(thm)],[c_3217]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_4,plain,
% 2.26/0.94      ( ~ v7_struct_0(X0)
% 2.26/0.94      | v1_zfmisc_1(u1_struct_0(X0))
% 2.26/0.94      | ~ l1_struct_0(X0) ),
% 2.26/0.94      inference(cnf_transformation,[],[f61]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_385,plain,
% 2.26/0.94      ( ~ v7_struct_0(X0)
% 2.26/0.94      | v1_zfmisc_1(u1_struct_0(X0))
% 2.26/0.94      | ~ l1_pre_topc(X0) ),
% 2.26/0.94      inference(resolution,[status(thm)],[c_1,c_4]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_19,plain,
% 2.26/0.94      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.26/0.94      | v7_struct_0(k1_tex_2(X1,X0))
% 2.26/0.94      | v2_struct_0(X1)
% 2.26/0.94      | ~ l1_pre_topc(X1) ),
% 2.26/0.94      inference(cnf_transformation,[],[f77]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_1613,plain,
% 2.26/0.94      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.26/0.94      | v1_zfmisc_1(u1_struct_0(X2))
% 2.26/0.94      | v2_struct_0(X1)
% 2.26/0.94      | ~ l1_pre_topc(X1)
% 2.26/0.94      | ~ l1_pre_topc(X2)
% 2.26/0.94      | k1_tex_2(X1,X0) != X2 ),
% 2.26/0.94      inference(resolution_lifted,[status(thm)],[c_385,c_19]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_1614,plain,
% 2.26/0.94      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.26/0.94      | v1_zfmisc_1(u1_struct_0(k1_tex_2(X1,X0)))
% 2.26/0.94      | v2_struct_0(X1)
% 2.26/0.94      | ~ l1_pre_topc(X1)
% 2.26/0.94      | ~ l1_pre_topc(k1_tex_2(X1,X0)) ),
% 2.26/0.94      inference(unflattening,[status(thm)],[c_1613]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_421,plain,
% 2.26/0.94      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.26/0.94      | v1_zfmisc_1(u1_struct_0(X2))
% 2.26/0.94      | v2_struct_0(X1)
% 2.26/0.94      | ~ l1_pre_topc(X1)
% 2.26/0.94      | ~ l1_pre_topc(X2)
% 2.26/0.94      | k1_tex_2(X1,X0) != X2 ),
% 2.26/0.94      inference(resolution_lifted,[status(thm)],[c_385,c_19]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_422,plain,
% 2.26/0.94      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.26/0.94      | v1_zfmisc_1(u1_struct_0(k1_tex_2(X1,X0)))
% 2.26/0.94      | v2_struct_0(X1)
% 2.26/0.94      | ~ l1_pre_topc(X1)
% 2.26/0.94      | ~ l1_pre_topc(k1_tex_2(X1,X0)) ),
% 2.26/0.94      inference(unflattening,[status(thm)],[c_421]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_2,plain,
% 2.26/0.94      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.26/0.94      inference(cnf_transformation,[],[f59]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_549,plain,
% 2.26/0.94      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.26/0.94      | v2_struct_0(X1)
% 2.26/0.94      | ~ l1_pre_topc(X2)
% 2.26/0.94      | ~ l1_pre_topc(X1)
% 2.26/0.94      | l1_pre_topc(X3)
% 2.26/0.94      | X1 != X2
% 2.26/0.94      | k1_tex_2(X1,X0) != X3 ),
% 2.26/0.94      inference(resolution_lifted,[status(thm)],[c_2,c_17]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_550,plain,
% 2.26/0.94      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.26/0.94      | v2_struct_0(X1)
% 2.26/0.94      | ~ l1_pre_topc(X1)
% 2.26/0.94      | l1_pre_topc(k1_tex_2(X1,X0)) ),
% 2.26/0.94      inference(unflattening,[status(thm)],[c_549]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_1616,plain,
% 2.26/0.94      ( ~ l1_pre_topc(X1)
% 2.26/0.94      | v2_struct_0(X1)
% 2.26/0.94      | v1_zfmisc_1(u1_struct_0(k1_tex_2(X1,X0)))
% 2.26/0.94      | ~ m1_subset_1(X0,u1_struct_0(X1)) ),
% 2.26/0.94      inference(global_propositional_subsumption,
% 2.26/0.94                [status(thm)],
% 2.26/0.94                [c_1614,c_422,c_550]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_1617,plain,
% 2.26/0.94      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.26/0.94      | v1_zfmisc_1(u1_struct_0(k1_tex_2(X1,X0)))
% 2.26/0.94      | v2_struct_0(X1)
% 2.26/0.94      | ~ l1_pre_topc(X1) ),
% 2.26/0.94      inference(renaming,[status(thm)],[c_1616]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_3140,plain,
% 2.26/0.94      ( ~ m1_subset_1(X0_46,u1_struct_0(X0_47))
% 2.26/0.94      | v1_zfmisc_1(u1_struct_0(k1_tex_2(X0_47,X0_46)))
% 2.26/0.94      | v2_struct_0(X0_47)
% 2.26/0.94      | ~ l1_pre_topc(X0_47) ),
% 2.26/0.94      inference(subtyping,[status(esa)],[c_1617]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_3242,plain,
% 2.26/0.94      ( m1_subset_1(X0_46,u1_struct_0(X0_47)) != iProver_top
% 2.26/0.94      | v1_zfmisc_1(u1_struct_0(k1_tex_2(X0_47,X0_46))) = iProver_top
% 2.26/0.94      | v2_struct_0(X0_47) = iProver_top
% 2.26/0.94      | l1_pre_topc(X0_47) != iProver_top ),
% 2.26/0.94      inference(predicate_to_equality,[status(thm)],[c_3140]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_3244,plain,
% 2.26/0.94      ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 2.26/0.94      | v1_zfmisc_1(u1_struct_0(k1_tex_2(sK2,sK3))) = iProver_top
% 2.26/0.94      | v2_struct_0(sK2) = iProver_top
% 2.26/0.94      | l1_pre_topc(sK2) != iProver_top ),
% 2.26/0.94      inference(instantiation,[status(thm)],[c_3242]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_3218,plain,
% 2.26/0.94      ( m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
% 2.26/0.94      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 2.26/0.94      | v2_struct_0(sK2)
% 2.26/0.94      | ~ l1_pre_topc(sK2) ),
% 2.26/0.94      inference(instantiation,[status(thm)],[c_3155]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_3320,plain,
% 2.26/0.94      ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 2.26/0.94      | v1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),u1_struct_0(sK2)) ),
% 2.26/0.94      inference(global_propositional_subsumption,
% 2.26/0.94                [status(thm)],
% 2.26/0.94                [c_3141,c_26,c_25,c_24,c_699,c_3218]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_3322,plain,
% 2.26/0.94      ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) = iProver_top
% 2.26/0.94      | v1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),u1_struct_0(sK2)) = iProver_top ),
% 2.26/0.94      inference(predicate_to_equality,[status(thm)],[c_3320]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_3161,plain,
% 2.26/0.94      ( ~ m1_pre_topc(X0_47,X1_47)
% 2.26/0.94      | m1_subset_1(u1_struct_0(X0_47),k1_zfmisc_1(u1_struct_0(X1_47)))
% 2.26/0.94      | ~ l1_pre_topc(X1_47) ),
% 2.26/0.94      inference(subtyping,[status(esa)],[c_6]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_3955,plain,
% 2.26/0.94      ( ~ m1_pre_topc(k1_tex_2(X0_47,X0_46),X0_47)
% 2.26/0.94      | m1_subset_1(u1_struct_0(k1_tex_2(X0_47,X0_46)),k1_zfmisc_1(u1_struct_0(X0_47)))
% 2.26/0.94      | ~ l1_pre_topc(X0_47) ),
% 2.26/0.94      inference(instantiation,[status(thm)],[c_3161]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_3956,plain,
% 2.26/0.94      ( m1_pre_topc(k1_tex_2(X0_47,X0_46),X0_47) != iProver_top
% 2.26/0.94      | m1_subset_1(u1_struct_0(k1_tex_2(X0_47,X0_46)),k1_zfmisc_1(u1_struct_0(X0_47))) = iProver_top
% 2.26/0.94      | l1_pre_topc(X0_47) != iProver_top ),
% 2.26/0.94      inference(predicate_to_equality,[status(thm)],[c_3955]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_3958,plain,
% 2.26/0.94      ( m1_pre_topc(k1_tex_2(sK2,sK3),sK2) != iProver_top
% 2.26/0.94      | m1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 2.26/0.94      | l1_pre_topc(sK2) != iProver_top ),
% 2.26/0.94      inference(instantiation,[status(thm)],[c_3956]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_3177,plain,
% 2.26/0.94      ( ~ v1_zfmisc_1(X0_46) | v1_zfmisc_1(X1_46) | X1_46 != X0_46 ),
% 2.26/0.94      theory(equality) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_3996,plain,
% 2.26/0.94      ( v1_zfmisc_1(X0_46)
% 2.26/0.94      | ~ v1_zfmisc_1(u1_struct_0(k1_tex_2(X0_47,X1_46)))
% 2.26/0.94      | X0_46 != u1_struct_0(k1_tex_2(X0_47,X1_46)) ),
% 2.26/0.94      inference(instantiation,[status(thm)],[c_3177]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_4081,plain,
% 2.26/0.94      ( v1_zfmisc_1(u1_struct_0(X0_47))
% 2.26/0.94      | ~ v1_zfmisc_1(u1_struct_0(k1_tex_2(X1_47,X0_46)))
% 2.26/0.94      | u1_struct_0(X0_47) != u1_struct_0(k1_tex_2(X1_47,X0_46)) ),
% 2.26/0.94      inference(instantiation,[status(thm)],[c_3996]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_4083,plain,
% 2.26/0.94      ( u1_struct_0(X0_47) != u1_struct_0(k1_tex_2(X1_47,X0_46))
% 2.26/0.94      | v1_zfmisc_1(u1_struct_0(X0_47)) = iProver_top
% 2.26/0.94      | v1_zfmisc_1(u1_struct_0(k1_tex_2(X1_47,X0_46))) != iProver_top ),
% 2.26/0.94      inference(predicate_to_equality,[status(thm)],[c_4081]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_4085,plain,
% 2.26/0.94      ( u1_struct_0(sK2) != u1_struct_0(k1_tex_2(sK2,sK3))
% 2.26/0.94      | v1_zfmisc_1(u1_struct_0(k1_tex_2(sK2,sK3))) != iProver_top
% 2.26/0.94      | v1_zfmisc_1(u1_struct_0(sK2)) = iProver_top ),
% 2.26/0.94      inference(instantiation,[status(thm)],[c_4083]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_15,plain,
% 2.26/0.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.26/0.94      | v1_subset_1(X0,X1)
% 2.26/0.94      | X1 = X0 ),
% 2.26/0.94      inference(cnf_transformation,[],[f73]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_3157,plain,
% 2.26/0.94      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(X1_46))
% 2.26/0.94      | v1_subset_1(X0_46,X1_46)
% 2.26/0.94      | X1_46 = X0_46 ),
% 2.26/0.94      inference(subtyping,[status(esa)],[c_15]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_4073,plain,
% 2.26/0.94      ( ~ m1_subset_1(u1_struct_0(k1_tex_2(X0_47,X0_46)),k1_zfmisc_1(X1_46))
% 2.26/0.94      | v1_subset_1(u1_struct_0(k1_tex_2(X0_47,X0_46)),X1_46)
% 2.26/0.94      | X1_46 = u1_struct_0(k1_tex_2(X0_47,X0_46)) ),
% 2.26/0.94      inference(instantiation,[status(thm)],[c_3157]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_4368,plain,
% 2.26/0.94      ( ~ m1_subset_1(u1_struct_0(k1_tex_2(X0_47,X0_46)),k1_zfmisc_1(u1_struct_0(X0_47)))
% 2.26/0.94      | v1_subset_1(u1_struct_0(k1_tex_2(X0_47,X0_46)),u1_struct_0(X0_47))
% 2.26/0.94      | u1_struct_0(X0_47) = u1_struct_0(k1_tex_2(X0_47,X0_46)) ),
% 2.26/0.94      inference(instantiation,[status(thm)],[c_4073]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_4369,plain,
% 2.26/0.94      ( u1_struct_0(X0_47) = u1_struct_0(k1_tex_2(X0_47,X0_46))
% 2.26/0.94      | m1_subset_1(u1_struct_0(k1_tex_2(X0_47,X0_46)),k1_zfmisc_1(u1_struct_0(X0_47))) != iProver_top
% 2.26/0.94      | v1_subset_1(u1_struct_0(k1_tex_2(X0_47,X0_46)),u1_struct_0(X0_47)) = iProver_top ),
% 2.26/0.94      inference(predicate_to_equality,[status(thm)],[c_4368]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_4371,plain,
% 2.26/0.94      ( u1_struct_0(sK2) = u1_struct_0(k1_tex_2(sK2,sK3))
% 2.26/0.94      | m1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.26/0.94      | v1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),u1_struct_0(sK2)) = iProver_top ),
% 2.26/0.94      inference(instantiation,[status(thm)],[c_4369]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_21,plain,
% 2.26/0.94      ( ~ m1_subset_1(X0,X1)
% 2.26/0.94      | ~ v1_subset_1(k6_domain_1(X1,X0),X1)
% 2.26/0.94      | ~ v1_zfmisc_1(X1)
% 2.26/0.94      | v1_xboole_0(X1) ),
% 2.26/0.94      inference(cnf_transformation,[],[f78]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_3153,plain,
% 2.26/0.94      ( ~ m1_subset_1(X0_46,X1_46)
% 2.26/0.94      | ~ v1_subset_1(k6_domain_1(X1_46,X0_46),X1_46)
% 2.26/0.94      | ~ v1_zfmisc_1(X1_46)
% 2.26/0.94      | v1_xboole_0(X1_46) ),
% 2.26/0.94      inference(subtyping,[status(esa)],[c_21]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_5704,plain,
% 2.26/0.94      ( ~ m1_subset_1(X0_46,u1_struct_0(X0_47))
% 2.26/0.94      | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0_47),X0_46),u1_struct_0(X0_47))
% 2.26/0.94      | ~ v1_zfmisc_1(u1_struct_0(X0_47))
% 2.26/0.94      | v1_xboole_0(u1_struct_0(X0_47)) ),
% 2.26/0.94      inference(instantiation,[status(thm)],[c_3153]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_5710,plain,
% 2.26/0.94      ( m1_subset_1(X0_46,u1_struct_0(X0_47)) != iProver_top
% 2.26/0.94      | v1_subset_1(k6_domain_1(u1_struct_0(X0_47),X0_46),u1_struct_0(X0_47)) != iProver_top
% 2.26/0.94      | v1_zfmisc_1(u1_struct_0(X0_47)) != iProver_top
% 2.26/0.94      | v1_xboole_0(u1_struct_0(X0_47)) = iProver_top ),
% 2.26/0.94      inference(predicate_to_equality,[status(thm)],[c_5704]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_5712,plain,
% 2.26/0.94      ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 2.26/0.94      | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) != iProver_top
% 2.26/0.94      | v1_zfmisc_1(u1_struct_0(sK2)) != iProver_top
% 2.26/0.94      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 2.26/0.94      inference(instantiation,[status(thm)],[c_5710]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_6015,plain,
% 2.26/0.94      ( v1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),u1_struct_0(sK2)) = iProver_top ),
% 2.26/0.94      inference(global_propositional_subsumption,
% 2.26/0.94                [status(thm)],
% 2.26/0.94                [c_3710,c_27,c_28,c_29,c_84,c_88,c_3219,c_3244,c_3322,
% 2.26/0.94                 c_3958,c_4085,c_4371,c_5712]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_3690,plain,
% 2.26/0.94      ( m1_pre_topc(X0_47,X1_47) != iProver_top
% 2.26/0.94      | m1_subset_1(u1_struct_0(X0_47),k1_zfmisc_1(u1_struct_0(X1_47))) = iProver_top
% 2.26/0.94      | l1_pre_topc(X1_47) != iProver_top ),
% 2.26/0.94      inference(predicate_to_equality,[status(thm)],[c_3161]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_7,plain,
% 2.26/0.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.26/0.94      | ~ v1_subset_1(X0,X1)
% 2.26/0.94      | ~ v1_zfmisc_1(X1)
% 2.26/0.94      | v1_xboole_0(X1)
% 2.26/0.94      | v1_xboole_0(X0) ),
% 2.26/0.94      inference(cnf_transformation,[],[f64]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_0,plain,
% 2.26/0.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.26/0.94      | ~ v1_subset_1(X0,X1)
% 2.26/0.94      | ~ v1_xboole_0(X1) ),
% 2.26/0.94      inference(cnf_transformation,[],[f57]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_170,plain,
% 2.26/0.94      ( ~ v1_zfmisc_1(X1)
% 2.26/0.94      | ~ v1_subset_1(X0,X1)
% 2.26/0.94      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.26/0.94      | v1_xboole_0(X0) ),
% 2.26/0.94      inference(global_propositional_subsumption,[status(thm)],[c_7,c_0]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_171,plain,
% 2.26/0.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.26/0.94      | ~ v1_subset_1(X0,X1)
% 2.26/0.94      | ~ v1_zfmisc_1(X1)
% 2.26/0.94      | v1_xboole_0(X0) ),
% 2.26/0.94      inference(renaming,[status(thm)],[c_170]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_3149,plain,
% 2.26/0.94      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(X1_46))
% 2.26/0.94      | ~ v1_subset_1(X0_46,X1_46)
% 2.26/0.94      | ~ v1_zfmisc_1(X1_46)
% 2.26/0.94      | v1_xboole_0(X0_46) ),
% 2.26/0.94      inference(subtyping,[status(esa)],[c_171]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_3702,plain,
% 2.26/0.94      ( m1_subset_1(X0_46,k1_zfmisc_1(X1_46)) != iProver_top
% 2.26/0.94      | v1_subset_1(X0_46,X1_46) != iProver_top
% 2.26/0.94      | v1_zfmisc_1(X1_46) != iProver_top
% 2.26/0.94      | v1_xboole_0(X0_46) = iProver_top ),
% 2.26/0.94      inference(predicate_to_equality,[status(thm)],[c_3149]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_4397,plain,
% 2.26/0.94      ( m1_pre_topc(X0_47,X1_47) != iProver_top
% 2.26/0.94      | v1_subset_1(u1_struct_0(X0_47),u1_struct_0(X1_47)) != iProver_top
% 2.26/0.94      | v1_zfmisc_1(u1_struct_0(X1_47)) != iProver_top
% 2.26/0.94      | l1_pre_topc(X1_47) != iProver_top
% 2.26/0.94      | v1_xboole_0(u1_struct_0(X0_47)) = iProver_top ),
% 2.26/0.94      inference(superposition,[status(thm)],[c_3690,c_3702]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_6020,plain,
% 2.26/0.94      ( m1_pre_topc(k1_tex_2(sK2,sK3),sK2) != iProver_top
% 2.26/0.94      | v1_zfmisc_1(u1_struct_0(sK2)) != iProver_top
% 2.26/0.94      | l1_pre_topc(sK2) != iProver_top
% 2.26/0.94      | v1_xboole_0(u1_struct_0(k1_tex_2(sK2,sK3))) = iProver_top ),
% 2.26/0.94      inference(superposition,[status(thm)],[c_6015,c_4397]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_3169,plain,
% 2.26/0.94      ( ~ v1_subset_1(X0_46,X1_46)
% 2.26/0.94      | v1_subset_1(X2_46,X3_46)
% 2.26/0.94      | X2_46 != X0_46
% 2.26/0.94      | X3_46 != X1_46 ),
% 2.26/0.94      theory(equality) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_3986,plain,
% 2.26/0.94      ( v1_subset_1(X0_46,X1_46)
% 2.26/0.94      | ~ v1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),u1_struct_0(sK2))
% 2.26/0.94      | X0_46 != u1_struct_0(k1_tex_2(sK2,sK3))
% 2.26/0.94      | X1_46 != u1_struct_0(sK2) ),
% 2.26/0.94      inference(instantiation,[status(thm)],[c_3169]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_4177,plain,
% 2.26/0.94      ( v1_subset_1(X0_46,u1_struct_0(sK2))
% 2.26/0.94      | ~ v1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),u1_struct_0(sK2))
% 2.26/0.94      | X0_46 != u1_struct_0(k1_tex_2(sK2,sK3))
% 2.26/0.94      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.26/0.94      inference(instantiation,[status(thm)],[c_3986]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_5071,plain,
% 2.26/0.94      ( v1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),u1_struct_0(sK2))
% 2.26/0.94      | ~ v1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),u1_struct_0(sK2))
% 2.26/0.94      | sK1(sK2,k1_tex_2(sK2,sK3)) != u1_struct_0(k1_tex_2(sK2,sK3))
% 2.26/0.94      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.26/0.94      inference(instantiation,[status(thm)],[c_4177]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_5072,plain,
% 2.26/0.94      ( sK1(sK2,k1_tex_2(sK2,sK3)) != u1_struct_0(k1_tex_2(sK2,sK3))
% 2.26/0.94      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 2.26/0.94      | v1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),u1_struct_0(sK2)) = iProver_top
% 2.26/0.94      | v1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),u1_struct_0(sK2)) != iProver_top ),
% 2.26/0.94      inference(predicate_to_equality,[status(thm)],[c_5071]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_5,plain,
% 2.26/0.94      ( ~ m1_subset_1(X0,X1)
% 2.26/0.94      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
% 2.26/0.94      | v1_xboole_0(X1) ),
% 2.26/0.94      inference(cnf_transformation,[],[f62]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_3162,plain,
% 2.26/0.94      ( ~ m1_subset_1(X0_46,X1_46)
% 2.26/0.94      | m1_subset_1(k6_domain_1(X1_46,X0_46),k1_zfmisc_1(X1_46))
% 2.26/0.94      | v1_xboole_0(X1_46) ),
% 2.26/0.94      inference(subtyping,[status(esa)],[c_5]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_3689,plain,
% 2.26/0.94      ( m1_subset_1(X0_46,X1_46) != iProver_top
% 2.26/0.94      | m1_subset_1(k6_domain_1(X1_46,X0_46),k1_zfmisc_1(X1_46)) = iProver_top
% 2.26/0.94      | v1_xboole_0(X1_46) = iProver_top ),
% 2.26/0.94      inference(predicate_to_equality,[status(thm)],[c_3162]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_3694,plain,
% 2.26/0.94      ( X0_46 = X1_46
% 2.26/0.94      | m1_subset_1(X1_46,k1_zfmisc_1(X0_46)) != iProver_top
% 2.26/0.94      | v1_subset_1(X1_46,X0_46) = iProver_top ),
% 2.26/0.94      inference(predicate_to_equality,[status(thm)],[c_3157]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_4197,plain,
% 2.26/0.94      ( k6_domain_1(X0_46,X1_46) = X0_46
% 2.26/0.94      | m1_subset_1(X1_46,X0_46) != iProver_top
% 2.26/0.94      | v1_subset_1(k6_domain_1(X0_46,X1_46),X0_46) = iProver_top
% 2.26/0.94      | v1_xboole_0(X0_46) = iProver_top ),
% 2.26/0.94      inference(superposition,[status(thm)],[c_3689,c_3694]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_12,plain,
% 2.26/0.94      ( v1_tex_2(X0,X1)
% 2.26/0.94      | ~ m1_pre_topc(X0,X1)
% 2.26/0.94      | ~ l1_pre_topc(X1)
% 2.26/0.94      | sK1(X1,X0) = u1_struct_0(X0) ),
% 2.26/0.94      inference(cnf_transformation,[],[f70]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_22,negated_conjecture,
% 2.26/0.94      ( ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2)
% 2.26/0.94      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) ),
% 2.26/0.94      inference(cnf_transformation,[],[f83]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_211,plain,
% 2.26/0.94      ( ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2)
% 2.26/0.94      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) ),
% 2.26/0.94      inference(prop_impl,[status(thm)],[c_22]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_664,plain,
% 2.26/0.94      ( ~ m1_pre_topc(X0,X1)
% 2.26/0.94      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 2.26/0.94      | ~ l1_pre_topc(X1)
% 2.26/0.94      | k1_tex_2(sK2,sK3) != X0
% 2.26/0.94      | sK1(X1,X0) = u1_struct_0(X0)
% 2.26/0.94      | sK2 != X1 ),
% 2.26/0.94      inference(resolution_lifted,[status(thm)],[c_12,c_211]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_665,plain,
% 2.26/0.94      ( ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
% 2.26/0.94      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 2.26/0.94      | ~ l1_pre_topc(sK2)
% 2.26/0.94      | sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(k1_tex_2(sK2,sK3)) ),
% 2.26/0.94      inference(unflattening,[status(thm)],[c_664]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_667,plain,
% 2.26/0.94      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 2.26/0.94      | ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
% 2.26/0.94      | sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(k1_tex_2(sK2,sK3)) ),
% 2.26/0.94      inference(global_propositional_subsumption,
% 2.26/0.94                [status(thm)],
% 2.26/0.94                [c_665,c_25]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_668,plain,
% 2.26/0.94      ( ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
% 2.26/0.94      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 2.26/0.94      | sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(k1_tex_2(sK2,sK3)) ),
% 2.26/0.94      inference(renaming,[status(thm)],[c_667]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_3143,plain,
% 2.26/0.94      ( ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
% 2.26/0.94      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 2.26/0.94      | sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(k1_tex_2(sK2,sK3)) ),
% 2.26/0.94      inference(subtyping,[status(esa)],[c_668]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_3708,plain,
% 2.26/0.94      ( sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(k1_tex_2(sK2,sK3))
% 2.26/0.94      | m1_pre_topc(k1_tex_2(sK2,sK3),sK2) != iProver_top
% 2.26/0.94      | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) != iProver_top ),
% 2.26/0.94      inference(predicate_to_equality,[status(thm)],[c_3143]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_3310,plain,
% 2.26/0.94      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 2.26/0.94      | sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(k1_tex_2(sK2,sK3)) ),
% 2.26/0.94      inference(global_propositional_subsumption,
% 2.26/0.94                [status(thm)],
% 2.26/0.94                [c_3143,c_26,c_25,c_24,c_3218]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_3312,plain,
% 2.26/0.94      ( sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(k1_tex_2(sK2,sK3))
% 2.26/0.94      | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) != iProver_top ),
% 2.26/0.94      inference(predicate_to_equality,[status(thm)],[c_3310]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_5004,plain,
% 2.26/0.94      ( sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(k1_tex_2(sK2,sK3))
% 2.26/0.94      | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) != iProver_top ),
% 2.26/0.94      inference(global_propositional_subsumption,
% 2.26/0.94                [status(thm)],
% 2.26/0.94                [c_3708,c_3312]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_5010,plain,
% 2.26/0.94      ( sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(k1_tex_2(sK2,sK3))
% 2.26/0.94      | k6_domain_1(u1_struct_0(sK2),sK3) = u1_struct_0(sK2)
% 2.26/0.94      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 2.26/0.94      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 2.26/0.94      inference(superposition,[status(thm)],[c_4197,c_5004]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_5011,plain,
% 2.26/0.94      ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 2.26/0.94      | v1_xboole_0(u1_struct_0(sK2))
% 2.26/0.94      | sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(k1_tex_2(sK2,sK3))
% 2.26/0.94      | k6_domain_1(u1_struct_0(sK2),sK3) = u1_struct_0(sK2) ),
% 2.26/0.94      inference(predicate_to_equality_rev,[status(thm)],[c_5010]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_3166,plain,( X0_46 = X0_46 ),theory(equality) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_4613,plain,
% 2.26/0.94      ( k6_domain_1(u1_struct_0(sK2),sK3) = k6_domain_1(u1_struct_0(sK2),sK3) ),
% 2.26/0.94      inference(instantiation,[status(thm)],[c_3166]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_4229,plain,
% 2.26/0.94      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.26/0.94      | v1_subset_1(X0_46,u1_struct_0(sK2))
% 2.26/0.94      | u1_struct_0(sK2) = X0_46 ),
% 2.26/0.94      inference(instantiation,[status(thm)],[c_3157]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_4565,plain,
% 2.26/0.94      ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.26/0.94      | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 2.26/0.94      | u1_struct_0(sK2) = k6_domain_1(u1_struct_0(sK2),sK3) ),
% 2.26/0.94      inference(instantiation,[status(thm)],[c_4229]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_4566,plain,
% 2.26/0.94      ( u1_struct_0(sK2) = k6_domain_1(u1_struct_0(sK2),sK3)
% 2.26/0.94      | m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.26/0.94      | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) = iProver_top ),
% 2.26/0.94      inference(predicate_to_equality,[status(thm)],[c_4565]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_3163,plain,
% 2.26/0.94      ( ~ m1_pre_topc(X0_47,X1_47)
% 2.26/0.94      | ~ l1_pre_topc(X1_47)
% 2.26/0.94      | l1_pre_topc(X0_47) ),
% 2.26/0.94      inference(subtyping,[status(esa)],[c_2]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_4324,plain,
% 2.26/0.94      ( ~ m1_pre_topc(k1_tex_2(X0_47,X0_46),X1_47)
% 2.26/0.94      | ~ l1_pre_topc(X1_47)
% 2.26/0.94      | l1_pre_topc(k1_tex_2(X0_47,X0_46)) ),
% 2.26/0.94      inference(instantiation,[status(thm)],[c_3163]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_4325,plain,
% 2.26/0.94      ( m1_pre_topc(k1_tex_2(X0_47,X0_46),X1_47) != iProver_top
% 2.26/0.94      | l1_pre_topc(X1_47) != iProver_top
% 2.26/0.94      | l1_pre_topc(k1_tex_2(X0_47,X0_46)) = iProver_top ),
% 2.26/0.94      inference(predicate_to_equality,[status(thm)],[c_4324]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_4327,plain,
% 2.26/0.94      ( m1_pre_topc(k1_tex_2(sK2,sK3),sK2) != iProver_top
% 2.26/0.94      | l1_pre_topc(k1_tex_2(sK2,sK3)) = iProver_top
% 2.26/0.94      | l1_pre_topc(sK2) != iProver_top ),
% 2.26/0.94      inference(instantiation,[status(thm)],[c_4325]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_399,plain,
% 2.26/0.94      ( v2_struct_0(X0)
% 2.26/0.94      | ~ l1_pre_topc(X0)
% 2.26/0.94      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.26/0.94      inference(resolution,[status(thm)],[c_1,c_3]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_3148,plain,
% 2.26/0.94      ( v2_struct_0(X0_47)
% 2.26/0.94      | ~ l1_pre_topc(X0_47)
% 2.26/0.94      | ~ v1_xboole_0(u1_struct_0(X0_47)) ),
% 2.26/0.94      inference(subtyping,[status(esa)],[c_399]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_4103,plain,
% 2.26/0.94      ( v2_struct_0(k1_tex_2(X0_47,X0_46))
% 2.26/0.94      | ~ l1_pre_topc(k1_tex_2(X0_47,X0_46))
% 2.26/0.94      | ~ v1_xboole_0(u1_struct_0(k1_tex_2(X0_47,X0_46))) ),
% 2.26/0.94      inference(instantiation,[status(thm)],[c_3148]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_4104,plain,
% 2.26/0.94      ( v2_struct_0(k1_tex_2(X0_47,X0_46)) = iProver_top
% 2.26/0.94      | l1_pre_topc(k1_tex_2(X0_47,X0_46)) != iProver_top
% 2.26/0.94      | v1_xboole_0(u1_struct_0(k1_tex_2(X0_47,X0_46))) != iProver_top ),
% 2.26/0.94      inference(predicate_to_equality,[status(thm)],[c_4103]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_4106,plain,
% 2.26/0.94      ( v2_struct_0(k1_tex_2(sK2,sK3)) = iProver_top
% 2.26/0.94      | l1_pre_topc(k1_tex_2(sK2,sK3)) != iProver_top
% 2.26/0.94      | v1_xboole_0(u1_struct_0(k1_tex_2(sK2,sK3))) != iProver_top ),
% 2.26/0.94      inference(instantiation,[status(thm)],[c_4104]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_8,plain,
% 2.26/0.94      ( ~ m1_subset_1(X0,X1)
% 2.26/0.94      | v1_zfmisc_1(X1)
% 2.26/0.94      | v1_xboole_0(X1)
% 2.26/0.94      | k6_domain_1(X1,X0) != X1 ),
% 2.26/0.94      inference(cnf_transformation,[],[f67]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_3160,plain,
% 2.26/0.94      ( ~ m1_subset_1(X0_46,X1_46)
% 2.26/0.94      | v1_zfmisc_1(X1_46)
% 2.26/0.94      | v1_xboole_0(X1_46)
% 2.26/0.94      | k6_domain_1(X1_46,X0_46) != X1_46 ),
% 2.26/0.94      inference(subtyping,[status(esa)],[c_8]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_3960,plain,
% 2.26/0.94      ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 2.26/0.94      | v1_zfmisc_1(u1_struct_0(sK2))
% 2.26/0.94      | v1_xboole_0(u1_struct_0(sK2))
% 2.26/0.94      | k6_domain_1(u1_struct_0(sK2),sK3) != u1_struct_0(sK2) ),
% 2.26/0.94      inference(instantiation,[status(thm)],[c_3160]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_3961,plain,
% 2.26/0.94      ( k6_domain_1(u1_struct_0(sK2),sK3) != u1_struct_0(sK2)
% 2.26/0.94      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 2.26/0.94      | v1_zfmisc_1(u1_struct_0(sK2)) = iProver_top
% 2.26/0.94      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 2.26/0.94      inference(predicate_to_equality,[status(thm)],[c_3960]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_3947,plain,
% 2.26/0.94      ( m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.26/0.94      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 2.26/0.94      | v1_xboole_0(u1_struct_0(sK2)) ),
% 2.26/0.94      inference(instantiation,[status(thm)],[c_3162]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_3948,plain,
% 2.26/0.94      ( m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 2.26/0.94      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 2.26/0.94      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 2.26/0.94      inference(predicate_to_equality,[status(thm)],[c_3947]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_11,plain,
% 2.26/0.94      ( v1_tex_2(X0,X1)
% 2.26/0.94      | ~ m1_pre_topc(X0,X1)
% 2.26/0.94      | ~ v1_subset_1(sK1(X1,X0),u1_struct_0(X1))
% 2.26/0.94      | ~ l1_pre_topc(X1) ),
% 2.26/0.94      inference(cnf_transformation,[],[f71]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_681,plain,
% 2.26/0.94      ( ~ m1_pre_topc(X0,X1)
% 2.26/0.94      | ~ v1_subset_1(sK1(X1,X0),u1_struct_0(X1))
% 2.26/0.94      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 2.26/0.94      | ~ l1_pre_topc(X1)
% 2.26/0.94      | k1_tex_2(sK2,sK3) != X0
% 2.26/0.94      | sK2 != X1 ),
% 2.26/0.94      inference(resolution_lifted,[status(thm)],[c_11,c_211]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_682,plain,
% 2.26/0.94      ( ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
% 2.26/0.94      | ~ v1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),u1_struct_0(sK2))
% 2.26/0.94      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 2.26/0.94      | ~ l1_pre_topc(sK2) ),
% 2.26/0.94      inference(unflattening,[status(thm)],[c_681]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_684,plain,
% 2.26/0.94      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 2.26/0.94      | ~ v1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),u1_struct_0(sK2))
% 2.26/0.94      | ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2) ),
% 2.26/0.94      inference(global_propositional_subsumption,
% 2.26/0.94                [status(thm)],
% 2.26/0.94                [c_682,c_25]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_685,plain,
% 2.26/0.94      ( ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
% 2.26/0.94      | ~ v1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),u1_struct_0(sK2))
% 2.26/0.94      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) ),
% 2.26/0.94      inference(renaming,[status(thm)],[c_684]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_3142,plain,
% 2.26/0.94      ( ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
% 2.26/0.94      | ~ v1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),u1_struct_0(sK2))
% 2.26/0.94      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) ),
% 2.26/0.94      inference(subtyping,[status(esa)],[c_685]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_3315,plain,
% 2.26/0.94      ( ~ v1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),u1_struct_0(sK2))
% 2.26/0.94      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) ),
% 2.26/0.94      inference(global_propositional_subsumption,
% 2.26/0.94                [status(thm)],
% 2.26/0.94                [c_3142,c_26,c_25,c_24,c_682,c_3218]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_3317,plain,
% 2.26/0.94      ( v1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),u1_struct_0(sK2)) != iProver_top
% 2.26/0.94      | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) != iProver_top ),
% 2.26/0.94      inference(predicate_to_equality,[status(thm)],[c_3315]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_20,plain,
% 2.26/0.94      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.26/0.94      | v2_struct_0(X1)
% 2.26/0.94      | ~ v2_struct_0(k1_tex_2(X1,X0))
% 2.26/0.94      | ~ l1_pre_topc(X1) ),
% 2.26/0.94      inference(cnf_transformation,[],[f76]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_3154,plain,
% 2.26/0.94      ( ~ m1_subset_1(X0_46,u1_struct_0(X0_47))
% 2.26/0.94      | v2_struct_0(X0_47)
% 2.26/0.94      | ~ v2_struct_0(k1_tex_2(X0_47,X0_46))
% 2.26/0.94      | ~ l1_pre_topc(X0_47) ),
% 2.26/0.94      inference(subtyping,[status(esa)],[c_20]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_3220,plain,
% 2.26/0.94      ( m1_subset_1(X0_46,u1_struct_0(X0_47)) != iProver_top
% 2.26/0.94      | v2_struct_0(X0_47) = iProver_top
% 2.26/0.94      | v2_struct_0(k1_tex_2(X0_47,X0_46)) != iProver_top
% 2.26/0.94      | l1_pre_topc(X0_47) != iProver_top ),
% 2.26/0.94      inference(predicate_to_equality,[status(thm)],[c_3154]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_3222,plain,
% 2.26/0.94      ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 2.26/0.94      | v2_struct_0(k1_tex_2(sK2,sK3)) != iProver_top
% 2.26/0.94      | v2_struct_0(sK2) = iProver_top
% 2.26/0.94      | l1_pre_topc(sK2) != iProver_top ),
% 2.26/0.94      inference(instantiation,[status(thm)],[c_3220]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_3167,plain,( X0_47 = X0_47 ),theory(equality) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_3195,plain,
% 2.26/0.94      ( sK2 = sK2 ),
% 2.26/0.94      inference(instantiation,[status(thm)],[c_3167]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_3175,plain,
% 2.26/0.94      ( X0_47 != X1_47 | u1_struct_0(X0_47) = u1_struct_0(X1_47) ),
% 2.26/0.94      theory(equality) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_3187,plain,
% 2.26/0.94      ( sK2 != sK2 | u1_struct_0(sK2) = u1_struct_0(sK2) ),
% 2.26/0.94      inference(instantiation,[status(thm)],[c_3175]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_87,plain,
% 2.26/0.94      ( ~ l1_pre_topc(sK2) | l1_struct_0(sK2) ),
% 2.26/0.94      inference(instantiation,[status(thm)],[c_1]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(c_83,plain,
% 2.26/0.94      ( v2_struct_0(sK2)
% 2.26/0.94      | ~ l1_struct_0(sK2)
% 2.26/0.94      | ~ v1_xboole_0(u1_struct_0(sK2)) ),
% 2.26/0.94      inference(instantiation,[status(thm)],[c_3]) ).
% 2.26/0.94  
% 2.26/0.94  cnf(contradiction,plain,
% 2.26/0.94      ( $false ),
% 2.26/0.94      inference(minisat,
% 2.26/0.94                [status(thm)],
% 2.26/0.94                [c_6179,c_6020,c_6015,c_5072,c_5011,c_4613,c_4566,c_4327,
% 2.26/0.94                 c_4106,c_3961,c_3948,c_3317,c_3222,c_3219,c_3195,c_3187,
% 2.26/0.94                 c_88,c_87,c_84,c_83,c_29,c_24,c_28,c_25,c_27,c_26]) ).
% 2.26/0.94  
% 2.26/0.94  
% 2.26/0.94  % SZS output end CNFRefutation for theBenchmark.p
% 2.26/0.94  
% 2.26/0.94  ------                               Statistics
% 2.26/0.94  
% 2.26/0.94  ------ General
% 2.26/0.94  
% 2.26/0.94  abstr_ref_over_cycles:                  0
% 2.26/0.94  abstr_ref_under_cycles:                 0
% 2.26/0.94  gc_basic_clause_elim:                   0
% 2.26/0.94  forced_gc_time:                         0
% 2.26/0.94  parsing_time:                           0.009
% 2.26/0.94  unif_index_cands_time:                  0.
% 2.26/0.94  unif_index_add_time:                    0.
% 2.26/0.94  orderings_time:                         0.
% 2.26/0.94  out_proof_time:                         0.012
% 2.26/0.94  total_time:                             0.175
% 2.26/0.94  num_of_symbols:                         51
% 2.26/0.94  num_of_terms:                           3190
% 2.26/0.94  
% 2.26/0.94  ------ Preprocessing
% 2.26/0.94  
% 2.26/0.94  num_of_splits:                          0
% 2.26/0.94  num_of_split_atoms:                     0
% 2.26/0.94  num_of_reused_defs:                     0
% 2.26/0.94  num_eq_ax_congr_red:                    8
% 2.26/0.94  num_of_sem_filtered_clauses:            1
% 2.26/0.94  num_of_subtypes:                        2
% 2.26/0.94  monotx_restored_types:                  1
% 2.26/0.94  sat_num_of_epr_types:                   0
% 2.26/0.94  sat_num_of_non_cyclic_types:            0
% 2.26/0.94  sat_guarded_non_collapsed_types:        0
% 2.26/0.94  num_pure_diseq_elim:                    0
% 2.26/0.94  simp_replaced_by:                       0
% 2.26/0.94  res_preprocessed:                       158
% 2.26/0.94  prep_upred:                             0
% 2.26/0.94  prep_unflattend:                        110
% 2.26/0.94  smt_new_axioms:                         0
% 2.26/0.94  pred_elim_cands:                        7
% 2.26/0.94  pred_elim:                              3
% 2.26/0.94  pred_elim_cl:                           1
% 2.26/0.94  pred_elim_cycles:                       15
% 2.26/0.94  merged_defs:                            2
% 2.26/0.94  merged_defs_ncl:                        0
% 2.26/0.94  bin_hyper_res:                          2
% 2.26/0.94  prep_cycles:                            5
% 2.26/0.94  pred_elim_time:                         0.027
% 2.26/0.94  splitting_time:                         0.
% 2.26/0.94  sem_filter_time:                        0.
% 2.26/0.94  monotx_time:                            0.
% 2.26/0.94  subtype_inf_time:                       0.001
% 2.26/0.94  
% 2.26/0.94  ------ Problem properties
% 2.26/0.94  
% 2.26/0.94  clauses:                                25
% 2.26/0.94  conjectures:                            3
% 2.26/0.94  epr:                                    3
% 2.26/0.94  horn:                                   15
% 2.26/0.94  ground:                                 7
% 2.26/0.94  unary:                                  3
% 2.26/0.94  binary:                                 1
% 2.26/0.94  lits:                                   77
% 2.26/0.94  lits_eq:                                5
% 2.26/0.94  fd_pure:                                0
% 2.26/0.94  fd_pseudo:                              0
% 2.26/0.94  fd_cond:                                0
% 2.26/0.94  fd_pseudo_cond:                         1
% 2.26/0.94  ac_symbols:                             0
% 2.26/0.94  
% 2.26/0.94  ------ Propositional Solver
% 2.26/0.94  
% 2.26/0.94  prop_solver_calls:                      32
% 2.26/0.94  prop_fast_solver_calls:                 1703
% 2.26/0.94  smt_solver_calls:                       0
% 2.26/0.94  smt_fast_solver_calls:                  0
% 2.26/0.94  prop_num_of_clauses:                    1233
% 2.26/0.94  prop_preprocess_simplified:             6283
% 2.26/0.94  prop_fo_subsumed:                       56
% 2.26/0.94  prop_solver_time:                       0.
% 2.26/0.94  smt_solver_time:                        0.
% 2.26/0.94  smt_fast_solver_time:                   0.
% 2.26/0.94  prop_fast_solver_time:                  0.
% 2.26/0.94  prop_unsat_core_time:                   0.
% 2.26/0.94  
% 2.26/0.94  ------ QBF
% 2.26/0.94  
% 2.26/0.94  qbf_q_res:                              0
% 2.26/0.94  qbf_num_tautologies:                    0
% 2.26/0.94  qbf_prep_cycles:                        0
% 2.26/0.94  
% 2.26/0.94  ------ BMC1
% 2.26/0.94  
% 2.26/0.94  bmc1_current_bound:                     -1
% 2.26/0.94  bmc1_last_solved_bound:                 -1
% 2.26/0.94  bmc1_unsat_core_size:                   -1
% 2.26/0.94  bmc1_unsat_core_parents_size:           -1
% 2.26/0.94  bmc1_merge_next_fun:                    0
% 2.26/0.94  bmc1_unsat_core_clauses_time:           0.
% 2.26/0.94  
% 2.26/0.94  ------ Instantiation
% 2.26/0.94  
% 2.26/0.94  inst_num_of_clauses:                    341
% 2.26/0.94  inst_num_in_passive:                    125
% 2.26/0.94  inst_num_in_active:                     213
% 2.26/0.94  inst_num_in_unprocessed:                2
% 2.26/0.94  inst_num_of_loops:                      232
% 2.26/0.94  inst_num_of_learning_restarts:          0
% 2.26/0.94  inst_num_moves_active_passive:          14
% 2.26/0.94  inst_lit_activity:                      0
% 2.26/0.94  inst_lit_activity_moves:                0
% 2.26/0.94  inst_num_tautologies:                   0
% 2.26/0.94  inst_num_prop_implied:                  0
% 2.26/0.94  inst_num_existing_simplified:           0
% 2.26/0.94  inst_num_eq_res_simplified:             0
% 2.26/0.94  inst_num_child_elim:                    0
% 2.26/0.94  inst_num_of_dismatching_blockings:      148
% 2.26/0.94  inst_num_of_non_proper_insts:           420
% 2.26/0.94  inst_num_of_duplicates:                 0
% 2.26/0.94  inst_inst_num_from_inst_to_res:         0
% 2.26/0.94  inst_dismatching_checking_time:         0.
% 2.26/0.94  
% 2.26/0.94  ------ Resolution
% 2.26/0.94  
% 2.26/0.94  res_num_of_clauses:                     0
% 2.26/0.94  res_num_in_passive:                     0
% 2.26/0.94  res_num_in_active:                      0
% 2.26/0.94  res_num_of_loops:                       163
% 2.26/0.94  res_forward_subset_subsumed:            47
% 2.26/0.94  res_backward_subset_subsumed:           0
% 2.26/0.94  res_forward_subsumed:                   0
% 2.26/0.94  res_backward_subsumed:                  0
% 2.26/0.94  res_forward_subsumption_resolution:     1
% 2.26/0.94  res_backward_subsumption_resolution:    0
% 2.26/0.94  res_clause_to_clause_subsumption:       243
% 2.26/0.94  res_orphan_elimination:                 0
% 2.26/0.94  res_tautology_del:                      76
% 2.26/0.94  res_num_eq_res_simplified:              0
% 2.26/0.94  res_num_sel_changes:                    0
% 2.26/0.94  res_moves_from_active_to_pass:          0
% 2.26/0.94  
% 2.26/0.94  ------ Superposition
% 2.26/0.94  
% 2.26/0.94  sup_time_total:                         0.
% 2.26/0.94  sup_time_generating:                    0.
% 2.26/0.94  sup_time_sim_full:                      0.
% 2.26/0.94  sup_time_sim_immed:                     0.
% 2.26/0.94  
% 2.26/0.94  sup_num_of_clauses:                     58
% 2.26/0.94  sup_num_in_active:                      42
% 2.26/0.94  sup_num_in_passive:                     16
% 2.26/0.94  sup_num_of_loops:                       46
% 2.26/0.94  sup_fw_superposition:                   19
% 2.26/0.94  sup_bw_superposition:                   26
% 2.26/0.94  sup_immediate_simplified:               8
% 2.26/0.94  sup_given_eliminated:                   0
% 2.26/0.94  comparisons_done:                       0
% 2.26/0.94  comparisons_avoided:                    0
% 2.26/0.94  
% 2.26/0.94  ------ Simplifications
% 2.26/0.94  
% 2.26/0.94  
% 2.26/0.94  sim_fw_subset_subsumed:                 7
% 2.26/0.94  sim_bw_subset_subsumed:                 2
% 2.26/0.94  sim_fw_subsumed:                        1
% 2.26/0.94  sim_bw_subsumed:                        0
% 2.26/0.94  sim_fw_subsumption_res:                 0
% 2.26/0.94  sim_bw_subsumption_res:                 0
% 2.26/0.94  sim_tautology_del:                      1
% 2.26/0.94  sim_eq_tautology_del:                   1
% 2.26/0.94  sim_eq_res_simp:                        0
% 2.26/0.94  sim_fw_demodulated:                     0
% 2.26/0.94  sim_bw_demodulated:                     3
% 2.26/0.94  sim_light_normalised:                   0
% 2.26/0.94  sim_joinable_taut:                      0
% 2.26/0.94  sim_joinable_simp:                      0
% 2.26/0.94  sim_ac_normalised:                      0
% 2.26/0.94  sim_smt_subsumption:                    0
% 2.26/0.94  
%------------------------------------------------------------------------------
