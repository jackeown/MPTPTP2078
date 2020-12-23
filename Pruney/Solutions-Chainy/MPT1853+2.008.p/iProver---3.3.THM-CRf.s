%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:25:35 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :  203 (1371 expanded)
%              Number of clauses        :  126 ( 383 expanded)
%              Number of leaves         :   19 ( 285 expanded)
%              Depth                    :   21
%              Number of atoms          :  785 (6995 expanded)
%              Number of equality atoms :  167 ( 314 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

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

fof(f29,plain,(
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

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f47,plain,(
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
    inference(rectify,[],[f46])).

fof(f48,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v1_subset_1(X2,u1_struct_0(X0))
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_subset_1(sK0(X0,X1),u1_struct_0(X0))
        & u1_struct_0(X1) = sK0(X0,X1)
        & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f47,f48])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | u1_struct_0(X1) = sK0(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f13,axiom,(
    ! [X0] :
      ( ( ~ v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v1_subset_1(k6_domain_1(X0,X1),X0)
      | ~ m1_subset_1(X1,X0)
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

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

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f45,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

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
    inference(nnf_transformation,[],[f45])).

fof(f54,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f53])).

fof(f56,plain,(
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

fof(f55,plain,
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

fof(f57,plain,
    ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
      | ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2) )
    & ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
      | v1_tex_2(k1_tex_2(sK2,sK3),sK2) )
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l1_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f54,f56,f55])).

fof(f86,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2) ),
    inference(cnf_transformation,[],[f57])).

fof(f82,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f57])).

fof(f83,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f57])).

fof(f4,axiom,(
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
    inference(ennf_transformation,[],[f4])).

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

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f59,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f84,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f57])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( ~ v1_subset_1(X1,u1_struct_0(X0))
          & ~ v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_subset_1(X1,u1_struct_0(X0))
          & ~ v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_subset_1(X1,u1_struct_0(X0))
          & ~ v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f51,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_subset_1(X1,u1_struct_0(X0))
          & ~ v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_subset_1(sK1(X0),u1_struct_0(X0))
        & ~ v1_zfmisc_1(sK1(X0))
        & ~ v1_xboole_0(sK1(X0))
        & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0] :
      ( ( ~ v1_subset_1(sK1(X0),u1_struct_0(X0))
        & ~ v1_zfmisc_1(sK1(X0))
        & ~ v1_xboole_0(sK1(X0))
        & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f37,f51])).

fof(f75,plain,(
    ! [X0] :
      ( m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ( v2_struct_0(X0)
       => v7_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( v7_struct_0(X0)
      | ~ v2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f20,plain,(
    ! [X0] :
      ( v7_struct_0(X0)
      | ~ v2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f58,plain,(
    ! [X0] :
      ( v7_struct_0(X0)
      | ~ v2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f77,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(sK1(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f78,plain,(
    ! [X0] :
      ( ~ v1_subset_1(sK1(X0),u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( ~ v2_struct_0(X1)
           => ( ~ v1_tex_2(X1,X0)
              & ~ v2_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tex_2(X1,X0)
            & ~ v2_struct_0(X1) )
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tex_2(X1,X0)
            & ~ v2_struct_0(X1) )
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ v1_tex_2(X1,X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f85,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | v1_tex_2(k1_tex_2(sK2,sK3),sK2) ),
    inference(cnf_transformation,[],[f57])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f26,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f62,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f12,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_zfmisc_1(X0)
          | ~ v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_zfmisc_1(X0)
          | ~ v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(X0)
      | ~ v1_subset_1(k6_domain_1(X0,X1),X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | ~ v1_subset_1(sK0(X0,X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f60,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f74,plain,(
    ! [X0,X1] :
      ( v7_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_pre_topc(k1_tex_2(X1,X0),X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_5541,plain,
    ( ~ m1_subset_1(X0_46,u1_struct_0(X0_47))
    | m1_pre_topc(k1_tex_2(X0_47,X0_46),X0_47)
    | ~ l1_pre_topc(X0_47)
    | v2_struct_0(X0_47) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_6255,plain,
    ( m1_subset_1(X0_46,u1_struct_0(X0_47)) != iProver_top
    | m1_pre_topc(k1_tex_2(X0_47,X0_46),X0_47) = iProver_top
    | l1_pre_topc(X0_47) != iProver_top
    | v2_struct_0(X0_47) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5541])).

cnf(c_8,plain,
    ( v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK0(X1,X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_5546,plain,
    ( v1_tex_2(X0_47,X1_47)
    | ~ m1_pre_topc(X0_47,X1_47)
    | ~ l1_pre_topc(X1_47)
    | sK0(X1_47,X0_47) = u1_struct_0(X0_47) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_6250,plain,
    ( sK0(X0_47,X1_47) = u1_struct_0(X1_47)
    | v1_tex_2(X1_47,X0_47) = iProver_top
    | m1_pre_topc(X1_47,X0_47) != iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5546])).

cnf(c_7049,plain,
    ( sK0(X0_47,k1_tex_2(X0_47,X0_46)) = u1_struct_0(k1_tex_2(X0_47,X0_46))
    | m1_subset_1(X0_46,u1_struct_0(X0_47)) != iProver_top
    | v1_tex_2(k1_tex_2(X0_47,X0_46),X0_47) = iProver_top
    | l1_pre_topc(X0_47) != iProver_top
    | v2_struct_0(X0_47) = iProver_top ),
    inference(superposition,[status(thm)],[c_6255,c_6250])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_subset_1(k6_domain_1(X1,X0),X1)
    | v1_zfmisc_1(X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_5537,plain,
    ( ~ m1_subset_1(X0_46,X1_46)
    | v1_subset_1(k6_domain_1(X1_46,X0_46),X1_46)
    | v1_zfmisc_1(X1_46)
    | v1_xboole_0(X1_46) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_6259,plain,
    ( m1_subset_1(X0_46,X1_46) != iProver_top
    | v1_subset_1(k6_domain_1(X1_46,X0_46),X1_46) = iProver_top
    | v1_zfmisc_1(X1_46) = iProver_top
    | v1_xboole_0(X1_46) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5537])).

cnf(c_24,negated_conjecture,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_5536,negated_conjecture,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_6260,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) != iProver_top
    | v1_tex_2(k1_tex_2(sK2,sK3),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5536])).

cnf(c_6653,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | v1_tex_2(k1_tex_2(sK2,sK3),sK2) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK2)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6259,c_6260])).

cnf(c_3184,plain,
    ( ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) ),
    inference(prop_impl,[status(thm)],[c_24])).

cnf(c_3185,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2) ),
    inference(renaming,[status(thm)],[c_3184])).

cnf(c_4668,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2)
    | v1_zfmisc_1(X1)
    | v1_xboole_0(X1)
    | k6_domain_1(u1_struct_0(sK2),sK3) != k6_domain_1(X1,X0)
    | u1_struct_0(sK2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_3185])).

cnf(c_4669,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2)
    | v1_zfmisc_1(u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2))
    | k6_domain_1(u1_struct_0(sK2),sK3) != k6_domain_1(u1_struct_0(sK2),X0) ),
    inference(unflattening,[status(thm)],[c_4668])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_27,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_3,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_91,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2))
    | ~ l1_struct_0(sK2)
    | v2_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_95,plain,
    ( ~ l1_pre_topc(sK2)
    | l1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2930,plain,
    ( v1_subset_1(k6_domain_1(X0,X1),X0)
    | v1_zfmisc_1(X0)
    | v1_xboole_0(X0)
    | u1_struct_0(sK2) != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_26])).

cnf(c_2931,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | v1_zfmisc_1(u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_2930])).

cnf(c_4671,plain,
    ( ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2)
    | v1_zfmisc_1(u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4669,c_28,c_27,c_24,c_91,c_95,c_2931])).

cnf(c_4673,plain,
    ( v1_tex_2(k1_tex_2(sK2,sK3),sK2) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4671])).

cnf(c_6771,plain,
    ( v1_zfmisc_1(u1_struct_0(sK2)) = iProver_top
    | v1_tex_2(k1_tex_2(sK2,sK3),sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6653,c_4673])).

cnf(c_6772,plain,
    ( v1_tex_2(k1_tex_2(sK2,sK3),sK2) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK2)) = iProver_top ),
    inference(renaming,[status(thm)],[c_6771])).

cnf(c_7905,plain,
    ( sK0(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(k1_tex_2(sK2,sK3))
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK2)) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_7049,c_6772])).

cnf(c_20,plain,
    ( m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v7_struct_0(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_0,plain,
    ( ~ l1_struct_0(X0)
    | ~ v2_struct_0(X0)
    | v7_struct_0(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_165,plain,
    ( ~ l1_struct_0(X0)
    | m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | v7_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_20,c_0])).

cnf(c_166,plain,
    ( m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_struct_0(X0)
    | v7_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_165])).

cnf(c_168,plain,
    ( m1_subset_1(sK1(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_struct_0(sK2)
    | v7_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_166])).

cnf(c_18,plain,
    ( ~ v1_zfmisc_1(sK1(X0))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v7_struct_0(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_179,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_zfmisc_1(sK1(X0))
    | v7_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_18,c_0])).

cnf(c_180,plain,
    ( ~ v1_zfmisc_1(sK1(X0))
    | ~ l1_struct_0(X0)
    | v7_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_179])).

cnf(c_182,plain,
    ( ~ v1_zfmisc_1(sK1(sK2))
    | ~ l1_struct_0(sK2)
    | v7_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_180])).

cnf(c_17,plain,
    ( ~ v1_subset_1(sK1(X0),u1_struct_0(X0))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v7_struct_0(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_186,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_subset_1(sK1(X0),u1_struct_0(X0))
    | v7_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17,c_0])).

cnf(c_187,plain,
    ( ~ v1_subset_1(sK1(X0),u1_struct_0(X0))
    | ~ l1_struct_0(X0)
    | v7_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_186])).

cnf(c_189,plain,
    ( ~ v1_subset_1(sK1(sK2),u1_struct_0(sK2))
    | ~ l1_struct_0(sK2)
    | v7_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_187])).

cnf(c_5,plain,
    ( ~ v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v7_struct_0(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_25,negated_conjecture,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | v1_tex_2(k1_tex_2(sK2,sK3),sK2) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_3186,plain,
    ( v1_tex_2(k1_tex_2(sK2,sK3),sK2)
    | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) ),
    inference(prop_impl,[status(thm)],[c_25])).

cnf(c_3187,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | v1_tex_2(k1_tex_2(sK2,sK3),sK2) ),
    inference(renaming,[status(thm)],[c_3186])).

cnf(c_3846,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v7_struct_0(X1)
    | k1_tex_2(sK2,sK3) != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_3187])).

cnf(c_3847,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(k1_tex_2(sK2,sK3))
    | v2_struct_0(sK2)
    | ~ v7_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_3846])).

cnf(c_4,plain,
    ( v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_struct_0(X0)
    | ~ v7_struct_0(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_88,plain,
    ( v1_zfmisc_1(u1_struct_0(sK2))
    | ~ l1_struct_0(sK2)
    | ~ v7_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_241,plain,
    ( v1_tex_2(k1_tex_2(sK2,sK3),sK2)
    | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) ),
    inference(prop_impl,[status(thm)],[c_25])).

cnf(c_242,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | v1_tex_2(k1_tex_2(sK2,sK3),sK2) ),
    inference(renaming,[status(thm)],[c_241])).

cnf(c_1279,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v7_struct_0(X1)
    | k1_tex_2(sK2,sK3) != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_242])).

cnf(c_1280,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(k1_tex_2(sK2,sK3))
    | v2_struct_0(sK2)
    | ~ v7_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_1279])).

cnf(c_1282,plain,
    ( v2_struct_0(k1_tex_2(sK2,sK3))
    | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
    | ~ v7_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1280,c_28,c_27])).

cnf(c_1283,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
    | v2_struct_0(k1_tex_2(sK2,sK3))
    | ~ v7_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_1282])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ v1_subset_1(k6_domain_1(X1,X0),X1)
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2944,plain,
    ( ~ v1_subset_1(k6_domain_1(X0,X1),X0)
    | ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0)
    | u1_struct_0(sK2) != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_26])).

cnf(c_2945,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | ~ v1_zfmisc_1(u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_2944])).

cnf(c_3849,plain,
    ( v2_struct_0(k1_tex_2(sK2,sK3))
    | ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
    | ~ v7_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3847,c_28,c_27,c_88,c_91,c_95,c_1283,c_2945])).

cnf(c_3850,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
    | v2_struct_0(k1_tex_2(sK2,sK3))
    | ~ v7_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_3849])).

cnf(c_5596,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_5541])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ v2_struct_0(k1_tex_2(X1,X0)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_5540,plain,
    ( ~ m1_subset_1(X0_46,u1_struct_0(X0_47))
    | ~ l1_pre_topc(X0_47)
    | v2_struct_0(X0_47)
    | ~ v2_struct_0(k1_tex_2(X0_47,X0_46)) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_5599,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2)
    | ~ v2_struct_0(k1_tex_2(sK2,sK3))
    | v2_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_5540])).

cnf(c_6533,plain,
    ( v1_tex_2(k1_tex_2(X0_47,X0_46),X0_47)
    | ~ m1_pre_topc(k1_tex_2(X0_47,X0_46),X0_47)
    | ~ l1_pre_topc(X0_47)
    | sK0(X0_47,k1_tex_2(X0_47,X0_46)) = u1_struct_0(k1_tex_2(X0_47,X0_46)) ),
    inference(instantiation,[status(thm)],[c_5546])).

cnf(c_6535,plain,
    ( v1_tex_2(k1_tex_2(sK2,sK3),sK2)
    | ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
    | ~ l1_pre_topc(sK2)
    | sK0(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(k1_tex_2(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_6533])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | v1_subset_1(X0,X1)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_5543,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(X1_46))
    | v1_subset_1(X0_46,X1_46)
    | X0_46 = X1_46 ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_6607,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_subset_1(X0_46,u1_struct_0(sK2))
    | X0_46 = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_5543])).

cnf(c_6730,plain,
    ( ~ m1_subset_1(sK1(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_subset_1(sK1(sK2),u1_struct_0(sK2))
    | sK1(sK2) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_6607])).

cnf(c_5560,plain,
    ( ~ v1_zfmisc_1(X0_46)
    | v1_zfmisc_1(X1_46)
    | X1_46 != X0_46 ),
    theory(equality)).

cnf(c_6579,plain,
    ( v1_zfmisc_1(X0_46)
    | ~ v1_zfmisc_1(u1_struct_0(X0_47))
    | X0_46 != u1_struct_0(X0_47) ),
    inference(instantiation,[status(thm)],[c_5560])).

cnf(c_6935,plain,
    ( v1_zfmisc_1(sK1(sK2))
    | ~ v1_zfmisc_1(u1_struct_0(sK2))
    | sK1(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_6579])).

cnf(c_8234,plain,
    ( sK0(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(k1_tex_2(sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7905,c_28,c_27,c_26,c_95,c_168,c_182,c_189,c_3850,c_4671,c_5596,c_5599,c_6535,c_6730,c_6935])).

cnf(c_9,plain,
    ( m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | v1_tex_2(X1,X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_5545,plain,
    ( m1_subset_1(sK0(X0_47,X1_47),k1_zfmisc_1(u1_struct_0(X0_47)))
    | v1_tex_2(X1_47,X0_47)
    | ~ m1_pre_topc(X1_47,X0_47)
    | ~ l1_pre_topc(X0_47) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_6251,plain,
    ( m1_subset_1(sK0(X0_47,X1_47),k1_zfmisc_1(u1_struct_0(X0_47))) = iProver_top
    | v1_tex_2(X1_47,X0_47) = iProver_top
    | m1_pre_topc(X1_47,X0_47) != iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5545])).

cnf(c_6253,plain,
    ( X0_46 = X1_46
    | m1_subset_1(X0_46,k1_zfmisc_1(X1_46)) != iProver_top
    | v1_subset_1(X0_46,X1_46) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5543])).

cnf(c_7171,plain,
    ( sK0(X0_47,X1_47) = u1_struct_0(X0_47)
    | v1_subset_1(sK0(X0_47,X1_47),u1_struct_0(X0_47)) = iProver_top
    | v1_tex_2(X1_47,X0_47) = iProver_top
    | m1_pre_topc(X1_47,X0_47) != iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(superposition,[status(thm)],[c_6251,c_6253])).

cnf(c_7,plain,
    ( ~ v1_subset_1(sK0(X0,X1),u1_struct_0(X0))
    | v1_tex_2(X1,X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_5547,plain,
    ( ~ v1_subset_1(sK0(X0_47,X1_47),u1_struct_0(X0_47))
    | v1_tex_2(X1_47,X0_47)
    | ~ m1_pre_topc(X1_47,X0_47)
    | ~ l1_pre_topc(X0_47) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_5585,plain,
    ( v1_subset_1(sK0(X0_47,X1_47),u1_struct_0(X0_47)) != iProver_top
    | v1_tex_2(X1_47,X0_47) = iProver_top
    | m1_pre_topc(X1_47,X0_47) != iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5547])).

cnf(c_7797,plain,
    ( sK0(X0_47,X1_47) = u1_struct_0(X0_47)
    | v1_tex_2(X1_47,X0_47) = iProver_top
    | m1_pre_topc(X1_47,X0_47) != iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7171,c_5585])).

cnf(c_7805,plain,
    ( sK0(X0_47,k1_tex_2(X0_47,X0_46)) = u1_struct_0(X0_47)
    | m1_subset_1(X0_46,u1_struct_0(X0_47)) != iProver_top
    | v1_tex_2(k1_tex_2(X0_47,X0_46),X0_47) = iProver_top
    | l1_pre_topc(X0_47) != iProver_top
    | v2_struct_0(X0_47) = iProver_top ),
    inference(superposition,[status(thm)],[c_6255,c_7797])).

cnf(c_7871,plain,
    ( sK0(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(sK2)
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK2)) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_7805,c_6772])).

cnf(c_239,plain,
    ( ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) ),
    inference(prop_impl,[status(thm)],[c_24])).

cnf(c_240,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2) ),
    inference(renaming,[status(thm)],[c_239])).

cnf(c_1208,plain,
    ( m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0)
    | k1_tex_2(sK2,sK3) != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_240])).

cnf(c_1209,plain,
    ( m1_subset_1(sK0(sK2,k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_1208])).

cnf(c_1225,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | ~ v1_subset_1(sK0(X0,X1),u1_struct_0(X0))
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0)
    | k1_tex_2(sK2,sK3) != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_240])).

cnf(c_1226,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | ~ v1_subset_1(sK0(sK2,k1_tex_2(sK2,sK3)),u1_struct_0(sK2))
    | ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_1225])).

cnf(c_7021,plain,
    ( ~ m1_subset_1(sK0(sK2,k1_tex_2(sK2,X0_46)),k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_subset_1(sK0(sK2,k1_tex_2(sK2,X0_46)),u1_struct_0(sK2))
    | sK0(sK2,k1_tex_2(sK2,X0_46)) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_6607])).

cnf(c_7025,plain,
    ( ~ m1_subset_1(sK0(sK2,k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_subset_1(sK0(sK2,k1_tex_2(sK2,sK3)),u1_struct_0(sK2))
    | sK0(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_7021])).

cnf(c_8127,plain,
    ( sK0(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7871,c_28,c_27,c_26,c_91,c_95,c_168,c_182,c_189,c_1209,c_1226,c_2931,c_3850,c_5596,c_5599,c_6730,c_6935,c_7025])).

cnf(c_8236,plain,
    ( u1_struct_0(k1_tex_2(sK2,sK3)) = u1_struct_0(sK2) ),
    inference(light_normalisation,[status(thm)],[c_8234,c_8127])).

cnf(c_633,plain,
    ( v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(X0)
    | ~ v7_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_1,c_4])).

cnf(c_5527,plain,
    ( v1_zfmisc_1(u1_struct_0(X0_47))
    | ~ l1_pre_topc(X0_47)
    | ~ v7_struct_0(X0_47) ),
    inference(subtyping,[status(esa)],[c_633])).

cnf(c_6269,plain,
    ( v1_zfmisc_1(u1_struct_0(X0_47)) = iProver_top
    | l1_pre_topc(X0_47) != iProver_top
    | v7_struct_0(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5527])).

cnf(c_8249,plain,
    ( v1_zfmisc_1(u1_struct_0(sK2)) = iProver_top
    | l1_pre_topc(k1_tex_2(sK2,sK3)) != iProver_top
    | v7_struct_0(k1_tex_2(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8236,c_6269])).

cnf(c_6936,plain,
    ( sK1(sK2) != u1_struct_0(sK2)
    | v1_zfmisc_1(sK1(sK2)) = iProver_top
    | v1_zfmisc_1(u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6935])).

cnf(c_2,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_5549,plain,
    ( ~ m1_pre_topc(X0_47,X1_47)
    | ~ l1_pre_topc(X1_47)
    | l1_pre_topc(X0_47) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_6688,plain,
    ( ~ m1_pre_topc(k1_tex_2(X0_47,X0_46),X1_47)
    | ~ l1_pre_topc(X1_47)
    | l1_pre_topc(k1_tex_2(X0_47,X0_46)) ),
    inference(instantiation,[status(thm)],[c_5549])).

cnf(c_6689,plain,
    ( m1_pre_topc(k1_tex_2(X0_47,X0_46),X1_47) != iProver_top
    | l1_pre_topc(X1_47) != iProver_top
    | l1_pre_topc(k1_tex_2(X0_47,X0_46)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6688])).

cnf(c_6691,plain,
    ( m1_pre_topc(k1_tex_2(sK2,sK3),sK2) != iProver_top
    | l1_pre_topc(k1_tex_2(sK2,sK3)) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6689])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v7_struct_0(k1_tex_2(X1,X0)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_5539,plain,
    ( ~ m1_subset_1(X0_46,u1_struct_0(X0_47))
    | ~ l1_pre_topc(X0_47)
    | v2_struct_0(X0_47)
    | v7_struct_0(k1_tex_2(X0_47,X0_46)) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_5601,plain,
    ( m1_subset_1(X0_46,u1_struct_0(X0_47)) != iProver_top
    | l1_pre_topc(X0_47) != iProver_top
    | v2_struct_0(X0_47) = iProver_top
    | v7_struct_0(k1_tex_2(X0_47,X0_46)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5539])).

cnf(c_5603,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v7_struct_0(k1_tex_2(sK2,sK3)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_5601])).

cnf(c_5598,plain,
    ( m1_subset_1(X0_46,u1_struct_0(X0_47)) != iProver_top
    | l1_pre_topc(X0_47) != iProver_top
    | v2_struct_0(X0_47) = iProver_top
    | v2_struct_0(k1_tex_2(X0_47,X0_46)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5540])).

cnf(c_5600,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(k1_tex_2(sK2,sK3)) != iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_5598])).

cnf(c_5595,plain,
    ( m1_subset_1(X0_46,u1_struct_0(X0_47)) != iProver_top
    | m1_pre_topc(k1_tex_2(X0_47,X0_46),X0_47) = iProver_top
    | l1_pre_topc(X0_47) != iProver_top
    | v2_struct_0(X0_47) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5541])).

cnf(c_5597,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | m1_pre_topc(k1_tex_2(sK2,sK3),sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_5595])).

cnf(c_3851,plain,
    ( m1_pre_topc(k1_tex_2(sK2,sK3),sK2) != iProver_top
    | v2_struct_0(k1_tex_2(sK2,sK3)) = iProver_top
    | v7_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3850])).

cnf(c_181,plain,
    ( v1_zfmisc_1(sK1(X0)) != iProver_top
    | l1_struct_0(X0) != iProver_top
    | v7_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_180])).

cnf(c_183,plain,
    ( v1_zfmisc_1(sK1(sK2)) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v7_struct_0(sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_181])).

cnf(c_94,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_96,plain,
    ( l1_pre_topc(sK2) != iProver_top
    | l1_struct_0(sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_94])).

cnf(c_31,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_30,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_29,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8249,c_6936,c_6730,c_6691,c_5603,c_5600,c_5599,c_5597,c_5596,c_3851,c_3850,c_189,c_183,c_168,c_96,c_95,c_31,c_26,c_30,c_27,c_29,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:03:00 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.09/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/0.98  
% 2.09/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.09/0.98  
% 2.09/0.98  ------  iProver source info
% 2.09/0.98  
% 2.09/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.09/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.09/0.98  git: non_committed_changes: false
% 2.09/0.98  git: last_make_outside_of_git: false
% 2.09/0.98  
% 2.09/0.98  ------ 
% 2.09/0.98  
% 2.09/0.98  ------ Input Options
% 2.09/0.98  
% 2.09/0.98  --out_options                           all
% 2.09/0.98  --tptp_safe_out                         true
% 2.09/0.98  --problem_path                          ""
% 2.09/0.98  --include_path                          ""
% 2.09/0.98  --clausifier                            res/vclausify_rel
% 2.09/0.98  --clausifier_options                    --mode clausify
% 2.09/0.98  --stdin                                 false
% 2.09/0.98  --stats_out                             all
% 2.09/0.98  
% 2.09/0.98  ------ General Options
% 2.09/0.98  
% 2.09/0.98  --fof                                   false
% 2.09/0.98  --time_out_real                         305.
% 2.09/0.98  --time_out_virtual                      -1.
% 2.09/0.98  --symbol_type_check                     false
% 2.09/0.98  --clausify_out                          false
% 2.09/0.98  --sig_cnt_out                           false
% 2.09/0.98  --trig_cnt_out                          false
% 2.09/0.98  --trig_cnt_out_tolerance                1.
% 2.09/0.98  --trig_cnt_out_sk_spl                   false
% 2.09/0.98  --abstr_cl_out                          false
% 2.09/0.98  
% 2.09/0.98  ------ Global Options
% 2.09/0.98  
% 2.09/0.98  --schedule                              default
% 2.09/0.98  --add_important_lit                     false
% 2.09/0.98  --prop_solver_per_cl                    1000
% 2.09/0.98  --min_unsat_core                        false
% 2.09/0.98  --soft_assumptions                      false
% 2.09/0.98  --soft_lemma_size                       3
% 2.09/0.98  --prop_impl_unit_size                   0
% 2.09/0.98  --prop_impl_unit                        []
% 2.09/0.98  --share_sel_clauses                     true
% 2.09/0.98  --reset_solvers                         false
% 2.09/0.98  --bc_imp_inh                            [conj_cone]
% 2.09/0.98  --conj_cone_tolerance                   3.
% 2.09/0.98  --extra_neg_conj                        none
% 2.09/0.98  --large_theory_mode                     true
% 2.09/0.98  --prolific_symb_bound                   200
% 2.09/0.98  --lt_threshold                          2000
% 2.09/0.98  --clause_weak_htbl                      true
% 2.09/0.98  --gc_record_bc_elim                     false
% 2.09/0.98  
% 2.09/0.98  ------ Preprocessing Options
% 2.09/0.98  
% 2.09/0.98  --preprocessing_flag                    true
% 2.09/0.98  --time_out_prep_mult                    0.1
% 2.09/0.98  --splitting_mode                        input
% 2.09/0.98  --splitting_grd                         true
% 2.09/0.98  --splitting_cvd                         false
% 2.09/0.98  --splitting_cvd_svl                     false
% 2.09/0.98  --splitting_nvd                         32
% 2.09/0.98  --sub_typing                            true
% 2.09/0.98  --prep_gs_sim                           true
% 2.09/0.98  --prep_unflatten                        true
% 2.09/0.98  --prep_res_sim                          true
% 2.09/0.98  --prep_upred                            true
% 2.09/0.98  --prep_sem_filter                       exhaustive
% 2.09/0.98  --prep_sem_filter_out                   false
% 2.09/0.98  --pred_elim                             true
% 2.09/0.98  --res_sim_input                         true
% 2.09/0.98  --eq_ax_congr_red                       true
% 2.09/0.98  --pure_diseq_elim                       true
% 2.09/0.98  --brand_transform                       false
% 2.09/0.98  --non_eq_to_eq                          false
% 2.09/0.98  --prep_def_merge                        true
% 2.09/0.98  --prep_def_merge_prop_impl              false
% 2.09/0.98  --prep_def_merge_mbd                    true
% 2.09/0.98  --prep_def_merge_tr_red                 false
% 2.09/0.98  --prep_def_merge_tr_cl                  false
% 2.09/0.98  --smt_preprocessing                     true
% 2.09/0.98  --smt_ac_axioms                         fast
% 2.09/0.98  --preprocessed_out                      false
% 2.09/0.98  --preprocessed_stats                    false
% 2.09/0.98  
% 2.09/0.98  ------ Abstraction refinement Options
% 2.09/0.98  
% 2.09/0.98  --abstr_ref                             []
% 2.09/0.98  --abstr_ref_prep                        false
% 2.09/0.98  --abstr_ref_until_sat                   false
% 2.09/0.98  --abstr_ref_sig_restrict                funpre
% 2.09/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.09/0.98  --abstr_ref_under                       []
% 2.09/0.98  
% 2.09/0.98  ------ SAT Options
% 2.09/0.98  
% 2.09/0.98  --sat_mode                              false
% 2.09/0.98  --sat_fm_restart_options                ""
% 2.09/0.98  --sat_gr_def                            false
% 2.09/0.98  --sat_epr_types                         true
% 2.09/0.98  --sat_non_cyclic_types                  false
% 2.09/0.98  --sat_finite_models                     false
% 2.09/0.98  --sat_fm_lemmas                         false
% 2.09/0.98  --sat_fm_prep                           false
% 2.09/0.99  --sat_fm_uc_incr                        true
% 2.09/0.99  --sat_out_model                         small
% 2.09/0.99  --sat_out_clauses                       false
% 2.09/0.99  
% 2.09/0.99  ------ QBF Options
% 2.09/0.99  
% 2.09/0.99  --qbf_mode                              false
% 2.09/0.99  --qbf_elim_univ                         false
% 2.09/0.99  --qbf_dom_inst                          none
% 2.09/0.99  --qbf_dom_pre_inst                      false
% 2.09/0.99  --qbf_sk_in                             false
% 2.09/0.99  --qbf_pred_elim                         true
% 2.09/0.99  --qbf_split                             512
% 2.09/0.99  
% 2.09/0.99  ------ BMC1 Options
% 2.09/0.99  
% 2.09/0.99  --bmc1_incremental                      false
% 2.09/0.99  --bmc1_axioms                           reachable_all
% 2.09/0.99  --bmc1_min_bound                        0
% 2.09/0.99  --bmc1_max_bound                        -1
% 2.09/0.99  --bmc1_max_bound_default                -1
% 2.09/0.99  --bmc1_symbol_reachability              true
% 2.09/0.99  --bmc1_property_lemmas                  false
% 2.09/0.99  --bmc1_k_induction                      false
% 2.09/0.99  --bmc1_non_equiv_states                 false
% 2.09/0.99  --bmc1_deadlock                         false
% 2.09/0.99  --bmc1_ucm                              false
% 2.09/0.99  --bmc1_add_unsat_core                   none
% 2.09/0.99  --bmc1_unsat_core_children              false
% 2.09/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.09/0.99  --bmc1_out_stat                         full
% 2.09/0.99  --bmc1_ground_init                      false
% 2.09/0.99  --bmc1_pre_inst_next_state              false
% 2.09/0.99  --bmc1_pre_inst_state                   false
% 2.09/0.99  --bmc1_pre_inst_reach_state             false
% 2.09/0.99  --bmc1_out_unsat_core                   false
% 2.09/0.99  --bmc1_aig_witness_out                  false
% 2.09/0.99  --bmc1_verbose                          false
% 2.09/0.99  --bmc1_dump_clauses_tptp                false
% 2.09/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.09/0.99  --bmc1_dump_file                        -
% 2.09/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.09/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.09/0.99  --bmc1_ucm_extend_mode                  1
% 2.09/0.99  --bmc1_ucm_init_mode                    2
% 2.09/0.99  --bmc1_ucm_cone_mode                    none
% 2.09/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.09/0.99  --bmc1_ucm_relax_model                  4
% 2.09/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.09/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.09/0.99  --bmc1_ucm_layered_model                none
% 2.09/0.99  --bmc1_ucm_max_lemma_size               10
% 2.09/0.99  
% 2.09/0.99  ------ AIG Options
% 2.09/0.99  
% 2.09/0.99  --aig_mode                              false
% 2.09/0.99  
% 2.09/0.99  ------ Instantiation Options
% 2.09/0.99  
% 2.09/0.99  --instantiation_flag                    true
% 2.09/0.99  --inst_sos_flag                         false
% 2.09/0.99  --inst_sos_phase                        true
% 2.09/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.09/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.09/0.99  --inst_lit_sel_side                     num_symb
% 2.09/0.99  --inst_solver_per_active                1400
% 2.09/0.99  --inst_solver_calls_frac                1.
% 2.09/0.99  --inst_passive_queue_type               priority_queues
% 2.09/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.09/0.99  --inst_passive_queues_freq              [25;2]
% 2.09/0.99  --inst_dismatching                      true
% 2.09/0.99  --inst_eager_unprocessed_to_passive     true
% 2.09/0.99  --inst_prop_sim_given                   true
% 2.09/0.99  --inst_prop_sim_new                     false
% 2.09/0.99  --inst_subs_new                         false
% 2.09/0.99  --inst_eq_res_simp                      false
% 2.09/0.99  --inst_subs_given                       false
% 2.09/0.99  --inst_orphan_elimination               true
% 2.09/0.99  --inst_learning_loop_flag               true
% 2.09/0.99  --inst_learning_start                   3000
% 2.09/0.99  --inst_learning_factor                  2
% 2.09/0.99  --inst_start_prop_sim_after_learn       3
% 2.09/0.99  --inst_sel_renew                        solver
% 2.09/0.99  --inst_lit_activity_flag                true
% 2.09/0.99  --inst_restr_to_given                   false
% 2.09/0.99  --inst_activity_threshold               500
% 2.09/0.99  --inst_out_proof                        true
% 2.09/0.99  
% 2.09/0.99  ------ Resolution Options
% 2.09/0.99  
% 2.09/0.99  --resolution_flag                       true
% 2.09/0.99  --res_lit_sel                           adaptive
% 2.09/0.99  --res_lit_sel_side                      none
% 2.09/0.99  --res_ordering                          kbo
% 2.09/0.99  --res_to_prop_solver                    active
% 2.09/0.99  --res_prop_simpl_new                    false
% 2.09/0.99  --res_prop_simpl_given                  true
% 2.09/0.99  --res_passive_queue_type                priority_queues
% 2.09/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.09/0.99  --res_passive_queues_freq               [15;5]
% 2.09/0.99  --res_forward_subs                      full
% 2.09/0.99  --res_backward_subs                     full
% 2.09/0.99  --res_forward_subs_resolution           true
% 2.09/0.99  --res_backward_subs_resolution          true
% 2.09/0.99  --res_orphan_elimination                true
% 2.09/0.99  --res_time_limit                        2.
% 2.09/0.99  --res_out_proof                         true
% 2.09/0.99  
% 2.09/0.99  ------ Superposition Options
% 2.09/0.99  
% 2.09/0.99  --superposition_flag                    true
% 2.09/0.99  --sup_passive_queue_type                priority_queues
% 2.09/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.09/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.09/0.99  --demod_completeness_check              fast
% 2.09/0.99  --demod_use_ground                      true
% 2.09/0.99  --sup_to_prop_solver                    passive
% 2.09/0.99  --sup_prop_simpl_new                    true
% 2.09/0.99  --sup_prop_simpl_given                  true
% 2.09/0.99  --sup_fun_splitting                     false
% 2.09/0.99  --sup_smt_interval                      50000
% 2.09/0.99  
% 2.09/0.99  ------ Superposition Simplification Setup
% 2.09/0.99  
% 2.09/0.99  --sup_indices_passive                   []
% 2.09/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.09/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.09/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.09/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.09/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.09/0.99  --sup_full_bw                           [BwDemod]
% 2.09/0.99  --sup_immed_triv                        [TrivRules]
% 2.09/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.09/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.09/0.99  --sup_immed_bw_main                     []
% 2.09/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.09/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.09/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.09/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.09/0.99  
% 2.09/0.99  ------ Combination Options
% 2.09/0.99  
% 2.09/0.99  --comb_res_mult                         3
% 2.09/0.99  --comb_sup_mult                         2
% 2.09/0.99  --comb_inst_mult                        10
% 2.09/0.99  
% 2.09/0.99  ------ Debug Options
% 2.09/0.99  
% 2.09/0.99  --dbg_backtrace                         false
% 2.09/0.99  --dbg_dump_prop_clauses                 false
% 2.09/0.99  --dbg_dump_prop_clauses_file            -
% 2.09/0.99  --dbg_out_stat                          false
% 2.09/0.99  ------ Parsing...
% 2.09/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.09/0.99  
% 2.09/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.09/0.99  
% 2.09/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.09/0.99  
% 2.09/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.09/0.99  ------ Proving...
% 2.09/0.99  ------ Problem Properties 
% 2.09/0.99  
% 2.09/0.99  
% 2.09/0.99  clauses                                 26
% 2.09/0.99  conjectures                             5
% 2.09/0.99  EPR                                     5
% 2.09/0.99  Horn                                    17
% 2.09/0.99  unary                                   3
% 2.09/0.99  binary                                  3
% 2.09/0.99  lits                                    84
% 2.09/0.99  lits eq                                 2
% 2.09/0.99  fd_pure                                 0
% 2.09/0.99  fd_pseudo                               0
% 2.09/0.99  fd_cond                                 0
% 2.09/0.99  fd_pseudo_cond                          1
% 2.09/0.99  AC symbols                              0
% 2.09/0.99  
% 2.09/0.99  ------ Schedule dynamic 5 is on 
% 2.09/0.99  
% 2.09/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.09/0.99  
% 2.09/0.99  
% 2.09/0.99  ------ 
% 2.09/0.99  Current options:
% 2.09/0.99  ------ 
% 2.09/0.99  
% 2.09/0.99  ------ Input Options
% 2.09/0.99  
% 2.09/0.99  --out_options                           all
% 2.09/0.99  --tptp_safe_out                         true
% 2.09/0.99  --problem_path                          ""
% 2.09/0.99  --include_path                          ""
% 2.09/0.99  --clausifier                            res/vclausify_rel
% 2.09/0.99  --clausifier_options                    --mode clausify
% 2.09/0.99  --stdin                                 false
% 2.09/0.99  --stats_out                             all
% 2.09/0.99  
% 2.09/0.99  ------ General Options
% 2.09/0.99  
% 2.09/0.99  --fof                                   false
% 2.09/0.99  --time_out_real                         305.
% 2.09/0.99  --time_out_virtual                      -1.
% 2.09/0.99  --symbol_type_check                     false
% 2.09/0.99  --clausify_out                          false
% 2.09/0.99  --sig_cnt_out                           false
% 2.09/0.99  --trig_cnt_out                          false
% 2.09/0.99  --trig_cnt_out_tolerance                1.
% 2.09/0.99  --trig_cnt_out_sk_spl                   false
% 2.09/0.99  --abstr_cl_out                          false
% 2.09/0.99  
% 2.09/0.99  ------ Global Options
% 2.09/0.99  
% 2.09/0.99  --schedule                              default
% 2.09/0.99  --add_important_lit                     false
% 2.09/0.99  --prop_solver_per_cl                    1000
% 2.09/0.99  --min_unsat_core                        false
% 2.09/0.99  --soft_assumptions                      false
% 2.09/0.99  --soft_lemma_size                       3
% 2.09/0.99  --prop_impl_unit_size                   0
% 2.09/0.99  --prop_impl_unit                        []
% 2.09/0.99  --share_sel_clauses                     true
% 2.09/0.99  --reset_solvers                         false
% 2.09/0.99  --bc_imp_inh                            [conj_cone]
% 2.09/0.99  --conj_cone_tolerance                   3.
% 2.09/0.99  --extra_neg_conj                        none
% 2.09/0.99  --large_theory_mode                     true
% 2.09/0.99  --prolific_symb_bound                   200
% 2.09/0.99  --lt_threshold                          2000
% 2.09/0.99  --clause_weak_htbl                      true
% 2.09/0.99  --gc_record_bc_elim                     false
% 2.09/0.99  
% 2.09/0.99  ------ Preprocessing Options
% 2.09/0.99  
% 2.09/0.99  --preprocessing_flag                    true
% 2.09/0.99  --time_out_prep_mult                    0.1
% 2.09/0.99  --splitting_mode                        input
% 2.09/0.99  --splitting_grd                         true
% 2.09/0.99  --splitting_cvd                         false
% 2.09/0.99  --splitting_cvd_svl                     false
% 2.09/0.99  --splitting_nvd                         32
% 2.09/0.99  --sub_typing                            true
% 2.09/0.99  --prep_gs_sim                           true
% 2.09/0.99  --prep_unflatten                        true
% 2.09/0.99  --prep_res_sim                          true
% 2.09/0.99  --prep_upred                            true
% 2.09/0.99  --prep_sem_filter                       exhaustive
% 2.09/0.99  --prep_sem_filter_out                   false
% 2.09/0.99  --pred_elim                             true
% 2.09/0.99  --res_sim_input                         true
% 2.09/0.99  --eq_ax_congr_red                       true
% 2.09/0.99  --pure_diseq_elim                       true
% 2.09/0.99  --brand_transform                       false
% 2.09/0.99  --non_eq_to_eq                          false
% 2.09/0.99  --prep_def_merge                        true
% 2.09/0.99  --prep_def_merge_prop_impl              false
% 2.09/0.99  --prep_def_merge_mbd                    true
% 2.09/0.99  --prep_def_merge_tr_red                 false
% 2.09/0.99  --prep_def_merge_tr_cl                  false
% 2.09/0.99  --smt_preprocessing                     true
% 2.09/0.99  --smt_ac_axioms                         fast
% 2.09/0.99  --preprocessed_out                      false
% 2.09/0.99  --preprocessed_stats                    false
% 2.09/0.99  
% 2.09/0.99  ------ Abstraction refinement Options
% 2.09/0.99  
% 2.09/0.99  --abstr_ref                             []
% 2.09/0.99  --abstr_ref_prep                        false
% 2.09/0.99  --abstr_ref_until_sat                   false
% 2.09/0.99  --abstr_ref_sig_restrict                funpre
% 2.09/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.09/0.99  --abstr_ref_under                       []
% 2.09/0.99  
% 2.09/0.99  ------ SAT Options
% 2.09/0.99  
% 2.09/0.99  --sat_mode                              false
% 2.09/0.99  --sat_fm_restart_options                ""
% 2.09/0.99  --sat_gr_def                            false
% 2.09/0.99  --sat_epr_types                         true
% 2.09/0.99  --sat_non_cyclic_types                  false
% 2.09/0.99  --sat_finite_models                     false
% 2.09/0.99  --sat_fm_lemmas                         false
% 2.09/0.99  --sat_fm_prep                           false
% 2.09/0.99  --sat_fm_uc_incr                        true
% 2.09/0.99  --sat_out_model                         small
% 2.09/0.99  --sat_out_clauses                       false
% 2.09/0.99  
% 2.09/0.99  ------ QBF Options
% 2.09/0.99  
% 2.09/0.99  --qbf_mode                              false
% 2.09/0.99  --qbf_elim_univ                         false
% 2.09/0.99  --qbf_dom_inst                          none
% 2.09/0.99  --qbf_dom_pre_inst                      false
% 2.09/0.99  --qbf_sk_in                             false
% 2.09/0.99  --qbf_pred_elim                         true
% 2.09/0.99  --qbf_split                             512
% 2.09/0.99  
% 2.09/0.99  ------ BMC1 Options
% 2.09/0.99  
% 2.09/0.99  --bmc1_incremental                      false
% 2.09/0.99  --bmc1_axioms                           reachable_all
% 2.09/0.99  --bmc1_min_bound                        0
% 2.09/0.99  --bmc1_max_bound                        -1
% 2.09/0.99  --bmc1_max_bound_default                -1
% 2.09/0.99  --bmc1_symbol_reachability              true
% 2.09/0.99  --bmc1_property_lemmas                  false
% 2.09/0.99  --bmc1_k_induction                      false
% 2.09/0.99  --bmc1_non_equiv_states                 false
% 2.09/0.99  --bmc1_deadlock                         false
% 2.09/0.99  --bmc1_ucm                              false
% 2.09/0.99  --bmc1_add_unsat_core                   none
% 2.09/0.99  --bmc1_unsat_core_children              false
% 2.09/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.09/0.99  --bmc1_out_stat                         full
% 2.09/0.99  --bmc1_ground_init                      false
% 2.09/0.99  --bmc1_pre_inst_next_state              false
% 2.09/0.99  --bmc1_pre_inst_state                   false
% 2.09/0.99  --bmc1_pre_inst_reach_state             false
% 2.09/0.99  --bmc1_out_unsat_core                   false
% 2.09/0.99  --bmc1_aig_witness_out                  false
% 2.09/0.99  --bmc1_verbose                          false
% 2.09/0.99  --bmc1_dump_clauses_tptp                false
% 2.09/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.09/0.99  --bmc1_dump_file                        -
% 2.09/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.09/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.09/0.99  --bmc1_ucm_extend_mode                  1
% 2.09/0.99  --bmc1_ucm_init_mode                    2
% 2.09/0.99  --bmc1_ucm_cone_mode                    none
% 2.09/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.09/0.99  --bmc1_ucm_relax_model                  4
% 2.09/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.09/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.09/0.99  --bmc1_ucm_layered_model                none
% 2.09/0.99  --bmc1_ucm_max_lemma_size               10
% 2.09/0.99  
% 2.09/0.99  ------ AIG Options
% 2.09/0.99  
% 2.09/0.99  --aig_mode                              false
% 2.09/0.99  
% 2.09/0.99  ------ Instantiation Options
% 2.09/0.99  
% 2.09/0.99  --instantiation_flag                    true
% 2.09/0.99  --inst_sos_flag                         false
% 2.09/0.99  --inst_sos_phase                        true
% 2.09/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.09/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.09/0.99  --inst_lit_sel_side                     none
% 2.09/0.99  --inst_solver_per_active                1400
% 2.09/0.99  --inst_solver_calls_frac                1.
% 2.09/0.99  --inst_passive_queue_type               priority_queues
% 2.09/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.09/0.99  --inst_passive_queues_freq              [25;2]
% 2.09/0.99  --inst_dismatching                      true
% 2.09/0.99  --inst_eager_unprocessed_to_passive     true
% 2.09/0.99  --inst_prop_sim_given                   true
% 2.09/0.99  --inst_prop_sim_new                     false
% 2.09/0.99  --inst_subs_new                         false
% 2.09/0.99  --inst_eq_res_simp                      false
% 2.09/0.99  --inst_subs_given                       false
% 2.09/0.99  --inst_orphan_elimination               true
% 2.09/0.99  --inst_learning_loop_flag               true
% 2.09/0.99  --inst_learning_start                   3000
% 2.09/0.99  --inst_learning_factor                  2
% 2.09/0.99  --inst_start_prop_sim_after_learn       3
% 2.09/0.99  --inst_sel_renew                        solver
% 2.09/0.99  --inst_lit_activity_flag                true
% 2.09/0.99  --inst_restr_to_given                   false
% 2.09/0.99  --inst_activity_threshold               500
% 2.09/0.99  --inst_out_proof                        true
% 2.09/0.99  
% 2.09/0.99  ------ Resolution Options
% 2.09/0.99  
% 2.09/0.99  --resolution_flag                       false
% 2.09/0.99  --res_lit_sel                           adaptive
% 2.09/0.99  --res_lit_sel_side                      none
% 2.09/0.99  --res_ordering                          kbo
% 2.09/0.99  --res_to_prop_solver                    active
% 2.09/0.99  --res_prop_simpl_new                    false
% 2.09/0.99  --res_prop_simpl_given                  true
% 2.09/0.99  --res_passive_queue_type                priority_queues
% 2.09/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.09/0.99  --res_passive_queues_freq               [15;5]
% 2.09/0.99  --res_forward_subs                      full
% 2.09/0.99  --res_backward_subs                     full
% 2.09/0.99  --res_forward_subs_resolution           true
% 2.09/0.99  --res_backward_subs_resolution          true
% 2.09/0.99  --res_orphan_elimination                true
% 2.09/0.99  --res_time_limit                        2.
% 2.09/0.99  --res_out_proof                         true
% 2.09/0.99  
% 2.09/0.99  ------ Superposition Options
% 2.09/0.99  
% 2.09/0.99  --superposition_flag                    true
% 2.09/0.99  --sup_passive_queue_type                priority_queues
% 2.09/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.09/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.09/0.99  --demod_completeness_check              fast
% 2.09/0.99  --demod_use_ground                      true
% 2.09/0.99  --sup_to_prop_solver                    passive
% 2.09/0.99  --sup_prop_simpl_new                    true
% 2.09/0.99  --sup_prop_simpl_given                  true
% 2.09/0.99  --sup_fun_splitting                     false
% 2.09/0.99  --sup_smt_interval                      50000
% 2.09/0.99  
% 2.09/0.99  ------ Superposition Simplification Setup
% 2.09/0.99  
% 2.09/0.99  --sup_indices_passive                   []
% 2.09/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.09/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.09/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.09/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.09/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.09/0.99  --sup_full_bw                           [BwDemod]
% 2.09/0.99  --sup_immed_triv                        [TrivRules]
% 2.09/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.09/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.09/0.99  --sup_immed_bw_main                     []
% 2.09/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.09/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.09/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.09/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.09/0.99  
% 2.09/0.99  ------ Combination Options
% 2.09/0.99  
% 2.09/0.99  --comb_res_mult                         3
% 2.09/0.99  --comb_sup_mult                         2
% 2.09/0.99  --comb_inst_mult                        10
% 2.09/0.99  
% 2.09/0.99  ------ Debug Options
% 2.09/0.99  
% 2.09/0.99  --dbg_backtrace                         false
% 2.09/0.99  --dbg_dump_prop_clauses                 false
% 2.09/0.99  --dbg_dump_prop_clauses_file            -
% 2.09/0.99  --dbg_out_stat                          false
% 2.09/0.99  
% 2.09/0.99  
% 2.09/0.99  
% 2.09/0.99  
% 2.09/0.99  ------ Proving...
% 2.09/0.99  
% 2.09/0.99  
% 2.09/0.99  % SZS status Theorem for theBenchmark.p
% 2.09/0.99  
% 2.09/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.09/0.99  
% 2.09/0.99  fof(f9,axiom,(
% 2.09/0.99    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 2.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f18,plain,(
% 2.09/0.99    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 2.09/0.99    inference(pure_predicate_removal,[],[f9])).
% 2.09/0.99  
% 2.09/0.99  fof(f32,plain,(
% 2.09/0.99    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.09/0.99    inference(ennf_transformation,[],[f18])).
% 2.09/0.99  
% 2.09/0.99  fof(f33,plain,(
% 2.09/0.99    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.09/0.99    inference(flattening,[],[f32])).
% 2.09/0.99  
% 2.09/0.99  fof(f72,plain,(
% 2.09/0.99    ( ! [X0,X1] : (m1_pre_topc(k1_tex_2(X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.09/0.99    inference(cnf_transformation,[],[f33])).
% 2.09/0.99  
% 2.09/0.99  fof(f7,axiom,(
% 2.09/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v1_subset_1(X2,u1_struct_0(X0)))))))),
% 2.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f29,plain,(
% 2.09/0.99    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : ((v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.09/0.99    inference(ennf_transformation,[],[f7])).
% 2.09/0.99  
% 2.09/0.99  fof(f30,plain,(
% 2.09/0.99    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.09/0.99    inference(flattening,[],[f29])).
% 2.09/0.99  
% 2.09/0.99  fof(f46,plain,(
% 2.09/0.99    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.09/0.99    inference(nnf_transformation,[],[f30])).
% 2.09/0.99  
% 2.09/0.99  fof(f47,plain,(
% 2.09/0.99    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.09/0.99    inference(rectify,[],[f46])).
% 2.09/0.99  
% 2.09/0.99  fof(f48,plain,(
% 2.09/0.99    ! [X1,X0] : (? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_subset_1(sK0(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK0(X0,X1) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.09/0.99    introduced(choice_axiom,[])).
% 2.09/0.99  
% 2.09/0.99  fof(f49,plain,(
% 2.09/0.99    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | (~v1_subset_1(sK0(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK0(X0,X1) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.09/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f47,f48])).
% 2.09/0.99  
% 2.09/0.99  fof(f67,plain,(
% 2.09/0.99    ( ! [X0,X1] : (v1_tex_2(X1,X0) | u1_struct_0(X1) = sK0(X0,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.09/0.99    inference(cnf_transformation,[],[f49])).
% 2.09/0.99  
% 2.09/0.99  fof(f13,axiom,(
% 2.09/0.99    ! [X0] : ((~v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,X0) => v1_subset_1(k6_domain_1(X0,X1),X0)))),
% 2.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f40,plain,(
% 2.09/0.99    ! [X0] : (! [X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | (v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 2.09/0.99    inference(ennf_transformation,[],[f13])).
% 2.09/0.99  
% 2.09/0.99  fof(f41,plain,(
% 2.09/0.99    ! [X0] : (! [X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 2.09/0.99    inference(flattening,[],[f40])).
% 2.09/0.99  
% 2.09/0.99  fof(f80,plain,(
% 2.09/0.99    ( ! [X0,X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0) | v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 2.09/0.99    inference(cnf_transformation,[],[f41])).
% 2.09/0.99  
% 2.09/0.99  fof(f15,conjecture,(
% 2.09/0.99    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 2.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f16,negated_conjecture,(
% 2.09/0.99    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 2.09/0.99    inference(negated_conjecture,[],[f15])).
% 2.09/0.99  
% 2.09/0.99  fof(f44,plain,(
% 2.09/0.99    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.09/0.99    inference(ennf_transformation,[],[f16])).
% 2.09/0.99  
% 2.09/0.99  fof(f45,plain,(
% 2.09/0.99    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.09/0.99    inference(flattening,[],[f44])).
% 2.09/0.99  
% 2.09/0.99  fof(f53,plain,(
% 2.09/0.99    ? [X0] : (? [X1] : (((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.09/0.99    inference(nnf_transformation,[],[f45])).
% 2.09/0.99  
% 2.09/0.99  fof(f54,plain,(
% 2.09/0.99    ? [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.09/0.99    inference(flattening,[],[f53])).
% 2.09/0.99  
% 2.09/0.99  fof(f56,plain,(
% 2.09/0.99    ( ! [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) => ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),sK3),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,sK3),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),sK3),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,sK3),X0)) & m1_subset_1(sK3,u1_struct_0(X0)))) )),
% 2.09/0.99    introduced(choice_axiom,[])).
% 2.09/0.99  
% 2.09/0.99  fof(f55,plain,(
% 2.09/0.99    ? [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(sK2),X1),u1_struct_0(sK2)) | ~v1_tex_2(k1_tex_2(sK2,X1),sK2)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK2),X1),u1_struct_0(sK2)) | v1_tex_2(k1_tex_2(sK2,X1),sK2)) & m1_subset_1(X1,u1_struct_0(sK2))) & l1_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 2.09/0.99    introduced(choice_axiom,[])).
% 2.09/0.99  
% 2.09/0.99  fof(f57,plain,(
% 2.09/0.99    ((~v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) | ~v1_tex_2(k1_tex_2(sK2,sK3),sK2)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) | v1_tex_2(k1_tex_2(sK2,sK3),sK2)) & m1_subset_1(sK3,u1_struct_0(sK2))) & l1_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 2.09/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f54,f56,f55])).
% 2.09/0.99  
% 2.09/0.99  fof(f86,plain,(
% 2.09/0.99    ~v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) | ~v1_tex_2(k1_tex_2(sK2,sK3),sK2)),
% 2.09/0.99    inference(cnf_transformation,[],[f57])).
% 2.09/0.99  
% 2.09/0.99  fof(f82,plain,(
% 2.09/0.99    ~v2_struct_0(sK2)),
% 2.09/0.99    inference(cnf_transformation,[],[f57])).
% 2.09/0.99  
% 2.09/0.99  fof(f83,plain,(
% 2.09/0.99    l1_pre_topc(sK2)),
% 2.09/0.99    inference(cnf_transformation,[],[f57])).
% 2.09/0.99  
% 2.09/0.99  fof(f4,axiom,(
% 2.09/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f23,plain,(
% 2.09/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.09/0.99    inference(ennf_transformation,[],[f4])).
% 2.09/0.99  
% 2.09/0.99  fof(f24,plain,(
% 2.09/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.09/0.99    inference(flattening,[],[f23])).
% 2.09/0.99  
% 2.09/0.99  fof(f61,plain,(
% 2.09/0.99    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.09/0.99    inference(cnf_transformation,[],[f24])).
% 2.09/0.99  
% 2.09/0.99  fof(f2,axiom,(
% 2.09/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f21,plain,(
% 2.09/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.09/0.99    inference(ennf_transformation,[],[f2])).
% 2.09/0.99  
% 2.09/0.99  fof(f59,plain,(
% 2.09/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.09/0.99    inference(cnf_transformation,[],[f21])).
% 2.09/0.99  
% 2.09/0.99  fof(f84,plain,(
% 2.09/0.99    m1_subset_1(sK3,u1_struct_0(sK2))),
% 2.09/0.99    inference(cnf_transformation,[],[f57])).
% 2.09/0.99  
% 2.09/0.99  fof(f11,axiom,(
% 2.09/0.99    ! [X0] : ((l1_struct_0(X0) & ~v7_struct_0(X0) & ~v2_struct_0(X0)) => ? [X1] : (~v1_subset_1(X1,u1_struct_0(X0)) & ~v1_zfmisc_1(X1) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f36,plain,(
% 2.09/0.99    ! [X0] : (? [X1] : (~v1_subset_1(X1,u1_struct_0(X0)) & ~v1_zfmisc_1(X1) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_struct_0(X0) | v7_struct_0(X0) | v2_struct_0(X0)))),
% 2.09/0.99    inference(ennf_transformation,[],[f11])).
% 2.09/0.99  
% 2.09/0.99  fof(f37,plain,(
% 2.09/0.99    ! [X0] : (? [X1] : (~v1_subset_1(X1,u1_struct_0(X0)) & ~v1_zfmisc_1(X1) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_struct_0(X0) | v7_struct_0(X0) | v2_struct_0(X0))),
% 2.09/0.99    inference(flattening,[],[f36])).
% 2.09/0.99  
% 2.09/0.99  fof(f51,plain,(
% 2.09/0.99    ! [X0] : (? [X1] : (~v1_subset_1(X1,u1_struct_0(X0)) & ~v1_zfmisc_1(X1) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_subset_1(sK1(X0),u1_struct_0(X0)) & ~v1_zfmisc_1(sK1(X0)) & ~v1_xboole_0(sK1(X0)) & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.09/0.99    introduced(choice_axiom,[])).
% 2.09/0.99  
% 2.09/0.99  fof(f52,plain,(
% 2.09/0.99    ! [X0] : ((~v1_subset_1(sK1(X0),u1_struct_0(X0)) & ~v1_zfmisc_1(sK1(X0)) & ~v1_xboole_0(sK1(X0)) & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_struct_0(X0) | v7_struct_0(X0) | v2_struct_0(X0))),
% 2.09/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f37,f51])).
% 2.09/0.99  
% 2.09/0.99  fof(f75,plain,(
% 2.09/0.99    ( ! [X0] : (m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0) | v7_struct_0(X0) | v2_struct_0(X0)) )),
% 2.09/0.99    inference(cnf_transformation,[],[f52])).
% 2.09/0.99  
% 2.09/0.99  fof(f1,axiom,(
% 2.09/0.99    ! [X0] : (l1_struct_0(X0) => (v2_struct_0(X0) => v7_struct_0(X0)))),
% 2.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f19,plain,(
% 2.09/0.99    ! [X0] : ((v7_struct_0(X0) | ~v2_struct_0(X0)) | ~l1_struct_0(X0))),
% 2.09/0.99    inference(ennf_transformation,[],[f1])).
% 2.09/0.99  
% 2.09/0.99  fof(f20,plain,(
% 2.09/0.99    ! [X0] : (v7_struct_0(X0) | ~v2_struct_0(X0) | ~l1_struct_0(X0))),
% 2.09/0.99    inference(flattening,[],[f19])).
% 2.09/0.99  
% 2.09/0.99  fof(f58,plain,(
% 2.09/0.99    ( ! [X0] : (v7_struct_0(X0) | ~v2_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.09/0.99    inference(cnf_transformation,[],[f20])).
% 2.09/0.99  
% 2.09/0.99  fof(f77,plain,(
% 2.09/0.99    ( ! [X0] : (~v1_zfmisc_1(sK1(X0)) | ~l1_struct_0(X0) | v7_struct_0(X0) | v2_struct_0(X0)) )),
% 2.09/0.99    inference(cnf_transformation,[],[f52])).
% 2.09/0.99  
% 2.09/0.99  fof(f78,plain,(
% 2.09/0.99    ( ! [X0] : (~v1_subset_1(sK1(X0),u1_struct_0(X0)) | ~l1_struct_0(X0) | v7_struct_0(X0) | v2_struct_0(X0)) )),
% 2.09/0.99    inference(cnf_transformation,[],[f52])).
% 2.09/0.99  
% 2.09/0.99  fof(f6,axiom,(
% 2.09/0.99    ! [X0] : ((l1_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (~v2_struct_0(X1) => (~v1_tex_2(X1,X0) & ~v2_struct_0(X1)))))),
% 2.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f27,plain,(
% 2.09/0.99    ! [X0] : (! [X1] : (((~v1_tex_2(X1,X0) & ~v2_struct_0(X1)) | v2_struct_0(X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0)))),
% 2.09/0.99    inference(ennf_transformation,[],[f6])).
% 2.09/0.99  
% 2.09/0.99  fof(f28,plain,(
% 2.09/0.99    ! [X0] : (! [X1] : ((~v1_tex_2(X1,X0) & ~v2_struct_0(X1)) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0))),
% 2.09/0.99    inference(flattening,[],[f27])).
% 2.09/0.99  
% 2.09/0.99  fof(f64,plain,(
% 2.09/0.99    ( ! [X0,X1] : (~v1_tex_2(X1,X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0)) )),
% 2.09/0.99    inference(cnf_transformation,[],[f28])).
% 2.09/0.99  
% 2.09/0.99  fof(f85,plain,(
% 2.09/0.99    v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) | v1_tex_2(k1_tex_2(sK2,sK3),sK2)),
% 2.09/0.99    inference(cnf_transformation,[],[f57])).
% 2.09/0.99  
% 2.09/0.99  fof(f5,axiom,(
% 2.09/0.99    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 2.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f25,plain,(
% 2.09/0.99    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 2.09/0.99    inference(ennf_transformation,[],[f5])).
% 2.09/0.99  
% 2.09/0.99  fof(f26,plain,(
% 2.09/0.99    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 2.09/0.99    inference(flattening,[],[f25])).
% 2.09/0.99  
% 2.09/0.99  fof(f62,plain,(
% 2.09/0.99    ( ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0)) )),
% 2.09/0.99    inference(cnf_transformation,[],[f26])).
% 2.09/0.99  
% 2.09/0.99  fof(f12,axiom,(
% 2.09/0.99    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 2.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f38,plain,(
% 2.09/0.99    ! [X0] : (! [X1] : ((~v1_zfmisc_1(X0) | ~v1_subset_1(k6_domain_1(X0,X1),X0)) | ~m1_subset_1(X1,X0)) | v1_xboole_0(X0))),
% 2.09/0.99    inference(ennf_transformation,[],[f12])).
% 2.09/0.99  
% 2.09/0.99  fof(f39,plain,(
% 2.09/0.99    ! [X0] : (! [X1] : (~v1_zfmisc_1(X0) | ~v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | v1_xboole_0(X0))),
% 2.09/0.99    inference(flattening,[],[f38])).
% 2.09/0.99  
% 2.09/0.99  fof(f79,plain,(
% 2.09/0.99    ( ! [X0,X1] : (~v1_zfmisc_1(X0) | ~v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.09/0.99    inference(cnf_transformation,[],[f39])).
% 2.09/0.99  
% 2.09/0.99  fof(f10,axiom,(
% 2.09/0.99    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 2.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f17,plain,(
% 2.09/0.99    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 2.09/0.99    inference(pure_predicate_removal,[],[f10])).
% 2.09/0.99  
% 2.09/0.99  fof(f34,plain,(
% 2.09/0.99    ! [X0,X1] : ((v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.09/0.99    inference(ennf_transformation,[],[f17])).
% 2.09/0.99  
% 2.09/0.99  fof(f35,plain,(
% 2.09/0.99    ! [X0,X1] : ((v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.09/0.99    inference(flattening,[],[f34])).
% 2.09/0.99  
% 2.09/0.99  fof(f73,plain,(
% 2.09/0.99    ( ! [X0,X1] : (~v2_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.09/0.99    inference(cnf_transformation,[],[f35])).
% 2.09/0.99  
% 2.09/0.99  fof(f8,axiom,(
% 2.09/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 2.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f31,plain,(
% 2.09/0.99    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.09/0.99    inference(ennf_transformation,[],[f8])).
% 2.09/0.99  
% 2.09/0.99  fof(f50,plain,(
% 2.09/0.99    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.09/0.99    inference(nnf_transformation,[],[f31])).
% 2.09/0.99  
% 2.09/0.99  fof(f70,plain,(
% 2.09/0.99    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.09/0.99    inference(cnf_transformation,[],[f50])).
% 2.09/0.99  
% 2.09/0.99  fof(f66,plain,(
% 2.09/0.99    ( ! [X0,X1] : (v1_tex_2(X1,X0) | m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.09/0.99    inference(cnf_transformation,[],[f49])).
% 2.09/0.99  
% 2.09/0.99  fof(f68,plain,(
% 2.09/0.99    ( ! [X0,X1] : (v1_tex_2(X1,X0) | ~v1_subset_1(sK0(X0,X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.09/0.99    inference(cnf_transformation,[],[f49])).
% 2.09/0.99  
% 2.09/0.99  fof(f3,axiom,(
% 2.09/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f22,plain,(
% 2.09/0.99    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.09/0.99    inference(ennf_transformation,[],[f3])).
% 2.09/0.99  
% 2.09/0.99  fof(f60,plain,(
% 2.09/0.99    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.09/0.99    inference(cnf_transformation,[],[f22])).
% 2.09/0.99  
% 2.09/0.99  fof(f74,plain,(
% 2.09/0.99    ( ! [X0,X1] : (v7_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.09/0.99    inference(cnf_transformation,[],[f35])).
% 2.09/0.99  
% 2.09/0.99  cnf(c_13,plain,
% 2.09/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.09/0.99      | m1_pre_topc(k1_tex_2(X1,X0),X1)
% 2.09/0.99      | ~ l1_pre_topc(X1)
% 2.09/0.99      | v2_struct_0(X1) ),
% 2.09/0.99      inference(cnf_transformation,[],[f72]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_5541,plain,
% 2.09/0.99      ( ~ m1_subset_1(X0_46,u1_struct_0(X0_47))
% 2.09/0.99      | m1_pre_topc(k1_tex_2(X0_47,X0_46),X0_47)
% 2.09/0.99      | ~ l1_pre_topc(X0_47)
% 2.09/0.99      | v2_struct_0(X0_47) ),
% 2.09/0.99      inference(subtyping,[status(esa)],[c_13]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_6255,plain,
% 2.09/0.99      ( m1_subset_1(X0_46,u1_struct_0(X0_47)) != iProver_top
% 2.09/0.99      | m1_pre_topc(k1_tex_2(X0_47,X0_46),X0_47) = iProver_top
% 2.09/0.99      | l1_pre_topc(X0_47) != iProver_top
% 2.09/0.99      | v2_struct_0(X0_47) = iProver_top ),
% 2.09/0.99      inference(predicate_to_equality,[status(thm)],[c_5541]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_8,plain,
% 2.09/0.99      ( v1_tex_2(X0,X1)
% 2.09/0.99      | ~ m1_pre_topc(X0,X1)
% 2.09/0.99      | ~ l1_pre_topc(X1)
% 2.09/0.99      | sK0(X1,X0) = u1_struct_0(X0) ),
% 2.09/0.99      inference(cnf_transformation,[],[f67]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_5546,plain,
% 2.09/0.99      ( v1_tex_2(X0_47,X1_47)
% 2.09/0.99      | ~ m1_pre_topc(X0_47,X1_47)
% 2.09/0.99      | ~ l1_pre_topc(X1_47)
% 2.09/0.99      | sK0(X1_47,X0_47) = u1_struct_0(X0_47) ),
% 2.09/0.99      inference(subtyping,[status(esa)],[c_8]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_6250,plain,
% 2.09/0.99      ( sK0(X0_47,X1_47) = u1_struct_0(X1_47)
% 2.09/0.99      | v1_tex_2(X1_47,X0_47) = iProver_top
% 2.09/0.99      | m1_pre_topc(X1_47,X0_47) != iProver_top
% 2.09/0.99      | l1_pre_topc(X0_47) != iProver_top ),
% 2.09/0.99      inference(predicate_to_equality,[status(thm)],[c_5546]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_7049,plain,
% 2.09/0.99      ( sK0(X0_47,k1_tex_2(X0_47,X0_46)) = u1_struct_0(k1_tex_2(X0_47,X0_46))
% 2.09/0.99      | m1_subset_1(X0_46,u1_struct_0(X0_47)) != iProver_top
% 2.09/0.99      | v1_tex_2(k1_tex_2(X0_47,X0_46),X0_47) = iProver_top
% 2.09/0.99      | l1_pre_topc(X0_47) != iProver_top
% 2.09/0.99      | v2_struct_0(X0_47) = iProver_top ),
% 2.09/0.99      inference(superposition,[status(thm)],[c_6255,c_6250]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_22,plain,
% 2.09/0.99      ( ~ m1_subset_1(X0,X1)
% 2.09/0.99      | v1_subset_1(k6_domain_1(X1,X0),X1)
% 2.09/0.99      | v1_zfmisc_1(X1)
% 2.09/0.99      | v1_xboole_0(X1) ),
% 2.09/0.99      inference(cnf_transformation,[],[f80]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_5537,plain,
% 2.09/0.99      ( ~ m1_subset_1(X0_46,X1_46)
% 2.09/0.99      | v1_subset_1(k6_domain_1(X1_46,X0_46),X1_46)
% 2.09/0.99      | v1_zfmisc_1(X1_46)
% 2.09/0.99      | v1_xboole_0(X1_46) ),
% 2.09/0.99      inference(subtyping,[status(esa)],[c_22]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_6259,plain,
% 2.09/0.99      ( m1_subset_1(X0_46,X1_46) != iProver_top
% 2.09/0.99      | v1_subset_1(k6_domain_1(X1_46,X0_46),X1_46) = iProver_top
% 2.09/0.99      | v1_zfmisc_1(X1_46) = iProver_top
% 2.09/0.99      | v1_xboole_0(X1_46) = iProver_top ),
% 2.09/0.99      inference(predicate_to_equality,[status(thm)],[c_5537]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_24,negated_conjecture,
% 2.09/0.99      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 2.09/0.99      | ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2) ),
% 2.09/0.99      inference(cnf_transformation,[],[f86]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_5536,negated_conjecture,
% 2.09/0.99      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 2.09/0.99      | ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2) ),
% 2.09/0.99      inference(subtyping,[status(esa)],[c_24]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_6260,plain,
% 2.09/0.99      ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) != iProver_top
% 2.09/0.99      | v1_tex_2(k1_tex_2(sK2,sK3),sK2) != iProver_top ),
% 2.09/0.99      inference(predicate_to_equality,[status(thm)],[c_5536]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_6653,plain,
% 2.09/0.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 2.09/0.99      | v1_tex_2(k1_tex_2(sK2,sK3),sK2) != iProver_top
% 2.09/0.99      | v1_zfmisc_1(u1_struct_0(sK2)) = iProver_top
% 2.09/0.99      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 2.09/0.99      inference(superposition,[status(thm)],[c_6259,c_6260]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_3184,plain,
% 2.09/0.99      ( ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2)
% 2.09/0.99      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) ),
% 2.09/0.99      inference(prop_impl,[status(thm)],[c_24]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_3185,plain,
% 2.09/0.99      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 2.09/0.99      | ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2) ),
% 2.09/0.99      inference(renaming,[status(thm)],[c_3184]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_4668,plain,
% 2.09/0.99      ( ~ m1_subset_1(X0,X1)
% 2.09/0.99      | ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2)
% 2.09/0.99      | v1_zfmisc_1(X1)
% 2.09/0.99      | v1_xboole_0(X1)
% 2.09/0.99      | k6_domain_1(u1_struct_0(sK2),sK3) != k6_domain_1(X1,X0)
% 2.09/0.99      | u1_struct_0(sK2) != X1 ),
% 2.09/0.99      inference(resolution_lifted,[status(thm)],[c_22,c_3185]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_4669,plain,
% 2.09/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.09/0.99      | ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2)
% 2.09/0.99      | v1_zfmisc_1(u1_struct_0(sK2))
% 2.09/0.99      | v1_xboole_0(u1_struct_0(sK2))
% 2.09/0.99      | k6_domain_1(u1_struct_0(sK2),sK3) != k6_domain_1(u1_struct_0(sK2),X0) ),
% 2.09/0.99      inference(unflattening,[status(thm)],[c_4668]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_28,negated_conjecture,
% 2.09/0.99      ( ~ v2_struct_0(sK2) ),
% 2.09/0.99      inference(cnf_transformation,[],[f82]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_27,negated_conjecture,
% 2.09/0.99      ( l1_pre_topc(sK2) ),
% 2.09/0.99      inference(cnf_transformation,[],[f83]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_3,plain,
% 2.09/0.99      ( ~ v1_xboole_0(u1_struct_0(X0))
% 2.09/0.99      | ~ l1_struct_0(X0)
% 2.09/0.99      | v2_struct_0(X0) ),
% 2.09/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_91,plain,
% 2.09/0.99      ( ~ v1_xboole_0(u1_struct_0(sK2))
% 2.09/0.99      | ~ l1_struct_0(sK2)
% 2.09/0.99      | v2_struct_0(sK2) ),
% 2.09/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1,plain,
% 2.09/0.99      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 2.09/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_95,plain,
% 2.09/0.99      ( ~ l1_pre_topc(sK2) | l1_struct_0(sK2) ),
% 2.09/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_26,negated_conjecture,
% 2.09/0.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 2.09/0.99      inference(cnf_transformation,[],[f84]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_2930,plain,
% 2.09/0.99      ( v1_subset_1(k6_domain_1(X0,X1),X0)
% 2.09/0.99      | v1_zfmisc_1(X0)
% 2.09/0.99      | v1_xboole_0(X0)
% 2.09/0.99      | u1_struct_0(sK2) != X0
% 2.09/0.99      | sK3 != X1 ),
% 2.09/0.99      inference(resolution_lifted,[status(thm)],[c_22,c_26]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_2931,plain,
% 2.09/0.99      ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 2.09/0.99      | v1_zfmisc_1(u1_struct_0(sK2))
% 2.09/0.99      | v1_xboole_0(u1_struct_0(sK2)) ),
% 2.09/0.99      inference(unflattening,[status(thm)],[c_2930]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_4671,plain,
% 2.09/0.99      ( ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2)
% 2.09/0.99      | v1_zfmisc_1(u1_struct_0(sK2)) ),
% 2.09/0.99      inference(global_propositional_subsumption,
% 2.09/0.99                [status(thm)],
% 2.09/0.99                [c_4669,c_28,c_27,c_24,c_91,c_95,c_2931]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_4673,plain,
% 2.09/0.99      ( v1_tex_2(k1_tex_2(sK2,sK3),sK2) != iProver_top
% 2.09/0.99      | v1_zfmisc_1(u1_struct_0(sK2)) = iProver_top ),
% 2.09/0.99      inference(predicate_to_equality,[status(thm)],[c_4671]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_6771,plain,
% 2.09/0.99      ( v1_zfmisc_1(u1_struct_0(sK2)) = iProver_top
% 2.09/0.99      | v1_tex_2(k1_tex_2(sK2,sK3),sK2) != iProver_top ),
% 2.09/0.99      inference(global_propositional_subsumption,
% 2.09/0.99                [status(thm)],
% 2.09/0.99                [c_6653,c_4673]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_6772,plain,
% 2.09/0.99      ( v1_tex_2(k1_tex_2(sK2,sK3),sK2) != iProver_top
% 2.09/0.99      | v1_zfmisc_1(u1_struct_0(sK2)) = iProver_top ),
% 2.09/0.99      inference(renaming,[status(thm)],[c_6771]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_7905,plain,
% 2.09/0.99      ( sK0(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(k1_tex_2(sK2,sK3))
% 2.09/0.99      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 2.09/0.99      | v1_zfmisc_1(u1_struct_0(sK2)) = iProver_top
% 2.09/0.99      | l1_pre_topc(sK2) != iProver_top
% 2.09/0.99      | v2_struct_0(sK2) = iProver_top ),
% 2.09/0.99      inference(superposition,[status(thm)],[c_7049,c_6772]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_20,plain,
% 2.09/0.99      ( m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 2.09/0.99      | ~ l1_struct_0(X0)
% 2.09/0.99      | v2_struct_0(X0)
% 2.09/0.99      | v7_struct_0(X0) ),
% 2.09/0.99      inference(cnf_transformation,[],[f75]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_0,plain,
% 2.09/0.99      ( ~ l1_struct_0(X0) | ~ v2_struct_0(X0) | v7_struct_0(X0) ),
% 2.09/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_165,plain,
% 2.09/0.99      ( ~ l1_struct_0(X0)
% 2.09/0.99      | m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 2.09/0.99      | v7_struct_0(X0) ),
% 2.09/0.99      inference(global_propositional_subsumption,
% 2.09/0.99                [status(thm)],
% 2.09/0.99                [c_20,c_0]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_166,plain,
% 2.09/0.99      ( m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 2.09/0.99      | ~ l1_struct_0(X0)
% 2.09/0.99      | v7_struct_0(X0) ),
% 2.09/0.99      inference(renaming,[status(thm)],[c_165]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_168,plain,
% 2.09/0.99      ( m1_subset_1(sK1(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.09/0.99      | ~ l1_struct_0(sK2)
% 2.09/0.99      | v7_struct_0(sK2) ),
% 2.09/0.99      inference(instantiation,[status(thm)],[c_166]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_18,plain,
% 2.09/0.99      ( ~ v1_zfmisc_1(sK1(X0))
% 2.09/0.99      | ~ l1_struct_0(X0)
% 2.09/0.99      | v2_struct_0(X0)
% 2.09/0.99      | v7_struct_0(X0) ),
% 2.09/0.99      inference(cnf_transformation,[],[f77]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_179,plain,
% 2.09/0.99      ( ~ l1_struct_0(X0) | ~ v1_zfmisc_1(sK1(X0)) | v7_struct_0(X0) ),
% 2.09/0.99      inference(global_propositional_subsumption,
% 2.09/0.99                [status(thm)],
% 2.09/0.99                [c_18,c_0]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_180,plain,
% 2.09/0.99      ( ~ v1_zfmisc_1(sK1(X0)) | ~ l1_struct_0(X0) | v7_struct_0(X0) ),
% 2.09/0.99      inference(renaming,[status(thm)],[c_179]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_182,plain,
% 2.09/0.99      ( ~ v1_zfmisc_1(sK1(sK2)) | ~ l1_struct_0(sK2) | v7_struct_0(sK2) ),
% 2.09/0.99      inference(instantiation,[status(thm)],[c_180]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_17,plain,
% 2.09/0.99      ( ~ v1_subset_1(sK1(X0),u1_struct_0(X0))
% 2.09/0.99      | ~ l1_struct_0(X0)
% 2.09/0.99      | v2_struct_0(X0)
% 2.09/0.99      | v7_struct_0(X0) ),
% 2.09/0.99      inference(cnf_transformation,[],[f78]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_186,plain,
% 2.09/0.99      ( ~ l1_struct_0(X0)
% 2.09/0.99      | ~ v1_subset_1(sK1(X0),u1_struct_0(X0))
% 2.09/0.99      | v7_struct_0(X0) ),
% 2.09/0.99      inference(global_propositional_subsumption,
% 2.09/0.99                [status(thm)],
% 2.09/0.99                [c_17,c_0]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_187,plain,
% 2.09/0.99      ( ~ v1_subset_1(sK1(X0),u1_struct_0(X0))
% 2.09/0.99      | ~ l1_struct_0(X0)
% 2.09/0.99      | v7_struct_0(X0) ),
% 2.09/0.99      inference(renaming,[status(thm)],[c_186]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_189,plain,
% 2.09/0.99      ( ~ v1_subset_1(sK1(sK2),u1_struct_0(sK2))
% 2.09/0.99      | ~ l1_struct_0(sK2)
% 2.09/0.99      | v7_struct_0(sK2) ),
% 2.09/0.99      inference(instantiation,[status(thm)],[c_187]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_5,plain,
% 2.09/0.99      ( ~ v1_tex_2(X0,X1)
% 2.09/0.99      | ~ m1_pre_topc(X0,X1)
% 2.09/0.99      | ~ l1_pre_topc(X1)
% 2.09/0.99      | v2_struct_0(X1)
% 2.09/0.99      | v2_struct_0(X0)
% 2.09/0.99      | ~ v7_struct_0(X1) ),
% 2.09/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_25,negated_conjecture,
% 2.09/0.99      ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 2.09/0.99      | v1_tex_2(k1_tex_2(sK2,sK3),sK2) ),
% 2.09/0.99      inference(cnf_transformation,[],[f85]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_3186,plain,
% 2.09/0.99      ( v1_tex_2(k1_tex_2(sK2,sK3),sK2)
% 2.09/0.99      | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) ),
% 2.09/0.99      inference(prop_impl,[status(thm)],[c_25]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_3187,plain,
% 2.09/0.99      ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 2.09/0.99      | v1_tex_2(k1_tex_2(sK2,sK3),sK2) ),
% 2.09/0.99      inference(renaming,[status(thm)],[c_3186]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_3846,plain,
% 2.09/0.99      ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 2.09/0.99      | ~ m1_pre_topc(X0,X1)
% 2.09/0.99      | ~ l1_pre_topc(X1)
% 2.09/0.99      | v2_struct_0(X0)
% 2.09/0.99      | v2_struct_0(X1)
% 2.09/0.99      | ~ v7_struct_0(X1)
% 2.09/0.99      | k1_tex_2(sK2,sK3) != X0
% 2.09/0.99      | sK2 != X1 ),
% 2.09/0.99      inference(resolution_lifted,[status(thm)],[c_5,c_3187]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_3847,plain,
% 2.09/0.99      ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 2.09/0.99      | ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
% 2.09/0.99      | ~ l1_pre_topc(sK2)
% 2.09/0.99      | v2_struct_0(k1_tex_2(sK2,sK3))
% 2.09/0.99      | v2_struct_0(sK2)
% 2.09/0.99      | ~ v7_struct_0(sK2) ),
% 2.09/0.99      inference(unflattening,[status(thm)],[c_3846]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_4,plain,
% 2.09/0.99      ( v1_zfmisc_1(u1_struct_0(X0))
% 2.09/0.99      | ~ l1_struct_0(X0)
% 2.09/0.99      | ~ v7_struct_0(X0) ),
% 2.09/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_88,plain,
% 2.09/0.99      ( v1_zfmisc_1(u1_struct_0(sK2))
% 2.09/0.99      | ~ l1_struct_0(sK2)
% 2.09/0.99      | ~ v7_struct_0(sK2) ),
% 2.09/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_241,plain,
% 2.09/0.99      ( v1_tex_2(k1_tex_2(sK2,sK3),sK2)
% 2.09/0.99      | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) ),
% 2.09/0.99      inference(prop_impl,[status(thm)],[c_25]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_242,plain,
% 2.09/0.99      ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 2.09/0.99      | v1_tex_2(k1_tex_2(sK2,sK3),sK2) ),
% 2.09/0.99      inference(renaming,[status(thm)],[c_241]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1279,plain,
% 2.09/0.99      ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 2.09/0.99      | ~ m1_pre_topc(X0,X1)
% 2.09/0.99      | ~ l1_pre_topc(X1)
% 2.09/0.99      | v2_struct_0(X0)
% 2.09/0.99      | v2_struct_0(X1)
% 2.09/0.99      | ~ v7_struct_0(X1)
% 2.09/0.99      | k1_tex_2(sK2,sK3) != X0
% 2.09/0.99      | sK2 != X1 ),
% 2.09/0.99      inference(resolution_lifted,[status(thm)],[c_5,c_242]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1280,plain,
% 2.09/0.99      ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 2.09/0.99      | ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
% 2.09/0.99      | ~ l1_pre_topc(sK2)
% 2.09/0.99      | v2_struct_0(k1_tex_2(sK2,sK3))
% 2.09/0.99      | v2_struct_0(sK2)
% 2.09/0.99      | ~ v7_struct_0(sK2) ),
% 2.09/0.99      inference(unflattening,[status(thm)],[c_1279]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1282,plain,
% 2.09/0.99      ( v2_struct_0(k1_tex_2(sK2,sK3))
% 2.09/0.99      | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 2.09/0.99      | ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
% 2.09/0.99      | ~ v7_struct_0(sK2) ),
% 2.09/0.99      inference(global_propositional_subsumption,
% 2.09/0.99                [status(thm)],
% 2.09/0.99                [c_1280,c_28,c_27]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1283,plain,
% 2.09/0.99      ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 2.09/0.99      | ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
% 2.09/0.99      | v2_struct_0(k1_tex_2(sK2,sK3))
% 2.09/0.99      | ~ v7_struct_0(sK2) ),
% 2.09/0.99      inference(renaming,[status(thm)],[c_1282]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_21,plain,
% 2.09/0.99      ( ~ m1_subset_1(X0,X1)
% 2.09/0.99      | ~ v1_subset_1(k6_domain_1(X1,X0),X1)
% 2.09/0.99      | ~ v1_zfmisc_1(X1)
% 2.09/0.99      | v1_xboole_0(X1) ),
% 2.09/0.99      inference(cnf_transformation,[],[f79]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_2944,plain,
% 2.09/0.99      ( ~ v1_subset_1(k6_domain_1(X0,X1),X0)
% 2.09/0.99      | ~ v1_zfmisc_1(X0)
% 2.09/0.99      | v1_xboole_0(X0)
% 2.09/0.99      | u1_struct_0(sK2) != X0
% 2.09/0.99      | sK3 != X1 ),
% 2.09/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_26]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_2945,plain,
% 2.09/0.99      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 2.09/0.99      | ~ v1_zfmisc_1(u1_struct_0(sK2))
% 2.09/0.99      | v1_xboole_0(u1_struct_0(sK2)) ),
% 2.09/0.99      inference(unflattening,[status(thm)],[c_2944]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_3849,plain,
% 2.09/0.99      ( v2_struct_0(k1_tex_2(sK2,sK3))
% 2.09/0.99      | ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
% 2.09/0.99      | ~ v7_struct_0(sK2) ),
% 2.09/0.99      inference(global_propositional_subsumption,
% 2.09/0.99                [status(thm)],
% 2.09/0.99                [c_3847,c_28,c_27,c_88,c_91,c_95,c_1283,c_2945]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_3850,plain,
% 2.09/0.99      ( ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
% 2.09/0.99      | v2_struct_0(k1_tex_2(sK2,sK3))
% 2.09/0.99      | ~ v7_struct_0(sK2) ),
% 2.09/0.99      inference(renaming,[status(thm)],[c_3849]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_5596,plain,
% 2.09/0.99      ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 2.09/0.99      | m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
% 2.09/0.99      | ~ l1_pre_topc(sK2)
% 2.09/0.99      | v2_struct_0(sK2) ),
% 2.09/0.99      inference(instantiation,[status(thm)],[c_5541]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_16,plain,
% 2.09/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.09/0.99      | ~ l1_pre_topc(X1)
% 2.09/0.99      | v2_struct_0(X1)
% 2.09/0.99      | ~ v2_struct_0(k1_tex_2(X1,X0)) ),
% 2.09/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_5540,plain,
% 2.09/0.99      ( ~ m1_subset_1(X0_46,u1_struct_0(X0_47))
% 2.09/0.99      | ~ l1_pre_topc(X0_47)
% 2.09/0.99      | v2_struct_0(X0_47)
% 2.09/0.99      | ~ v2_struct_0(k1_tex_2(X0_47,X0_46)) ),
% 2.09/0.99      inference(subtyping,[status(esa)],[c_16]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_5599,plain,
% 2.09/0.99      ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 2.09/0.99      | ~ l1_pre_topc(sK2)
% 2.09/0.99      | ~ v2_struct_0(k1_tex_2(sK2,sK3))
% 2.09/0.99      | v2_struct_0(sK2) ),
% 2.09/0.99      inference(instantiation,[status(thm)],[c_5540]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_6533,plain,
% 2.09/0.99      ( v1_tex_2(k1_tex_2(X0_47,X0_46),X0_47)
% 2.09/0.99      | ~ m1_pre_topc(k1_tex_2(X0_47,X0_46),X0_47)
% 2.09/0.99      | ~ l1_pre_topc(X0_47)
% 2.09/0.99      | sK0(X0_47,k1_tex_2(X0_47,X0_46)) = u1_struct_0(k1_tex_2(X0_47,X0_46)) ),
% 2.09/0.99      inference(instantiation,[status(thm)],[c_5546]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_6535,plain,
% 2.09/0.99      ( v1_tex_2(k1_tex_2(sK2,sK3),sK2)
% 2.09/0.99      | ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
% 2.09/0.99      | ~ l1_pre_topc(sK2)
% 2.09/0.99      | sK0(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(k1_tex_2(sK2,sK3)) ),
% 2.09/0.99      inference(instantiation,[status(thm)],[c_6533]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_11,plain,
% 2.09/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.09/0.99      | v1_subset_1(X0,X1)
% 2.09/0.99      | X0 = X1 ),
% 2.09/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_5543,plain,
% 2.09/0.99      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(X1_46))
% 2.09/0.99      | v1_subset_1(X0_46,X1_46)
% 2.09/0.99      | X0_46 = X1_46 ),
% 2.09/0.99      inference(subtyping,[status(esa)],[c_11]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_6607,plain,
% 2.09/0.99      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.09/0.99      | v1_subset_1(X0_46,u1_struct_0(sK2))
% 2.09/0.99      | X0_46 = u1_struct_0(sK2) ),
% 2.09/0.99      inference(instantiation,[status(thm)],[c_5543]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_6730,plain,
% 2.09/0.99      ( ~ m1_subset_1(sK1(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.09/0.99      | v1_subset_1(sK1(sK2),u1_struct_0(sK2))
% 2.09/0.99      | sK1(sK2) = u1_struct_0(sK2) ),
% 2.09/0.99      inference(instantiation,[status(thm)],[c_6607]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_5560,plain,
% 2.09/0.99      ( ~ v1_zfmisc_1(X0_46) | v1_zfmisc_1(X1_46) | X1_46 != X0_46 ),
% 2.09/0.99      theory(equality) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_6579,plain,
% 2.09/0.99      ( v1_zfmisc_1(X0_46)
% 2.09/0.99      | ~ v1_zfmisc_1(u1_struct_0(X0_47))
% 2.09/0.99      | X0_46 != u1_struct_0(X0_47) ),
% 2.09/0.99      inference(instantiation,[status(thm)],[c_5560]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_6935,plain,
% 2.09/0.99      ( v1_zfmisc_1(sK1(sK2))
% 2.09/0.99      | ~ v1_zfmisc_1(u1_struct_0(sK2))
% 2.09/0.99      | sK1(sK2) != u1_struct_0(sK2) ),
% 2.09/0.99      inference(instantiation,[status(thm)],[c_6579]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_8234,plain,
% 2.09/0.99      ( sK0(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(k1_tex_2(sK2,sK3)) ),
% 2.09/0.99      inference(global_propositional_subsumption,
% 2.09/0.99                [status(thm)],
% 2.09/0.99                [c_7905,c_28,c_27,c_26,c_95,c_168,c_182,c_189,c_3850,
% 2.09/0.99                 c_4671,c_5596,c_5599,c_6535,c_6730,c_6935]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_9,plain,
% 2.09/0.99      ( m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
% 2.09/0.99      | v1_tex_2(X1,X0)
% 2.09/0.99      | ~ m1_pre_topc(X1,X0)
% 2.09/0.99      | ~ l1_pre_topc(X0) ),
% 2.09/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_5545,plain,
% 2.09/0.99      ( m1_subset_1(sK0(X0_47,X1_47),k1_zfmisc_1(u1_struct_0(X0_47)))
% 2.09/0.99      | v1_tex_2(X1_47,X0_47)
% 2.09/0.99      | ~ m1_pre_topc(X1_47,X0_47)
% 2.09/0.99      | ~ l1_pre_topc(X0_47) ),
% 2.09/0.99      inference(subtyping,[status(esa)],[c_9]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_6251,plain,
% 2.09/0.99      ( m1_subset_1(sK0(X0_47,X1_47),k1_zfmisc_1(u1_struct_0(X0_47))) = iProver_top
% 2.09/0.99      | v1_tex_2(X1_47,X0_47) = iProver_top
% 2.09/0.99      | m1_pre_topc(X1_47,X0_47) != iProver_top
% 2.09/0.99      | l1_pre_topc(X0_47) != iProver_top ),
% 2.09/0.99      inference(predicate_to_equality,[status(thm)],[c_5545]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_6253,plain,
% 2.09/0.99      ( X0_46 = X1_46
% 2.09/0.99      | m1_subset_1(X0_46,k1_zfmisc_1(X1_46)) != iProver_top
% 2.09/0.99      | v1_subset_1(X0_46,X1_46) = iProver_top ),
% 2.09/0.99      inference(predicate_to_equality,[status(thm)],[c_5543]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_7171,plain,
% 2.09/0.99      ( sK0(X0_47,X1_47) = u1_struct_0(X0_47)
% 2.09/0.99      | v1_subset_1(sK0(X0_47,X1_47),u1_struct_0(X0_47)) = iProver_top
% 2.09/0.99      | v1_tex_2(X1_47,X0_47) = iProver_top
% 2.09/0.99      | m1_pre_topc(X1_47,X0_47) != iProver_top
% 2.09/0.99      | l1_pre_topc(X0_47) != iProver_top ),
% 2.09/0.99      inference(superposition,[status(thm)],[c_6251,c_6253]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_7,plain,
% 2.09/0.99      ( ~ v1_subset_1(sK0(X0,X1),u1_struct_0(X0))
% 2.09/0.99      | v1_tex_2(X1,X0)
% 2.09/0.99      | ~ m1_pre_topc(X1,X0)
% 2.09/0.99      | ~ l1_pre_topc(X0) ),
% 2.09/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_5547,plain,
% 2.09/0.99      ( ~ v1_subset_1(sK0(X0_47,X1_47),u1_struct_0(X0_47))
% 2.09/0.99      | v1_tex_2(X1_47,X0_47)
% 2.09/0.99      | ~ m1_pre_topc(X1_47,X0_47)
% 2.09/0.99      | ~ l1_pre_topc(X0_47) ),
% 2.09/0.99      inference(subtyping,[status(esa)],[c_7]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_5585,plain,
% 2.09/0.99      ( v1_subset_1(sK0(X0_47,X1_47),u1_struct_0(X0_47)) != iProver_top
% 2.09/0.99      | v1_tex_2(X1_47,X0_47) = iProver_top
% 2.09/0.99      | m1_pre_topc(X1_47,X0_47) != iProver_top
% 2.09/0.99      | l1_pre_topc(X0_47) != iProver_top ),
% 2.09/0.99      inference(predicate_to_equality,[status(thm)],[c_5547]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_7797,plain,
% 2.09/0.99      ( sK0(X0_47,X1_47) = u1_struct_0(X0_47)
% 2.09/0.99      | v1_tex_2(X1_47,X0_47) = iProver_top
% 2.09/0.99      | m1_pre_topc(X1_47,X0_47) != iProver_top
% 2.09/0.99      | l1_pre_topc(X0_47) != iProver_top ),
% 2.09/0.99      inference(global_propositional_subsumption,
% 2.09/0.99                [status(thm)],
% 2.09/0.99                [c_7171,c_5585]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_7805,plain,
% 2.09/0.99      ( sK0(X0_47,k1_tex_2(X0_47,X0_46)) = u1_struct_0(X0_47)
% 2.09/0.99      | m1_subset_1(X0_46,u1_struct_0(X0_47)) != iProver_top
% 2.09/0.99      | v1_tex_2(k1_tex_2(X0_47,X0_46),X0_47) = iProver_top
% 2.09/0.99      | l1_pre_topc(X0_47) != iProver_top
% 2.09/0.99      | v2_struct_0(X0_47) = iProver_top ),
% 2.09/0.99      inference(superposition,[status(thm)],[c_6255,c_7797]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_7871,plain,
% 2.09/0.99      ( sK0(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(sK2)
% 2.09/0.99      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 2.09/0.99      | v1_zfmisc_1(u1_struct_0(sK2)) = iProver_top
% 2.09/0.99      | l1_pre_topc(sK2) != iProver_top
% 2.09/0.99      | v2_struct_0(sK2) = iProver_top ),
% 2.09/0.99      inference(superposition,[status(thm)],[c_7805,c_6772]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_239,plain,
% 2.09/0.99      ( ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2)
% 2.09/0.99      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) ),
% 2.09/0.99      inference(prop_impl,[status(thm)],[c_24]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_240,plain,
% 2.09/0.99      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 2.09/0.99      | ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2) ),
% 2.09/0.99      inference(renaming,[status(thm)],[c_239]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1208,plain,
% 2.09/0.99      ( m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
% 2.09/0.99      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 2.09/0.99      | ~ m1_pre_topc(X1,X0)
% 2.09/0.99      | ~ l1_pre_topc(X0)
% 2.09/0.99      | k1_tex_2(sK2,sK3) != X1
% 2.09/0.99      | sK2 != X0 ),
% 2.09/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_240]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1209,plain,
% 2.09/0.99      ( m1_subset_1(sK0(sK2,k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.09/0.99      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 2.09/0.99      | ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
% 2.09/0.99      | ~ l1_pre_topc(sK2) ),
% 2.09/0.99      inference(unflattening,[status(thm)],[c_1208]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1225,plain,
% 2.09/0.99      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 2.09/0.99      | ~ v1_subset_1(sK0(X0,X1),u1_struct_0(X0))
% 2.09/0.99      | ~ m1_pre_topc(X1,X0)
% 2.09/0.99      | ~ l1_pre_topc(X0)
% 2.09/0.99      | k1_tex_2(sK2,sK3) != X1
% 2.09/0.99      | sK2 != X0 ),
% 2.09/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_240]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1226,plain,
% 2.09/0.99      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 2.09/0.99      | ~ v1_subset_1(sK0(sK2,k1_tex_2(sK2,sK3)),u1_struct_0(sK2))
% 2.09/0.99      | ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
% 2.09/0.99      | ~ l1_pre_topc(sK2) ),
% 2.09/0.99      inference(unflattening,[status(thm)],[c_1225]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_7021,plain,
% 2.09/0.99      ( ~ m1_subset_1(sK0(sK2,k1_tex_2(sK2,X0_46)),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.09/0.99      | v1_subset_1(sK0(sK2,k1_tex_2(sK2,X0_46)),u1_struct_0(sK2))
% 2.09/0.99      | sK0(sK2,k1_tex_2(sK2,X0_46)) = u1_struct_0(sK2) ),
% 2.09/0.99      inference(instantiation,[status(thm)],[c_6607]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_7025,plain,
% 2.09/0.99      ( ~ m1_subset_1(sK0(sK2,k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.09/0.99      | v1_subset_1(sK0(sK2,k1_tex_2(sK2,sK3)),u1_struct_0(sK2))
% 2.09/0.99      | sK0(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(sK2) ),
% 2.09/0.99      inference(instantiation,[status(thm)],[c_7021]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_8127,plain,
% 2.09/0.99      ( sK0(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(sK2) ),
% 2.09/0.99      inference(global_propositional_subsumption,
% 2.09/0.99                [status(thm)],
% 2.09/0.99                [c_7871,c_28,c_27,c_26,c_91,c_95,c_168,c_182,c_189,
% 2.09/0.99                 c_1209,c_1226,c_2931,c_3850,c_5596,c_5599,c_6730,c_6935,
% 2.09/0.99                 c_7025]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_8236,plain,
% 2.09/0.99      ( u1_struct_0(k1_tex_2(sK2,sK3)) = u1_struct_0(sK2) ),
% 2.09/0.99      inference(light_normalisation,[status(thm)],[c_8234,c_8127]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_633,plain,
% 2.09/0.99      ( v1_zfmisc_1(u1_struct_0(X0))
% 2.09/0.99      | ~ l1_pre_topc(X0)
% 2.09/0.99      | ~ v7_struct_0(X0) ),
% 2.09/0.99      inference(resolution,[status(thm)],[c_1,c_4]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_5527,plain,
% 2.09/0.99      ( v1_zfmisc_1(u1_struct_0(X0_47))
% 2.09/0.99      | ~ l1_pre_topc(X0_47)
% 2.09/0.99      | ~ v7_struct_0(X0_47) ),
% 2.09/0.99      inference(subtyping,[status(esa)],[c_633]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_6269,plain,
% 2.09/0.99      ( v1_zfmisc_1(u1_struct_0(X0_47)) = iProver_top
% 2.09/0.99      | l1_pre_topc(X0_47) != iProver_top
% 2.09/0.99      | v7_struct_0(X0_47) != iProver_top ),
% 2.09/0.99      inference(predicate_to_equality,[status(thm)],[c_5527]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_8249,plain,
% 2.09/0.99      ( v1_zfmisc_1(u1_struct_0(sK2)) = iProver_top
% 2.09/0.99      | l1_pre_topc(k1_tex_2(sK2,sK3)) != iProver_top
% 2.09/0.99      | v7_struct_0(k1_tex_2(sK2,sK3)) != iProver_top ),
% 2.09/0.99      inference(superposition,[status(thm)],[c_8236,c_6269]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_6936,plain,
% 2.09/0.99      ( sK1(sK2) != u1_struct_0(sK2)
% 2.09/0.99      | v1_zfmisc_1(sK1(sK2)) = iProver_top
% 2.09/0.99      | v1_zfmisc_1(u1_struct_0(sK2)) != iProver_top ),
% 2.09/0.99      inference(predicate_to_equality,[status(thm)],[c_6935]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_2,plain,
% 2.09/0.99      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.09/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_5549,plain,
% 2.09/0.99      ( ~ m1_pre_topc(X0_47,X1_47)
% 2.09/0.99      | ~ l1_pre_topc(X1_47)
% 2.09/0.99      | l1_pre_topc(X0_47) ),
% 2.09/0.99      inference(subtyping,[status(esa)],[c_2]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_6688,plain,
% 2.09/0.99      ( ~ m1_pre_topc(k1_tex_2(X0_47,X0_46),X1_47)
% 2.09/0.99      | ~ l1_pre_topc(X1_47)
% 2.09/0.99      | l1_pre_topc(k1_tex_2(X0_47,X0_46)) ),
% 2.09/0.99      inference(instantiation,[status(thm)],[c_5549]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_6689,plain,
% 2.09/0.99      ( m1_pre_topc(k1_tex_2(X0_47,X0_46),X1_47) != iProver_top
% 2.09/0.99      | l1_pre_topc(X1_47) != iProver_top
% 2.09/0.99      | l1_pre_topc(k1_tex_2(X0_47,X0_46)) = iProver_top ),
% 2.09/0.99      inference(predicate_to_equality,[status(thm)],[c_6688]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_6691,plain,
% 2.09/0.99      ( m1_pre_topc(k1_tex_2(sK2,sK3),sK2) != iProver_top
% 2.09/0.99      | l1_pre_topc(k1_tex_2(sK2,sK3)) = iProver_top
% 2.09/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 2.09/0.99      inference(instantiation,[status(thm)],[c_6689]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_15,plain,
% 2.09/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.09/0.99      | ~ l1_pre_topc(X1)
% 2.09/0.99      | v2_struct_0(X1)
% 2.09/0.99      | v7_struct_0(k1_tex_2(X1,X0)) ),
% 2.09/0.99      inference(cnf_transformation,[],[f74]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_5539,plain,
% 2.09/0.99      ( ~ m1_subset_1(X0_46,u1_struct_0(X0_47))
% 2.09/0.99      | ~ l1_pre_topc(X0_47)
% 2.09/0.99      | v2_struct_0(X0_47)
% 2.09/0.99      | v7_struct_0(k1_tex_2(X0_47,X0_46)) ),
% 2.09/0.99      inference(subtyping,[status(esa)],[c_15]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_5601,plain,
% 2.09/0.99      ( m1_subset_1(X0_46,u1_struct_0(X0_47)) != iProver_top
% 2.09/0.99      | l1_pre_topc(X0_47) != iProver_top
% 2.09/0.99      | v2_struct_0(X0_47) = iProver_top
% 2.09/0.99      | v7_struct_0(k1_tex_2(X0_47,X0_46)) = iProver_top ),
% 2.09/0.99      inference(predicate_to_equality,[status(thm)],[c_5539]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_5603,plain,
% 2.09/0.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 2.09/0.99      | l1_pre_topc(sK2) != iProver_top
% 2.09/0.99      | v2_struct_0(sK2) = iProver_top
% 2.09/0.99      | v7_struct_0(k1_tex_2(sK2,sK3)) = iProver_top ),
% 2.09/0.99      inference(instantiation,[status(thm)],[c_5601]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_5598,plain,
% 2.09/0.99      ( m1_subset_1(X0_46,u1_struct_0(X0_47)) != iProver_top
% 2.09/0.99      | l1_pre_topc(X0_47) != iProver_top
% 2.09/0.99      | v2_struct_0(X0_47) = iProver_top
% 2.09/0.99      | v2_struct_0(k1_tex_2(X0_47,X0_46)) != iProver_top ),
% 2.09/0.99      inference(predicate_to_equality,[status(thm)],[c_5540]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_5600,plain,
% 2.09/0.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 2.09/0.99      | l1_pre_topc(sK2) != iProver_top
% 2.09/0.99      | v2_struct_0(k1_tex_2(sK2,sK3)) != iProver_top
% 2.09/0.99      | v2_struct_0(sK2) = iProver_top ),
% 2.09/0.99      inference(instantiation,[status(thm)],[c_5598]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_5595,plain,
% 2.09/0.99      ( m1_subset_1(X0_46,u1_struct_0(X0_47)) != iProver_top
% 2.09/0.99      | m1_pre_topc(k1_tex_2(X0_47,X0_46),X0_47) = iProver_top
% 2.09/0.99      | l1_pre_topc(X0_47) != iProver_top
% 2.09/0.99      | v2_struct_0(X0_47) = iProver_top ),
% 2.09/0.99      inference(predicate_to_equality,[status(thm)],[c_5541]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_5597,plain,
% 2.09/0.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 2.09/0.99      | m1_pre_topc(k1_tex_2(sK2,sK3),sK2) = iProver_top
% 2.09/0.99      | l1_pre_topc(sK2) != iProver_top
% 2.09/0.99      | v2_struct_0(sK2) = iProver_top ),
% 2.09/0.99      inference(instantiation,[status(thm)],[c_5595]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_3851,plain,
% 2.09/0.99      ( m1_pre_topc(k1_tex_2(sK2,sK3),sK2) != iProver_top
% 2.09/0.99      | v2_struct_0(k1_tex_2(sK2,sK3)) = iProver_top
% 2.09/0.99      | v7_struct_0(sK2) != iProver_top ),
% 2.09/0.99      inference(predicate_to_equality,[status(thm)],[c_3850]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_181,plain,
% 2.09/0.99      ( v1_zfmisc_1(sK1(X0)) != iProver_top
% 2.09/0.99      | l1_struct_0(X0) != iProver_top
% 2.09/0.99      | v7_struct_0(X0) = iProver_top ),
% 2.09/0.99      inference(predicate_to_equality,[status(thm)],[c_180]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_183,plain,
% 2.09/0.99      ( v1_zfmisc_1(sK1(sK2)) != iProver_top
% 2.09/0.99      | l1_struct_0(sK2) != iProver_top
% 2.09/0.99      | v7_struct_0(sK2) = iProver_top ),
% 2.09/0.99      inference(instantiation,[status(thm)],[c_181]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_94,plain,
% 2.09/0.99      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 2.09/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_96,plain,
% 2.09/0.99      ( l1_pre_topc(sK2) != iProver_top
% 2.09/0.99      | l1_struct_0(sK2) = iProver_top ),
% 2.09/0.99      inference(instantiation,[status(thm)],[c_94]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_31,plain,
% 2.09/0.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
% 2.09/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_30,plain,
% 2.09/0.99      ( l1_pre_topc(sK2) = iProver_top ),
% 2.09/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_29,plain,
% 2.09/0.99      ( v2_struct_0(sK2) != iProver_top ),
% 2.09/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(contradiction,plain,
% 2.09/0.99      ( $false ),
% 2.09/0.99      inference(minisat,
% 2.09/0.99                [status(thm)],
% 2.09/0.99                [c_8249,c_6936,c_6730,c_6691,c_5603,c_5600,c_5599,c_5597,
% 2.09/0.99                 c_5596,c_3851,c_3850,c_189,c_183,c_168,c_96,c_95,c_31,
% 2.09/0.99                 c_26,c_30,c_27,c_29,c_28]) ).
% 2.09/0.99  
% 2.09/0.99  
% 2.09/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.09/0.99  
% 2.09/0.99  ------                               Statistics
% 2.09/0.99  
% 2.09/0.99  ------ General
% 2.09/0.99  
% 2.09/0.99  abstr_ref_over_cycles:                  0
% 2.09/0.99  abstr_ref_under_cycles:                 0
% 2.09/0.99  gc_basic_clause_elim:                   0
% 2.09/0.99  forced_gc_time:                         0
% 2.09/0.99  parsing_time:                           0.01
% 2.09/0.99  unif_index_cands_time:                  0.
% 2.09/0.99  unif_index_add_time:                    0.
% 2.09/0.99  orderings_time:                         0.
% 2.09/0.99  out_proof_time:                         0.01
% 2.09/0.99  total_time:                             0.196
% 2.09/0.99  num_of_symbols:                         51
% 2.09/0.99  num_of_terms:                           3989
% 2.09/0.99  
% 2.09/0.99  ------ Preprocessing
% 2.09/0.99  
% 2.09/0.99  num_of_splits:                          0
% 2.09/0.99  num_of_split_atoms:                     0
% 2.09/0.99  num_of_reused_defs:                     0
% 2.09/0.99  num_eq_ax_congr_red:                    13
% 2.09/0.99  num_of_sem_filtered_clauses:            1
% 2.09/0.99  num_of_subtypes:                        2
% 2.09/0.99  monotx_restored_types:                  1
% 2.09/0.99  sat_num_of_epr_types:                   0
% 2.09/0.99  sat_num_of_non_cyclic_types:            0
% 2.09/0.99  sat_guarded_non_collapsed_types:        0
% 2.09/0.99  num_pure_diseq_elim:                    0
% 2.09/0.99  simp_replaced_by:                       0
% 2.09/0.99  res_preprocessed:                       138
% 2.09/0.99  prep_upred:                             0
% 2.09/0.99  prep_unflattend:                        207
% 2.09/0.99  smt_new_axioms:                         0
% 2.09/0.99  pred_elim_cands:                        9
% 2.09/0.99  pred_elim:                              1
% 2.09/0.99  pred_elim_cl:                           1
% 2.09/0.99  pred_elim_cycles:                       17
% 2.09/0.99  merged_defs:                            8
% 2.09/0.99  merged_defs_ncl:                        0
% 2.09/0.99  bin_hyper_res:                          8
% 2.09/0.99  prep_cycles:                            4
% 2.09/0.99  pred_elim_time:                         0.073
% 2.09/0.99  splitting_time:                         0.
% 2.09/0.99  sem_filter_time:                        0.
% 2.09/0.99  monotx_time:                            0.
% 2.09/0.99  subtype_inf_time:                       0.001
% 2.09/0.99  
% 2.09/0.99  ------ Problem properties
% 2.09/0.99  
% 2.09/0.99  clauses:                                26
% 2.09/0.99  conjectures:                            5
% 2.09/0.99  epr:                                    5
% 2.09/0.99  horn:                                   17
% 2.09/0.99  ground:                                 5
% 2.09/0.99  unary:                                  3
% 2.09/0.99  binary:                                 3
% 2.09/0.99  lits:                                   84
% 2.09/0.99  lits_eq:                                2
% 2.09/0.99  fd_pure:                                0
% 2.09/0.99  fd_pseudo:                              0
% 2.09/0.99  fd_cond:                                0
% 2.09/0.99  fd_pseudo_cond:                         1
% 2.09/0.99  ac_symbols:                             0
% 2.09/0.99  
% 2.09/0.99  ------ Propositional Solver
% 2.09/0.99  
% 2.09/0.99  prop_solver_calls:                      28
% 2.09/0.99  prop_fast_solver_calls:                 2224
% 2.09/0.99  smt_solver_calls:                       0
% 2.09/0.99  smt_fast_solver_calls:                  0
% 2.09/0.99  prop_num_of_clauses:                    1406
% 2.09/0.99  prop_preprocess_simplified:             6557
% 2.09/0.99  prop_fo_subsumed:                       88
% 2.09/0.99  prop_solver_time:                       0.
% 2.09/0.99  smt_solver_time:                        0.
% 2.09/0.99  smt_fast_solver_time:                   0.
% 2.09/0.99  prop_fast_solver_time:                  0.
% 2.09/0.99  prop_unsat_core_time:                   0.
% 2.09/0.99  
% 2.09/0.99  ------ QBF
% 2.09/0.99  
% 2.09/0.99  qbf_q_res:                              0
% 2.09/0.99  qbf_num_tautologies:                    0
% 2.09/0.99  qbf_prep_cycles:                        0
% 2.09/0.99  
% 2.09/0.99  ------ BMC1
% 2.09/0.99  
% 2.09/0.99  bmc1_current_bound:                     -1
% 2.09/0.99  bmc1_last_solved_bound:                 -1
% 2.09/0.99  bmc1_unsat_core_size:                   -1
% 2.09/0.99  bmc1_unsat_core_parents_size:           -1
% 2.09/0.99  bmc1_merge_next_fun:                    0
% 2.09/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.09/0.99  
% 2.09/0.99  ------ Instantiation
% 2.09/0.99  
% 2.09/0.99  inst_num_of_clauses:                    364
% 2.09/0.99  inst_num_in_passive:                    157
% 2.09/0.99  inst_num_in_active:                     199
% 2.09/0.99  inst_num_in_unprocessed:                8
% 2.09/0.99  inst_num_of_loops:                      220
% 2.09/0.99  inst_num_of_learning_restarts:          0
% 2.09/0.99  inst_num_moves_active_passive:          17
% 2.09/0.99  inst_lit_activity:                      0
% 2.09/0.99  inst_lit_activity_moves:                0
% 2.09/0.99  inst_num_tautologies:                   0
% 2.09/0.99  inst_num_prop_implied:                  0
% 2.09/0.99  inst_num_existing_simplified:           0
% 2.09/0.99  inst_num_eq_res_simplified:             0
% 2.09/0.99  inst_num_child_elim:                    0
% 2.09/0.99  inst_num_of_dismatching_blockings:      95
% 2.09/0.99  inst_num_of_non_proper_insts:           374
% 2.09/0.99  inst_num_of_duplicates:                 0
% 2.09/0.99  inst_inst_num_from_inst_to_res:         0
% 2.09/0.99  inst_dismatching_checking_time:         0.
% 2.09/0.99  
% 2.09/0.99  ------ Resolution
% 2.09/0.99  
% 2.09/0.99  res_num_of_clauses:                     0
% 2.09/0.99  res_num_in_passive:                     0
% 2.09/0.99  res_num_in_active:                      0
% 2.09/0.99  res_num_of_loops:                       142
% 2.09/0.99  res_forward_subset_subsumed:            23
% 2.09/0.99  res_backward_subset_subsumed:           2
% 2.09/0.99  res_forward_subsumed:                   5
% 2.09/0.99  res_backward_subsumed:                  0
% 2.09/0.99  res_forward_subsumption_resolution:     3
% 2.09/0.99  res_backward_subsumption_resolution:    0
% 2.09/0.99  res_clause_to_clause_subsumption:       213
% 2.09/0.99  res_orphan_elimination:                 0
% 2.09/0.99  res_tautology_del:                      73
% 2.09/0.99  res_num_eq_res_simplified:              0
% 2.09/0.99  res_num_sel_changes:                    0
% 2.09/0.99  res_moves_from_active_to_pass:          0
% 2.09/0.99  
% 2.09/0.99  ------ Superposition
% 2.09/0.99  
% 2.09/0.99  sup_time_total:                         0.
% 2.09/0.99  sup_time_generating:                    0.
% 2.09/0.99  sup_time_sim_full:                      0.
% 2.09/0.99  sup_time_sim_immed:                     0.
% 2.09/0.99  
% 2.09/0.99  sup_num_of_clauses:                     52
% 2.09/0.99  sup_num_in_active:                      43
% 2.09/0.99  sup_num_in_passive:                     9
% 2.09/0.99  sup_num_of_loops:                       42
% 2.09/0.99  sup_fw_superposition:                   10
% 2.09/0.99  sup_bw_superposition:                   33
% 2.09/0.99  sup_immediate_simplified:               12
% 2.09/0.99  sup_given_eliminated:                   0
% 2.09/0.99  comparisons_done:                       0
% 2.09/0.99  comparisons_avoided:                    0
% 2.09/0.99  
% 2.09/0.99  ------ Simplifications
% 2.09/0.99  
% 2.09/0.99  
% 2.09/0.99  sim_fw_subset_subsumed:                 8
% 2.09/0.99  sim_bw_subset_subsumed:                 0
% 2.09/0.99  sim_fw_subsumed:                        1
% 2.09/0.99  sim_bw_subsumed:                        0
% 2.09/0.99  sim_fw_subsumption_res:                 0
% 2.09/0.99  sim_bw_subsumption_res:                 0
% 2.09/0.99  sim_tautology_del:                      2
% 2.09/0.99  sim_eq_tautology_del:                   1
% 2.09/0.99  sim_eq_res_simp:                        0
% 2.09/0.99  sim_fw_demodulated:                     0
% 2.09/0.99  sim_bw_demodulated:                     0
% 2.09/0.99  sim_light_normalised:                   4
% 2.09/0.99  sim_joinable_taut:                      0
% 2.09/0.99  sim_joinable_simp:                      0
% 2.09/0.99  sim_ac_normalised:                      0
% 2.09/0.99  sim_smt_subsumption:                    0
% 2.09/0.99  
%------------------------------------------------------------------------------
