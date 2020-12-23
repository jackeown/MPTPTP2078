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
% DateTime   : Thu Dec  3 12:25:37 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :  227 (1393 expanded)
%              Number of clauses        :  152 ( 442 expanded)
%              Number of leaves         :   24 ( 278 expanded)
%              Depth                    :   24
%              Number of atoms          :  790 (6912 expanded)
%              Number of equality atoms :  258 ( 579 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f11])).

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

fof(f45,plain,(
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

fof(f46,plain,(
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
    inference(rectify,[],[f45])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v1_subset_1(X2,u1_struct_0(X0))
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_subset_1(sK0(X0,X1),u1_struct_0(X0))
        & u1_struct_0(X1) = sK0(X0,X1)
        & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f46,f47])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | u1_struct_0(X1) = sK0(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f15,axiom,(
    ! [X0] :
      ( ( ~ v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f75,plain,(
    ! [X0,X1] :
      ( v1_subset_1(k6_domain_1(X0,X1),X0)
      | ~ m1_subset_1(X1,X0)
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f17,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( v1_tex_2(k1_tex_2(X0,X1),X0)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f50,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f51,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f50])).

fof(f53,plain,(
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

fof(f52,plain,
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

fof(f54,plain,
    ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
      | ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1) )
    & ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
      | v1_tex_2(k1_tex_2(sK1,sK2),sK1) )
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l1_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f51,f53,f52])).

fof(f81,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f77,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f78,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f79,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f54])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v7_struct_0(X0) )
     => ~ v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f59,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( ~ v2_struct_0(X1)
           => ( ~ v1_tex_2(X1,X0)
              & ~ v2_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tex_2(X1,X0)
            & ~ v2_struct_0(X1) )
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tex_2(X1,X0)
            & ~ v2_struct_0(X1) )
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ v1_tex_2(X1,X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f80,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f74,plain,(
    ! [X0,X1] :
      ( v7_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f62,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f60,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ~ ( v7_struct_0(X0)
              & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v7_struct_0(X0)
          | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v7_struct_0(X0)
          | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ v7_struct_0(X0)
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | ~ v1_subset_1(sK0(X0,X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_zfmisc_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_zfmisc_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v1_zfmisc_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_zfmisc_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_3836,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_4508,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3836])).

cnf(c_16,plain,
    ( m1_pre_topc(k1_tex_2(X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_3824,plain,
    ( m1_pre_topc(k1_tex_2(X0_46,X0_47),X0_46)
    | ~ m1_subset_1(X0_47,u1_struct_0(X0_46))
    | v2_struct_0(X0_46)
    | ~ l1_pre_topc(X0_46) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_4520,plain,
    ( m1_pre_topc(k1_tex_2(X0_46,X0_47),X0_46) = iProver_top
    | m1_subset_1(X0_47,u1_struct_0(X0_46)) != iProver_top
    | v2_struct_0(X0_46) = iProver_top
    | l1_pre_topc(X0_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3824])).

cnf(c_11,plain,
    ( v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK0(X1,X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_3829,plain,
    ( v1_tex_2(X0_46,X1_46)
    | ~ m1_pre_topc(X0_46,X1_46)
    | ~ l1_pre_topc(X1_46)
    | sK0(X1_46,X0_46) = u1_struct_0(X0_46) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_4515,plain,
    ( sK0(X0_46,X1_46) = u1_struct_0(X1_46)
    | v1_tex_2(X1_46,X0_46) = iProver_top
    | m1_pre_topc(X1_46,X0_46) != iProver_top
    | l1_pre_topc(X0_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3829])).

cnf(c_5445,plain,
    ( sK0(X0_46,k1_tex_2(X0_46,X0_47)) = u1_struct_0(k1_tex_2(X0_46,X0_47))
    | v1_tex_2(k1_tex_2(X0_46,X0_47),X0_46) = iProver_top
    | m1_subset_1(X0_47,u1_struct_0(X0_46)) != iProver_top
    | v2_struct_0(X0_46) = iProver_top
    | l1_pre_topc(X0_46) != iProver_top ),
    inference(superposition,[status(thm)],[c_4520,c_4515])).

cnf(c_20,plain,
    ( v1_subset_1(k6_domain_1(X0,X1),X0)
    | ~ m1_subset_1(X1,X0)
    | v1_zfmisc_1(X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_3821,plain,
    ( v1_subset_1(k6_domain_1(X0_47,X1_47),X0_47)
    | ~ m1_subset_1(X1_47,X0_47)
    | v1_zfmisc_1(X0_47)
    | v1_xboole_0(X0_47) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_4523,plain,
    ( v1_subset_1(k6_domain_1(X0_47,X1_47),X0_47) = iProver_top
    | m1_subset_1(X1_47,X0_47) != iProver_top
    | v1_zfmisc_1(X0_47) = iProver_top
    | v1_xboole_0(X0_47) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3821])).

cnf(c_22,negated_conjecture,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_3820,negated_conjecture,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_4524,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top
    | v1_tex_2(k1_tex_2(sK1,sK2),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3820])).

cnf(c_5289,plain,
    ( v1_tex_2(k1_tex_2(sK1,sK2),sK1) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK1)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4523,c_4524])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_27,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_25,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_28,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_29,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_31,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top
    | v1_tex_2(k1_tex_2(sK1,sK2),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_6,plain,
    ( v7_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_zfmisc_1(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_73,plain,
    ( v7_struct_0(X0) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | v1_zfmisc_1(u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_75,plain,
    ( v7_struct_0(sK1) = iProver_top
    | l1_struct_0(sK1) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_73])).

cnf(c_4,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_77,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_79,plain,
    ( l1_pre_topc(sK1) != iProver_top
    | l1_struct_0(sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_77])).

cnf(c_8,plain,
    ( ~ v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v7_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_23,negated_conjecture,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_199,plain,
    ( v1_tex_2(k1_tex_2(sK1,sK2),sK1)
    | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) ),
    inference(prop_impl,[status(thm)],[c_23])).

cnf(c_200,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
    inference(renaming,[status(thm)],[c_199])).

cnf(c_908,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v7_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k1_tex_2(sK1,sK2) != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_200])).

cnf(c_909,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
    | v2_struct_0(k1_tex_2(sK1,sK2))
    | v2_struct_0(sK1)
    | ~ v7_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_908])).

cnf(c_911,plain,
    ( ~ v7_struct_0(sK1)
    | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
    | v2_struct_0(k1_tex_2(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_909,c_26,c_25])).

cnf(c_912,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
    | v2_struct_0(k1_tex_2(sK1,sK2))
    | ~ v7_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_911])).

cnf(c_913,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) = iProver_top
    | m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top
    | v2_struct_0(k1_tex_2(sK1,sK2)) = iProver_top
    | v7_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_912])).

cnf(c_2131,plain,
    ( ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) ),
    inference(prop_impl,[status(thm)],[c_22])).

cnf(c_2132,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
    inference(renaming,[status(thm)],[c_2131])).

cnf(c_3075,plain,
    ( ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1)
    | ~ m1_subset_1(X0,X1)
    | v1_zfmisc_1(X1)
    | v1_xboole_0(X1)
    | k6_domain_1(u1_struct_0(sK1),sK2) != k6_domain_1(X1,X0)
    | u1_struct_0(sK1) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_2132])).

cnf(c_3076,plain,
    ( ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | v1_zfmisc_1(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1))
    | k6_domain_1(u1_struct_0(sK1),sK2) != k6_domain_1(u1_struct_0(sK1),X0) ),
    inference(unflattening,[status(thm)],[c_3075])).

cnf(c_1914,plain,
    ( v1_subset_1(k6_domain_1(X0,X1),X0)
    | v1_zfmisc_1(X0)
    | v1_xboole_0(X0)
    | u1_struct_0(sK1) != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_24])).

cnf(c_1915,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | v1_zfmisc_1(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_1914])).

cnf(c_3078,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | v1_zfmisc_1(u1_struct_0(sK1))
    | ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3076,c_22,c_1915])).

cnf(c_3079,plain,
    ( ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1)
    | v1_zfmisc_1(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_3078])).

cnf(c_3080,plain,
    ( v1_tex_2(k1_tex_2(sK1,sK2),sK1) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK1)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3079])).

cnf(c_3888,plain,
    ( m1_pre_topc(k1_tex_2(X0_46,X0_47),X0_46) = iProver_top
    | m1_subset_1(X0_47,u1_struct_0(X0_46)) != iProver_top
    | v2_struct_0(X0_46) = iProver_top
    | l1_pre_topc(X0_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3824])).

cnf(c_3890,plain,
    ( m1_pre_topc(k1_tex_2(sK1,sK2),sK1) = iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3888])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k1_tex_2(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_3823,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(X0_46))
    | v2_struct_0(X0_46)
    | ~ v2_struct_0(k1_tex_2(X0_46,X0_47))
    | ~ l1_pre_topc(X0_46) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_3891,plain,
    ( m1_subset_1(X0_47,u1_struct_0(X0_46)) != iProver_top
    | v2_struct_0(X0_46) = iProver_top
    | v2_struct_0(k1_tex_2(X0_46,X0_47)) != iProver_top
    | l1_pre_topc(X0_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3823])).

cnf(c_3893,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | v2_struct_0(k1_tex_2(sK1,sK2)) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3891])).

cnf(c_5590,plain,
    ( v1_tex_2(k1_tex_2(sK1,sK2),sK1) != iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5289,c_27,c_28,c_29,c_75,c_79,c_913,c_3080,c_3890,c_3893,c_3907])).

cnf(c_6663,plain,
    ( sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(k1_tex_2(sK1,sK2))
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5445,c_5590])).

cnf(c_7057,plain,
    ( sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(k1_tex_2(sK1,sK2))
    | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6663,c_27,c_28,c_29])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_3835,plain,
    ( ~ v1_xboole_0(X0_47)
    | ~ v1_xboole_0(X1_47)
    | X1_47 = X0_47 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_4509,plain,
    ( X0_47 = X1_47
    | v1_xboole_0(X1_47) != iProver_top
    | v1_xboole_0(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3835])).

cnf(c_7065,plain,
    ( sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(k1_tex_2(sK1,sK2))
    | u1_struct_0(sK1) = X0_47
    | v1_xboole_0(X0_47) != iProver_top ),
    inference(superposition,[status(thm)],[c_7057,c_4509])).

cnf(c_74,plain,
    ( v7_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | ~ v1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_78,plain,
    ( ~ l1_pre_topc(sK1)
    | l1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_87,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3847,plain,
    ( u1_struct_0(X0_46) = u1_struct_0(X1_46)
    | X0_46 != X1_46 ),
    theory(equality)).

cnf(c_3860,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_3847])).

cnf(c_3838,plain,
    ( X0_46 = X0_46 ),
    theory(equality)).

cnf(c_3868,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_3838])).

cnf(c_3889,plain,
    ( m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_3824])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v7_struct_0(k1_tex_2(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_3822,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(X0_46))
    | v2_struct_0(X0_46)
    | v7_struct_0(k1_tex_2(X0_46,X0_47))
    | ~ l1_pre_topc(X0_46) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_3895,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | v7_struct_0(k1_tex_2(sK1,sK2))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_3822])).

cnf(c_7,plain,
    ( ~ v7_struct_0(X0)
    | ~ l1_struct_0(X0)
    | v1_zfmisc_1(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_363,plain,
    ( ~ v7_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | v1_zfmisc_1(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_4,c_7])).

cnf(c_3814,plain,
    ( ~ v7_struct_0(X0_46)
    | ~ l1_pre_topc(X0_46)
    | v1_zfmisc_1(u1_struct_0(X0_46)) ),
    inference(subtyping,[status(esa)],[c_363])).

cnf(c_4739,plain,
    ( ~ v7_struct_0(k1_tex_2(X0_46,X0_47))
    | ~ l1_pre_topc(k1_tex_2(X0_46,X0_47))
    | v1_zfmisc_1(u1_struct_0(k1_tex_2(X0_46,X0_47))) ),
    inference(instantiation,[status(thm)],[c_3814])).

cnf(c_4741,plain,
    ( ~ v7_struct_0(k1_tex_2(sK1,sK2))
    | ~ l1_pre_topc(k1_tex_2(sK1,sK2))
    | v1_zfmisc_1(u1_struct_0(k1_tex_2(sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_4739])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_3832,plain,
    ( ~ m1_pre_topc(X0_46,X1_46)
    | ~ l1_pre_topc(X1_46)
    | l1_pre_topc(X0_46) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_4862,plain,
    ( ~ m1_pre_topc(k1_tex_2(X0_46,X0_47),X1_46)
    | ~ l1_pre_topc(X1_46)
    | l1_pre_topc(k1_tex_2(X0_46,X0_47)) ),
    inference(instantiation,[status(thm)],[c_3832])).

cnf(c_4864,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
    | l1_pre_topc(k1_tex_2(sK1,sK2))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_4862])).

cnf(c_4963,plain,
    ( ~ v1_xboole_0(X0_47)
    | ~ v1_xboole_0(u1_struct_0(sK1))
    | u1_struct_0(sK1) = X0_47 ),
    inference(instantiation,[status(thm)],[c_3835])).

cnf(c_4969,plain,
    ( u1_struct_0(sK1) = X0_47
    | v1_xboole_0(X0_47) != iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4963])).

cnf(c_3841,plain,
    ( ~ v1_xboole_0(X0_47)
    | v1_xboole_0(X1_47)
    | X1_47 != X0_47 ),
    theory(equality)).

cnf(c_4804,plain,
    ( v1_xboole_0(X0_47)
    | ~ v1_xboole_0(k1_xboole_0)
    | X0_47 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3841])).

cnf(c_5316,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ v1_xboole_0(k1_xboole_0)
    | u1_struct_0(sK1) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4804])).

cnf(c_5322,plain,
    ( u1_struct_0(sK1) != k1_xboole_0
    | v1_xboole_0(u1_struct_0(sK1)) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5316])).

cnf(c_3840,plain,
    ( X0_47 != X1_47
    | X2_47 != X1_47
    | X2_47 = X0_47 ),
    theory(equality)).

cnf(c_4974,plain,
    ( X0_47 != X1_47
    | u1_struct_0(sK1) != X1_47
    | u1_struct_0(sK1) = X0_47 ),
    inference(instantiation,[status(thm)],[c_3840])).

cnf(c_5047,plain,
    ( X0_47 != u1_struct_0(sK1)
    | u1_struct_0(sK1) = X0_47
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_4974])).

cnf(c_5229,plain,
    ( u1_struct_0(X0_46) != u1_struct_0(sK1)
    | u1_struct_0(sK1) = u1_struct_0(X0_46)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_5047])).

cnf(c_5536,plain,
    ( u1_struct_0(k1_tex_2(X0_46,X0_47)) != u1_struct_0(sK1)
    | u1_struct_0(sK1) = u1_struct_0(k1_tex_2(X0_46,X0_47))
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_5229])).

cnf(c_5537,plain,
    ( u1_struct_0(k1_tex_2(sK1,sK2)) != u1_struct_0(sK1)
    | u1_struct_0(sK1) = u1_struct_0(k1_tex_2(sK1,sK2))
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_5536])).

cnf(c_3819,negated_conjecture,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_4525,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) = iProver_top
    | v1_tex_2(k1_tex_2(sK1,sK2),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3819])).

cnf(c_21,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v7_struct_0(X0)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_343,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v7_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_4,c_21])).

cnf(c_3815,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0_46),X0_47),u1_struct_0(X0_46))
    | ~ m1_subset_1(X0_47,u1_struct_0(X0_46))
    | v2_struct_0(X0_46)
    | ~ v7_struct_0(X0_46)
    | ~ l1_pre_topc(X0_46) ),
    inference(subtyping,[status(esa)],[c_343])).

cnf(c_4529,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(X0_46),X0_47),u1_struct_0(X0_46)) != iProver_top
    | m1_subset_1(X0_47,u1_struct_0(X0_46)) != iProver_top
    | v2_struct_0(X0_46) = iProver_top
    | v7_struct_0(X0_46) != iProver_top
    | l1_pre_topc(X0_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3815])).

cnf(c_5746,plain,
    ( v1_tex_2(k1_tex_2(sK1,sK2),sK1) = iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v7_struct_0(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4525,c_4529])).

cnf(c_3905,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(X0_46),X0_47),u1_struct_0(X0_46)) != iProver_top
    | m1_subset_1(X0_47,u1_struct_0(X0_46)) != iProver_top
    | v2_struct_0(X0_46) = iProver_top
    | v7_struct_0(X0_46) != iProver_top
    | l1_pre_topc(X0_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3815])).

cnf(c_3907,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v7_struct_0(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3905])).

cnf(c_5837,plain,
    ( v7_struct_0(sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5746,c_27,c_28,c_29,c_913,c_3890,c_3893,c_3907])).

cnf(c_5839,plain,
    ( ~ v7_struct_0(sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5837])).

cnf(c_3844,plain,
    ( ~ v1_zfmisc_1(X0_47)
    | v1_zfmisc_1(X1_47)
    | X1_47 != X0_47 ),
    theory(equality)).

cnf(c_5118,plain,
    ( v1_zfmisc_1(X0_47)
    | ~ v1_zfmisc_1(u1_struct_0(k1_tex_2(X0_46,X1_47)))
    | X0_47 != u1_struct_0(k1_tex_2(X0_46,X1_47)) ),
    inference(instantiation,[status(thm)],[c_3844])).

cnf(c_5938,plain,
    ( v1_zfmisc_1(u1_struct_0(X0_46))
    | ~ v1_zfmisc_1(u1_struct_0(k1_tex_2(X1_46,X0_47)))
    | u1_struct_0(X0_46) != u1_struct_0(k1_tex_2(X1_46,X0_47)) ),
    inference(instantiation,[status(thm)],[c_5118])).

cnf(c_5941,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(k1_tex_2(sK1,sK2)))
    | v1_zfmisc_1(u1_struct_0(sK1))
    | u1_struct_0(sK1) != u1_struct_0(k1_tex_2(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_5938])).

cnf(c_12,plain,
    ( v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_3828,plain,
    ( v1_tex_2(X0_46,X1_46)
    | ~ m1_pre_topc(X0_46,X1_46)
    | m1_subset_1(sK0(X1_46,X0_46),k1_zfmisc_1(u1_struct_0(X1_46)))
    | ~ l1_pre_topc(X1_46) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_4516,plain,
    ( v1_tex_2(X0_46,X1_46) = iProver_top
    | m1_pre_topc(X0_46,X1_46) != iProver_top
    | m1_subset_1(sK0(X1_46,X0_46),k1_zfmisc_1(u1_struct_0(X1_46))) = iProver_top
    | l1_pre_topc(X1_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3828])).

cnf(c_14,plain,
    ( v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X1 = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_3826,plain,
    ( v1_subset_1(X0_47,X1_47)
    | ~ m1_subset_1(X0_47,k1_zfmisc_1(X1_47))
    | X1_47 = X0_47 ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_4518,plain,
    ( X0_47 = X1_47
    | v1_subset_1(X1_47,X0_47) = iProver_top
    | m1_subset_1(X1_47,k1_zfmisc_1(X0_47)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3826])).

cnf(c_5848,plain,
    ( sK0(X0_46,X1_46) = u1_struct_0(X0_46)
    | v1_subset_1(sK0(X0_46,X1_46),u1_struct_0(X0_46)) = iProver_top
    | v1_tex_2(X1_46,X0_46) = iProver_top
    | m1_pre_topc(X1_46,X0_46) != iProver_top
    | l1_pre_topc(X0_46) != iProver_top ),
    inference(superposition,[status(thm)],[c_4516,c_4518])).

cnf(c_10,plain,
    ( ~ v1_subset_1(sK0(X0,X1),u1_struct_0(X0))
    | v1_tex_2(X1,X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_3830,plain,
    ( ~ v1_subset_1(sK0(X0_46,X1_46),u1_struct_0(X0_46))
    | v1_tex_2(X1_46,X0_46)
    | ~ m1_pre_topc(X1_46,X0_46)
    | ~ l1_pre_topc(X0_46) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_3878,plain,
    ( v1_subset_1(sK0(X0_46,X1_46),u1_struct_0(X0_46)) != iProver_top
    | v1_tex_2(X1_46,X0_46) = iProver_top
    | m1_pre_topc(X1_46,X0_46) != iProver_top
    | l1_pre_topc(X0_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3830])).

cnf(c_6163,plain,
    ( sK0(X0_46,X1_46) = u1_struct_0(X0_46)
    | v1_tex_2(X1_46,X0_46) = iProver_top
    | m1_pre_topc(X1_46,X0_46) != iProver_top
    | l1_pre_topc(X0_46) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5848,c_3878])).

cnf(c_6171,plain,
    ( sK0(X0_46,k1_tex_2(X0_46,X0_47)) = u1_struct_0(X0_46)
    | v1_tex_2(k1_tex_2(X0_46,X0_47),X0_46) = iProver_top
    | m1_subset_1(X0_47,u1_struct_0(X0_46)) != iProver_top
    | v2_struct_0(X0_46) = iProver_top
    | l1_pre_topc(X0_46) != iProver_top ),
    inference(superposition,[status(thm)],[c_4520,c_6163])).

cnf(c_6289,plain,
    ( sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(sK1)
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6171,c_5590])).

cnf(c_6318,plain,
    ( sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(sK1)
    | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6289,c_27,c_28,c_29])).

cnf(c_4917,plain,
    ( k1_xboole_0 = X0_47
    | v1_xboole_0(X0_47) != iProver_top ),
    inference(superposition,[status(thm)],[c_4508,c_4509])).

cnf(c_6324,plain,
    ( sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(sK1)
    | u1_struct_0(sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6318,c_4917])).

cnf(c_7064,plain,
    ( sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(k1_tex_2(sK1,sK2))
    | u1_struct_0(sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7057,c_4917])).

cnf(c_7081,plain,
    ( u1_struct_0(k1_tex_2(sK1,sK2)) = u1_struct_0(sK1)
    | u1_struct_0(sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6324,c_7064])).

cnf(c_7239,plain,
    ( u1_struct_0(sK1) = X0_47
    | v1_xboole_0(X0_47) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7065,c_26,c_25,c_24,c_74,c_78,c_87,c_3860,c_3868,c_3889,c_3895,c_4741,c_4864,c_4969,c_5322,c_5537,c_5839,c_5941,c_7081])).

cnf(c_7247,plain,
    ( u1_struct_0(sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4508,c_7239])).

cnf(c_377,plain,
    ( v7_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_zfmisc_1(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_4,c_6])).

cnf(c_3813,plain,
    ( v7_struct_0(X0_46)
    | ~ l1_pre_topc(X0_46)
    | ~ v1_zfmisc_1(u1_struct_0(X0_46)) ),
    inference(subtyping,[status(esa)],[c_377])).

cnf(c_4531,plain,
    ( v7_struct_0(X0_46) = iProver_top
    | l1_pre_topc(X0_46) != iProver_top
    | v1_zfmisc_1(u1_struct_0(X0_46)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3813])).

cnf(c_7286,plain,
    ( v7_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_zfmisc_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7247,c_4531])).

cnf(c_3818,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_4526,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3818])).

cnf(c_4522,plain,
    ( m1_subset_1(X0_47,u1_struct_0(X0_46)) != iProver_top
    | v2_struct_0(X0_46) = iProver_top
    | v7_struct_0(k1_tex_2(X0_46,X0_47)) = iProver_top
    | l1_pre_topc(X0_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3822])).

cnf(c_5368,plain,
    ( v2_struct_0(sK1) = iProver_top
    | v7_struct_0(k1_tex_2(sK1,sK2)) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4526,c_4522])).

cnf(c_3894,plain,
    ( m1_subset_1(X0_47,u1_struct_0(X0_46)) != iProver_top
    | v2_struct_0(X0_46) = iProver_top
    | v7_struct_0(k1_tex_2(X0_46,X0_47)) = iProver_top
    | l1_pre_topc(X0_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3822])).

cnf(c_3896,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v7_struct_0(k1_tex_2(sK1,sK2)) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3894])).

cnf(c_5471,plain,
    ( v7_struct_0(k1_tex_2(sK1,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5368,c_27,c_28,c_29,c_3896])).

cnf(c_4530,plain,
    ( v7_struct_0(X0_46) != iProver_top
    | l1_pre_topc(X0_46) != iProver_top
    | v1_zfmisc_1(u1_struct_0(X0_46)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3814])).

cnf(c_2,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_3834,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0_47)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_4510,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0_47)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3834])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_zfmisc_1(X1)
    | v1_zfmisc_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_3833,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(X1_47))
    | ~ v1_zfmisc_1(X1_47)
    | v1_zfmisc_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_4511,plain,
    ( m1_subset_1(X0_47,k1_zfmisc_1(X1_47)) != iProver_top
    | v1_zfmisc_1(X1_47) != iProver_top
    | v1_zfmisc_1(X0_47) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3833])).

cnf(c_4825,plain,
    ( v1_zfmisc_1(X0_47) != iProver_top
    | v1_zfmisc_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4510,c_4511])).

cnf(c_5143,plain,
    ( v7_struct_0(X0_46) != iProver_top
    | l1_pre_topc(X0_46) != iProver_top
    | v1_zfmisc_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4530,c_4825])).

cnf(c_5476,plain,
    ( l1_pre_topc(k1_tex_2(sK1,sK2)) != iProver_top
    | v1_zfmisc_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5471,c_5143])).

cnf(c_4863,plain,
    ( m1_pre_topc(k1_tex_2(X0_46,X0_47),X1_46) != iProver_top
    | l1_pre_topc(X1_46) != iProver_top
    | l1_pre_topc(k1_tex_2(X0_46,X0_47)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4862])).

cnf(c_4865,plain,
    ( m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top
    | l1_pre_topc(k1_tex_2(sK1,sK2)) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4863])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7286,c_5837,c_5476,c_4865,c_3890,c_29,c_28,c_27])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 19:43:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.06/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/0.99  
% 2.06/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.06/0.99  
% 2.06/0.99  ------  iProver source info
% 2.06/0.99  
% 2.06/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.06/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.06/0.99  git: non_committed_changes: false
% 2.06/0.99  git: last_make_outside_of_git: false
% 2.06/0.99  
% 2.06/0.99  ------ 
% 2.06/0.99  
% 2.06/0.99  ------ Input Options
% 2.06/0.99  
% 2.06/0.99  --out_options                           all
% 2.06/0.99  --tptp_safe_out                         true
% 2.06/0.99  --problem_path                          ""
% 2.06/0.99  --include_path                          ""
% 2.06/0.99  --clausifier                            res/vclausify_rel
% 2.06/0.99  --clausifier_options                    --mode clausify
% 2.06/0.99  --stdin                                 false
% 2.06/0.99  --stats_out                             all
% 2.06/0.99  
% 2.06/0.99  ------ General Options
% 2.06/0.99  
% 2.06/0.99  --fof                                   false
% 2.06/0.99  --time_out_real                         305.
% 2.06/0.99  --time_out_virtual                      -1.
% 2.06/0.99  --symbol_type_check                     false
% 2.06/0.99  --clausify_out                          false
% 2.06/0.99  --sig_cnt_out                           false
% 2.06/0.99  --trig_cnt_out                          false
% 2.06/0.99  --trig_cnt_out_tolerance                1.
% 2.06/0.99  --trig_cnt_out_sk_spl                   false
% 2.06/0.99  --abstr_cl_out                          false
% 2.06/0.99  
% 2.06/0.99  ------ Global Options
% 2.06/0.99  
% 2.06/0.99  --schedule                              default
% 2.06/0.99  --add_important_lit                     false
% 2.06/0.99  --prop_solver_per_cl                    1000
% 2.06/0.99  --min_unsat_core                        false
% 2.06/0.99  --soft_assumptions                      false
% 2.06/0.99  --soft_lemma_size                       3
% 2.06/0.99  --prop_impl_unit_size                   0
% 2.06/0.99  --prop_impl_unit                        []
% 2.06/0.99  --share_sel_clauses                     true
% 2.06/0.99  --reset_solvers                         false
% 2.06/0.99  --bc_imp_inh                            [conj_cone]
% 2.06/0.99  --conj_cone_tolerance                   3.
% 2.06/0.99  --extra_neg_conj                        none
% 2.06/0.99  --large_theory_mode                     true
% 2.06/0.99  --prolific_symb_bound                   200
% 2.06/0.99  --lt_threshold                          2000
% 2.06/0.99  --clause_weak_htbl                      true
% 2.06/0.99  --gc_record_bc_elim                     false
% 2.06/0.99  
% 2.06/0.99  ------ Preprocessing Options
% 2.06/0.99  
% 2.06/0.99  --preprocessing_flag                    true
% 2.06/0.99  --time_out_prep_mult                    0.1
% 2.06/0.99  --splitting_mode                        input
% 2.06/0.99  --splitting_grd                         true
% 2.06/0.99  --splitting_cvd                         false
% 2.06/0.99  --splitting_cvd_svl                     false
% 2.06/0.99  --splitting_nvd                         32
% 2.06/0.99  --sub_typing                            true
% 2.06/0.99  --prep_gs_sim                           true
% 2.06/0.99  --prep_unflatten                        true
% 2.06/0.99  --prep_res_sim                          true
% 2.06/0.99  --prep_upred                            true
% 2.06/0.99  --prep_sem_filter                       exhaustive
% 2.06/0.99  --prep_sem_filter_out                   false
% 2.06/0.99  --pred_elim                             true
% 2.06/0.99  --res_sim_input                         true
% 2.06/0.99  --eq_ax_congr_red                       true
% 2.06/0.99  --pure_diseq_elim                       true
% 2.06/0.99  --brand_transform                       false
% 2.06/0.99  --non_eq_to_eq                          false
% 2.06/0.99  --prep_def_merge                        true
% 2.06/0.99  --prep_def_merge_prop_impl              false
% 2.06/0.99  --prep_def_merge_mbd                    true
% 2.06/0.99  --prep_def_merge_tr_red                 false
% 2.06/0.99  --prep_def_merge_tr_cl                  false
% 2.06/0.99  --smt_preprocessing                     true
% 2.06/0.99  --smt_ac_axioms                         fast
% 2.06/0.99  --preprocessed_out                      false
% 2.06/0.99  --preprocessed_stats                    false
% 2.06/0.99  
% 2.06/0.99  ------ Abstraction refinement Options
% 2.06/0.99  
% 2.06/0.99  --abstr_ref                             []
% 2.06/0.99  --abstr_ref_prep                        false
% 2.06/0.99  --abstr_ref_until_sat                   false
% 2.06/0.99  --abstr_ref_sig_restrict                funpre
% 2.06/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.06/0.99  --abstr_ref_under                       []
% 2.06/0.99  
% 2.06/0.99  ------ SAT Options
% 2.06/0.99  
% 2.06/0.99  --sat_mode                              false
% 2.06/0.99  --sat_fm_restart_options                ""
% 2.06/0.99  --sat_gr_def                            false
% 2.06/0.99  --sat_epr_types                         true
% 2.06/0.99  --sat_non_cyclic_types                  false
% 2.06/0.99  --sat_finite_models                     false
% 2.06/0.99  --sat_fm_lemmas                         false
% 2.06/0.99  --sat_fm_prep                           false
% 2.06/0.99  --sat_fm_uc_incr                        true
% 2.06/0.99  --sat_out_model                         small
% 2.06/0.99  --sat_out_clauses                       false
% 2.06/0.99  
% 2.06/0.99  ------ QBF Options
% 2.06/0.99  
% 2.06/0.99  --qbf_mode                              false
% 2.06/0.99  --qbf_elim_univ                         false
% 2.06/0.99  --qbf_dom_inst                          none
% 2.06/0.99  --qbf_dom_pre_inst                      false
% 2.06/0.99  --qbf_sk_in                             false
% 2.06/0.99  --qbf_pred_elim                         true
% 2.06/0.99  --qbf_split                             512
% 2.06/0.99  
% 2.06/0.99  ------ BMC1 Options
% 2.06/0.99  
% 2.06/0.99  --bmc1_incremental                      false
% 2.06/0.99  --bmc1_axioms                           reachable_all
% 2.06/0.99  --bmc1_min_bound                        0
% 2.06/0.99  --bmc1_max_bound                        -1
% 2.06/0.99  --bmc1_max_bound_default                -1
% 2.06/0.99  --bmc1_symbol_reachability              true
% 2.06/0.99  --bmc1_property_lemmas                  false
% 2.06/0.99  --bmc1_k_induction                      false
% 2.06/0.99  --bmc1_non_equiv_states                 false
% 2.06/0.99  --bmc1_deadlock                         false
% 2.06/0.99  --bmc1_ucm                              false
% 2.06/0.99  --bmc1_add_unsat_core                   none
% 2.06/0.99  --bmc1_unsat_core_children              false
% 2.06/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.06/0.99  --bmc1_out_stat                         full
% 2.06/0.99  --bmc1_ground_init                      false
% 2.06/0.99  --bmc1_pre_inst_next_state              false
% 2.06/0.99  --bmc1_pre_inst_state                   false
% 2.06/0.99  --bmc1_pre_inst_reach_state             false
% 2.06/0.99  --bmc1_out_unsat_core                   false
% 2.06/0.99  --bmc1_aig_witness_out                  false
% 2.06/0.99  --bmc1_verbose                          false
% 2.06/0.99  --bmc1_dump_clauses_tptp                false
% 2.06/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.06/0.99  --bmc1_dump_file                        -
% 2.06/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.06/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.06/0.99  --bmc1_ucm_extend_mode                  1
% 2.06/0.99  --bmc1_ucm_init_mode                    2
% 2.06/0.99  --bmc1_ucm_cone_mode                    none
% 2.06/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.06/0.99  --bmc1_ucm_relax_model                  4
% 2.06/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.06/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.06/0.99  --bmc1_ucm_layered_model                none
% 2.06/0.99  --bmc1_ucm_max_lemma_size               10
% 2.06/0.99  
% 2.06/0.99  ------ AIG Options
% 2.06/0.99  
% 2.06/0.99  --aig_mode                              false
% 2.06/0.99  
% 2.06/0.99  ------ Instantiation Options
% 2.06/0.99  
% 2.06/0.99  --instantiation_flag                    true
% 2.06/0.99  --inst_sos_flag                         false
% 2.06/0.99  --inst_sos_phase                        true
% 2.06/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.06/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.06/0.99  --inst_lit_sel_side                     num_symb
% 2.06/0.99  --inst_solver_per_active                1400
% 2.06/0.99  --inst_solver_calls_frac                1.
% 2.06/0.99  --inst_passive_queue_type               priority_queues
% 2.06/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.06/0.99  --inst_passive_queues_freq              [25;2]
% 2.06/0.99  --inst_dismatching                      true
% 2.06/0.99  --inst_eager_unprocessed_to_passive     true
% 2.06/0.99  --inst_prop_sim_given                   true
% 2.06/0.99  --inst_prop_sim_new                     false
% 2.06/0.99  --inst_subs_new                         false
% 2.06/0.99  --inst_eq_res_simp                      false
% 2.06/0.99  --inst_subs_given                       false
% 2.06/0.99  --inst_orphan_elimination               true
% 2.06/0.99  --inst_learning_loop_flag               true
% 2.06/0.99  --inst_learning_start                   3000
% 2.06/0.99  --inst_learning_factor                  2
% 2.06/0.99  --inst_start_prop_sim_after_learn       3
% 2.06/0.99  --inst_sel_renew                        solver
% 2.06/0.99  --inst_lit_activity_flag                true
% 2.06/0.99  --inst_restr_to_given                   false
% 2.06/0.99  --inst_activity_threshold               500
% 2.06/0.99  --inst_out_proof                        true
% 2.06/0.99  
% 2.06/0.99  ------ Resolution Options
% 2.06/0.99  
% 2.06/0.99  --resolution_flag                       true
% 2.06/0.99  --res_lit_sel                           adaptive
% 2.06/0.99  --res_lit_sel_side                      none
% 2.06/0.99  --res_ordering                          kbo
% 2.06/0.99  --res_to_prop_solver                    active
% 2.06/0.99  --res_prop_simpl_new                    false
% 2.06/0.99  --res_prop_simpl_given                  true
% 2.06/0.99  --res_passive_queue_type                priority_queues
% 2.06/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.06/0.99  --res_passive_queues_freq               [15;5]
% 2.06/0.99  --res_forward_subs                      full
% 2.06/0.99  --res_backward_subs                     full
% 2.06/0.99  --res_forward_subs_resolution           true
% 2.06/0.99  --res_backward_subs_resolution          true
% 2.06/0.99  --res_orphan_elimination                true
% 2.06/0.99  --res_time_limit                        2.
% 2.06/0.99  --res_out_proof                         true
% 2.06/0.99  
% 2.06/0.99  ------ Superposition Options
% 2.06/0.99  
% 2.06/0.99  --superposition_flag                    true
% 2.06/0.99  --sup_passive_queue_type                priority_queues
% 2.06/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.06/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.06/0.99  --demod_completeness_check              fast
% 2.06/0.99  --demod_use_ground                      true
% 2.06/0.99  --sup_to_prop_solver                    passive
% 2.06/0.99  --sup_prop_simpl_new                    true
% 2.06/0.99  --sup_prop_simpl_given                  true
% 2.06/0.99  --sup_fun_splitting                     false
% 2.06/0.99  --sup_smt_interval                      50000
% 2.06/0.99  
% 2.06/0.99  ------ Superposition Simplification Setup
% 2.06/0.99  
% 2.06/0.99  --sup_indices_passive                   []
% 2.06/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.06/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.06/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.06/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.06/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.06/0.99  --sup_full_bw                           [BwDemod]
% 2.06/0.99  --sup_immed_triv                        [TrivRules]
% 2.06/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.06/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.06/0.99  --sup_immed_bw_main                     []
% 2.06/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.06/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.06/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.06/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.06/0.99  
% 2.06/0.99  ------ Combination Options
% 2.06/0.99  
% 2.06/0.99  --comb_res_mult                         3
% 2.06/0.99  --comb_sup_mult                         2
% 2.06/0.99  --comb_inst_mult                        10
% 2.06/0.99  
% 2.06/0.99  ------ Debug Options
% 2.06/0.99  
% 2.06/0.99  --dbg_backtrace                         false
% 2.06/0.99  --dbg_dump_prop_clauses                 false
% 2.06/0.99  --dbg_dump_prop_clauses_file            -
% 2.06/0.99  --dbg_out_stat                          false
% 2.06/0.99  ------ Parsing...
% 2.06/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.06/0.99  
% 2.06/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.06/0.99  
% 2.06/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.06/0.99  
% 2.06/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.06/0.99  ------ Proving...
% 2.06/0.99  ------ Problem Properties 
% 2.06/0.99  
% 2.06/0.99  
% 2.06/0.99  clauses                                 24
% 2.06/0.99  conjectures                             5
% 2.06/0.99  EPR                                     6
% 2.06/0.99  Horn                                    16
% 2.06/0.99  unary                                   5
% 2.06/0.99  binary                                  3
% 2.06/0.99  lits                                    73
% 2.06/0.99  lits eq                                 3
% 2.06/0.99  fd_pure                                 0
% 2.06/0.99  fd_pseudo                               0
% 2.06/0.99  fd_cond                                 0
% 2.06/0.99  fd_pseudo_cond                          2
% 2.06/0.99  AC symbols                              0
% 2.06/0.99  
% 2.06/0.99  ------ Schedule dynamic 5 is on 
% 2.06/0.99  
% 2.06/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.06/0.99  
% 2.06/0.99  
% 2.06/0.99  ------ 
% 2.06/0.99  Current options:
% 2.06/0.99  ------ 
% 2.06/0.99  
% 2.06/0.99  ------ Input Options
% 2.06/0.99  
% 2.06/0.99  --out_options                           all
% 2.06/0.99  --tptp_safe_out                         true
% 2.06/0.99  --problem_path                          ""
% 2.06/0.99  --include_path                          ""
% 2.06/0.99  --clausifier                            res/vclausify_rel
% 2.06/0.99  --clausifier_options                    --mode clausify
% 2.06/0.99  --stdin                                 false
% 2.06/0.99  --stats_out                             all
% 2.06/0.99  
% 2.06/0.99  ------ General Options
% 2.06/0.99  
% 2.06/0.99  --fof                                   false
% 2.06/0.99  --time_out_real                         305.
% 2.06/0.99  --time_out_virtual                      -1.
% 2.06/0.99  --symbol_type_check                     false
% 2.06/0.99  --clausify_out                          false
% 2.06/0.99  --sig_cnt_out                           false
% 2.06/0.99  --trig_cnt_out                          false
% 2.06/0.99  --trig_cnt_out_tolerance                1.
% 2.06/0.99  --trig_cnt_out_sk_spl                   false
% 2.06/0.99  --abstr_cl_out                          false
% 2.06/0.99  
% 2.06/0.99  ------ Global Options
% 2.06/0.99  
% 2.06/0.99  --schedule                              default
% 2.06/0.99  --add_important_lit                     false
% 2.06/0.99  --prop_solver_per_cl                    1000
% 2.06/0.99  --min_unsat_core                        false
% 2.06/0.99  --soft_assumptions                      false
% 2.06/0.99  --soft_lemma_size                       3
% 2.06/0.99  --prop_impl_unit_size                   0
% 2.06/0.99  --prop_impl_unit                        []
% 2.06/0.99  --share_sel_clauses                     true
% 2.06/0.99  --reset_solvers                         false
% 2.06/0.99  --bc_imp_inh                            [conj_cone]
% 2.06/0.99  --conj_cone_tolerance                   3.
% 2.06/0.99  --extra_neg_conj                        none
% 2.06/0.99  --large_theory_mode                     true
% 2.06/0.99  --prolific_symb_bound                   200
% 2.06/0.99  --lt_threshold                          2000
% 2.06/0.99  --clause_weak_htbl                      true
% 2.06/0.99  --gc_record_bc_elim                     false
% 2.06/0.99  
% 2.06/0.99  ------ Preprocessing Options
% 2.06/0.99  
% 2.06/0.99  --preprocessing_flag                    true
% 2.06/0.99  --time_out_prep_mult                    0.1
% 2.06/0.99  --splitting_mode                        input
% 2.06/0.99  --splitting_grd                         true
% 2.06/0.99  --splitting_cvd                         false
% 2.06/0.99  --splitting_cvd_svl                     false
% 2.06/0.99  --splitting_nvd                         32
% 2.06/0.99  --sub_typing                            true
% 2.06/0.99  --prep_gs_sim                           true
% 2.06/0.99  --prep_unflatten                        true
% 2.06/0.99  --prep_res_sim                          true
% 2.06/0.99  --prep_upred                            true
% 2.06/0.99  --prep_sem_filter                       exhaustive
% 2.06/0.99  --prep_sem_filter_out                   false
% 2.06/0.99  --pred_elim                             true
% 2.06/0.99  --res_sim_input                         true
% 2.06/0.99  --eq_ax_congr_red                       true
% 2.06/0.99  --pure_diseq_elim                       true
% 2.06/0.99  --brand_transform                       false
% 2.06/0.99  --non_eq_to_eq                          false
% 2.06/0.99  --prep_def_merge                        true
% 2.06/0.99  --prep_def_merge_prop_impl              false
% 2.06/0.99  --prep_def_merge_mbd                    true
% 2.06/0.99  --prep_def_merge_tr_red                 false
% 2.06/0.99  --prep_def_merge_tr_cl                  false
% 2.06/0.99  --smt_preprocessing                     true
% 2.06/0.99  --smt_ac_axioms                         fast
% 2.06/0.99  --preprocessed_out                      false
% 2.06/0.99  --preprocessed_stats                    false
% 2.06/0.99  
% 2.06/0.99  ------ Abstraction refinement Options
% 2.06/0.99  
% 2.06/0.99  --abstr_ref                             []
% 2.06/0.99  --abstr_ref_prep                        false
% 2.06/0.99  --abstr_ref_until_sat                   false
% 2.06/0.99  --abstr_ref_sig_restrict                funpre
% 2.06/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.06/0.99  --abstr_ref_under                       []
% 2.06/0.99  
% 2.06/0.99  ------ SAT Options
% 2.06/0.99  
% 2.06/0.99  --sat_mode                              false
% 2.06/0.99  --sat_fm_restart_options                ""
% 2.06/0.99  --sat_gr_def                            false
% 2.06/0.99  --sat_epr_types                         true
% 2.06/0.99  --sat_non_cyclic_types                  false
% 2.06/0.99  --sat_finite_models                     false
% 2.06/0.99  --sat_fm_lemmas                         false
% 2.06/0.99  --sat_fm_prep                           false
% 2.06/0.99  --sat_fm_uc_incr                        true
% 2.06/0.99  --sat_out_model                         small
% 2.06/0.99  --sat_out_clauses                       false
% 2.06/0.99  
% 2.06/0.99  ------ QBF Options
% 2.06/0.99  
% 2.06/0.99  --qbf_mode                              false
% 2.06/0.99  --qbf_elim_univ                         false
% 2.06/0.99  --qbf_dom_inst                          none
% 2.06/0.99  --qbf_dom_pre_inst                      false
% 2.06/0.99  --qbf_sk_in                             false
% 2.06/0.99  --qbf_pred_elim                         true
% 2.06/0.99  --qbf_split                             512
% 2.06/0.99  
% 2.06/0.99  ------ BMC1 Options
% 2.06/0.99  
% 2.06/0.99  --bmc1_incremental                      false
% 2.06/0.99  --bmc1_axioms                           reachable_all
% 2.06/0.99  --bmc1_min_bound                        0
% 2.06/0.99  --bmc1_max_bound                        -1
% 2.06/0.99  --bmc1_max_bound_default                -1
% 2.06/0.99  --bmc1_symbol_reachability              true
% 2.06/0.99  --bmc1_property_lemmas                  false
% 2.06/0.99  --bmc1_k_induction                      false
% 2.06/0.99  --bmc1_non_equiv_states                 false
% 2.06/0.99  --bmc1_deadlock                         false
% 2.06/0.99  --bmc1_ucm                              false
% 2.06/0.99  --bmc1_add_unsat_core                   none
% 2.06/0.99  --bmc1_unsat_core_children              false
% 2.06/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.06/0.99  --bmc1_out_stat                         full
% 2.06/0.99  --bmc1_ground_init                      false
% 2.06/0.99  --bmc1_pre_inst_next_state              false
% 2.06/0.99  --bmc1_pre_inst_state                   false
% 2.06/0.99  --bmc1_pre_inst_reach_state             false
% 2.06/0.99  --bmc1_out_unsat_core                   false
% 2.06/0.99  --bmc1_aig_witness_out                  false
% 2.06/0.99  --bmc1_verbose                          false
% 2.06/0.99  --bmc1_dump_clauses_tptp                false
% 2.06/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.06/0.99  --bmc1_dump_file                        -
% 2.06/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.06/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.06/0.99  --bmc1_ucm_extend_mode                  1
% 2.06/0.99  --bmc1_ucm_init_mode                    2
% 2.06/0.99  --bmc1_ucm_cone_mode                    none
% 2.06/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.06/0.99  --bmc1_ucm_relax_model                  4
% 2.06/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.06/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.06/0.99  --bmc1_ucm_layered_model                none
% 2.06/0.99  --bmc1_ucm_max_lemma_size               10
% 2.06/0.99  
% 2.06/0.99  ------ AIG Options
% 2.06/0.99  
% 2.06/0.99  --aig_mode                              false
% 2.06/0.99  
% 2.06/0.99  ------ Instantiation Options
% 2.06/0.99  
% 2.06/0.99  --instantiation_flag                    true
% 2.06/0.99  --inst_sos_flag                         false
% 2.06/0.99  --inst_sos_phase                        true
% 2.06/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.06/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.06/0.99  --inst_lit_sel_side                     none
% 2.06/0.99  --inst_solver_per_active                1400
% 2.06/0.99  --inst_solver_calls_frac                1.
% 2.06/0.99  --inst_passive_queue_type               priority_queues
% 2.06/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.06/0.99  --inst_passive_queues_freq              [25;2]
% 2.06/0.99  --inst_dismatching                      true
% 2.06/0.99  --inst_eager_unprocessed_to_passive     true
% 2.06/0.99  --inst_prop_sim_given                   true
% 2.06/0.99  --inst_prop_sim_new                     false
% 2.06/0.99  --inst_subs_new                         false
% 2.06/0.99  --inst_eq_res_simp                      false
% 2.06/0.99  --inst_subs_given                       false
% 2.06/0.99  --inst_orphan_elimination               true
% 2.06/0.99  --inst_learning_loop_flag               true
% 2.06/0.99  --inst_learning_start                   3000
% 2.06/0.99  --inst_learning_factor                  2
% 2.06/0.99  --inst_start_prop_sim_after_learn       3
% 2.06/0.99  --inst_sel_renew                        solver
% 2.06/0.99  --inst_lit_activity_flag                true
% 2.06/0.99  --inst_restr_to_given                   false
% 2.06/0.99  --inst_activity_threshold               500
% 2.06/0.99  --inst_out_proof                        true
% 2.06/0.99  
% 2.06/0.99  ------ Resolution Options
% 2.06/0.99  
% 2.06/0.99  --resolution_flag                       false
% 2.06/0.99  --res_lit_sel                           adaptive
% 2.06/0.99  --res_lit_sel_side                      none
% 2.06/0.99  --res_ordering                          kbo
% 2.06/0.99  --res_to_prop_solver                    active
% 2.06/0.99  --res_prop_simpl_new                    false
% 2.06/0.99  --res_prop_simpl_given                  true
% 2.06/0.99  --res_passive_queue_type                priority_queues
% 2.06/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.06/0.99  --res_passive_queues_freq               [15;5]
% 2.06/0.99  --res_forward_subs                      full
% 2.06/0.99  --res_backward_subs                     full
% 2.06/0.99  --res_forward_subs_resolution           true
% 2.06/0.99  --res_backward_subs_resolution          true
% 2.06/0.99  --res_orphan_elimination                true
% 2.06/0.99  --res_time_limit                        2.
% 2.06/0.99  --res_out_proof                         true
% 2.06/0.99  
% 2.06/0.99  ------ Superposition Options
% 2.06/0.99  
% 2.06/0.99  --superposition_flag                    true
% 2.06/0.99  --sup_passive_queue_type                priority_queues
% 2.06/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.06/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.06/0.99  --demod_completeness_check              fast
% 2.06/0.99  --demod_use_ground                      true
% 2.06/0.99  --sup_to_prop_solver                    passive
% 2.06/0.99  --sup_prop_simpl_new                    true
% 2.06/0.99  --sup_prop_simpl_given                  true
% 2.06/0.99  --sup_fun_splitting                     false
% 2.06/0.99  --sup_smt_interval                      50000
% 2.06/0.99  
% 2.06/0.99  ------ Superposition Simplification Setup
% 2.06/0.99  
% 2.06/0.99  --sup_indices_passive                   []
% 2.06/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.06/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.06/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.06/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.06/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.06/0.99  --sup_full_bw                           [BwDemod]
% 2.06/0.99  --sup_immed_triv                        [TrivRules]
% 2.06/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.06/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.06/0.99  --sup_immed_bw_main                     []
% 2.06/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.06/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.06/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.06/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.06/0.99  
% 2.06/0.99  ------ Combination Options
% 2.06/0.99  
% 2.06/0.99  --comb_res_mult                         3
% 2.06/0.99  --comb_sup_mult                         2
% 2.06/0.99  --comb_inst_mult                        10
% 2.06/0.99  
% 2.06/0.99  ------ Debug Options
% 2.06/0.99  
% 2.06/0.99  --dbg_backtrace                         false
% 2.06/0.99  --dbg_dump_prop_clauses                 false
% 2.06/0.99  --dbg_dump_prop_clauses_file            -
% 2.06/0.99  --dbg_out_stat                          false
% 2.06/0.99  
% 2.06/0.99  
% 2.06/0.99  
% 2.06/0.99  
% 2.06/0.99  ------ Proving...
% 2.06/0.99  
% 2.06/0.99  
% 2.06/0.99  % SZS status Theorem for theBenchmark.p
% 2.06/0.99  
% 2.06/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.06/0.99  
% 2.06/0.99  fof(f1,axiom,(
% 2.06/0.99    v1_xboole_0(k1_xboole_0)),
% 2.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.06/0.99  
% 2.06/0.99  fof(f55,plain,(
% 2.06/0.99    v1_xboole_0(k1_xboole_0)),
% 2.06/0.99    inference(cnf_transformation,[],[f1])).
% 2.06/0.99  
% 2.06/0.99  fof(f13,axiom,(
% 2.06/0.99    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 2.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.06/0.99  
% 2.06/0.99  fof(f20,plain,(
% 2.06/0.99    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 2.06/0.99    inference(pure_predicate_removal,[],[f13])).
% 2.06/0.99  
% 2.06/0.99  fof(f35,plain,(
% 2.06/0.99    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.06/0.99    inference(ennf_transformation,[],[f20])).
% 2.06/0.99  
% 2.06/0.99  fof(f36,plain,(
% 2.06/0.99    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.06/0.99    inference(flattening,[],[f35])).
% 2.06/0.99  
% 2.06/0.99  fof(f72,plain,(
% 2.06/0.99    ( ! [X0,X1] : (m1_pre_topc(k1_tex_2(X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.06/0.99    inference(cnf_transformation,[],[f36])).
% 2.06/0.99  
% 2.06/0.99  fof(f11,axiom,(
% 2.06/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v1_subset_1(X2,u1_struct_0(X0)))))))),
% 2.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.06/0.99  
% 2.06/0.99  fof(f32,plain,(
% 2.06/0.99    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : ((v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.06/0.99    inference(ennf_transformation,[],[f11])).
% 2.06/0.99  
% 2.06/0.99  fof(f33,plain,(
% 2.06/0.99    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.06/0.99    inference(flattening,[],[f32])).
% 2.06/0.99  
% 2.06/0.99  fof(f45,plain,(
% 2.06/0.99    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.06/0.99    inference(nnf_transformation,[],[f33])).
% 2.06/0.99  
% 2.06/0.99  fof(f46,plain,(
% 2.06/0.99    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.06/0.99    inference(rectify,[],[f45])).
% 2.06/0.99  
% 2.06/0.99  fof(f47,plain,(
% 2.06/0.99    ! [X1,X0] : (? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_subset_1(sK0(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK0(X0,X1) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.06/0.99    introduced(choice_axiom,[])).
% 2.06/0.99  
% 2.06/0.99  fof(f48,plain,(
% 2.06/0.99    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | (~v1_subset_1(sK0(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK0(X0,X1) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.06/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f46,f47])).
% 2.06/0.99  
% 2.06/0.99  fof(f67,plain,(
% 2.06/0.99    ( ! [X0,X1] : (v1_tex_2(X1,X0) | u1_struct_0(X1) = sK0(X0,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.06/0.99    inference(cnf_transformation,[],[f48])).
% 2.06/0.99  
% 2.06/0.99  fof(f15,axiom,(
% 2.06/0.99    ! [X0] : ((~v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,X0) => v1_subset_1(k6_domain_1(X0,X1),X0)))),
% 2.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.06/0.99  
% 2.06/0.99  fof(f39,plain,(
% 2.06/0.99    ! [X0] : (! [X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | (v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 2.06/0.99    inference(ennf_transformation,[],[f15])).
% 2.06/0.99  
% 2.06/0.99  fof(f40,plain,(
% 2.06/0.99    ! [X0] : (! [X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 2.06/0.99    inference(flattening,[],[f39])).
% 2.06/0.99  
% 2.06/0.99  fof(f75,plain,(
% 2.06/0.99    ( ! [X0,X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0) | v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 2.06/0.99    inference(cnf_transformation,[],[f40])).
% 2.06/0.99  
% 2.06/0.99  fof(f17,conjecture,(
% 2.06/0.99    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 2.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.06/0.99  
% 2.06/0.99  fof(f18,negated_conjecture,(
% 2.06/0.99    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 2.06/0.99    inference(negated_conjecture,[],[f17])).
% 2.06/0.99  
% 2.06/0.99  fof(f43,plain,(
% 2.06/0.99    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.06/0.99    inference(ennf_transformation,[],[f18])).
% 2.06/0.99  
% 2.06/0.99  fof(f44,plain,(
% 2.06/0.99    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.06/0.99    inference(flattening,[],[f43])).
% 2.06/0.99  
% 2.06/0.99  fof(f50,plain,(
% 2.06/0.99    ? [X0] : (? [X1] : (((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.06/0.99    inference(nnf_transformation,[],[f44])).
% 2.06/0.99  
% 2.06/0.99  fof(f51,plain,(
% 2.06/0.99    ? [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.06/0.99    inference(flattening,[],[f50])).
% 2.06/0.99  
% 2.06/0.99  fof(f53,plain,(
% 2.06/0.99    ( ! [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) => ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),sK2),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,sK2),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),sK2),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,sK2),X0)) & m1_subset_1(sK2,u1_struct_0(X0)))) )),
% 2.06/0.99    introduced(choice_axiom,[])).
% 2.06/0.99  
% 2.06/0.99  fof(f52,plain,(
% 2.06/0.99    ? [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(sK1),X1),u1_struct_0(sK1)) | ~v1_tex_2(k1_tex_2(sK1,X1),sK1)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK1),X1),u1_struct_0(sK1)) | v1_tex_2(k1_tex_2(sK1,X1),sK1)) & m1_subset_1(X1,u1_struct_0(sK1))) & l1_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 2.06/0.99    introduced(choice_axiom,[])).
% 2.06/0.99  
% 2.06/0.99  fof(f54,plain,(
% 2.06/0.99    ((~v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) | ~v1_tex_2(k1_tex_2(sK1,sK2),sK1)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) | v1_tex_2(k1_tex_2(sK1,sK2),sK1)) & m1_subset_1(sK2,u1_struct_0(sK1))) & l1_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 2.06/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f51,f53,f52])).
% 2.06/0.99  
% 2.06/0.99  fof(f81,plain,(
% 2.06/0.99    ~v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) | ~v1_tex_2(k1_tex_2(sK1,sK2),sK1)),
% 2.06/0.99    inference(cnf_transformation,[],[f54])).
% 2.06/0.99  
% 2.06/0.99  fof(f77,plain,(
% 2.06/0.99    ~v2_struct_0(sK1)),
% 2.06/0.99    inference(cnf_transformation,[],[f54])).
% 2.06/0.99  
% 2.06/0.99  fof(f78,plain,(
% 2.06/0.99    l1_pre_topc(sK1)),
% 2.06/0.99    inference(cnf_transformation,[],[f54])).
% 2.06/0.99  
% 2.06/0.99  fof(f79,plain,(
% 2.06/0.99    m1_subset_1(sK2,u1_struct_0(sK1))),
% 2.06/0.99    inference(cnf_transformation,[],[f54])).
% 2.06/0.99  
% 2.06/0.99  fof(f8,axiom,(
% 2.06/0.99    ! [X0] : ((l1_struct_0(X0) & ~v7_struct_0(X0)) => ~v1_zfmisc_1(u1_struct_0(X0)))),
% 2.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.06/0.99  
% 2.06/0.99  fof(f26,plain,(
% 2.06/0.99    ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | v7_struct_0(X0)))),
% 2.06/0.99    inference(ennf_transformation,[],[f8])).
% 2.06/0.99  
% 2.06/0.99  fof(f27,plain,(
% 2.06/0.99    ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | v7_struct_0(X0))),
% 2.06/0.99    inference(flattening,[],[f26])).
% 2.06/0.99  
% 2.06/0.99  fof(f61,plain,(
% 2.06/0.99    ( ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | v7_struct_0(X0)) )),
% 2.06/0.99    inference(cnf_transformation,[],[f27])).
% 2.06/0.99  
% 2.06/0.99  fof(f6,axiom,(
% 2.06/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.06/0.99  
% 2.06/0.99  fof(f24,plain,(
% 2.06/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.06/0.99    inference(ennf_transformation,[],[f6])).
% 2.06/0.99  
% 2.06/0.99  fof(f59,plain,(
% 2.06/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.06/0.99    inference(cnf_transformation,[],[f24])).
% 2.06/0.99  
% 2.06/0.99  fof(f10,axiom,(
% 2.06/0.99    ! [X0] : ((l1_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (~v2_struct_0(X1) => (~v1_tex_2(X1,X0) & ~v2_struct_0(X1)))))),
% 2.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.06/0.99  
% 2.06/0.99  fof(f30,plain,(
% 2.06/0.99    ! [X0] : (! [X1] : (((~v1_tex_2(X1,X0) & ~v2_struct_0(X1)) | v2_struct_0(X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0)))),
% 2.06/0.99    inference(ennf_transformation,[],[f10])).
% 2.06/0.99  
% 2.06/0.99  fof(f31,plain,(
% 2.06/0.99    ! [X0] : (! [X1] : ((~v1_tex_2(X1,X0) & ~v2_struct_0(X1)) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0))),
% 2.06/0.99    inference(flattening,[],[f30])).
% 2.06/0.99  
% 2.06/0.99  fof(f64,plain,(
% 2.06/0.99    ( ! [X0,X1] : (~v1_tex_2(X1,X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0)) )),
% 2.06/0.99    inference(cnf_transformation,[],[f31])).
% 2.06/0.99  
% 2.06/0.99  fof(f80,plain,(
% 2.06/0.99    v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) | v1_tex_2(k1_tex_2(sK1,sK2),sK1)),
% 2.06/0.99    inference(cnf_transformation,[],[f54])).
% 2.06/0.99  
% 2.06/0.99  fof(f14,axiom,(
% 2.06/0.99    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 2.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.06/0.99  
% 2.06/0.99  fof(f19,plain,(
% 2.06/0.99    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 2.06/0.99    inference(pure_predicate_removal,[],[f14])).
% 2.06/0.99  
% 2.06/0.99  fof(f37,plain,(
% 2.06/0.99    ! [X0,X1] : ((v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.06/0.99    inference(ennf_transformation,[],[f19])).
% 2.06/0.99  
% 2.06/0.99  fof(f38,plain,(
% 2.06/0.99    ! [X0,X1] : ((v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.06/0.99    inference(flattening,[],[f37])).
% 2.06/0.99  
% 2.06/0.99  fof(f73,plain,(
% 2.06/0.99    ( ! [X0,X1] : (~v2_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.06/0.99    inference(cnf_transformation,[],[f38])).
% 2.06/0.99  
% 2.06/0.99  fof(f2,axiom,(
% 2.06/0.99    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 2.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.06/0.99  
% 2.06/0.99  fof(f22,plain,(
% 2.06/0.99    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 2.06/0.99    inference(ennf_transformation,[],[f2])).
% 2.06/0.99  
% 2.06/0.99  fof(f56,plain,(
% 2.06/0.99    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 2.06/0.99    inference(cnf_transformation,[],[f22])).
% 2.06/0.99  
% 2.06/0.99  fof(f74,plain,(
% 2.06/0.99    ( ! [X0,X1] : (v7_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.06/0.99    inference(cnf_transformation,[],[f38])).
% 2.06/0.99  
% 2.06/0.99  fof(f9,axiom,(
% 2.06/0.99    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 2.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.06/0.99  
% 2.06/0.99  fof(f28,plain,(
% 2.06/0.99    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 2.06/0.99    inference(ennf_transformation,[],[f9])).
% 2.06/0.99  
% 2.06/0.99  fof(f29,plain,(
% 2.06/0.99    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 2.06/0.99    inference(flattening,[],[f28])).
% 2.06/0.99  
% 2.06/0.99  fof(f62,plain,(
% 2.06/0.99    ( ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0)) )),
% 2.06/0.99    inference(cnf_transformation,[],[f29])).
% 2.06/0.99  
% 2.06/0.99  fof(f7,axiom,(
% 2.06/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.06/0.99  
% 2.06/0.99  fof(f25,plain,(
% 2.06/0.99    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.06/0.99    inference(ennf_transformation,[],[f7])).
% 2.06/0.99  
% 2.06/0.99  fof(f60,plain,(
% 2.06/0.99    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.06/0.99    inference(cnf_transformation,[],[f25])).
% 2.06/0.99  
% 2.06/0.99  fof(f16,axiom,(
% 2.06/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~(v7_struct_0(X0) & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 2.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.06/0.99  
% 2.06/0.99  fof(f41,plain,(
% 2.06/0.99    ! [X0] : (! [X1] : ((~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.06/0.99    inference(ennf_transformation,[],[f16])).
% 2.06/0.99  
% 2.06/0.99  fof(f42,plain,(
% 2.06/0.99    ! [X0] : (! [X1] : (~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.06/0.99    inference(flattening,[],[f41])).
% 2.06/0.99  
% 2.06/0.99  fof(f76,plain,(
% 2.06/0.99    ( ! [X0,X1] : (~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.06/0.99    inference(cnf_transformation,[],[f42])).
% 2.06/0.99  
% 2.06/0.99  fof(f66,plain,(
% 2.06/0.99    ( ! [X0,X1] : (v1_tex_2(X1,X0) | m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.06/0.99    inference(cnf_transformation,[],[f48])).
% 2.06/0.99  
% 2.06/0.99  fof(f12,axiom,(
% 2.06/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 2.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.06/0.99  
% 2.06/0.99  fof(f34,plain,(
% 2.06/0.99    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.06/0.99    inference(ennf_transformation,[],[f12])).
% 2.06/0.99  
% 2.06/0.99  fof(f49,plain,(
% 2.06/0.99    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.06/0.99    inference(nnf_transformation,[],[f34])).
% 2.06/0.99  
% 2.06/0.99  fof(f70,plain,(
% 2.06/0.99    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.06/0.99    inference(cnf_transformation,[],[f49])).
% 2.06/0.99  
% 2.06/0.99  fof(f68,plain,(
% 2.06/0.99    ( ! [X0,X1] : (v1_tex_2(X1,X0) | ~v1_subset_1(sK0(X0,X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.06/0.99    inference(cnf_transformation,[],[f48])).
% 2.06/0.99  
% 2.06/0.99  fof(f3,axiom,(
% 2.06/0.99    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.06/0.99  
% 2.06/0.99  fof(f57,plain,(
% 2.06/0.99    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.06/0.99    inference(cnf_transformation,[],[f3])).
% 2.06/0.99  
% 2.06/0.99  fof(f5,axiom,(
% 2.06/0.99    ! [X0] : (v1_zfmisc_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_zfmisc_1(X1)))),
% 2.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.06/0.99  
% 2.06/0.99  fof(f23,plain,(
% 2.06/0.99    ! [X0] : (! [X1] : (v1_zfmisc_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_zfmisc_1(X0))),
% 2.06/0.99    inference(ennf_transformation,[],[f5])).
% 2.06/0.99  
% 2.06/0.99  fof(f58,plain,(
% 2.06/0.99    ( ! [X0,X1] : (v1_zfmisc_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_zfmisc_1(X0)) )),
% 2.06/0.99    inference(cnf_transformation,[],[f23])).
% 2.06/0.99  
% 2.06/0.99  cnf(c_0,plain,
% 2.06/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 2.06/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_3836,plain,
% 2.06/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 2.06/0.99      inference(subtyping,[status(esa)],[c_0]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_4508,plain,
% 2.06/0.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.06/0.99      inference(predicate_to_equality,[status(thm)],[c_3836]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_16,plain,
% 2.06/0.99      ( m1_pre_topc(k1_tex_2(X0,X1),X0)
% 2.06/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.06/0.99      | v2_struct_0(X0)
% 2.06/0.99      | ~ l1_pre_topc(X0) ),
% 2.06/0.99      inference(cnf_transformation,[],[f72]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_3824,plain,
% 2.06/0.99      ( m1_pre_topc(k1_tex_2(X0_46,X0_47),X0_46)
% 2.06/0.99      | ~ m1_subset_1(X0_47,u1_struct_0(X0_46))
% 2.06/0.99      | v2_struct_0(X0_46)
% 2.06/0.99      | ~ l1_pre_topc(X0_46) ),
% 2.06/0.99      inference(subtyping,[status(esa)],[c_16]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_4520,plain,
% 2.06/0.99      ( m1_pre_topc(k1_tex_2(X0_46,X0_47),X0_46) = iProver_top
% 2.06/0.99      | m1_subset_1(X0_47,u1_struct_0(X0_46)) != iProver_top
% 2.06/0.99      | v2_struct_0(X0_46) = iProver_top
% 2.06/0.99      | l1_pre_topc(X0_46) != iProver_top ),
% 2.06/0.99      inference(predicate_to_equality,[status(thm)],[c_3824]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_11,plain,
% 2.06/0.99      ( v1_tex_2(X0,X1)
% 2.06/0.99      | ~ m1_pre_topc(X0,X1)
% 2.06/0.99      | ~ l1_pre_topc(X1)
% 2.06/0.99      | sK0(X1,X0) = u1_struct_0(X0) ),
% 2.06/0.99      inference(cnf_transformation,[],[f67]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_3829,plain,
% 2.06/0.99      ( v1_tex_2(X0_46,X1_46)
% 2.06/0.99      | ~ m1_pre_topc(X0_46,X1_46)
% 2.06/0.99      | ~ l1_pre_topc(X1_46)
% 2.06/0.99      | sK0(X1_46,X0_46) = u1_struct_0(X0_46) ),
% 2.06/0.99      inference(subtyping,[status(esa)],[c_11]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_4515,plain,
% 2.06/0.99      ( sK0(X0_46,X1_46) = u1_struct_0(X1_46)
% 2.06/0.99      | v1_tex_2(X1_46,X0_46) = iProver_top
% 2.06/0.99      | m1_pre_topc(X1_46,X0_46) != iProver_top
% 2.06/0.99      | l1_pre_topc(X0_46) != iProver_top ),
% 2.06/0.99      inference(predicate_to_equality,[status(thm)],[c_3829]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_5445,plain,
% 2.06/0.99      ( sK0(X0_46,k1_tex_2(X0_46,X0_47)) = u1_struct_0(k1_tex_2(X0_46,X0_47))
% 2.06/0.99      | v1_tex_2(k1_tex_2(X0_46,X0_47),X0_46) = iProver_top
% 2.06/0.99      | m1_subset_1(X0_47,u1_struct_0(X0_46)) != iProver_top
% 2.06/0.99      | v2_struct_0(X0_46) = iProver_top
% 2.06/0.99      | l1_pre_topc(X0_46) != iProver_top ),
% 2.06/0.99      inference(superposition,[status(thm)],[c_4520,c_4515]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_20,plain,
% 2.06/0.99      ( v1_subset_1(k6_domain_1(X0,X1),X0)
% 2.06/0.99      | ~ m1_subset_1(X1,X0)
% 2.06/0.99      | v1_zfmisc_1(X0)
% 2.06/0.99      | v1_xboole_0(X0) ),
% 2.06/0.99      inference(cnf_transformation,[],[f75]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_3821,plain,
% 2.06/0.99      ( v1_subset_1(k6_domain_1(X0_47,X1_47),X0_47)
% 2.06/0.99      | ~ m1_subset_1(X1_47,X0_47)
% 2.06/0.99      | v1_zfmisc_1(X0_47)
% 2.06/0.99      | v1_xboole_0(X0_47) ),
% 2.06/0.99      inference(subtyping,[status(esa)],[c_20]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_4523,plain,
% 2.06/0.99      ( v1_subset_1(k6_domain_1(X0_47,X1_47),X0_47) = iProver_top
% 2.06/0.99      | m1_subset_1(X1_47,X0_47) != iProver_top
% 2.06/0.99      | v1_zfmisc_1(X0_47) = iProver_top
% 2.06/0.99      | v1_xboole_0(X0_47) = iProver_top ),
% 2.06/0.99      inference(predicate_to_equality,[status(thm)],[c_3821]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_22,negated_conjecture,
% 2.06/0.99      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 2.06/0.99      | ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
% 2.06/0.99      inference(cnf_transformation,[],[f81]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_3820,negated_conjecture,
% 2.06/0.99      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 2.06/0.99      | ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
% 2.06/0.99      inference(subtyping,[status(esa)],[c_22]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_4524,plain,
% 2.06/0.99      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top
% 2.06/0.99      | v1_tex_2(k1_tex_2(sK1,sK2),sK1) != iProver_top ),
% 2.06/0.99      inference(predicate_to_equality,[status(thm)],[c_3820]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_5289,plain,
% 2.06/0.99      ( v1_tex_2(k1_tex_2(sK1,sK2),sK1) != iProver_top
% 2.06/0.99      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 2.06/0.99      | v1_zfmisc_1(u1_struct_0(sK1)) = iProver_top
% 2.06/0.99      | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
% 2.06/0.99      inference(superposition,[status(thm)],[c_4523,c_4524]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_26,negated_conjecture,
% 2.06/0.99      ( ~ v2_struct_0(sK1) ),
% 2.06/0.99      inference(cnf_transformation,[],[f77]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_27,plain,
% 2.06/0.99      ( v2_struct_0(sK1) != iProver_top ),
% 2.06/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_25,negated_conjecture,
% 2.06/0.99      ( l1_pre_topc(sK1) ),
% 2.06/0.99      inference(cnf_transformation,[],[f78]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_28,plain,
% 2.06/0.99      ( l1_pre_topc(sK1) = iProver_top ),
% 2.06/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_24,negated_conjecture,
% 2.06/0.99      ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 2.06/0.99      inference(cnf_transformation,[],[f79]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_29,plain,
% 2.06/0.99      ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
% 2.06/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_31,plain,
% 2.06/0.99      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top
% 2.06/0.99      | v1_tex_2(k1_tex_2(sK1,sK2),sK1) != iProver_top ),
% 2.06/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_6,plain,
% 2.06/0.99      ( v7_struct_0(X0)
% 2.06/0.99      | ~ l1_struct_0(X0)
% 2.06/0.99      | ~ v1_zfmisc_1(u1_struct_0(X0)) ),
% 2.06/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_73,plain,
% 2.06/0.99      ( v7_struct_0(X0) = iProver_top
% 2.06/0.99      | l1_struct_0(X0) != iProver_top
% 2.06/0.99      | v1_zfmisc_1(u1_struct_0(X0)) != iProver_top ),
% 2.06/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_75,plain,
% 2.06/0.99      ( v7_struct_0(sK1) = iProver_top
% 2.06/0.99      | l1_struct_0(sK1) != iProver_top
% 2.06/0.99      | v1_zfmisc_1(u1_struct_0(sK1)) != iProver_top ),
% 2.06/0.99      inference(instantiation,[status(thm)],[c_73]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_4,plain,
% 2.06/0.99      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 2.06/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_77,plain,
% 2.06/0.99      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 2.06/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_79,plain,
% 2.06/0.99      ( l1_pre_topc(sK1) != iProver_top
% 2.06/0.99      | l1_struct_0(sK1) = iProver_top ),
% 2.06/0.99      inference(instantiation,[status(thm)],[c_77]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_8,plain,
% 2.06/0.99      ( ~ v1_tex_2(X0,X1)
% 2.06/0.99      | ~ m1_pre_topc(X0,X1)
% 2.06/0.99      | v2_struct_0(X1)
% 2.06/0.99      | v2_struct_0(X0)
% 2.06/0.99      | ~ v7_struct_0(X1)
% 2.06/0.99      | ~ l1_pre_topc(X1) ),
% 2.06/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_23,negated_conjecture,
% 2.06/0.99      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 2.06/0.99      | v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
% 2.06/0.99      inference(cnf_transformation,[],[f80]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_199,plain,
% 2.06/0.99      ( v1_tex_2(k1_tex_2(sK1,sK2),sK1)
% 2.06/0.99      | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) ),
% 2.06/0.99      inference(prop_impl,[status(thm)],[c_23]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_200,plain,
% 2.06/0.99      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 2.06/0.99      | v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
% 2.06/0.99      inference(renaming,[status(thm)],[c_199]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_908,plain,
% 2.06/0.99      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 2.06/0.99      | ~ m1_pre_topc(X0,X1)
% 2.06/0.99      | v2_struct_0(X1)
% 2.06/0.99      | v2_struct_0(X0)
% 2.06/0.99      | ~ v7_struct_0(X1)
% 2.06/0.99      | ~ l1_pre_topc(X1)
% 2.06/0.99      | k1_tex_2(sK1,sK2) != X0
% 2.06/0.99      | sK1 != X1 ),
% 2.06/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_200]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_909,plain,
% 2.06/0.99      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 2.06/0.99      | ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
% 2.06/0.99      | v2_struct_0(k1_tex_2(sK1,sK2))
% 2.06/0.99      | v2_struct_0(sK1)
% 2.06/0.99      | ~ v7_struct_0(sK1)
% 2.06/0.99      | ~ l1_pre_topc(sK1) ),
% 2.06/0.99      inference(unflattening,[status(thm)],[c_908]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_911,plain,
% 2.06/0.99      ( ~ v7_struct_0(sK1)
% 2.06/0.99      | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 2.06/0.99      | ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
% 2.06/0.99      | v2_struct_0(k1_tex_2(sK1,sK2)) ),
% 2.06/0.99      inference(global_propositional_subsumption,
% 2.06/0.99                [status(thm)],
% 2.06/0.99                [c_909,c_26,c_25]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_912,plain,
% 2.06/0.99      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 2.06/0.99      | ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
% 2.06/0.99      | v2_struct_0(k1_tex_2(sK1,sK2))
% 2.06/0.99      | ~ v7_struct_0(sK1) ),
% 2.06/0.99      inference(renaming,[status(thm)],[c_911]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_913,plain,
% 2.06/0.99      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) = iProver_top
% 2.06/0.99      | m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top
% 2.06/0.99      | v2_struct_0(k1_tex_2(sK1,sK2)) = iProver_top
% 2.06/0.99      | v7_struct_0(sK1) != iProver_top ),
% 2.06/0.99      inference(predicate_to_equality,[status(thm)],[c_912]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_2131,plain,
% 2.06/0.99      ( ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1)
% 2.06/0.99      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) ),
% 2.06/0.99      inference(prop_impl,[status(thm)],[c_22]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_2132,plain,
% 2.06/0.99      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 2.06/0.99      | ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
% 2.06/0.99      inference(renaming,[status(thm)],[c_2131]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_3075,plain,
% 2.06/0.99      ( ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1)
% 2.06/0.99      | ~ m1_subset_1(X0,X1)
% 2.06/0.99      | v1_zfmisc_1(X1)
% 2.06/0.99      | v1_xboole_0(X1)
% 2.06/0.99      | k6_domain_1(u1_struct_0(sK1),sK2) != k6_domain_1(X1,X0)
% 2.06/0.99      | u1_struct_0(sK1) != X1 ),
% 2.06/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_2132]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_3076,plain,
% 2.06/0.99      ( ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1)
% 2.06/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.06/0.99      | v1_zfmisc_1(u1_struct_0(sK1))
% 2.06/0.99      | v1_xboole_0(u1_struct_0(sK1))
% 2.06/0.99      | k6_domain_1(u1_struct_0(sK1),sK2) != k6_domain_1(u1_struct_0(sK1),X0) ),
% 2.06/0.99      inference(unflattening,[status(thm)],[c_3075]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_1914,plain,
% 2.06/0.99      ( v1_subset_1(k6_domain_1(X0,X1),X0)
% 2.06/0.99      | v1_zfmisc_1(X0)
% 2.06/0.99      | v1_xboole_0(X0)
% 2.06/0.99      | u1_struct_0(sK1) != X0
% 2.06/0.99      | sK2 != X1 ),
% 2.06/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_24]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_1915,plain,
% 2.06/0.99      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 2.06/0.99      | v1_zfmisc_1(u1_struct_0(sK1))
% 2.06/0.99      | v1_xboole_0(u1_struct_0(sK1)) ),
% 2.06/0.99      inference(unflattening,[status(thm)],[c_1914]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_3078,plain,
% 2.06/0.99      ( v1_xboole_0(u1_struct_0(sK1))
% 2.06/0.99      | v1_zfmisc_1(u1_struct_0(sK1))
% 2.06/0.99      | ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
% 2.06/0.99      inference(global_propositional_subsumption,
% 2.06/0.99                [status(thm)],
% 2.06/0.99                [c_3076,c_22,c_1915]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_3079,plain,
% 2.06/0.99      ( ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1)
% 2.06/0.99      | v1_zfmisc_1(u1_struct_0(sK1))
% 2.06/0.99      | v1_xboole_0(u1_struct_0(sK1)) ),
% 2.06/0.99      inference(renaming,[status(thm)],[c_3078]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_3080,plain,
% 2.06/0.99      ( v1_tex_2(k1_tex_2(sK1,sK2),sK1) != iProver_top
% 2.06/0.99      | v1_zfmisc_1(u1_struct_0(sK1)) = iProver_top
% 2.06/0.99      | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
% 2.06/0.99      inference(predicate_to_equality,[status(thm)],[c_3079]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_3888,plain,
% 2.06/0.99      ( m1_pre_topc(k1_tex_2(X0_46,X0_47),X0_46) = iProver_top
% 2.06/0.99      | m1_subset_1(X0_47,u1_struct_0(X0_46)) != iProver_top
% 2.06/0.99      | v2_struct_0(X0_46) = iProver_top
% 2.06/0.99      | l1_pre_topc(X0_46) != iProver_top ),
% 2.06/0.99      inference(predicate_to_equality,[status(thm)],[c_3824]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_3890,plain,
% 2.06/0.99      ( m1_pre_topc(k1_tex_2(sK1,sK2),sK1) = iProver_top
% 2.06/0.99      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 2.06/0.99      | v2_struct_0(sK1) = iProver_top
% 2.06/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 2.06/0.99      inference(instantiation,[status(thm)],[c_3888]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_19,plain,
% 2.06/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.06/0.99      | v2_struct_0(X1)
% 2.06/0.99      | ~ v2_struct_0(k1_tex_2(X1,X0))
% 2.06/0.99      | ~ l1_pre_topc(X1) ),
% 2.06/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_3823,plain,
% 2.06/0.99      ( ~ m1_subset_1(X0_47,u1_struct_0(X0_46))
% 2.06/0.99      | v2_struct_0(X0_46)
% 2.06/0.99      | ~ v2_struct_0(k1_tex_2(X0_46,X0_47))
% 2.06/0.99      | ~ l1_pre_topc(X0_46) ),
% 2.06/0.99      inference(subtyping,[status(esa)],[c_19]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_3891,plain,
% 2.06/0.99      ( m1_subset_1(X0_47,u1_struct_0(X0_46)) != iProver_top
% 2.06/0.99      | v2_struct_0(X0_46) = iProver_top
% 2.06/0.99      | v2_struct_0(k1_tex_2(X0_46,X0_47)) != iProver_top
% 2.06/0.99      | l1_pre_topc(X0_46) != iProver_top ),
% 2.06/0.99      inference(predicate_to_equality,[status(thm)],[c_3823]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_3893,plain,
% 2.06/0.99      ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 2.06/0.99      | v2_struct_0(k1_tex_2(sK1,sK2)) != iProver_top
% 2.06/0.99      | v2_struct_0(sK1) = iProver_top
% 2.06/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 2.06/0.99      inference(instantiation,[status(thm)],[c_3891]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_5590,plain,
% 2.06/0.99      ( v1_tex_2(k1_tex_2(sK1,sK2),sK1) != iProver_top
% 2.06/0.99      | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
% 2.06/0.99      inference(global_propositional_subsumption,
% 2.06/0.99                [status(thm)],
% 2.06/0.99                [c_5289,c_27,c_28,c_29,c_75,c_79,c_913,c_3080,c_3890,
% 2.06/0.99                 c_3893,c_3907]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_6663,plain,
% 2.06/0.99      ( sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(k1_tex_2(sK1,sK2))
% 2.06/0.99      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 2.06/0.99      | v2_struct_0(sK1) = iProver_top
% 2.06/0.99      | l1_pre_topc(sK1) != iProver_top
% 2.06/0.99      | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
% 2.06/0.99      inference(superposition,[status(thm)],[c_5445,c_5590]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_7057,plain,
% 2.06/0.99      ( sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(k1_tex_2(sK1,sK2))
% 2.06/0.99      | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
% 2.06/0.99      inference(global_propositional_subsumption,
% 2.06/0.99                [status(thm)],
% 2.06/0.99                [c_6663,c_27,c_28,c_29]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_1,plain,
% 2.06/0.99      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X1 = X0 ),
% 2.06/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_3835,plain,
% 2.06/0.99      ( ~ v1_xboole_0(X0_47) | ~ v1_xboole_0(X1_47) | X1_47 = X0_47 ),
% 2.06/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_4509,plain,
% 2.06/0.99      ( X0_47 = X1_47
% 2.06/0.99      | v1_xboole_0(X1_47) != iProver_top
% 2.06/0.99      | v1_xboole_0(X0_47) != iProver_top ),
% 2.06/0.99      inference(predicate_to_equality,[status(thm)],[c_3835]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_7065,plain,
% 2.06/0.99      ( sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(k1_tex_2(sK1,sK2))
% 2.06/0.99      | u1_struct_0(sK1) = X0_47
% 2.06/0.99      | v1_xboole_0(X0_47) != iProver_top ),
% 2.06/0.99      inference(superposition,[status(thm)],[c_7057,c_4509]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_74,plain,
% 2.06/0.99      ( v7_struct_0(sK1)
% 2.06/0.99      | ~ l1_struct_0(sK1)
% 2.06/0.99      | ~ v1_zfmisc_1(u1_struct_0(sK1)) ),
% 2.06/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_78,plain,
% 2.06/0.99      ( ~ l1_pre_topc(sK1) | l1_struct_0(sK1) ),
% 2.06/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_87,plain,
% 2.06/0.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.06/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_3847,plain,
% 2.06/0.99      ( u1_struct_0(X0_46) = u1_struct_0(X1_46) | X0_46 != X1_46 ),
% 2.06/0.99      theory(equality) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_3860,plain,
% 2.06/0.99      ( u1_struct_0(sK1) = u1_struct_0(sK1) | sK1 != sK1 ),
% 2.06/0.99      inference(instantiation,[status(thm)],[c_3847]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_3838,plain,( X0_46 = X0_46 ),theory(equality) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_3868,plain,
% 2.06/0.99      ( sK1 = sK1 ),
% 2.06/0.99      inference(instantiation,[status(thm)],[c_3838]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_3889,plain,
% 2.06/0.99      ( m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
% 2.06/0.99      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 2.06/0.99      | v2_struct_0(sK1)
% 2.06/0.99      | ~ l1_pre_topc(sK1) ),
% 2.06/0.99      inference(instantiation,[status(thm)],[c_3824]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_18,plain,
% 2.06/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.06/0.99      | v2_struct_0(X1)
% 2.06/0.99      | v7_struct_0(k1_tex_2(X1,X0))
% 2.06/0.99      | ~ l1_pre_topc(X1) ),
% 2.06/0.99      inference(cnf_transformation,[],[f74]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_3822,plain,
% 2.06/0.99      ( ~ m1_subset_1(X0_47,u1_struct_0(X0_46))
% 2.06/0.99      | v2_struct_0(X0_46)
% 2.06/0.99      | v7_struct_0(k1_tex_2(X0_46,X0_47))
% 2.06/0.99      | ~ l1_pre_topc(X0_46) ),
% 2.06/0.99      inference(subtyping,[status(esa)],[c_18]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_3895,plain,
% 2.06/0.99      ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 2.06/0.99      | v2_struct_0(sK1)
% 2.06/0.99      | v7_struct_0(k1_tex_2(sK1,sK2))
% 2.06/0.99      | ~ l1_pre_topc(sK1) ),
% 2.06/0.99      inference(instantiation,[status(thm)],[c_3822]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_7,plain,
% 2.06/0.99      ( ~ v7_struct_0(X0)
% 2.06/0.99      | ~ l1_struct_0(X0)
% 2.06/0.99      | v1_zfmisc_1(u1_struct_0(X0)) ),
% 2.06/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_363,plain,
% 2.06/0.99      ( ~ v7_struct_0(X0)
% 2.06/0.99      | ~ l1_pre_topc(X0)
% 2.06/0.99      | v1_zfmisc_1(u1_struct_0(X0)) ),
% 2.06/0.99      inference(resolution,[status(thm)],[c_4,c_7]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_3814,plain,
% 2.06/0.99      ( ~ v7_struct_0(X0_46)
% 2.06/0.99      | ~ l1_pre_topc(X0_46)
% 2.06/0.99      | v1_zfmisc_1(u1_struct_0(X0_46)) ),
% 2.06/0.99      inference(subtyping,[status(esa)],[c_363]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_4739,plain,
% 2.06/0.99      ( ~ v7_struct_0(k1_tex_2(X0_46,X0_47))
% 2.06/0.99      | ~ l1_pre_topc(k1_tex_2(X0_46,X0_47))
% 2.06/0.99      | v1_zfmisc_1(u1_struct_0(k1_tex_2(X0_46,X0_47))) ),
% 2.06/0.99      inference(instantiation,[status(thm)],[c_3814]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_4741,plain,
% 2.06/0.99      ( ~ v7_struct_0(k1_tex_2(sK1,sK2))
% 2.06/0.99      | ~ l1_pre_topc(k1_tex_2(sK1,sK2))
% 2.06/0.99      | v1_zfmisc_1(u1_struct_0(k1_tex_2(sK1,sK2))) ),
% 2.06/0.99      inference(instantiation,[status(thm)],[c_4739]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_5,plain,
% 2.06/0.99      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.06/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_3832,plain,
% 2.06/0.99      ( ~ m1_pre_topc(X0_46,X1_46)
% 2.06/0.99      | ~ l1_pre_topc(X1_46)
% 2.06/0.99      | l1_pre_topc(X0_46) ),
% 2.06/0.99      inference(subtyping,[status(esa)],[c_5]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_4862,plain,
% 2.06/0.99      ( ~ m1_pre_topc(k1_tex_2(X0_46,X0_47),X1_46)
% 2.06/0.99      | ~ l1_pre_topc(X1_46)
% 2.06/0.99      | l1_pre_topc(k1_tex_2(X0_46,X0_47)) ),
% 2.06/0.99      inference(instantiation,[status(thm)],[c_3832]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_4864,plain,
% 2.06/0.99      ( ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
% 2.06/0.99      | l1_pre_topc(k1_tex_2(sK1,sK2))
% 2.06/0.99      | ~ l1_pre_topc(sK1) ),
% 2.06/0.99      inference(instantiation,[status(thm)],[c_4862]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_4963,plain,
% 2.06/0.99      ( ~ v1_xboole_0(X0_47)
% 2.06/0.99      | ~ v1_xboole_0(u1_struct_0(sK1))
% 2.06/0.99      | u1_struct_0(sK1) = X0_47 ),
% 2.06/0.99      inference(instantiation,[status(thm)],[c_3835]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_4969,plain,
% 2.06/0.99      ( u1_struct_0(sK1) = X0_47
% 2.06/0.99      | v1_xboole_0(X0_47) != iProver_top
% 2.06/0.99      | v1_xboole_0(u1_struct_0(sK1)) != iProver_top ),
% 2.06/0.99      inference(predicate_to_equality,[status(thm)],[c_4963]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_3841,plain,
% 2.06/0.99      ( ~ v1_xboole_0(X0_47) | v1_xboole_0(X1_47) | X1_47 != X0_47 ),
% 2.06/0.99      theory(equality) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_4804,plain,
% 2.06/0.99      ( v1_xboole_0(X0_47)
% 2.06/0.99      | ~ v1_xboole_0(k1_xboole_0)
% 2.06/0.99      | X0_47 != k1_xboole_0 ),
% 2.06/0.99      inference(instantiation,[status(thm)],[c_3841]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_5316,plain,
% 2.06/0.99      ( v1_xboole_0(u1_struct_0(sK1))
% 2.06/0.99      | ~ v1_xboole_0(k1_xboole_0)
% 2.06/0.99      | u1_struct_0(sK1) != k1_xboole_0 ),
% 2.06/0.99      inference(instantiation,[status(thm)],[c_4804]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_5322,plain,
% 2.06/0.99      ( u1_struct_0(sK1) != k1_xboole_0
% 2.06/0.99      | v1_xboole_0(u1_struct_0(sK1)) = iProver_top
% 2.06/0.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.06/0.99      inference(predicate_to_equality,[status(thm)],[c_5316]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_3840,plain,
% 2.06/0.99      ( X0_47 != X1_47 | X2_47 != X1_47 | X2_47 = X0_47 ),
% 2.06/0.99      theory(equality) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_4974,plain,
% 2.06/0.99      ( X0_47 != X1_47
% 2.06/0.99      | u1_struct_0(sK1) != X1_47
% 2.06/0.99      | u1_struct_0(sK1) = X0_47 ),
% 2.06/0.99      inference(instantiation,[status(thm)],[c_3840]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_5047,plain,
% 2.06/0.99      ( X0_47 != u1_struct_0(sK1)
% 2.06/0.99      | u1_struct_0(sK1) = X0_47
% 2.06/0.99      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 2.06/0.99      inference(instantiation,[status(thm)],[c_4974]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_5229,plain,
% 2.06/0.99      ( u1_struct_0(X0_46) != u1_struct_0(sK1)
% 2.06/0.99      | u1_struct_0(sK1) = u1_struct_0(X0_46)
% 2.06/0.99      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 2.06/0.99      inference(instantiation,[status(thm)],[c_5047]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_5536,plain,
% 2.06/0.99      ( u1_struct_0(k1_tex_2(X0_46,X0_47)) != u1_struct_0(sK1)
% 2.06/0.99      | u1_struct_0(sK1) = u1_struct_0(k1_tex_2(X0_46,X0_47))
% 2.06/0.99      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 2.06/0.99      inference(instantiation,[status(thm)],[c_5229]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_5537,plain,
% 2.06/0.99      ( u1_struct_0(k1_tex_2(sK1,sK2)) != u1_struct_0(sK1)
% 2.06/0.99      | u1_struct_0(sK1) = u1_struct_0(k1_tex_2(sK1,sK2))
% 2.06/0.99      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 2.06/0.99      inference(instantiation,[status(thm)],[c_5536]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_3819,negated_conjecture,
% 2.06/0.99      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 2.06/0.99      | v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
% 2.06/0.99      inference(subtyping,[status(esa)],[c_23]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_4525,plain,
% 2.06/0.99      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) = iProver_top
% 2.06/0.99      | v1_tex_2(k1_tex_2(sK1,sK2),sK1) = iProver_top ),
% 2.06/0.99      inference(predicate_to_equality,[status(thm)],[c_3819]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_21,plain,
% 2.06/0.99      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
% 2.06/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.06/0.99      | v2_struct_0(X0)
% 2.06/0.99      | ~ v7_struct_0(X0)
% 2.06/0.99      | ~ l1_struct_0(X0) ),
% 2.06/0.99      inference(cnf_transformation,[],[f76]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_343,plain,
% 2.06/0.99      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
% 2.06/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.06/0.99      | v2_struct_0(X0)
% 2.06/0.99      | ~ v7_struct_0(X0)
% 2.06/0.99      | ~ l1_pre_topc(X0) ),
% 2.06/0.99      inference(resolution,[status(thm)],[c_4,c_21]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_3815,plain,
% 2.06/0.99      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0_46),X0_47),u1_struct_0(X0_46))
% 2.06/0.99      | ~ m1_subset_1(X0_47,u1_struct_0(X0_46))
% 2.06/0.99      | v2_struct_0(X0_46)
% 2.06/0.99      | ~ v7_struct_0(X0_46)
% 2.06/0.99      | ~ l1_pre_topc(X0_46) ),
% 2.06/0.99      inference(subtyping,[status(esa)],[c_343]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_4529,plain,
% 2.06/0.99      ( v1_subset_1(k6_domain_1(u1_struct_0(X0_46),X0_47),u1_struct_0(X0_46)) != iProver_top
% 2.06/0.99      | m1_subset_1(X0_47,u1_struct_0(X0_46)) != iProver_top
% 2.06/0.99      | v2_struct_0(X0_46) = iProver_top
% 2.06/0.99      | v7_struct_0(X0_46) != iProver_top
% 2.06/0.99      | l1_pre_topc(X0_46) != iProver_top ),
% 2.06/0.99      inference(predicate_to_equality,[status(thm)],[c_3815]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_5746,plain,
% 2.06/0.99      ( v1_tex_2(k1_tex_2(sK1,sK2),sK1) = iProver_top
% 2.06/0.99      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 2.06/0.99      | v2_struct_0(sK1) = iProver_top
% 2.06/0.99      | v7_struct_0(sK1) != iProver_top
% 2.06/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 2.06/0.99      inference(superposition,[status(thm)],[c_4525,c_4529]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_3905,plain,
% 2.06/0.99      ( v1_subset_1(k6_domain_1(u1_struct_0(X0_46),X0_47),u1_struct_0(X0_46)) != iProver_top
% 2.06/0.99      | m1_subset_1(X0_47,u1_struct_0(X0_46)) != iProver_top
% 2.06/0.99      | v2_struct_0(X0_46) = iProver_top
% 2.06/0.99      | v7_struct_0(X0_46) != iProver_top
% 2.06/0.99      | l1_pre_topc(X0_46) != iProver_top ),
% 2.06/0.99      inference(predicate_to_equality,[status(thm)],[c_3815]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_3907,plain,
% 2.06/0.99      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top
% 2.06/0.99      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 2.06/0.99      | v2_struct_0(sK1) = iProver_top
% 2.06/0.99      | v7_struct_0(sK1) != iProver_top
% 2.06/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 2.06/0.99      inference(instantiation,[status(thm)],[c_3905]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_5837,plain,
% 2.06/0.99      ( v7_struct_0(sK1) != iProver_top ),
% 2.06/0.99      inference(global_propositional_subsumption,
% 2.06/0.99                [status(thm)],
% 2.06/0.99                [c_5746,c_27,c_28,c_29,c_913,c_3890,c_3893,c_3907]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_5839,plain,
% 2.06/0.99      ( ~ v7_struct_0(sK1) ),
% 2.06/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_5837]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_3844,plain,
% 2.06/0.99      ( ~ v1_zfmisc_1(X0_47) | v1_zfmisc_1(X1_47) | X1_47 != X0_47 ),
% 2.06/0.99      theory(equality) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_5118,plain,
% 2.06/0.99      ( v1_zfmisc_1(X0_47)
% 2.06/0.99      | ~ v1_zfmisc_1(u1_struct_0(k1_tex_2(X0_46,X1_47)))
% 2.06/0.99      | X0_47 != u1_struct_0(k1_tex_2(X0_46,X1_47)) ),
% 2.06/0.99      inference(instantiation,[status(thm)],[c_3844]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_5938,plain,
% 2.06/0.99      ( v1_zfmisc_1(u1_struct_0(X0_46))
% 2.06/0.99      | ~ v1_zfmisc_1(u1_struct_0(k1_tex_2(X1_46,X0_47)))
% 2.06/0.99      | u1_struct_0(X0_46) != u1_struct_0(k1_tex_2(X1_46,X0_47)) ),
% 2.06/0.99      inference(instantiation,[status(thm)],[c_5118]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_5941,plain,
% 2.06/0.99      ( ~ v1_zfmisc_1(u1_struct_0(k1_tex_2(sK1,sK2)))
% 2.06/0.99      | v1_zfmisc_1(u1_struct_0(sK1))
% 2.06/0.99      | u1_struct_0(sK1) != u1_struct_0(k1_tex_2(sK1,sK2)) ),
% 2.06/0.99      inference(instantiation,[status(thm)],[c_5938]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_12,plain,
% 2.06/0.99      ( v1_tex_2(X0,X1)
% 2.06/0.99      | ~ m1_pre_topc(X0,X1)
% 2.06/0.99      | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.06/0.99      | ~ l1_pre_topc(X1) ),
% 2.06/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_3828,plain,
% 2.06/0.99      ( v1_tex_2(X0_46,X1_46)
% 2.06/0.99      | ~ m1_pre_topc(X0_46,X1_46)
% 2.06/0.99      | m1_subset_1(sK0(X1_46,X0_46),k1_zfmisc_1(u1_struct_0(X1_46)))
% 2.06/0.99      | ~ l1_pre_topc(X1_46) ),
% 2.06/0.99      inference(subtyping,[status(esa)],[c_12]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_4516,plain,
% 2.06/0.99      ( v1_tex_2(X0_46,X1_46) = iProver_top
% 2.06/0.99      | m1_pre_topc(X0_46,X1_46) != iProver_top
% 2.06/0.99      | m1_subset_1(sK0(X1_46,X0_46),k1_zfmisc_1(u1_struct_0(X1_46))) = iProver_top
% 2.06/0.99      | l1_pre_topc(X1_46) != iProver_top ),
% 2.06/0.99      inference(predicate_to_equality,[status(thm)],[c_3828]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_14,plain,
% 2.06/0.99      ( v1_subset_1(X0,X1)
% 2.06/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.06/0.99      | X1 = X0 ),
% 2.06/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_3826,plain,
% 2.06/0.99      ( v1_subset_1(X0_47,X1_47)
% 2.06/0.99      | ~ m1_subset_1(X0_47,k1_zfmisc_1(X1_47))
% 2.06/0.99      | X1_47 = X0_47 ),
% 2.06/0.99      inference(subtyping,[status(esa)],[c_14]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_4518,plain,
% 2.06/0.99      ( X0_47 = X1_47
% 2.06/0.99      | v1_subset_1(X1_47,X0_47) = iProver_top
% 2.06/0.99      | m1_subset_1(X1_47,k1_zfmisc_1(X0_47)) != iProver_top ),
% 2.06/0.99      inference(predicate_to_equality,[status(thm)],[c_3826]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_5848,plain,
% 2.06/0.99      ( sK0(X0_46,X1_46) = u1_struct_0(X0_46)
% 2.06/0.99      | v1_subset_1(sK0(X0_46,X1_46),u1_struct_0(X0_46)) = iProver_top
% 2.06/0.99      | v1_tex_2(X1_46,X0_46) = iProver_top
% 2.06/0.99      | m1_pre_topc(X1_46,X0_46) != iProver_top
% 2.06/0.99      | l1_pre_topc(X0_46) != iProver_top ),
% 2.06/0.99      inference(superposition,[status(thm)],[c_4516,c_4518]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_10,plain,
% 2.06/0.99      ( ~ v1_subset_1(sK0(X0,X1),u1_struct_0(X0))
% 2.06/0.99      | v1_tex_2(X1,X0)
% 2.06/0.99      | ~ m1_pre_topc(X1,X0)
% 2.06/0.99      | ~ l1_pre_topc(X0) ),
% 2.06/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_3830,plain,
% 2.06/0.99      ( ~ v1_subset_1(sK0(X0_46,X1_46),u1_struct_0(X0_46))
% 2.06/0.99      | v1_tex_2(X1_46,X0_46)
% 2.06/0.99      | ~ m1_pre_topc(X1_46,X0_46)
% 2.06/0.99      | ~ l1_pre_topc(X0_46) ),
% 2.06/0.99      inference(subtyping,[status(esa)],[c_10]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_3878,plain,
% 2.06/0.99      ( v1_subset_1(sK0(X0_46,X1_46),u1_struct_0(X0_46)) != iProver_top
% 2.06/0.99      | v1_tex_2(X1_46,X0_46) = iProver_top
% 2.06/0.99      | m1_pre_topc(X1_46,X0_46) != iProver_top
% 2.06/0.99      | l1_pre_topc(X0_46) != iProver_top ),
% 2.06/0.99      inference(predicate_to_equality,[status(thm)],[c_3830]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_6163,plain,
% 2.06/0.99      ( sK0(X0_46,X1_46) = u1_struct_0(X0_46)
% 2.06/0.99      | v1_tex_2(X1_46,X0_46) = iProver_top
% 2.06/0.99      | m1_pre_topc(X1_46,X0_46) != iProver_top
% 2.06/0.99      | l1_pre_topc(X0_46) != iProver_top ),
% 2.06/0.99      inference(global_propositional_subsumption,
% 2.06/0.99                [status(thm)],
% 2.06/0.99                [c_5848,c_3878]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_6171,plain,
% 2.06/0.99      ( sK0(X0_46,k1_tex_2(X0_46,X0_47)) = u1_struct_0(X0_46)
% 2.06/0.99      | v1_tex_2(k1_tex_2(X0_46,X0_47),X0_46) = iProver_top
% 2.06/0.99      | m1_subset_1(X0_47,u1_struct_0(X0_46)) != iProver_top
% 2.06/0.99      | v2_struct_0(X0_46) = iProver_top
% 2.06/0.99      | l1_pre_topc(X0_46) != iProver_top ),
% 2.06/0.99      inference(superposition,[status(thm)],[c_4520,c_6163]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_6289,plain,
% 2.06/0.99      ( sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(sK1)
% 2.06/0.99      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 2.06/0.99      | v2_struct_0(sK1) = iProver_top
% 2.06/0.99      | l1_pre_topc(sK1) != iProver_top
% 2.06/0.99      | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
% 2.06/0.99      inference(superposition,[status(thm)],[c_6171,c_5590]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_6318,plain,
% 2.06/0.99      ( sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(sK1)
% 2.06/0.99      | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
% 2.06/0.99      inference(global_propositional_subsumption,
% 2.06/0.99                [status(thm)],
% 2.06/0.99                [c_6289,c_27,c_28,c_29]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_4917,plain,
% 2.06/0.99      ( k1_xboole_0 = X0_47 | v1_xboole_0(X0_47) != iProver_top ),
% 2.06/0.99      inference(superposition,[status(thm)],[c_4508,c_4509]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_6324,plain,
% 2.06/0.99      ( sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(sK1)
% 2.06/0.99      | u1_struct_0(sK1) = k1_xboole_0 ),
% 2.06/0.99      inference(superposition,[status(thm)],[c_6318,c_4917]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_7064,plain,
% 2.06/0.99      ( sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(k1_tex_2(sK1,sK2))
% 2.06/0.99      | u1_struct_0(sK1) = k1_xboole_0 ),
% 2.06/0.99      inference(superposition,[status(thm)],[c_7057,c_4917]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_7081,plain,
% 2.06/0.99      ( u1_struct_0(k1_tex_2(sK1,sK2)) = u1_struct_0(sK1)
% 2.06/0.99      | u1_struct_0(sK1) = k1_xboole_0 ),
% 2.06/0.99      inference(superposition,[status(thm)],[c_6324,c_7064]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_7239,plain,
% 2.06/0.99      ( u1_struct_0(sK1) = X0_47 | v1_xboole_0(X0_47) != iProver_top ),
% 2.06/0.99      inference(global_propositional_subsumption,
% 2.06/0.99                [status(thm)],
% 2.06/0.99                [c_7065,c_26,c_25,c_24,c_74,c_78,c_87,c_3860,c_3868,
% 2.06/0.99                 c_3889,c_3895,c_4741,c_4864,c_4969,c_5322,c_5537,c_5839,
% 2.06/0.99                 c_5941,c_7081]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_7247,plain,
% 2.06/0.99      ( u1_struct_0(sK1) = k1_xboole_0 ),
% 2.06/0.99      inference(superposition,[status(thm)],[c_4508,c_7239]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_377,plain,
% 2.06/0.99      ( v7_struct_0(X0)
% 2.06/0.99      | ~ l1_pre_topc(X0)
% 2.06/0.99      | ~ v1_zfmisc_1(u1_struct_0(X0)) ),
% 2.06/0.99      inference(resolution,[status(thm)],[c_4,c_6]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_3813,plain,
% 2.06/0.99      ( v7_struct_0(X0_46)
% 2.06/0.99      | ~ l1_pre_topc(X0_46)
% 2.06/0.99      | ~ v1_zfmisc_1(u1_struct_0(X0_46)) ),
% 2.06/0.99      inference(subtyping,[status(esa)],[c_377]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_4531,plain,
% 2.06/0.99      ( v7_struct_0(X0_46) = iProver_top
% 2.06/0.99      | l1_pre_topc(X0_46) != iProver_top
% 2.06/0.99      | v1_zfmisc_1(u1_struct_0(X0_46)) != iProver_top ),
% 2.06/0.99      inference(predicate_to_equality,[status(thm)],[c_3813]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_7286,plain,
% 2.06/0.99      ( v7_struct_0(sK1) = iProver_top
% 2.06/0.99      | l1_pre_topc(sK1) != iProver_top
% 2.06/0.99      | v1_zfmisc_1(k1_xboole_0) != iProver_top ),
% 2.06/0.99      inference(superposition,[status(thm)],[c_7247,c_4531]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_3818,negated_conjecture,
% 2.06/0.99      ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 2.06/0.99      inference(subtyping,[status(esa)],[c_24]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_4526,plain,
% 2.06/0.99      ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
% 2.06/0.99      inference(predicate_to_equality,[status(thm)],[c_3818]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_4522,plain,
% 2.06/0.99      ( m1_subset_1(X0_47,u1_struct_0(X0_46)) != iProver_top
% 2.06/0.99      | v2_struct_0(X0_46) = iProver_top
% 2.06/0.99      | v7_struct_0(k1_tex_2(X0_46,X0_47)) = iProver_top
% 2.06/0.99      | l1_pre_topc(X0_46) != iProver_top ),
% 2.06/0.99      inference(predicate_to_equality,[status(thm)],[c_3822]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_5368,plain,
% 2.06/0.99      ( v2_struct_0(sK1) = iProver_top
% 2.06/0.99      | v7_struct_0(k1_tex_2(sK1,sK2)) = iProver_top
% 2.06/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 2.06/0.99      inference(superposition,[status(thm)],[c_4526,c_4522]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_3894,plain,
% 2.06/0.99      ( m1_subset_1(X0_47,u1_struct_0(X0_46)) != iProver_top
% 2.06/0.99      | v2_struct_0(X0_46) = iProver_top
% 2.06/0.99      | v7_struct_0(k1_tex_2(X0_46,X0_47)) = iProver_top
% 2.06/0.99      | l1_pre_topc(X0_46) != iProver_top ),
% 2.06/0.99      inference(predicate_to_equality,[status(thm)],[c_3822]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_3896,plain,
% 2.06/0.99      ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 2.06/0.99      | v2_struct_0(sK1) = iProver_top
% 2.06/0.99      | v7_struct_0(k1_tex_2(sK1,sK2)) = iProver_top
% 2.06/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 2.06/0.99      inference(instantiation,[status(thm)],[c_3894]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_5471,plain,
% 2.06/0.99      ( v7_struct_0(k1_tex_2(sK1,sK2)) = iProver_top ),
% 2.06/0.99      inference(global_propositional_subsumption,
% 2.06/0.99                [status(thm)],
% 2.06/0.99                [c_5368,c_27,c_28,c_29,c_3896]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_4530,plain,
% 2.06/0.99      ( v7_struct_0(X0_46) != iProver_top
% 2.06/0.99      | l1_pre_topc(X0_46) != iProver_top
% 2.06/0.99      | v1_zfmisc_1(u1_struct_0(X0_46)) = iProver_top ),
% 2.06/0.99      inference(predicate_to_equality,[status(thm)],[c_3814]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_2,plain,
% 2.06/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.06/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_3834,plain,
% 2.06/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0_47)) ),
% 2.06/0.99      inference(subtyping,[status(esa)],[c_2]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_4510,plain,
% 2.06/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0_47)) = iProver_top ),
% 2.06/0.99      inference(predicate_to_equality,[status(thm)],[c_3834]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_3,plain,
% 2.06/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.06/0.99      | ~ v1_zfmisc_1(X1)
% 2.06/0.99      | v1_zfmisc_1(X0) ),
% 2.06/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_3833,plain,
% 2.06/0.99      ( ~ m1_subset_1(X0_47,k1_zfmisc_1(X1_47))
% 2.06/0.99      | ~ v1_zfmisc_1(X1_47)
% 2.06/0.99      | v1_zfmisc_1(X0_47) ),
% 2.06/0.99      inference(subtyping,[status(esa)],[c_3]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_4511,plain,
% 2.06/0.99      ( m1_subset_1(X0_47,k1_zfmisc_1(X1_47)) != iProver_top
% 2.06/0.99      | v1_zfmisc_1(X1_47) != iProver_top
% 2.06/0.99      | v1_zfmisc_1(X0_47) = iProver_top ),
% 2.06/0.99      inference(predicate_to_equality,[status(thm)],[c_3833]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_4825,plain,
% 2.06/0.99      ( v1_zfmisc_1(X0_47) != iProver_top
% 2.06/0.99      | v1_zfmisc_1(k1_xboole_0) = iProver_top ),
% 2.06/0.99      inference(superposition,[status(thm)],[c_4510,c_4511]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_5143,plain,
% 2.06/0.99      ( v7_struct_0(X0_46) != iProver_top
% 2.06/0.99      | l1_pre_topc(X0_46) != iProver_top
% 2.06/0.99      | v1_zfmisc_1(k1_xboole_0) = iProver_top ),
% 2.06/0.99      inference(superposition,[status(thm)],[c_4530,c_4825]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_5476,plain,
% 2.06/0.99      ( l1_pre_topc(k1_tex_2(sK1,sK2)) != iProver_top
% 2.06/0.99      | v1_zfmisc_1(k1_xboole_0) = iProver_top ),
% 2.06/0.99      inference(superposition,[status(thm)],[c_5471,c_5143]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_4863,plain,
% 2.06/0.99      ( m1_pre_topc(k1_tex_2(X0_46,X0_47),X1_46) != iProver_top
% 2.06/0.99      | l1_pre_topc(X1_46) != iProver_top
% 2.06/0.99      | l1_pre_topc(k1_tex_2(X0_46,X0_47)) = iProver_top ),
% 2.06/0.99      inference(predicate_to_equality,[status(thm)],[c_4862]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_4865,plain,
% 2.06/0.99      ( m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top
% 2.06/0.99      | l1_pre_topc(k1_tex_2(sK1,sK2)) = iProver_top
% 2.06/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 2.06/0.99      inference(instantiation,[status(thm)],[c_4863]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(contradiction,plain,
% 2.06/0.99      ( $false ),
% 2.06/0.99      inference(minisat,
% 2.06/0.99                [status(thm)],
% 2.06/0.99                [c_7286,c_5837,c_5476,c_4865,c_3890,c_29,c_28,c_27]) ).
% 2.06/0.99  
% 2.06/0.99  
% 2.06/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.06/0.99  
% 2.06/0.99  ------                               Statistics
% 2.06/0.99  
% 2.06/0.99  ------ General
% 2.06/0.99  
% 2.06/0.99  abstr_ref_over_cycles:                  0
% 2.06/0.99  abstr_ref_under_cycles:                 0
% 2.06/0.99  gc_basic_clause_elim:                   0
% 2.06/0.99  forced_gc_time:                         0
% 2.06/0.99  parsing_time:                           0.009
% 2.06/0.99  unif_index_cands_time:                  0.
% 2.06/0.99  unif_index_add_time:                    0.
% 2.06/0.99  orderings_time:                         0.
% 2.06/0.99  out_proof_time:                         0.01
% 2.06/0.99  total_time:                             0.181
% 2.06/0.99  num_of_symbols:                         51
% 2.06/0.99  num_of_terms:                           4270
% 2.06/0.99  
% 2.06/0.99  ------ Preprocessing
% 2.06/0.99  
% 2.06/0.99  num_of_splits:                          0
% 2.06/0.99  num_of_split_atoms:                     0
% 2.06/0.99  num_of_reused_defs:                     0
% 2.06/0.99  num_eq_ax_congr_red:                    10
% 2.06/0.99  num_of_sem_filtered_clauses:            1
% 2.06/0.99  num_of_subtypes:                        2
% 2.06/0.99  monotx_restored_types:                  1
% 2.06/0.99  sat_num_of_epr_types:                   0
% 2.06/0.99  sat_num_of_non_cyclic_types:            0
% 2.06/0.99  sat_guarded_non_collapsed_types:        0
% 2.06/0.99  num_pure_diseq_elim:                    0
% 2.06/0.99  simp_replaced_by:                       0
% 2.06/0.99  res_preprocessed:                       130
% 2.06/0.99  prep_upred:                             0
% 2.06/0.99  prep_unflattend:                        142
% 2.06/0.99  smt_new_axioms:                         0
% 2.06/0.99  pred_elim_cands:                        9
% 2.06/0.99  pred_elim:                              1
% 2.06/0.99  pred_elim_cl:                           1
% 2.06/0.99  pred_elim_cycles:                       11
% 2.06/0.99  merged_defs:                            8
% 2.06/0.99  merged_defs_ncl:                        0
% 2.06/0.99  bin_hyper_res:                          8
% 2.06/0.99  prep_cycles:                            4
% 2.06/0.99  pred_elim_time:                         0.054
% 2.06/0.99  splitting_time:                         0.
% 2.06/0.99  sem_filter_time:                        0.
% 2.06/0.99  monotx_time:                            0.001
% 2.06/0.99  subtype_inf_time:                       0.001
% 2.06/0.99  
% 2.06/0.99  ------ Problem properties
% 2.06/0.99  
% 2.06/0.99  clauses:                                24
% 2.06/0.99  conjectures:                            5
% 2.06/0.99  epr:                                    6
% 2.06/0.99  horn:                                   16
% 2.06/0.99  ground:                                 6
% 2.06/0.99  unary:                                  5
% 2.06/0.99  binary:                                 3
% 2.06/0.99  lits:                                   73
% 2.06/0.99  lits_eq:                                3
% 2.06/0.99  fd_pure:                                0
% 2.06/0.99  fd_pseudo:                              0
% 2.06/0.99  fd_cond:                                0
% 2.06/0.99  fd_pseudo_cond:                         2
% 2.06/0.99  ac_symbols:                             0
% 2.06/0.99  
% 2.06/0.99  ------ Propositional Solver
% 2.06/0.99  
% 2.06/0.99  prop_solver_calls:                      29
% 2.06/0.99  prop_fast_solver_calls:                 1725
% 2.06/0.99  smt_solver_calls:                       0
% 2.06/0.99  smt_fast_solver_calls:                  0
% 2.06/0.99  prop_num_of_clauses:                    1417
% 2.06/0.99  prop_preprocess_simplified:             6189
% 2.06/0.99  prop_fo_subsumed:                       49
% 2.06/0.99  prop_solver_time:                       0.
% 2.06/0.99  smt_solver_time:                        0.
% 2.06/0.99  smt_fast_solver_time:                   0.
% 2.06/0.99  prop_fast_solver_time:                  0.
% 2.06/0.99  prop_unsat_core_time:                   0.
% 2.06/0.99  
% 2.06/0.99  ------ QBF
% 2.06/0.99  
% 2.06/0.99  qbf_q_res:                              0
% 2.06/0.99  qbf_num_tautologies:                    0
% 2.06/0.99  qbf_prep_cycles:                        0
% 2.06/0.99  
% 2.06/0.99  ------ BMC1
% 2.06/0.99  
% 2.06/0.99  bmc1_current_bound:                     -1
% 2.06/0.99  bmc1_last_solved_bound:                 -1
% 2.06/0.99  bmc1_unsat_core_size:                   -1
% 2.06/0.99  bmc1_unsat_core_parents_size:           -1
% 2.06/0.99  bmc1_merge_next_fun:                    0
% 2.06/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.06/0.99  
% 2.06/0.99  ------ Instantiation
% 2.06/0.99  
% 2.06/0.99  inst_num_of_clauses:                    417
% 2.06/0.99  inst_num_in_passive:                    92
% 2.06/0.99  inst_num_in_active:                     249
% 2.06/0.99  inst_num_in_unprocessed:                77
% 2.06/0.99  inst_num_of_loops:                      260
% 2.06/0.99  inst_num_of_learning_restarts:          0
% 2.06/0.99  inst_num_moves_active_passive:          7
% 2.06/0.99  inst_lit_activity:                      0
% 2.06/0.99  inst_lit_activity_moves:                0
% 2.06/0.99  inst_num_tautologies:                   0
% 2.06/0.99  inst_num_prop_implied:                  0
% 2.06/0.99  inst_num_existing_simplified:           0
% 2.06/0.99  inst_num_eq_res_simplified:             0
% 2.06/0.99  inst_num_child_elim:                    0
% 2.06/0.99  inst_num_of_dismatching_blockings:      161
% 2.06/0.99  inst_num_of_non_proper_insts:           517
% 2.06/0.99  inst_num_of_duplicates:                 0
% 2.06/0.99  inst_inst_num_from_inst_to_res:         0
% 2.06/0.99  inst_dismatching_checking_time:         0.
% 2.06/0.99  
% 2.06/0.99  ------ Resolution
% 2.06/0.99  
% 2.06/0.99  res_num_of_clauses:                     0
% 2.06/0.99  res_num_in_passive:                     0
% 2.06/0.99  res_num_in_active:                      0
% 2.06/0.99  res_num_of_loops:                       134
% 2.06/0.99  res_forward_subset_subsumed:            79
% 2.06/0.99  res_backward_subset_subsumed:           2
% 2.06/0.99  res_forward_subsumed:                   2
% 2.06/0.99  res_backward_subsumed:                  0
% 2.06/0.99  res_forward_subsumption_resolution:     3
% 2.06/0.99  res_backward_subsumption_resolution:    0
% 2.06/0.99  res_clause_to_clause_subsumption:       172
% 2.06/0.99  res_orphan_elimination:                 0
% 2.06/0.99  res_tautology_del:                      105
% 2.06/0.99  res_num_eq_res_simplified:              0
% 2.06/0.99  res_num_sel_changes:                    0
% 2.06/0.99  res_moves_from_active_to_pass:          0
% 2.06/0.99  
% 2.06/0.99  ------ Superposition
% 2.06/0.99  
% 2.06/0.99  sup_time_total:                         0.
% 2.06/0.99  sup_time_generating:                    0.
% 2.06/0.99  sup_time_sim_full:                      0.
% 2.06/0.99  sup_time_sim_immed:                     0.
% 2.06/0.99  
% 2.06/0.99  sup_num_of_clauses:                     52
% 2.06/0.99  sup_num_in_active:                      40
% 2.06/0.99  sup_num_in_passive:                     12
% 2.06/0.99  sup_num_of_loops:                       51
% 2.06/0.99  sup_fw_superposition:                   20
% 2.06/0.99  sup_bw_superposition:                   44
% 2.06/0.99  sup_immediate_simplified:               14
% 2.06/0.99  sup_given_eliminated:                   1
% 2.06/0.99  comparisons_done:                       0
% 2.06/0.99  comparisons_avoided:                    3
% 2.06/0.99  
% 2.06/0.99  ------ Simplifications
% 2.06/0.99  
% 2.06/0.99  
% 2.06/0.99  sim_fw_subset_subsumed:                 12
% 2.06/0.99  sim_bw_subset_subsumed:                 7
% 2.06/0.99  sim_fw_subsumed:                        0
% 2.06/0.99  sim_bw_subsumed:                        0
% 2.06/0.99  sim_fw_subsumption_res:                 0
% 2.06/0.99  sim_bw_subsumption_res:                 1
% 2.06/0.99  sim_tautology_del:                      4
% 2.06/0.99  sim_eq_tautology_del:                   9
% 2.06/0.99  sim_eq_res_simp:                        0
% 2.06/0.99  sim_fw_demodulated:                     0
% 2.06/0.99  sim_bw_demodulated:                     9
% 2.06/0.99  sim_light_normalised:                   2
% 2.06/0.99  sim_joinable_taut:                      0
% 2.06/0.99  sim_joinable_simp:                      0
% 2.06/0.99  sim_ac_normalised:                      0
% 2.06/0.99  sim_smt_subsumption:                    0
% 2.06/0.99  
%------------------------------------------------------------------------------
