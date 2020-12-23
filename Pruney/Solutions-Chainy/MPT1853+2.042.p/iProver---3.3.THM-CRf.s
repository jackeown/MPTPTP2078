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
% DateTime   : Thu Dec  3 12:25:43 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :  220 (10876 expanded)
%              Number of clauses        :  151 (3366 expanded)
%              Number of leaves         :   19 (2159 expanded)
%              Depth                    :   31
%              Number of atoms          :  840 (56427 expanded)
%              Number of equality atoms :  309 (5811 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f25,plain,(
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

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f39,plain,(
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
    inference(rectify,[],[f38])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v1_subset_1(X2,u1_struct_0(X0))
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_subset_1(sK0(X0,X1),u1_struct_0(X0))
        & u1_struct_0(X1) = sK0(X0,X1)
        & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f39,f40])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( v1_subset_1(X3,u1_struct_0(X0))
      | u1_struct_0(X1) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( v1_tex_2(k1_tex_2(X0,X1),X0)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f46,plain,(
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

fof(f45,plain,
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

fof(f47,plain,
    ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
      | ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1) )
    & ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
      | v1_tex_2(k1_tex_2(sK1,sK2),sK1) )
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l1_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f44,f46,f45])).

fof(f69,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f67,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f66,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f68,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f47])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f70,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | ~ v1_subset_1(sK0(X0,X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( ~ v1_xboole_0(X1)
           => ~ v1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ~ v1_subset_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
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
    inference(ennf_transformation,[],[f3])).

fof(f50,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f11,axiom,(
    ! [X0] :
      ( ( ~ v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v1_subset_1(k6_domain_1(X0,X1),X0)
      | ~ m1_subset_1(X1,X0)
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f4,axiom,(
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
    inference(ennf_transformation,[],[f4])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f49,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | u1_struct_0(X1) = sK0(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ~ ( v7_struct_0(X0)
              & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v7_struct_0(X0)
          | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v7_struct_0(X0)
          | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ v7_struct_0(X0)
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v7_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_9,plain,
    ( ~ v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_134,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_tex_2(X0,X1)
    | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9,c_4])).

cnf(c_135,plain,
    ( ~ v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_134])).

cnf(c_19,negated_conjecture,
    ( v1_tex_2(k1_tex_2(sK1,sK2),sK1)
    | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_181,plain,
    ( v1_tex_2(k1_tex_2(sK1,sK2),sK1)
    | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) ),
    inference(prop_impl,[status(thm)],[c_19])).

cnf(c_803,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | k1_tex_2(sK1,sK2) != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_135,c_181])).

cnf(c_804,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
    | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_803])).

cnf(c_21,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_806,plain,
    ( v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1))
    | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_804,c_21])).

cnf(c_807,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
    | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_806])).

cnf(c_3469,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
    | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_807])).

cnf(c_3984,plain,
    ( m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top
    | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) = iProver_top
    | v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3469])).

cnf(c_22,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_23,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_24,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_25,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_805,plain,
    ( m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top
    | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) = iProver_top
    | v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1)) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_804])).

cnf(c_12,plain,
    ( m1_pre_topc(k1_tex_2(X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_3485,plain,
    ( m1_pre_topc(k1_tex_2(X0_45,X0_46),X0_45)
    | ~ m1_subset_1(X0_46,u1_struct_0(X0_45))
    | v2_struct_0(X0_45)
    | ~ l1_pre_topc(X0_45) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_3531,plain,
    ( m1_pre_topc(k1_tex_2(X0_45,X0_46),X0_45) = iProver_top
    | m1_subset_1(X0_46,u1_struct_0(X0_45)) != iProver_top
    | v2_struct_0(X0_45) = iProver_top
    | l1_pre_topc(X0_45) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3485])).

cnf(c_3533,plain,
    ( m1_pre_topc(k1_tex_2(sK1,sK2),sK1) = iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3531])).

cnf(c_5452,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) = iProver_top
    | v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3984,c_23,c_24,c_25,c_805,c_3533])).

cnf(c_8,plain,
    ( v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_18,negated_conjecture,
    ( ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_179,plain,
    ( ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) ),
    inference(prop_impl,[status(thm)],[c_18])).

cnf(c_752,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | ~ l1_pre_topc(X1)
    | k1_tex_2(sK1,sK2) != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_179])).

cnf(c_753,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
    | m1_subset_1(sK0(sK1,k1_tex_2(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_752])).

cnf(c_755,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | m1_subset_1(sK0(sK1,k1_tex_2(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_753,c_21])).

cnf(c_756,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
    | m1_subset_1(sK0(sK1,k1_tex_2(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_755])).

cnf(c_3472,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
    | m1_subset_1(sK0(sK1,k1_tex_2(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_756])).

cnf(c_3981,plain,
    ( m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top
    | m1_subset_1(sK0(sK1,k1_tex_2(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3472])).

cnf(c_3532,plain,
    ( m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_3485])).

cnf(c_3615,plain,
    ( m1_subset_1(sK0(sK1,k1_tex_2(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3472,c_22,c_21,c_20,c_753,c_3532])).

cnf(c_3617,plain,
    ( m1_subset_1(sK0(sK1,k1_tex_2(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3615])).

cnf(c_4809,plain,
    ( m1_subset_1(sK0(sK1,k1_tex_2(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3981,c_3617])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | v1_subset_1(X0,X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_3487,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(X1_46))
    | v1_subset_1(X0_46,X1_46)
    | X1_46 = X0_46 ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_3966,plain,
    ( X0_46 = X1_46
    | m1_subset_1(X1_46,k1_zfmisc_1(X0_46)) != iProver_top
    | v1_subset_1(X1_46,X0_46) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3487])).

cnf(c_4817,plain,
    ( sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(sK1)
    | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top
    | v1_subset_1(sK0(sK1,k1_tex_2(sK1,sK2)),u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4809,c_3966])).

cnf(c_6,plain,
    ( v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v1_subset_1(sK0(X1,X0),u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_786,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | ~ v1_subset_1(sK0(X1,X0),u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | k1_tex_2(sK1,sK2) != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_179])).

cnf(c_787,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | ~ v1_subset_1(sK0(sK1,k1_tex_2(sK1,sK2)),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_786])).

cnf(c_788,plain,
    ( m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top
    | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top
    | v1_subset_1(sK0(sK1,k1_tex_2(sK1,sK2)),u1_struct_0(sK1)) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_787])).

cnf(c_5594,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top
    | sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4817,c_23,c_24,c_25,c_788,c_3533])).

cnf(c_5595,plain,
    ( sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(sK1)
    | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5594])).

cnf(c_5600,plain,
    ( sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(sK1)
    | v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5452,c_5595])).

cnf(c_3488,plain,
    ( ~ m1_pre_topc(X0_45,X1_45)
    | m1_subset_1(u1_struct_0(X0_45),k1_zfmisc_1(u1_struct_0(X1_45)))
    | ~ l1_pre_topc(X1_45) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_3965,plain,
    ( m1_pre_topc(X0_45,X1_45) != iProver_top
    | m1_subset_1(u1_struct_0(X0_45),k1_zfmisc_1(u1_struct_0(X1_45))) = iProver_top
    | l1_pre_topc(X1_45) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3488])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_subset_1(X0,X1)
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_subset_1(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_144,plain,
    ( ~ v1_zfmisc_1(X1)
    | ~ v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5,c_0])).

cnf(c_145,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_subset_1(X0,X1)
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_144])).

cnf(c_3478,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(X1_46))
    | ~ v1_subset_1(X0_46,X1_46)
    | ~ v1_zfmisc_1(X1_46)
    | v1_xboole_0(X0_46) ),
    inference(subtyping,[status(esa)],[c_145])).

cnf(c_3975,plain,
    ( m1_subset_1(X0_46,k1_zfmisc_1(X1_46)) != iProver_top
    | v1_subset_1(X0_46,X1_46) != iProver_top
    | v1_zfmisc_1(X1_46) != iProver_top
    | v1_xboole_0(X0_46) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3478])).

cnf(c_4620,plain,
    ( m1_pre_topc(X0_45,X1_45) != iProver_top
    | v1_subset_1(u1_struct_0(X0_45),u1_struct_0(X1_45)) != iProver_top
    | v1_zfmisc_1(u1_struct_0(X1_45)) != iProver_top
    | l1_pre_topc(X1_45) != iProver_top
    | v1_xboole_0(u1_struct_0(X0_45)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3965,c_3975])).

cnf(c_5823,plain,
    ( sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(sK1)
    | m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK1)) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_xboole_0(u1_struct_0(k1_tex_2(sK1,sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5600,c_4620])).

cnf(c_3501,plain,
    ( u1_struct_0(X0_45) = u1_struct_0(X1_45)
    | X0_45 != X1_45 ),
    theory(equality)).

cnf(c_3513,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_3501])).

cnf(c_3492,plain,
    ( X0_45 = X0_45 ),
    theory(equality)).

cnf(c_3520,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_3492])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k1_tex_2(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_3484,plain,
    ( ~ m1_subset_1(X0_46,u1_struct_0(X0_45))
    | v2_struct_0(X0_45)
    | ~ v2_struct_0(k1_tex_2(X0_45,X0_46))
    | ~ l1_pre_topc(X0_45) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_3534,plain,
    ( m1_subset_1(X0_46,u1_struct_0(X0_45)) != iProver_top
    | v2_struct_0(X0_45) = iProver_top
    | v2_struct_0(k1_tex_2(X0_45,X0_46)) != iProver_top
    | l1_pre_topc(X0_45) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3484])).

cnf(c_3536,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | v2_struct_0(k1_tex_2(sK1,sK2)) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3534])).

cnf(c_2,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_3489,plain,
    ( ~ m1_pre_topc(X0_45,X1_45)
    | ~ l1_pre_topc(X1_45)
    | l1_pre_topc(X0_45) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_4327,plain,
    ( ~ m1_pre_topc(k1_tex_2(X0_45,X0_46),X1_45)
    | ~ l1_pre_topc(X1_45)
    | l1_pre_topc(k1_tex_2(X0_45,X0_46)) ),
    inference(instantiation,[status(thm)],[c_3489])).

cnf(c_4328,plain,
    ( m1_pre_topc(k1_tex_2(X0_45,X0_46),X1_45) != iProver_top
    | l1_pre_topc(X1_45) != iProver_top
    | l1_pre_topc(k1_tex_2(X0_45,X0_46)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4327])).

cnf(c_4330,plain,
    ( m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top
    | l1_pre_topc(k1_tex_2(sK1,sK2)) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4328])).

cnf(c_3494,plain,
    ( X0_46 != X1_46
    | X2_46 != X1_46
    | X2_46 = X0_46 ),
    theory(equality)).

cnf(c_4253,plain,
    ( X0_46 != X1_46
    | X0_46 = u1_struct_0(sK1)
    | u1_struct_0(sK1) != X1_46 ),
    inference(instantiation,[status(thm)],[c_3494])).

cnf(c_4390,plain,
    ( X0_46 != u1_struct_0(X0_45)
    | X0_46 = u1_struct_0(sK1)
    | u1_struct_0(sK1) != u1_struct_0(X0_45) ),
    inference(instantiation,[status(thm)],[c_4253])).

cnf(c_4472,plain,
    ( sK0(sK1,k1_tex_2(sK1,X0_46)) != u1_struct_0(k1_tex_2(sK1,X0_46))
    | sK0(sK1,k1_tex_2(sK1,X0_46)) = u1_struct_0(sK1)
    | u1_struct_0(sK1) != u1_struct_0(k1_tex_2(sK1,X0_46)) ),
    inference(instantiation,[status(thm)],[c_4390])).

cnf(c_4473,plain,
    ( sK0(sK1,k1_tex_2(sK1,sK2)) != u1_struct_0(k1_tex_2(sK1,sK2))
    | sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(sK1)
    | u1_struct_0(sK1) != u1_struct_0(k1_tex_2(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_4472])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_subset_1(k6_domain_1(X1,X0),X1)
    | v1_zfmisc_1(X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_3482,plain,
    ( ~ m1_subset_1(X0_46,X1_46)
    | v1_subset_1(k6_domain_1(X1_46,X0_46),X1_46)
    | v1_zfmisc_1(X1_46)
    | v1_xboole_0(X1_46) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_3971,plain,
    ( m1_subset_1(X0_46,X1_46) != iProver_top
    | v1_subset_1(k6_domain_1(X1_46,X0_46),X1_46) = iProver_top
    | v1_zfmisc_1(X1_46) = iProver_top
    | v1_xboole_0(X1_46) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3482])).

cnf(c_5601,plain,
    ( sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(sK1)
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK1)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3971,c_5595])).

cnf(c_3,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_66,plain,
    ( v2_struct_0(X0) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_68,plain,
    ( v2_struct_0(sK1) = iProver_top
    | l1_struct_0(sK1) != iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_66])).

cnf(c_1,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_70,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_72,plain,
    ( l1_pre_topc(sK1) != iProver_top
    | l1_struct_0(sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_70])).

cnf(c_5693,plain,
    ( v1_zfmisc_1(u1_struct_0(sK1)) = iProver_top
    | sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5601,c_23,c_24,c_25,c_68,c_72])).

cnf(c_5694,plain,
    ( sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(sK1)
    | v1_zfmisc_1(u1_struct_0(sK1)) = iProver_top ),
    inference(renaming,[status(thm)],[c_5693])).

cnf(c_4389,plain,
    ( X0_46 != X1_46
    | u1_struct_0(sK1) != X1_46
    | u1_struct_0(sK1) = X0_46 ),
    inference(instantiation,[status(thm)],[c_3494])).

cnf(c_4459,plain,
    ( X0_46 != u1_struct_0(sK1)
    | u1_struct_0(sK1) = X0_46
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_4389])).

cnf(c_4633,plain,
    ( u1_struct_0(X0_45) != u1_struct_0(sK1)
    | u1_struct_0(sK1) = u1_struct_0(X0_45)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_4459])).

cnf(c_6216,plain,
    ( u1_struct_0(k1_tex_2(sK1,X0_46)) != u1_struct_0(sK1)
    | u1_struct_0(sK1) = u1_struct_0(k1_tex_2(sK1,X0_46))
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_4633])).

cnf(c_6218,plain,
    ( u1_struct_0(k1_tex_2(sK1,sK2)) != u1_struct_0(sK1)
    | u1_struct_0(sK1) = u1_struct_0(k1_tex_2(sK1,sK2))
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_6216])).

cnf(c_3968,plain,
    ( m1_pre_topc(k1_tex_2(X0_45,X0_46),X0_45) = iProver_top
    | m1_subset_1(X0_46,u1_struct_0(X0_45)) != iProver_top
    | v2_struct_0(X0_45) = iProver_top
    | l1_pre_topc(X0_45) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3485])).

cnf(c_4342,plain,
    ( u1_struct_0(X0_45) = u1_struct_0(X1_45)
    | m1_pre_topc(X0_45,X1_45) != iProver_top
    | v1_subset_1(u1_struct_0(X0_45),u1_struct_0(X1_45)) = iProver_top
    | l1_pre_topc(X1_45) != iProver_top ),
    inference(superposition,[status(thm)],[c_3965,c_3966])).

cnf(c_5303,plain,
    ( u1_struct_0(X0_45) = u1_struct_0(X1_45)
    | m1_pre_topc(X0_45,X1_45) != iProver_top
    | v1_zfmisc_1(u1_struct_0(X1_45)) != iProver_top
    | l1_pre_topc(X1_45) != iProver_top
    | v1_xboole_0(u1_struct_0(X0_45)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4342,c_4620])).

cnf(c_5998,plain,
    ( u1_struct_0(k1_tex_2(X0_45,X0_46)) = u1_struct_0(X0_45)
    | m1_subset_1(X0_46,u1_struct_0(X0_45)) != iProver_top
    | v1_zfmisc_1(u1_struct_0(X0_45)) != iProver_top
    | v2_struct_0(X0_45) = iProver_top
    | l1_pre_topc(X0_45) != iProver_top
    | v1_xboole_0(u1_struct_0(k1_tex_2(X0_45,X0_46))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3968,c_5303])).

cnf(c_372,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_1,c_3])).

cnf(c_3477,plain,
    ( v2_struct_0(X0_45)
    | ~ l1_pre_topc(X0_45)
    | ~ v1_xboole_0(u1_struct_0(X0_45)) ),
    inference(subtyping,[status(esa)],[c_372])).

cnf(c_3976,plain,
    ( v2_struct_0(X0_45) = iProver_top
    | l1_pre_topc(X0_45) != iProver_top
    | v1_xboole_0(u1_struct_0(X0_45)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3477])).

cnf(c_6371,plain,
    ( u1_struct_0(k1_tex_2(X0_45,X0_46)) = u1_struct_0(X0_45)
    | m1_subset_1(X0_46,u1_struct_0(X0_45)) != iProver_top
    | v1_zfmisc_1(u1_struct_0(X0_45)) != iProver_top
    | v2_struct_0(X0_45) = iProver_top
    | v2_struct_0(k1_tex_2(X0_45,X0_46)) = iProver_top
    | l1_pre_topc(X0_45) != iProver_top
    | l1_pre_topc(k1_tex_2(X0_45,X0_46)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5998,c_3976])).

cnf(c_6373,plain,
    ( u1_struct_0(k1_tex_2(sK1,sK2)) = u1_struct_0(sK1)
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK1)) != iProver_top
    | v2_struct_0(k1_tex_2(sK1,sK2)) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(k1_tex_2(sK1,sK2)) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6371])).

cnf(c_7,plain,
    ( v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK0(X1,X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_717,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | sK0(X1,X0) = u1_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_7,c_135])).

cnf(c_3474,plain,
    ( ~ m1_pre_topc(X0_45,X1_45)
    | v1_subset_1(u1_struct_0(X0_45),u1_struct_0(X1_45))
    | ~ l1_pre_topc(X1_45)
    | sK0(X1_45,X0_45) = u1_struct_0(X0_45) ),
    inference(subtyping,[status(esa)],[c_717])).

cnf(c_3979,plain,
    ( sK0(X0_45,X1_45) = u1_struct_0(X1_45)
    | m1_pre_topc(X1_45,X0_45) != iProver_top
    | v1_subset_1(u1_struct_0(X1_45),u1_struct_0(X0_45)) = iProver_top
    | l1_pre_topc(X0_45) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3474])).

cnf(c_5304,plain,
    ( sK0(X0_45,X1_45) = u1_struct_0(X1_45)
    | m1_pre_topc(X1_45,X0_45) != iProver_top
    | v1_zfmisc_1(u1_struct_0(X0_45)) != iProver_top
    | l1_pre_topc(X0_45) != iProver_top
    | v1_xboole_0(u1_struct_0(X1_45)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3979,c_4620])).

cnf(c_6116,plain,
    ( sK0(X0_45,k1_tex_2(X0_45,X0_46)) = u1_struct_0(k1_tex_2(X0_45,X0_46))
    | m1_subset_1(X0_46,u1_struct_0(X0_45)) != iProver_top
    | v1_zfmisc_1(u1_struct_0(X0_45)) != iProver_top
    | v2_struct_0(X0_45) = iProver_top
    | l1_pre_topc(X0_45) != iProver_top
    | v1_xboole_0(u1_struct_0(k1_tex_2(X0_45,X0_46))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3968,c_5304])).

cnf(c_6495,plain,
    ( sK0(X0_45,k1_tex_2(X0_45,X0_46)) = u1_struct_0(k1_tex_2(X0_45,X0_46))
    | m1_subset_1(X0_46,u1_struct_0(X0_45)) != iProver_top
    | v1_zfmisc_1(u1_struct_0(X0_45)) != iProver_top
    | v2_struct_0(X0_45) = iProver_top
    | v2_struct_0(k1_tex_2(X0_45,X0_46)) = iProver_top
    | l1_pre_topc(X0_45) != iProver_top
    | l1_pre_topc(k1_tex_2(X0_45,X0_46)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6116,c_3976])).

cnf(c_6497,plain,
    ( sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(k1_tex_2(sK1,sK2))
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK1)) != iProver_top
    | v2_struct_0(k1_tex_2(sK1,sK2)) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(k1_tex_2(sK1,sK2)) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6495])).

cnf(c_6613,plain,
    ( sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5823,c_23,c_24,c_25,c_3513,c_3520,c_3533,c_3536,c_4330,c_4473,c_5694,c_6218,c_6373,c_6497])).

cnf(c_769,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | ~ l1_pre_topc(X1)
    | k1_tex_2(sK1,sK2) != X0
    | sK0(X1,X0) = u1_struct_0(X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_179])).

cnf(c_770,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(k1_tex_2(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_769])).

cnf(c_772,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
    | sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(k1_tex_2(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_770,c_21])).

cnf(c_773,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(k1_tex_2(sK1,sK2)) ),
    inference(renaming,[status(thm)],[c_772])).

cnf(c_3471,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(k1_tex_2(sK1,sK2)) ),
    inference(subtyping,[status(esa)],[c_773])).

cnf(c_3982,plain,
    ( sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(k1_tex_2(sK1,sK2))
    | m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top
    | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3471])).

cnf(c_3620,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(k1_tex_2(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3471,c_22,c_21,c_20,c_3532])).

cnf(c_3622,plain,
    ( sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(k1_tex_2(sK1,sK2))
    | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3620])).

cnf(c_4690,plain,
    ( sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(k1_tex_2(sK1,sK2))
    | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3982,c_3622])).

cnf(c_6620,plain,
    ( u1_struct_0(k1_tex_2(sK1,sK2)) = u1_struct_0(sK1)
    | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6613,c_4690])).

cnf(c_3535,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ v2_struct_0(k1_tex_2(sK1,sK2))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_3484])).

cnf(c_4329,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
    | l1_pre_topc(k1_tex_2(sK1,sK2))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_4327])).

cnf(c_6372,plain,
    ( ~ m1_subset_1(X0_46,u1_struct_0(X0_45))
    | ~ v1_zfmisc_1(u1_struct_0(X0_45))
    | v2_struct_0(X0_45)
    | v2_struct_0(k1_tex_2(X0_45,X0_46))
    | ~ l1_pre_topc(X0_45)
    | ~ l1_pre_topc(k1_tex_2(X0_45,X0_46))
    | u1_struct_0(k1_tex_2(X0_45,X0_46)) = u1_struct_0(X0_45) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6371])).

cnf(c_6374,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ v1_zfmisc_1(u1_struct_0(sK1))
    | v2_struct_0(k1_tex_2(sK1,sK2))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(k1_tex_2(sK1,sK2))
    | ~ l1_pre_topc(sK1)
    | u1_struct_0(k1_tex_2(sK1,sK2)) = u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_6372])).

cnf(c_4696,plain,
    ( sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(k1_tex_2(sK1,sK2))
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK1)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3971,c_4690])).

cnf(c_5587,plain,
    ( v1_zfmisc_1(u1_struct_0(sK1)) = iProver_top
    | sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(k1_tex_2(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4696,c_23,c_24,c_25,c_68,c_72])).

cnf(c_5588,plain,
    ( sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(k1_tex_2(sK1,sK2))
    | v1_zfmisc_1(u1_struct_0(sK1)) = iProver_top ),
    inference(renaming,[status(thm)],[c_5587])).

cnf(c_6617,plain,
    ( u1_struct_0(k1_tex_2(sK1,sK2)) = u1_struct_0(sK1)
    | v1_zfmisc_1(u1_struct_0(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6613,c_5588])).

cnf(c_6642,plain,
    ( v1_zfmisc_1(u1_struct_0(sK1))
    | u1_struct_0(k1_tex_2(sK1,sK2)) = u1_struct_0(sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6617])).

cnf(c_6803,plain,
    ( u1_struct_0(k1_tex_2(sK1,sK2)) = u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6620,c_22,c_21,c_20,c_3532,c_3535,c_4329,c_6374,c_6642])).

cnf(c_6823,plain,
    ( m1_pre_topc(k1_tex_2(sK1,sK2),X0_45) != iProver_top
    | v1_subset_1(u1_struct_0(sK1),u1_struct_0(X0_45)) != iProver_top
    | v1_zfmisc_1(u1_struct_0(X0_45)) != iProver_top
    | l1_pre_topc(X0_45) != iProver_top
    | v1_xboole_0(u1_struct_0(k1_tex_2(sK1,sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_6803,c_4620])).

cnf(c_6922,plain,
    ( m1_pre_topc(k1_tex_2(sK1,sK2),X0_45) != iProver_top
    | v1_subset_1(u1_struct_0(sK1),u1_struct_0(X0_45)) != iProver_top
    | v1_zfmisc_1(u1_struct_0(X0_45)) != iProver_top
    | l1_pre_topc(X0_45) != iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6823,c_6803])).

cnf(c_7040,plain,
    ( m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top
    | v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK1)) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK1)) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_6922])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(X1),X0),u1_struct_0(X1))
    | ~ v7_struct_0(X1)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_386,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(X1),X0),u1_struct_0(X1))
    | ~ v7_struct_0(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X2)
    | X2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_1])).

cnf(c_387,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(X1),X0),u1_struct_0(X1))
    | ~ v7_struct_0(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_386])).

cnf(c_3476,plain,
    ( ~ m1_subset_1(X0_46,u1_struct_0(X0_45))
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0_45),X0_46),u1_struct_0(X0_45))
    | ~ v7_struct_0(X0_45)
    | v2_struct_0(X0_45)
    | ~ l1_pre_topc(X0_45) ),
    inference(subtyping,[status(esa)],[c_387])).

cnf(c_3977,plain,
    ( m1_subset_1(X0_46,u1_struct_0(X0_45)) != iProver_top
    | v1_subset_1(k6_domain_1(u1_struct_0(X0_45),X0_46),u1_struct_0(X0_45)) != iProver_top
    | v7_struct_0(X0_45) != iProver_top
    | v2_struct_0(X0_45) = iProver_top
    | l1_pre_topc(X0_45) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3476])).

cnf(c_6827,plain,
    ( m1_subset_1(X0_46,u1_struct_0(k1_tex_2(sK1,sK2))) != iProver_top
    | v1_subset_1(k6_domain_1(u1_struct_0(sK1),X0_46),u1_struct_0(sK1)) != iProver_top
    | v7_struct_0(k1_tex_2(sK1,sK2)) != iProver_top
    | v2_struct_0(k1_tex_2(sK1,sK2)) = iProver_top
    | l1_pre_topc(k1_tex_2(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6803,c_3977])).

cnf(c_6886,plain,
    ( m1_subset_1(X0_46,u1_struct_0(sK1)) != iProver_top
    | v1_subset_1(k6_domain_1(u1_struct_0(sK1),X0_46),u1_struct_0(sK1)) != iProver_top
    | v7_struct_0(k1_tex_2(sK1,sK2)) != iProver_top
    | v2_struct_0(k1_tex_2(sK1,sK2)) = iProver_top
    | l1_pre_topc(k1_tex_2(sK1,sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6827,c_6803])).

cnf(c_7036,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top
    | v7_struct_0(k1_tex_2(sK1,sK2)) != iProver_top
    | v2_struct_0(k1_tex_2(sK1,sK2)) = iProver_top
    | l1_pre_topc(k1_tex_2(sK1,sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6886])).

cnf(c_6807,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) = iProver_top
    | v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6803,c_5452])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v7_struct_0(k1_tex_2(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_3483,plain,
    ( ~ m1_subset_1(X0_46,u1_struct_0(X0_45))
    | v7_struct_0(k1_tex_2(X0_45,X0_46))
    | v2_struct_0(X0_45)
    | ~ l1_pre_topc(X0_45) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_3537,plain,
    ( m1_subset_1(X0_46,u1_struct_0(X0_45)) != iProver_top
    | v7_struct_0(k1_tex_2(X0_45,X0_46)) = iProver_top
    | v2_struct_0(X0_45) = iProver_top
    | l1_pre_topc(X0_45) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3483])).

cnf(c_3539,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | v7_struct_0(k1_tex_2(sK1,sK2)) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3537])).

cnf(c_1830,plain,
    ( v1_subset_1(k6_domain_1(X0,X1),X0)
    | v1_zfmisc_1(X0)
    | v1_xboole_0(X0)
    | u1_struct_0(sK1) != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_20])).

cnf(c_1831,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | v1_zfmisc_1(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_1830])).

cnf(c_1832,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) = iProver_top
    | v1_zfmisc_1(u1_struct_0(sK1)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1831])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7040,c_7036,c_6807,c_4330,c_3539,c_3536,c_3533,c_1832,c_72,c_68,c_25,c_24,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:09:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.18/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.00  
% 2.18/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.18/1.00  
% 2.18/1.00  ------  iProver source info
% 2.18/1.00  
% 2.18/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.18/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.18/1.00  git: non_committed_changes: false
% 2.18/1.00  git: last_make_outside_of_git: false
% 2.18/1.00  
% 2.18/1.00  ------ 
% 2.18/1.00  
% 2.18/1.00  ------ Input Options
% 2.18/1.00  
% 2.18/1.00  --out_options                           all
% 2.18/1.00  --tptp_safe_out                         true
% 2.18/1.00  --problem_path                          ""
% 2.18/1.00  --include_path                          ""
% 2.18/1.00  --clausifier                            res/vclausify_rel
% 2.18/1.00  --clausifier_options                    --mode clausify
% 2.18/1.00  --stdin                                 false
% 2.18/1.00  --stats_out                             all
% 2.18/1.00  
% 2.18/1.00  ------ General Options
% 2.18/1.00  
% 2.18/1.00  --fof                                   false
% 2.18/1.00  --time_out_real                         305.
% 2.18/1.00  --time_out_virtual                      -1.
% 2.18/1.00  --symbol_type_check                     false
% 2.18/1.00  --clausify_out                          false
% 2.18/1.00  --sig_cnt_out                           false
% 2.18/1.00  --trig_cnt_out                          false
% 2.18/1.00  --trig_cnt_out_tolerance                1.
% 2.18/1.00  --trig_cnt_out_sk_spl                   false
% 2.18/1.00  --abstr_cl_out                          false
% 2.18/1.00  
% 2.18/1.00  ------ Global Options
% 2.18/1.00  
% 2.18/1.00  --schedule                              default
% 2.18/1.00  --add_important_lit                     false
% 2.18/1.00  --prop_solver_per_cl                    1000
% 2.18/1.00  --min_unsat_core                        false
% 2.18/1.00  --soft_assumptions                      false
% 2.18/1.00  --soft_lemma_size                       3
% 2.18/1.00  --prop_impl_unit_size                   0
% 2.18/1.00  --prop_impl_unit                        []
% 2.18/1.00  --share_sel_clauses                     true
% 2.18/1.00  --reset_solvers                         false
% 2.18/1.00  --bc_imp_inh                            [conj_cone]
% 2.18/1.00  --conj_cone_tolerance                   3.
% 2.18/1.00  --extra_neg_conj                        none
% 2.18/1.00  --large_theory_mode                     true
% 2.18/1.00  --prolific_symb_bound                   200
% 2.18/1.00  --lt_threshold                          2000
% 2.18/1.00  --clause_weak_htbl                      true
% 2.18/1.00  --gc_record_bc_elim                     false
% 2.18/1.00  
% 2.18/1.00  ------ Preprocessing Options
% 2.18/1.00  
% 2.18/1.00  --preprocessing_flag                    true
% 2.18/1.00  --time_out_prep_mult                    0.1
% 2.18/1.00  --splitting_mode                        input
% 2.18/1.00  --splitting_grd                         true
% 2.18/1.00  --splitting_cvd                         false
% 2.18/1.00  --splitting_cvd_svl                     false
% 2.18/1.00  --splitting_nvd                         32
% 2.18/1.00  --sub_typing                            true
% 2.18/1.00  --prep_gs_sim                           true
% 2.18/1.00  --prep_unflatten                        true
% 2.18/1.00  --prep_res_sim                          true
% 2.18/1.00  --prep_upred                            true
% 2.18/1.00  --prep_sem_filter                       exhaustive
% 2.18/1.00  --prep_sem_filter_out                   false
% 2.18/1.00  --pred_elim                             true
% 2.18/1.00  --res_sim_input                         true
% 2.18/1.00  --eq_ax_congr_red                       true
% 2.18/1.00  --pure_diseq_elim                       true
% 2.18/1.00  --brand_transform                       false
% 2.18/1.00  --non_eq_to_eq                          false
% 2.18/1.00  --prep_def_merge                        true
% 2.18/1.00  --prep_def_merge_prop_impl              false
% 2.18/1.00  --prep_def_merge_mbd                    true
% 2.18/1.00  --prep_def_merge_tr_red                 false
% 2.18/1.00  --prep_def_merge_tr_cl                  false
% 2.18/1.00  --smt_preprocessing                     true
% 2.18/1.00  --smt_ac_axioms                         fast
% 2.18/1.00  --preprocessed_out                      false
% 2.18/1.00  --preprocessed_stats                    false
% 2.18/1.00  
% 2.18/1.00  ------ Abstraction refinement Options
% 2.18/1.00  
% 2.18/1.00  --abstr_ref                             []
% 2.18/1.00  --abstr_ref_prep                        false
% 2.18/1.00  --abstr_ref_until_sat                   false
% 2.18/1.00  --abstr_ref_sig_restrict                funpre
% 2.18/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.18/1.00  --abstr_ref_under                       []
% 2.18/1.00  
% 2.18/1.00  ------ SAT Options
% 2.18/1.00  
% 2.18/1.00  --sat_mode                              false
% 2.18/1.00  --sat_fm_restart_options                ""
% 2.18/1.00  --sat_gr_def                            false
% 2.18/1.00  --sat_epr_types                         true
% 2.18/1.00  --sat_non_cyclic_types                  false
% 2.18/1.00  --sat_finite_models                     false
% 2.18/1.00  --sat_fm_lemmas                         false
% 2.18/1.00  --sat_fm_prep                           false
% 2.18/1.00  --sat_fm_uc_incr                        true
% 2.18/1.00  --sat_out_model                         small
% 2.18/1.00  --sat_out_clauses                       false
% 2.18/1.00  
% 2.18/1.00  ------ QBF Options
% 2.18/1.00  
% 2.18/1.00  --qbf_mode                              false
% 2.18/1.00  --qbf_elim_univ                         false
% 2.18/1.00  --qbf_dom_inst                          none
% 2.18/1.00  --qbf_dom_pre_inst                      false
% 2.18/1.00  --qbf_sk_in                             false
% 2.18/1.00  --qbf_pred_elim                         true
% 2.18/1.00  --qbf_split                             512
% 2.18/1.00  
% 2.18/1.00  ------ BMC1 Options
% 2.18/1.00  
% 2.18/1.00  --bmc1_incremental                      false
% 2.18/1.00  --bmc1_axioms                           reachable_all
% 2.18/1.00  --bmc1_min_bound                        0
% 2.18/1.00  --bmc1_max_bound                        -1
% 2.18/1.00  --bmc1_max_bound_default                -1
% 2.18/1.00  --bmc1_symbol_reachability              true
% 2.18/1.00  --bmc1_property_lemmas                  false
% 2.18/1.00  --bmc1_k_induction                      false
% 2.18/1.00  --bmc1_non_equiv_states                 false
% 2.18/1.00  --bmc1_deadlock                         false
% 2.18/1.00  --bmc1_ucm                              false
% 2.18/1.00  --bmc1_add_unsat_core                   none
% 2.18/1.00  --bmc1_unsat_core_children              false
% 2.18/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.18/1.00  --bmc1_out_stat                         full
% 2.18/1.00  --bmc1_ground_init                      false
% 2.18/1.00  --bmc1_pre_inst_next_state              false
% 2.18/1.00  --bmc1_pre_inst_state                   false
% 2.18/1.00  --bmc1_pre_inst_reach_state             false
% 2.18/1.00  --bmc1_out_unsat_core                   false
% 2.18/1.00  --bmc1_aig_witness_out                  false
% 2.18/1.00  --bmc1_verbose                          false
% 2.18/1.00  --bmc1_dump_clauses_tptp                false
% 2.18/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.18/1.00  --bmc1_dump_file                        -
% 2.18/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.18/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.18/1.00  --bmc1_ucm_extend_mode                  1
% 2.18/1.00  --bmc1_ucm_init_mode                    2
% 2.18/1.00  --bmc1_ucm_cone_mode                    none
% 2.18/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.18/1.00  --bmc1_ucm_relax_model                  4
% 2.18/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.18/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.18/1.00  --bmc1_ucm_layered_model                none
% 2.18/1.00  --bmc1_ucm_max_lemma_size               10
% 2.18/1.00  
% 2.18/1.00  ------ AIG Options
% 2.18/1.00  
% 2.18/1.00  --aig_mode                              false
% 2.18/1.00  
% 2.18/1.00  ------ Instantiation Options
% 2.18/1.00  
% 2.18/1.00  --instantiation_flag                    true
% 2.18/1.00  --inst_sos_flag                         false
% 2.18/1.00  --inst_sos_phase                        true
% 2.18/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.18/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.18/1.00  --inst_lit_sel_side                     num_symb
% 2.18/1.00  --inst_solver_per_active                1400
% 2.18/1.00  --inst_solver_calls_frac                1.
% 2.18/1.00  --inst_passive_queue_type               priority_queues
% 2.18/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.18/1.00  --inst_passive_queues_freq              [25;2]
% 2.18/1.00  --inst_dismatching                      true
% 2.18/1.00  --inst_eager_unprocessed_to_passive     true
% 2.18/1.00  --inst_prop_sim_given                   true
% 2.18/1.00  --inst_prop_sim_new                     false
% 2.18/1.00  --inst_subs_new                         false
% 2.18/1.00  --inst_eq_res_simp                      false
% 2.18/1.00  --inst_subs_given                       false
% 2.18/1.00  --inst_orphan_elimination               true
% 2.18/1.00  --inst_learning_loop_flag               true
% 2.18/1.00  --inst_learning_start                   3000
% 2.18/1.00  --inst_learning_factor                  2
% 2.18/1.00  --inst_start_prop_sim_after_learn       3
% 2.18/1.00  --inst_sel_renew                        solver
% 2.18/1.00  --inst_lit_activity_flag                true
% 2.18/1.00  --inst_restr_to_given                   false
% 2.18/1.00  --inst_activity_threshold               500
% 2.18/1.00  --inst_out_proof                        true
% 2.18/1.00  
% 2.18/1.00  ------ Resolution Options
% 2.18/1.00  
% 2.18/1.00  --resolution_flag                       true
% 2.18/1.00  --res_lit_sel                           adaptive
% 2.18/1.00  --res_lit_sel_side                      none
% 2.18/1.00  --res_ordering                          kbo
% 2.18/1.00  --res_to_prop_solver                    active
% 2.18/1.00  --res_prop_simpl_new                    false
% 2.18/1.00  --res_prop_simpl_given                  true
% 2.18/1.00  --res_passive_queue_type                priority_queues
% 2.18/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.18/1.00  --res_passive_queues_freq               [15;5]
% 2.18/1.00  --res_forward_subs                      full
% 2.18/1.00  --res_backward_subs                     full
% 2.18/1.00  --res_forward_subs_resolution           true
% 2.18/1.00  --res_backward_subs_resolution          true
% 2.18/1.00  --res_orphan_elimination                true
% 2.18/1.00  --res_time_limit                        2.
% 2.18/1.00  --res_out_proof                         true
% 2.18/1.00  
% 2.18/1.00  ------ Superposition Options
% 2.18/1.00  
% 2.18/1.00  --superposition_flag                    true
% 2.18/1.00  --sup_passive_queue_type                priority_queues
% 2.18/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.18/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.18/1.00  --demod_completeness_check              fast
% 2.18/1.00  --demod_use_ground                      true
% 2.18/1.00  --sup_to_prop_solver                    passive
% 2.18/1.00  --sup_prop_simpl_new                    true
% 2.18/1.00  --sup_prop_simpl_given                  true
% 2.18/1.00  --sup_fun_splitting                     false
% 2.18/1.00  --sup_smt_interval                      50000
% 2.18/1.00  
% 2.18/1.00  ------ Superposition Simplification Setup
% 2.18/1.00  
% 2.18/1.00  --sup_indices_passive                   []
% 2.18/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.18/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.18/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.18/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.18/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.18/1.00  --sup_full_bw                           [BwDemod]
% 2.18/1.00  --sup_immed_triv                        [TrivRules]
% 2.18/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.18/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.18/1.00  --sup_immed_bw_main                     []
% 2.18/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.18/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.18/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.18/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.18/1.00  
% 2.18/1.00  ------ Combination Options
% 2.18/1.00  
% 2.18/1.00  --comb_res_mult                         3
% 2.18/1.00  --comb_sup_mult                         2
% 2.18/1.00  --comb_inst_mult                        10
% 2.18/1.00  
% 2.18/1.00  ------ Debug Options
% 2.18/1.00  
% 2.18/1.00  --dbg_backtrace                         false
% 2.18/1.00  --dbg_dump_prop_clauses                 false
% 2.18/1.00  --dbg_dump_prop_clauses_file            -
% 2.18/1.00  --dbg_out_stat                          false
% 2.18/1.00  ------ Parsing...
% 2.18/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.18/1.00  
% 2.18/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.18/1.00  
% 2.18/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.18/1.00  
% 2.18/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.18/1.00  ------ Proving...
% 2.18/1.00  ------ Problem Properties 
% 2.18/1.00  
% 2.18/1.00  
% 2.18/1.00  clauses                                 22
% 2.18/1.00  conjectures                             3
% 2.18/1.00  EPR                                     3
% 2.18/1.00  Horn                                    15
% 2.18/1.00  unary                                   3
% 2.18/1.00  binary                                  1
% 2.18/1.00  lits                                    69
% 2.18/1.00  lits eq                                 3
% 2.18/1.00  fd_pure                                 0
% 2.18/1.00  fd_pseudo                               0
% 2.18/1.00  fd_cond                                 0
% 2.18/1.00  fd_pseudo_cond                          1
% 2.18/1.00  AC symbols                              0
% 2.18/1.00  
% 2.18/1.00  ------ Schedule dynamic 5 is on 
% 2.18/1.00  
% 2.18/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.18/1.00  
% 2.18/1.00  
% 2.18/1.00  ------ 
% 2.18/1.00  Current options:
% 2.18/1.00  ------ 
% 2.18/1.00  
% 2.18/1.00  ------ Input Options
% 2.18/1.00  
% 2.18/1.00  --out_options                           all
% 2.18/1.00  --tptp_safe_out                         true
% 2.18/1.00  --problem_path                          ""
% 2.18/1.00  --include_path                          ""
% 2.18/1.00  --clausifier                            res/vclausify_rel
% 2.18/1.00  --clausifier_options                    --mode clausify
% 2.18/1.00  --stdin                                 false
% 2.18/1.00  --stats_out                             all
% 2.18/1.00  
% 2.18/1.00  ------ General Options
% 2.18/1.00  
% 2.18/1.00  --fof                                   false
% 2.18/1.00  --time_out_real                         305.
% 2.18/1.00  --time_out_virtual                      -1.
% 2.18/1.00  --symbol_type_check                     false
% 2.18/1.00  --clausify_out                          false
% 2.18/1.00  --sig_cnt_out                           false
% 2.18/1.00  --trig_cnt_out                          false
% 2.18/1.00  --trig_cnt_out_tolerance                1.
% 2.18/1.00  --trig_cnt_out_sk_spl                   false
% 2.18/1.00  --abstr_cl_out                          false
% 2.18/1.00  
% 2.18/1.00  ------ Global Options
% 2.18/1.00  
% 2.18/1.00  --schedule                              default
% 2.18/1.00  --add_important_lit                     false
% 2.18/1.00  --prop_solver_per_cl                    1000
% 2.18/1.00  --min_unsat_core                        false
% 2.18/1.00  --soft_assumptions                      false
% 2.18/1.00  --soft_lemma_size                       3
% 2.18/1.00  --prop_impl_unit_size                   0
% 2.18/1.00  --prop_impl_unit                        []
% 2.18/1.00  --share_sel_clauses                     true
% 2.18/1.00  --reset_solvers                         false
% 2.18/1.00  --bc_imp_inh                            [conj_cone]
% 2.18/1.00  --conj_cone_tolerance                   3.
% 2.18/1.00  --extra_neg_conj                        none
% 2.18/1.00  --large_theory_mode                     true
% 2.18/1.00  --prolific_symb_bound                   200
% 2.18/1.00  --lt_threshold                          2000
% 2.18/1.00  --clause_weak_htbl                      true
% 2.18/1.00  --gc_record_bc_elim                     false
% 2.18/1.00  
% 2.18/1.00  ------ Preprocessing Options
% 2.18/1.00  
% 2.18/1.00  --preprocessing_flag                    true
% 2.18/1.00  --time_out_prep_mult                    0.1
% 2.18/1.00  --splitting_mode                        input
% 2.18/1.00  --splitting_grd                         true
% 2.18/1.00  --splitting_cvd                         false
% 2.18/1.00  --splitting_cvd_svl                     false
% 2.18/1.00  --splitting_nvd                         32
% 2.18/1.00  --sub_typing                            true
% 2.18/1.00  --prep_gs_sim                           true
% 2.18/1.00  --prep_unflatten                        true
% 2.18/1.00  --prep_res_sim                          true
% 2.18/1.00  --prep_upred                            true
% 2.18/1.00  --prep_sem_filter                       exhaustive
% 2.18/1.00  --prep_sem_filter_out                   false
% 2.18/1.00  --pred_elim                             true
% 2.18/1.00  --res_sim_input                         true
% 2.18/1.00  --eq_ax_congr_red                       true
% 2.18/1.00  --pure_diseq_elim                       true
% 2.18/1.00  --brand_transform                       false
% 2.18/1.00  --non_eq_to_eq                          false
% 2.18/1.00  --prep_def_merge                        true
% 2.18/1.00  --prep_def_merge_prop_impl              false
% 2.18/1.00  --prep_def_merge_mbd                    true
% 2.18/1.00  --prep_def_merge_tr_red                 false
% 2.18/1.00  --prep_def_merge_tr_cl                  false
% 2.18/1.00  --smt_preprocessing                     true
% 2.18/1.00  --smt_ac_axioms                         fast
% 2.18/1.00  --preprocessed_out                      false
% 2.18/1.00  --preprocessed_stats                    false
% 2.18/1.00  
% 2.18/1.00  ------ Abstraction refinement Options
% 2.18/1.00  
% 2.18/1.00  --abstr_ref                             []
% 2.18/1.00  --abstr_ref_prep                        false
% 2.18/1.00  --abstr_ref_until_sat                   false
% 2.18/1.00  --abstr_ref_sig_restrict                funpre
% 2.18/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.18/1.00  --abstr_ref_under                       []
% 2.18/1.00  
% 2.18/1.00  ------ SAT Options
% 2.18/1.00  
% 2.18/1.00  --sat_mode                              false
% 2.18/1.00  --sat_fm_restart_options                ""
% 2.18/1.00  --sat_gr_def                            false
% 2.18/1.00  --sat_epr_types                         true
% 2.18/1.00  --sat_non_cyclic_types                  false
% 2.18/1.00  --sat_finite_models                     false
% 2.18/1.00  --sat_fm_lemmas                         false
% 2.18/1.00  --sat_fm_prep                           false
% 2.18/1.00  --sat_fm_uc_incr                        true
% 2.18/1.00  --sat_out_model                         small
% 2.18/1.00  --sat_out_clauses                       false
% 2.18/1.00  
% 2.18/1.00  ------ QBF Options
% 2.18/1.00  
% 2.18/1.00  --qbf_mode                              false
% 2.18/1.00  --qbf_elim_univ                         false
% 2.18/1.00  --qbf_dom_inst                          none
% 2.18/1.00  --qbf_dom_pre_inst                      false
% 2.18/1.00  --qbf_sk_in                             false
% 2.18/1.00  --qbf_pred_elim                         true
% 2.18/1.00  --qbf_split                             512
% 2.18/1.00  
% 2.18/1.00  ------ BMC1 Options
% 2.18/1.00  
% 2.18/1.00  --bmc1_incremental                      false
% 2.18/1.00  --bmc1_axioms                           reachable_all
% 2.18/1.00  --bmc1_min_bound                        0
% 2.18/1.00  --bmc1_max_bound                        -1
% 2.18/1.00  --bmc1_max_bound_default                -1
% 2.18/1.00  --bmc1_symbol_reachability              true
% 2.18/1.00  --bmc1_property_lemmas                  false
% 2.18/1.00  --bmc1_k_induction                      false
% 2.18/1.00  --bmc1_non_equiv_states                 false
% 2.18/1.00  --bmc1_deadlock                         false
% 2.18/1.00  --bmc1_ucm                              false
% 2.18/1.00  --bmc1_add_unsat_core                   none
% 2.18/1.00  --bmc1_unsat_core_children              false
% 2.18/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.18/1.00  --bmc1_out_stat                         full
% 2.18/1.00  --bmc1_ground_init                      false
% 2.18/1.00  --bmc1_pre_inst_next_state              false
% 2.18/1.00  --bmc1_pre_inst_state                   false
% 2.18/1.00  --bmc1_pre_inst_reach_state             false
% 2.18/1.00  --bmc1_out_unsat_core                   false
% 2.18/1.00  --bmc1_aig_witness_out                  false
% 2.18/1.00  --bmc1_verbose                          false
% 2.18/1.00  --bmc1_dump_clauses_tptp                false
% 2.18/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.18/1.00  --bmc1_dump_file                        -
% 2.18/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.18/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.18/1.00  --bmc1_ucm_extend_mode                  1
% 2.18/1.00  --bmc1_ucm_init_mode                    2
% 2.18/1.00  --bmc1_ucm_cone_mode                    none
% 2.18/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.18/1.00  --bmc1_ucm_relax_model                  4
% 2.18/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.18/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.18/1.00  --bmc1_ucm_layered_model                none
% 2.18/1.00  --bmc1_ucm_max_lemma_size               10
% 2.18/1.00  
% 2.18/1.00  ------ AIG Options
% 2.18/1.00  
% 2.18/1.00  --aig_mode                              false
% 2.18/1.00  
% 2.18/1.00  ------ Instantiation Options
% 2.18/1.00  
% 2.18/1.00  --instantiation_flag                    true
% 2.18/1.00  --inst_sos_flag                         false
% 2.18/1.00  --inst_sos_phase                        true
% 2.18/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.18/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.18/1.00  --inst_lit_sel_side                     none
% 2.18/1.00  --inst_solver_per_active                1400
% 2.18/1.00  --inst_solver_calls_frac                1.
% 2.18/1.00  --inst_passive_queue_type               priority_queues
% 2.18/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.18/1.00  --inst_passive_queues_freq              [25;2]
% 2.18/1.00  --inst_dismatching                      true
% 2.18/1.00  --inst_eager_unprocessed_to_passive     true
% 2.18/1.00  --inst_prop_sim_given                   true
% 2.18/1.00  --inst_prop_sim_new                     false
% 2.18/1.00  --inst_subs_new                         false
% 2.18/1.00  --inst_eq_res_simp                      false
% 2.18/1.00  --inst_subs_given                       false
% 2.18/1.00  --inst_orphan_elimination               true
% 2.18/1.00  --inst_learning_loop_flag               true
% 2.18/1.00  --inst_learning_start                   3000
% 2.18/1.00  --inst_learning_factor                  2
% 2.18/1.00  --inst_start_prop_sim_after_learn       3
% 2.18/1.00  --inst_sel_renew                        solver
% 2.18/1.00  --inst_lit_activity_flag                true
% 2.18/1.00  --inst_restr_to_given                   false
% 2.18/1.00  --inst_activity_threshold               500
% 2.18/1.00  --inst_out_proof                        true
% 2.18/1.00  
% 2.18/1.00  ------ Resolution Options
% 2.18/1.00  
% 2.18/1.00  --resolution_flag                       false
% 2.18/1.00  --res_lit_sel                           adaptive
% 2.18/1.00  --res_lit_sel_side                      none
% 2.18/1.00  --res_ordering                          kbo
% 2.18/1.00  --res_to_prop_solver                    active
% 2.18/1.00  --res_prop_simpl_new                    false
% 2.18/1.00  --res_prop_simpl_given                  true
% 2.18/1.00  --res_passive_queue_type                priority_queues
% 2.18/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.18/1.00  --res_passive_queues_freq               [15;5]
% 2.18/1.00  --res_forward_subs                      full
% 2.18/1.00  --res_backward_subs                     full
% 2.18/1.00  --res_forward_subs_resolution           true
% 2.18/1.00  --res_backward_subs_resolution          true
% 2.18/1.00  --res_orphan_elimination                true
% 2.18/1.00  --res_time_limit                        2.
% 2.18/1.00  --res_out_proof                         true
% 2.18/1.00  
% 2.18/1.00  ------ Superposition Options
% 2.18/1.00  
% 2.18/1.00  --superposition_flag                    true
% 2.18/1.00  --sup_passive_queue_type                priority_queues
% 2.18/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.18/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.18/1.00  --demod_completeness_check              fast
% 2.18/1.00  --demod_use_ground                      true
% 2.18/1.00  --sup_to_prop_solver                    passive
% 2.18/1.00  --sup_prop_simpl_new                    true
% 2.18/1.00  --sup_prop_simpl_given                  true
% 2.18/1.00  --sup_fun_splitting                     false
% 2.18/1.00  --sup_smt_interval                      50000
% 2.18/1.00  
% 2.18/1.00  ------ Superposition Simplification Setup
% 2.18/1.00  
% 2.18/1.00  --sup_indices_passive                   []
% 2.18/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.18/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.18/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.18/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.18/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.18/1.00  --sup_full_bw                           [BwDemod]
% 2.18/1.00  --sup_immed_triv                        [TrivRules]
% 2.18/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.18/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.18/1.00  --sup_immed_bw_main                     []
% 2.18/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.18/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.18/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.18/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.18/1.00  
% 2.18/1.00  ------ Combination Options
% 2.18/1.00  
% 2.18/1.00  --comb_res_mult                         3
% 2.18/1.00  --comb_sup_mult                         2
% 2.18/1.00  --comb_inst_mult                        10
% 2.18/1.00  
% 2.18/1.00  ------ Debug Options
% 2.18/1.00  
% 2.18/1.00  --dbg_backtrace                         false
% 2.18/1.00  --dbg_dump_prop_clauses                 false
% 2.18/1.00  --dbg_dump_prop_clauses_file            -
% 2.18/1.00  --dbg_out_stat                          false
% 2.18/1.00  
% 2.18/1.00  
% 2.18/1.00  
% 2.18/1.00  
% 2.18/1.00  ------ Proving...
% 2.18/1.00  
% 2.18/1.00  
% 2.18/1.00  % SZS status Theorem for theBenchmark.p
% 2.18/1.00  
% 2.18/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.18/1.00  
% 2.18/1.00  fof(f7,axiom,(
% 2.18/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v1_subset_1(X2,u1_struct_0(X0)))))))),
% 2.18/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/1.00  
% 2.18/1.00  fof(f25,plain,(
% 2.18/1.00    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : ((v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.18/1.00    inference(ennf_transformation,[],[f7])).
% 2.18/1.00  
% 2.18/1.00  fof(f26,plain,(
% 2.18/1.00    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.18/1.00    inference(flattening,[],[f25])).
% 2.18/1.00  
% 2.18/1.00  fof(f38,plain,(
% 2.18/1.00    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.18/1.00    inference(nnf_transformation,[],[f26])).
% 2.18/1.00  
% 2.18/1.00  fof(f39,plain,(
% 2.18/1.00    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.18/1.00    inference(rectify,[],[f38])).
% 2.18/1.00  
% 2.18/1.00  fof(f40,plain,(
% 2.18/1.00    ! [X1,X0] : (? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_subset_1(sK0(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK0(X0,X1) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.18/1.00    introduced(choice_axiom,[])).
% 2.18/1.00  
% 2.18/1.00  fof(f41,plain,(
% 2.18/1.00    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | (~v1_subset_1(sK0(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK0(X0,X1) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.18/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f39,f40])).
% 2.18/1.00  
% 2.18/1.00  fof(f54,plain,(
% 2.18/1.00    ( ! [X0,X3,X1] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.18/1.00    inference(cnf_transformation,[],[f41])).
% 2.18/1.00  
% 2.18/1.00  fof(f71,plain,(
% 2.18/1.00    ( ! [X0,X1] : (v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.18/1.00    inference(equality_resolution,[],[f54])).
% 2.18/1.00  
% 2.18/1.00  fof(f5,axiom,(
% 2.18/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.18/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/1.00  
% 2.18/1.00  fof(f22,plain,(
% 2.18/1.00    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.18/1.00    inference(ennf_transformation,[],[f5])).
% 2.18/1.00  
% 2.18/1.00  fof(f52,plain,(
% 2.18/1.00    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.18/1.00    inference(cnf_transformation,[],[f22])).
% 2.18/1.00  
% 2.18/1.00  fof(f13,conjecture,(
% 2.18/1.00    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 2.18/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/1.00  
% 2.18/1.00  fof(f14,negated_conjecture,(
% 2.18/1.00    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 2.18/1.00    inference(negated_conjecture,[],[f13])).
% 2.18/1.00  
% 2.18/1.00  fof(f36,plain,(
% 2.18/1.00    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.18/1.00    inference(ennf_transformation,[],[f14])).
% 2.18/1.00  
% 2.18/1.00  fof(f37,plain,(
% 2.18/1.00    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.18/1.00    inference(flattening,[],[f36])).
% 2.18/1.00  
% 2.18/1.00  fof(f43,plain,(
% 2.18/1.00    ? [X0] : (? [X1] : (((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.18/1.00    inference(nnf_transformation,[],[f37])).
% 2.18/1.00  
% 2.18/1.00  fof(f44,plain,(
% 2.18/1.00    ? [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.18/1.00    inference(flattening,[],[f43])).
% 2.18/1.00  
% 2.18/1.00  fof(f46,plain,(
% 2.18/1.00    ( ! [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) => ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),sK2),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,sK2),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),sK2),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,sK2),X0)) & m1_subset_1(sK2,u1_struct_0(X0)))) )),
% 2.18/1.00    introduced(choice_axiom,[])).
% 2.18/1.00  
% 2.18/1.00  fof(f45,plain,(
% 2.18/1.00    ? [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(sK1),X1),u1_struct_0(sK1)) | ~v1_tex_2(k1_tex_2(sK1,X1),sK1)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK1),X1),u1_struct_0(sK1)) | v1_tex_2(k1_tex_2(sK1,X1),sK1)) & m1_subset_1(X1,u1_struct_0(sK1))) & l1_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 2.18/1.00    introduced(choice_axiom,[])).
% 2.18/1.00  
% 2.18/1.00  fof(f47,plain,(
% 2.18/1.00    ((~v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) | ~v1_tex_2(k1_tex_2(sK1,sK2),sK1)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) | v1_tex_2(k1_tex_2(sK1,sK2),sK1)) & m1_subset_1(sK2,u1_struct_0(sK1))) & l1_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 2.18/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f44,f46,f45])).
% 2.18/1.00  
% 2.18/1.00  fof(f69,plain,(
% 2.18/1.00    v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) | v1_tex_2(k1_tex_2(sK1,sK2),sK1)),
% 2.18/1.00    inference(cnf_transformation,[],[f47])).
% 2.18/1.00  
% 2.18/1.00  fof(f67,plain,(
% 2.18/1.00    l1_pre_topc(sK1)),
% 2.18/1.00    inference(cnf_transformation,[],[f47])).
% 2.18/1.00  
% 2.18/1.00  fof(f66,plain,(
% 2.18/1.00    ~v2_struct_0(sK1)),
% 2.18/1.00    inference(cnf_transformation,[],[f47])).
% 2.18/1.00  
% 2.18/1.00  fof(f68,plain,(
% 2.18/1.00    m1_subset_1(sK2,u1_struct_0(sK1))),
% 2.18/1.00    inference(cnf_transformation,[],[f47])).
% 2.18/1.00  
% 2.18/1.00  fof(f9,axiom,(
% 2.18/1.00    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 2.18/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/1.00  
% 2.18/1.00  fof(f16,plain,(
% 2.18/1.00    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 2.18/1.00    inference(pure_predicate_removal,[],[f9])).
% 2.18/1.00  
% 2.18/1.00  fof(f28,plain,(
% 2.18/1.00    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.18/1.00    inference(ennf_transformation,[],[f16])).
% 2.18/1.00  
% 2.18/1.00  fof(f29,plain,(
% 2.18/1.00    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.18/1.00    inference(flattening,[],[f28])).
% 2.18/1.00  
% 2.18/1.00  fof(f61,plain,(
% 2.18/1.00    ( ! [X0,X1] : (m1_pre_topc(k1_tex_2(X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.18/1.00    inference(cnf_transformation,[],[f29])).
% 2.18/1.00  
% 2.18/1.00  fof(f55,plain,(
% 2.18/1.00    ( ! [X0,X1] : (v1_tex_2(X1,X0) | m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.18/1.00    inference(cnf_transformation,[],[f41])).
% 2.18/1.00  
% 2.18/1.00  fof(f70,plain,(
% 2.18/1.00    ~v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) | ~v1_tex_2(k1_tex_2(sK1,sK2),sK1)),
% 2.18/1.00    inference(cnf_transformation,[],[f47])).
% 2.18/1.00  
% 2.18/1.00  fof(f8,axiom,(
% 2.18/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 2.18/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/1.00  
% 2.18/1.00  fof(f27,plain,(
% 2.18/1.00    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.18/1.00    inference(ennf_transformation,[],[f8])).
% 2.18/1.00  
% 2.18/1.00  fof(f42,plain,(
% 2.18/1.00    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.18/1.00    inference(nnf_transformation,[],[f27])).
% 2.18/1.00  
% 2.18/1.00  fof(f59,plain,(
% 2.18/1.00    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.18/1.00    inference(cnf_transformation,[],[f42])).
% 2.18/1.00  
% 2.18/1.00  fof(f57,plain,(
% 2.18/1.00    ( ! [X0,X1] : (v1_tex_2(X1,X0) | ~v1_subset_1(sK0(X0,X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.18/1.00    inference(cnf_transformation,[],[f41])).
% 2.18/1.00  
% 2.18/1.00  fof(f6,axiom,(
% 2.18/1.00    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (~v1_xboole_0(X1) => ~v1_subset_1(X1,X0))))),
% 2.18/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/1.00  
% 2.18/1.00  fof(f23,plain,(
% 2.18/1.00    ! [X0] : (! [X1] : ((~v1_subset_1(X1,X0) | v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | (~v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 2.18/1.00    inference(ennf_transformation,[],[f6])).
% 2.18/1.00  
% 2.18/1.00  fof(f24,plain,(
% 2.18/1.00    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 2.18/1.00    inference(flattening,[],[f23])).
% 2.18/1.00  
% 2.18/1.00  fof(f53,plain,(
% 2.18/1.00    ( ! [X0,X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 2.18/1.00    inference(cnf_transformation,[],[f24])).
% 2.18/1.00  
% 2.18/1.00  fof(f1,axiom,(
% 2.18/1.00    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~v1_subset_1(X1,X0)))),
% 2.18/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/1.00  
% 2.18/1.00  fof(f17,plain,(
% 2.18/1.00    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 2.18/1.00    inference(ennf_transformation,[],[f1])).
% 2.18/1.00  
% 2.18/1.00  fof(f48,plain,(
% 2.18/1.00    ( ! [X0,X1] : (~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 2.18/1.00    inference(cnf_transformation,[],[f17])).
% 2.18/1.00  
% 2.18/1.00  fof(f10,axiom,(
% 2.18/1.00    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 2.18/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/1.00  
% 2.18/1.00  fof(f15,plain,(
% 2.18/1.00    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 2.18/1.00    inference(pure_predicate_removal,[],[f10])).
% 2.18/1.00  
% 2.18/1.00  fof(f30,plain,(
% 2.18/1.00    ! [X0,X1] : ((v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.18/1.00    inference(ennf_transformation,[],[f15])).
% 2.18/1.00  
% 2.18/1.00  fof(f31,plain,(
% 2.18/1.00    ! [X0,X1] : ((v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.18/1.00    inference(flattening,[],[f30])).
% 2.18/1.00  
% 2.18/1.00  fof(f62,plain,(
% 2.18/1.00    ( ! [X0,X1] : (~v2_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.18/1.00    inference(cnf_transformation,[],[f31])).
% 2.18/1.00  
% 2.18/1.00  fof(f3,axiom,(
% 2.18/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.18/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/1.00  
% 2.18/1.00  fof(f19,plain,(
% 2.18/1.00    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.18/1.00    inference(ennf_transformation,[],[f3])).
% 2.18/1.00  
% 2.18/1.00  fof(f50,plain,(
% 2.18/1.00    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.18/1.00    inference(cnf_transformation,[],[f19])).
% 2.18/1.00  
% 2.18/1.00  fof(f11,axiom,(
% 2.18/1.00    ! [X0] : ((~v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,X0) => v1_subset_1(k6_domain_1(X0,X1),X0)))),
% 2.18/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/1.00  
% 2.18/1.00  fof(f32,plain,(
% 2.18/1.00    ! [X0] : (! [X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | (v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 2.18/1.00    inference(ennf_transformation,[],[f11])).
% 2.18/1.00  
% 2.18/1.00  fof(f33,plain,(
% 2.18/1.00    ! [X0] : (! [X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 2.18/1.00    inference(flattening,[],[f32])).
% 2.18/1.00  
% 2.18/1.00  fof(f64,plain,(
% 2.18/1.00    ( ! [X0,X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0) | v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 2.18/1.00    inference(cnf_transformation,[],[f33])).
% 2.18/1.00  
% 2.18/1.00  fof(f4,axiom,(
% 2.18/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.18/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/1.00  
% 2.18/1.00  fof(f20,plain,(
% 2.18/1.00    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.18/1.00    inference(ennf_transformation,[],[f4])).
% 2.18/1.00  
% 2.18/1.00  fof(f21,plain,(
% 2.18/1.00    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.18/1.00    inference(flattening,[],[f20])).
% 2.18/1.00  
% 2.18/1.00  fof(f51,plain,(
% 2.18/1.00    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.18/1.00    inference(cnf_transformation,[],[f21])).
% 2.18/1.00  
% 2.18/1.00  fof(f2,axiom,(
% 2.18/1.00    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.18/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/1.00  
% 2.18/1.00  fof(f18,plain,(
% 2.18/1.00    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.18/1.00    inference(ennf_transformation,[],[f2])).
% 2.18/1.00  
% 2.18/1.00  fof(f49,plain,(
% 2.18/1.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.18/1.00    inference(cnf_transformation,[],[f18])).
% 2.18/1.00  
% 2.18/1.00  fof(f56,plain,(
% 2.18/1.00    ( ! [X0,X1] : (v1_tex_2(X1,X0) | u1_struct_0(X1) = sK0(X0,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.18/1.00    inference(cnf_transformation,[],[f41])).
% 2.18/1.00  
% 2.18/1.00  fof(f12,axiom,(
% 2.18/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~(v7_struct_0(X0) & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 2.18/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/1.00  
% 2.18/1.00  fof(f34,plain,(
% 2.18/1.00    ! [X0] : (! [X1] : ((~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.18/1.00    inference(ennf_transformation,[],[f12])).
% 2.18/1.00  
% 2.18/1.00  fof(f35,plain,(
% 2.18/1.00    ! [X0] : (! [X1] : (~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.18/1.00    inference(flattening,[],[f34])).
% 2.18/1.00  
% 2.18/1.00  fof(f65,plain,(
% 2.18/1.00    ( ! [X0,X1] : (~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.18/1.00    inference(cnf_transformation,[],[f35])).
% 2.18/1.00  
% 2.18/1.00  fof(f63,plain,(
% 2.18/1.00    ( ! [X0,X1] : (v7_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.18/1.00    inference(cnf_transformation,[],[f31])).
% 2.18/1.00  
% 2.18/1.00  cnf(c_9,plain,
% 2.18/1.00      ( ~ v1_tex_2(X0,X1)
% 2.18/1.00      | ~ m1_pre_topc(X0,X1)
% 2.18/1.00      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.18/1.00      | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
% 2.18/1.00      | ~ l1_pre_topc(X1) ),
% 2.18/1.00      inference(cnf_transformation,[],[f71]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_4,plain,
% 2.18/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.18/1.00      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.18/1.00      | ~ l1_pre_topc(X1) ),
% 2.18/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_134,plain,
% 2.18/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.18/1.00      | ~ v1_tex_2(X0,X1)
% 2.18/1.00      | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
% 2.18/1.00      | ~ l1_pre_topc(X1) ),
% 2.18/1.00      inference(global_propositional_subsumption,[status(thm)],[c_9,c_4]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_135,plain,
% 2.18/1.00      ( ~ v1_tex_2(X0,X1)
% 2.18/1.00      | ~ m1_pre_topc(X0,X1)
% 2.18/1.00      | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
% 2.18/1.00      | ~ l1_pre_topc(X1) ),
% 2.18/1.00      inference(renaming,[status(thm)],[c_134]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_19,negated_conjecture,
% 2.18/1.00      ( v1_tex_2(k1_tex_2(sK1,sK2),sK1)
% 2.18/1.00      | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) ),
% 2.18/1.00      inference(cnf_transformation,[],[f69]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_181,plain,
% 2.18/1.00      ( v1_tex_2(k1_tex_2(sK1,sK2),sK1)
% 2.18/1.00      | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) ),
% 2.18/1.00      inference(prop_impl,[status(thm)],[c_19]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_803,plain,
% 2.18/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.18/1.00      | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 2.18/1.00      | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
% 2.18/1.00      | ~ l1_pre_topc(X1)
% 2.18/1.00      | k1_tex_2(sK1,sK2) != X0
% 2.18/1.00      | sK1 != X1 ),
% 2.18/1.00      inference(resolution_lifted,[status(thm)],[c_135,c_181]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_804,plain,
% 2.18/1.00      ( ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
% 2.18/1.00      | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 2.18/1.00      | v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1))
% 2.18/1.00      | ~ l1_pre_topc(sK1) ),
% 2.18/1.00      inference(unflattening,[status(thm)],[c_803]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_21,negated_conjecture,
% 2.18/1.00      ( l1_pre_topc(sK1) ),
% 2.18/1.00      inference(cnf_transformation,[],[f67]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_806,plain,
% 2.18/1.00      ( v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1))
% 2.18/1.00      | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 2.18/1.00      | ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1) ),
% 2.18/1.00      inference(global_propositional_subsumption,
% 2.18/1.00                [status(thm)],
% 2.18/1.00                [c_804,c_21]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_807,plain,
% 2.18/1.00      ( ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
% 2.18/1.00      | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 2.18/1.00      | v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1)) ),
% 2.18/1.00      inference(renaming,[status(thm)],[c_806]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_3469,plain,
% 2.18/1.00      ( ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
% 2.18/1.00      | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 2.18/1.00      | v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1)) ),
% 2.18/1.00      inference(subtyping,[status(esa)],[c_807]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_3984,plain,
% 2.18/1.00      ( m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top
% 2.18/1.00      | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) = iProver_top
% 2.18/1.00      | v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1)) = iProver_top ),
% 2.18/1.00      inference(predicate_to_equality,[status(thm)],[c_3469]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_22,negated_conjecture,
% 2.18/1.00      ( ~ v2_struct_0(sK1) ),
% 2.18/1.00      inference(cnf_transformation,[],[f66]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_23,plain,
% 2.18/1.00      ( v2_struct_0(sK1) != iProver_top ),
% 2.18/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_24,plain,
% 2.18/1.00      ( l1_pre_topc(sK1) = iProver_top ),
% 2.18/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_20,negated_conjecture,
% 2.18/1.00      ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 2.18/1.00      inference(cnf_transformation,[],[f68]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_25,plain,
% 2.18/1.00      ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
% 2.18/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_805,plain,
% 2.18/1.00      ( m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top
% 2.18/1.00      | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) = iProver_top
% 2.18/1.00      | v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1)) = iProver_top
% 2.18/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.18/1.00      inference(predicate_to_equality,[status(thm)],[c_804]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_12,plain,
% 2.18/1.00      ( m1_pre_topc(k1_tex_2(X0,X1),X0)
% 2.18/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.18/1.00      | v2_struct_0(X0)
% 2.18/1.00      | ~ l1_pre_topc(X0) ),
% 2.18/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_3485,plain,
% 2.18/1.00      ( m1_pre_topc(k1_tex_2(X0_45,X0_46),X0_45)
% 2.18/1.00      | ~ m1_subset_1(X0_46,u1_struct_0(X0_45))
% 2.18/1.00      | v2_struct_0(X0_45)
% 2.18/1.00      | ~ l1_pre_topc(X0_45) ),
% 2.18/1.00      inference(subtyping,[status(esa)],[c_12]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_3531,plain,
% 2.18/1.00      ( m1_pre_topc(k1_tex_2(X0_45,X0_46),X0_45) = iProver_top
% 2.18/1.00      | m1_subset_1(X0_46,u1_struct_0(X0_45)) != iProver_top
% 2.18/1.00      | v2_struct_0(X0_45) = iProver_top
% 2.18/1.00      | l1_pre_topc(X0_45) != iProver_top ),
% 2.18/1.00      inference(predicate_to_equality,[status(thm)],[c_3485]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_3533,plain,
% 2.18/1.00      ( m1_pre_topc(k1_tex_2(sK1,sK2),sK1) = iProver_top
% 2.18/1.00      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 2.18/1.00      | v2_struct_0(sK1) = iProver_top
% 2.18/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.18/1.00      inference(instantiation,[status(thm)],[c_3531]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_5452,plain,
% 2.18/1.00      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) = iProver_top
% 2.18/1.00      | v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1)) = iProver_top ),
% 2.18/1.00      inference(global_propositional_subsumption,
% 2.18/1.00                [status(thm)],
% 2.18/1.00                [c_3984,c_23,c_24,c_25,c_805,c_3533]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_8,plain,
% 2.18/1.00      ( v1_tex_2(X0,X1)
% 2.18/1.00      | ~ m1_pre_topc(X0,X1)
% 2.18/1.00      | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.18/1.00      | ~ l1_pre_topc(X1) ),
% 2.18/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_18,negated_conjecture,
% 2.18/1.00      ( ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1)
% 2.18/1.00      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) ),
% 2.18/1.00      inference(cnf_transformation,[],[f70]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_179,plain,
% 2.18/1.00      ( ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1)
% 2.18/1.00      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) ),
% 2.18/1.00      inference(prop_impl,[status(thm)],[c_18]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_752,plain,
% 2.18/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.18/1.00      | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.18/1.00      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 2.18/1.00      | ~ l1_pre_topc(X1)
% 2.18/1.00      | k1_tex_2(sK1,sK2) != X0
% 2.18/1.00      | sK1 != X1 ),
% 2.18/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_179]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_753,plain,
% 2.18/1.00      ( ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
% 2.18/1.00      | m1_subset_1(sK0(sK1,k1_tex_2(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.18/1.00      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 2.18/1.00      | ~ l1_pre_topc(sK1) ),
% 2.18/1.00      inference(unflattening,[status(thm)],[c_752]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_755,plain,
% 2.18/1.00      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 2.18/1.00      | m1_subset_1(sK0(sK1,k1_tex_2(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.18/1.00      | ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1) ),
% 2.18/1.00      inference(global_propositional_subsumption,
% 2.18/1.00                [status(thm)],
% 2.18/1.00                [c_753,c_21]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_756,plain,
% 2.18/1.00      ( ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
% 2.18/1.00      | m1_subset_1(sK0(sK1,k1_tex_2(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.18/1.00      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) ),
% 2.18/1.00      inference(renaming,[status(thm)],[c_755]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_3472,plain,
% 2.18/1.00      ( ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
% 2.18/1.00      | m1_subset_1(sK0(sK1,k1_tex_2(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.18/1.00      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) ),
% 2.18/1.00      inference(subtyping,[status(esa)],[c_756]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_3981,plain,
% 2.18/1.00      ( m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top
% 2.18/1.00      | m1_subset_1(sK0(sK1,k1_tex_2(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 2.18/1.00      | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top ),
% 2.18/1.00      inference(predicate_to_equality,[status(thm)],[c_3472]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_3532,plain,
% 2.18/1.00      ( m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
% 2.18/1.00      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 2.18/1.00      | v2_struct_0(sK1)
% 2.18/1.00      | ~ l1_pre_topc(sK1) ),
% 2.18/1.00      inference(instantiation,[status(thm)],[c_3485]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_3615,plain,
% 2.18/1.00      ( m1_subset_1(sK0(sK1,k1_tex_2(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.18/1.00      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) ),
% 2.18/1.00      inference(global_propositional_subsumption,
% 2.18/1.00                [status(thm)],
% 2.18/1.00                [c_3472,c_22,c_21,c_20,c_753,c_3532]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_3617,plain,
% 2.18/1.00      ( m1_subset_1(sK0(sK1,k1_tex_2(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 2.18/1.00      | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top ),
% 2.18/1.00      inference(predicate_to_equality,[status(thm)],[c_3615]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_4809,plain,
% 2.18/1.00      ( m1_subset_1(sK0(sK1,k1_tex_2(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 2.18/1.00      | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top ),
% 2.18/1.00      inference(global_propositional_subsumption,
% 2.18/1.00                [status(thm)],
% 2.18/1.00                [c_3981,c_3617]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_10,plain,
% 2.18/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.18/1.00      | v1_subset_1(X0,X1)
% 2.18/1.00      | X1 = X0 ),
% 2.18/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_3487,plain,
% 2.18/1.00      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(X1_46))
% 2.18/1.00      | v1_subset_1(X0_46,X1_46)
% 2.18/1.00      | X1_46 = X0_46 ),
% 2.18/1.00      inference(subtyping,[status(esa)],[c_10]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_3966,plain,
% 2.18/1.00      ( X0_46 = X1_46
% 2.18/1.00      | m1_subset_1(X1_46,k1_zfmisc_1(X0_46)) != iProver_top
% 2.18/1.00      | v1_subset_1(X1_46,X0_46) = iProver_top ),
% 2.18/1.00      inference(predicate_to_equality,[status(thm)],[c_3487]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_4817,plain,
% 2.18/1.00      ( sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(sK1)
% 2.18/1.00      | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top
% 2.18/1.00      | v1_subset_1(sK0(sK1,k1_tex_2(sK1,sK2)),u1_struct_0(sK1)) = iProver_top ),
% 2.18/1.00      inference(superposition,[status(thm)],[c_4809,c_3966]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_6,plain,
% 2.18/1.00      ( v1_tex_2(X0,X1)
% 2.18/1.00      | ~ m1_pre_topc(X0,X1)
% 2.18/1.00      | ~ v1_subset_1(sK0(X1,X0),u1_struct_0(X1))
% 2.18/1.00      | ~ l1_pre_topc(X1) ),
% 2.18/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_786,plain,
% 2.18/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.18/1.00      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 2.18/1.00      | ~ v1_subset_1(sK0(X1,X0),u1_struct_0(X1))
% 2.18/1.00      | ~ l1_pre_topc(X1)
% 2.18/1.00      | k1_tex_2(sK1,sK2) != X0
% 2.18/1.00      | sK1 != X1 ),
% 2.18/1.00      inference(resolution_lifted,[status(thm)],[c_6,c_179]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_787,plain,
% 2.18/1.00      ( ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
% 2.18/1.00      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 2.18/1.00      | ~ v1_subset_1(sK0(sK1,k1_tex_2(sK1,sK2)),u1_struct_0(sK1))
% 2.18/1.00      | ~ l1_pre_topc(sK1) ),
% 2.18/1.00      inference(unflattening,[status(thm)],[c_786]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_788,plain,
% 2.18/1.00      ( m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top
% 2.18/1.00      | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top
% 2.18/1.00      | v1_subset_1(sK0(sK1,k1_tex_2(sK1,sK2)),u1_struct_0(sK1)) != iProver_top
% 2.18/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.18/1.00      inference(predicate_to_equality,[status(thm)],[c_787]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_5594,plain,
% 2.18/1.00      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top
% 2.18/1.00      | sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(sK1) ),
% 2.18/1.00      inference(global_propositional_subsumption,
% 2.18/1.00                [status(thm)],
% 2.18/1.00                [c_4817,c_23,c_24,c_25,c_788,c_3533]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_5595,plain,
% 2.18/1.00      ( sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(sK1)
% 2.18/1.00      | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top ),
% 2.18/1.00      inference(renaming,[status(thm)],[c_5594]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_5600,plain,
% 2.18/1.00      ( sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(sK1)
% 2.18/1.00      | v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1)) = iProver_top ),
% 2.18/1.00      inference(superposition,[status(thm)],[c_5452,c_5595]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_3488,plain,
% 2.18/1.00      ( ~ m1_pre_topc(X0_45,X1_45)
% 2.18/1.00      | m1_subset_1(u1_struct_0(X0_45),k1_zfmisc_1(u1_struct_0(X1_45)))
% 2.18/1.00      | ~ l1_pre_topc(X1_45) ),
% 2.18/1.00      inference(subtyping,[status(esa)],[c_4]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_3965,plain,
% 2.18/1.00      ( m1_pre_topc(X0_45,X1_45) != iProver_top
% 2.18/1.00      | m1_subset_1(u1_struct_0(X0_45),k1_zfmisc_1(u1_struct_0(X1_45))) = iProver_top
% 2.18/1.00      | l1_pre_topc(X1_45) != iProver_top ),
% 2.18/1.00      inference(predicate_to_equality,[status(thm)],[c_3488]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_5,plain,
% 2.18/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.18/1.00      | ~ v1_subset_1(X0,X1)
% 2.18/1.00      | ~ v1_zfmisc_1(X1)
% 2.18/1.00      | v1_xboole_0(X1)
% 2.18/1.00      | v1_xboole_0(X0) ),
% 2.18/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_0,plain,
% 2.18/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.18/1.00      | ~ v1_subset_1(X0,X1)
% 2.18/1.00      | ~ v1_xboole_0(X1) ),
% 2.18/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_144,plain,
% 2.18/1.00      ( ~ v1_zfmisc_1(X1)
% 2.18/1.00      | ~ v1_subset_1(X0,X1)
% 2.18/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.18/1.00      | v1_xboole_0(X0) ),
% 2.18/1.00      inference(global_propositional_subsumption,[status(thm)],[c_5,c_0]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_145,plain,
% 2.18/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.18/1.00      | ~ v1_subset_1(X0,X1)
% 2.18/1.00      | ~ v1_zfmisc_1(X1)
% 2.18/1.00      | v1_xboole_0(X0) ),
% 2.18/1.00      inference(renaming,[status(thm)],[c_144]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_3478,plain,
% 2.18/1.00      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(X1_46))
% 2.18/1.00      | ~ v1_subset_1(X0_46,X1_46)
% 2.18/1.00      | ~ v1_zfmisc_1(X1_46)
% 2.18/1.00      | v1_xboole_0(X0_46) ),
% 2.18/1.00      inference(subtyping,[status(esa)],[c_145]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_3975,plain,
% 2.18/1.00      ( m1_subset_1(X0_46,k1_zfmisc_1(X1_46)) != iProver_top
% 2.18/1.00      | v1_subset_1(X0_46,X1_46) != iProver_top
% 2.18/1.00      | v1_zfmisc_1(X1_46) != iProver_top
% 2.18/1.00      | v1_xboole_0(X0_46) = iProver_top ),
% 2.18/1.00      inference(predicate_to_equality,[status(thm)],[c_3478]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_4620,plain,
% 2.18/1.00      ( m1_pre_topc(X0_45,X1_45) != iProver_top
% 2.18/1.00      | v1_subset_1(u1_struct_0(X0_45),u1_struct_0(X1_45)) != iProver_top
% 2.18/1.00      | v1_zfmisc_1(u1_struct_0(X1_45)) != iProver_top
% 2.18/1.00      | l1_pre_topc(X1_45) != iProver_top
% 2.18/1.00      | v1_xboole_0(u1_struct_0(X0_45)) = iProver_top ),
% 2.18/1.00      inference(superposition,[status(thm)],[c_3965,c_3975]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_5823,plain,
% 2.18/1.00      ( sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(sK1)
% 2.18/1.00      | m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top
% 2.18/1.00      | v1_zfmisc_1(u1_struct_0(sK1)) != iProver_top
% 2.18/1.00      | l1_pre_topc(sK1) != iProver_top
% 2.18/1.00      | v1_xboole_0(u1_struct_0(k1_tex_2(sK1,sK2))) = iProver_top ),
% 2.18/1.00      inference(superposition,[status(thm)],[c_5600,c_4620]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_3501,plain,
% 2.18/1.00      ( u1_struct_0(X0_45) = u1_struct_0(X1_45) | X0_45 != X1_45 ),
% 2.18/1.00      theory(equality) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_3513,plain,
% 2.18/1.00      ( u1_struct_0(sK1) = u1_struct_0(sK1) | sK1 != sK1 ),
% 2.18/1.00      inference(instantiation,[status(thm)],[c_3501]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_3492,plain,( X0_45 = X0_45 ),theory(equality) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_3520,plain,
% 2.18/1.00      ( sK1 = sK1 ),
% 2.18/1.00      inference(instantiation,[status(thm)],[c_3492]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_15,plain,
% 2.18/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.18/1.00      | v2_struct_0(X1)
% 2.18/1.00      | ~ v2_struct_0(k1_tex_2(X1,X0))
% 2.18/1.00      | ~ l1_pre_topc(X1) ),
% 2.18/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_3484,plain,
% 2.18/1.00      ( ~ m1_subset_1(X0_46,u1_struct_0(X0_45))
% 2.18/1.00      | v2_struct_0(X0_45)
% 2.18/1.00      | ~ v2_struct_0(k1_tex_2(X0_45,X0_46))
% 2.18/1.00      | ~ l1_pre_topc(X0_45) ),
% 2.18/1.00      inference(subtyping,[status(esa)],[c_15]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_3534,plain,
% 2.18/1.00      ( m1_subset_1(X0_46,u1_struct_0(X0_45)) != iProver_top
% 2.18/1.00      | v2_struct_0(X0_45) = iProver_top
% 2.18/1.00      | v2_struct_0(k1_tex_2(X0_45,X0_46)) != iProver_top
% 2.18/1.00      | l1_pre_topc(X0_45) != iProver_top ),
% 2.18/1.00      inference(predicate_to_equality,[status(thm)],[c_3484]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_3536,plain,
% 2.18/1.00      ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 2.18/1.00      | v2_struct_0(k1_tex_2(sK1,sK2)) != iProver_top
% 2.18/1.00      | v2_struct_0(sK1) = iProver_top
% 2.18/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.18/1.00      inference(instantiation,[status(thm)],[c_3534]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_2,plain,
% 2.18/1.00      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.18/1.00      inference(cnf_transformation,[],[f50]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_3489,plain,
% 2.18/1.00      ( ~ m1_pre_topc(X0_45,X1_45)
% 2.18/1.00      | ~ l1_pre_topc(X1_45)
% 2.18/1.00      | l1_pre_topc(X0_45) ),
% 2.18/1.00      inference(subtyping,[status(esa)],[c_2]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_4327,plain,
% 2.18/1.00      ( ~ m1_pre_topc(k1_tex_2(X0_45,X0_46),X1_45)
% 2.18/1.00      | ~ l1_pre_topc(X1_45)
% 2.18/1.00      | l1_pre_topc(k1_tex_2(X0_45,X0_46)) ),
% 2.18/1.00      inference(instantiation,[status(thm)],[c_3489]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_4328,plain,
% 2.18/1.00      ( m1_pre_topc(k1_tex_2(X0_45,X0_46),X1_45) != iProver_top
% 2.18/1.00      | l1_pre_topc(X1_45) != iProver_top
% 2.18/1.00      | l1_pre_topc(k1_tex_2(X0_45,X0_46)) = iProver_top ),
% 2.18/1.00      inference(predicate_to_equality,[status(thm)],[c_4327]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_4330,plain,
% 2.18/1.00      ( m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top
% 2.18/1.00      | l1_pre_topc(k1_tex_2(sK1,sK2)) = iProver_top
% 2.18/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.18/1.00      inference(instantiation,[status(thm)],[c_4328]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_3494,plain,
% 2.18/1.00      ( X0_46 != X1_46 | X2_46 != X1_46 | X2_46 = X0_46 ),
% 2.18/1.00      theory(equality) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_4253,plain,
% 2.18/1.00      ( X0_46 != X1_46
% 2.18/1.00      | X0_46 = u1_struct_0(sK1)
% 2.18/1.00      | u1_struct_0(sK1) != X1_46 ),
% 2.18/1.00      inference(instantiation,[status(thm)],[c_3494]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_4390,plain,
% 2.18/1.00      ( X0_46 != u1_struct_0(X0_45)
% 2.18/1.00      | X0_46 = u1_struct_0(sK1)
% 2.18/1.00      | u1_struct_0(sK1) != u1_struct_0(X0_45) ),
% 2.18/1.00      inference(instantiation,[status(thm)],[c_4253]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_4472,plain,
% 2.18/1.00      ( sK0(sK1,k1_tex_2(sK1,X0_46)) != u1_struct_0(k1_tex_2(sK1,X0_46))
% 2.18/1.00      | sK0(sK1,k1_tex_2(sK1,X0_46)) = u1_struct_0(sK1)
% 2.18/1.00      | u1_struct_0(sK1) != u1_struct_0(k1_tex_2(sK1,X0_46)) ),
% 2.18/1.00      inference(instantiation,[status(thm)],[c_4390]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_4473,plain,
% 2.18/1.00      ( sK0(sK1,k1_tex_2(sK1,sK2)) != u1_struct_0(k1_tex_2(sK1,sK2))
% 2.18/1.00      | sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(sK1)
% 2.18/1.00      | u1_struct_0(sK1) != u1_struct_0(k1_tex_2(sK1,sK2)) ),
% 2.18/1.00      inference(instantiation,[status(thm)],[c_4472]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_16,plain,
% 2.18/1.00      ( ~ m1_subset_1(X0,X1)
% 2.18/1.00      | v1_subset_1(k6_domain_1(X1,X0),X1)
% 2.18/1.00      | v1_zfmisc_1(X1)
% 2.18/1.00      | v1_xboole_0(X1) ),
% 2.18/1.00      inference(cnf_transformation,[],[f64]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_3482,plain,
% 2.18/1.00      ( ~ m1_subset_1(X0_46,X1_46)
% 2.18/1.00      | v1_subset_1(k6_domain_1(X1_46,X0_46),X1_46)
% 2.18/1.00      | v1_zfmisc_1(X1_46)
% 2.18/1.00      | v1_xboole_0(X1_46) ),
% 2.18/1.00      inference(subtyping,[status(esa)],[c_16]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_3971,plain,
% 2.18/1.00      ( m1_subset_1(X0_46,X1_46) != iProver_top
% 2.18/1.00      | v1_subset_1(k6_domain_1(X1_46,X0_46),X1_46) = iProver_top
% 2.18/1.00      | v1_zfmisc_1(X1_46) = iProver_top
% 2.18/1.00      | v1_xboole_0(X1_46) = iProver_top ),
% 2.18/1.00      inference(predicate_to_equality,[status(thm)],[c_3482]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_5601,plain,
% 2.18/1.00      ( sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(sK1)
% 2.18/1.00      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 2.18/1.00      | v1_zfmisc_1(u1_struct_0(sK1)) = iProver_top
% 2.18/1.00      | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
% 2.18/1.00      inference(superposition,[status(thm)],[c_3971,c_5595]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_3,plain,
% 2.18/1.00      ( v2_struct_0(X0)
% 2.18/1.00      | ~ l1_struct_0(X0)
% 2.18/1.00      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.18/1.00      inference(cnf_transformation,[],[f51]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_66,plain,
% 2.18/1.00      ( v2_struct_0(X0) = iProver_top
% 2.18/1.00      | l1_struct_0(X0) != iProver_top
% 2.18/1.00      | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
% 2.18/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_68,plain,
% 2.18/1.00      ( v2_struct_0(sK1) = iProver_top
% 2.18/1.00      | l1_struct_0(sK1) != iProver_top
% 2.18/1.00      | v1_xboole_0(u1_struct_0(sK1)) != iProver_top ),
% 2.18/1.00      inference(instantiation,[status(thm)],[c_66]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_1,plain,
% 2.18/1.00      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 2.18/1.00      inference(cnf_transformation,[],[f49]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_70,plain,
% 2.18/1.00      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 2.18/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_72,plain,
% 2.18/1.00      ( l1_pre_topc(sK1) != iProver_top
% 2.18/1.00      | l1_struct_0(sK1) = iProver_top ),
% 2.18/1.00      inference(instantiation,[status(thm)],[c_70]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_5693,plain,
% 2.18/1.00      ( v1_zfmisc_1(u1_struct_0(sK1)) = iProver_top
% 2.18/1.00      | sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(sK1) ),
% 2.18/1.00      inference(global_propositional_subsumption,
% 2.18/1.00                [status(thm)],
% 2.18/1.00                [c_5601,c_23,c_24,c_25,c_68,c_72]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_5694,plain,
% 2.18/1.00      ( sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(sK1)
% 2.18/1.00      | v1_zfmisc_1(u1_struct_0(sK1)) = iProver_top ),
% 2.18/1.00      inference(renaming,[status(thm)],[c_5693]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_4389,plain,
% 2.18/1.00      ( X0_46 != X1_46
% 2.18/1.00      | u1_struct_0(sK1) != X1_46
% 2.18/1.00      | u1_struct_0(sK1) = X0_46 ),
% 2.18/1.00      inference(instantiation,[status(thm)],[c_3494]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_4459,plain,
% 2.18/1.00      ( X0_46 != u1_struct_0(sK1)
% 2.18/1.00      | u1_struct_0(sK1) = X0_46
% 2.18/1.00      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 2.18/1.00      inference(instantiation,[status(thm)],[c_4389]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_4633,plain,
% 2.18/1.00      ( u1_struct_0(X0_45) != u1_struct_0(sK1)
% 2.18/1.00      | u1_struct_0(sK1) = u1_struct_0(X0_45)
% 2.18/1.00      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 2.18/1.00      inference(instantiation,[status(thm)],[c_4459]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_6216,plain,
% 2.18/1.00      ( u1_struct_0(k1_tex_2(sK1,X0_46)) != u1_struct_0(sK1)
% 2.18/1.00      | u1_struct_0(sK1) = u1_struct_0(k1_tex_2(sK1,X0_46))
% 2.18/1.00      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 2.18/1.00      inference(instantiation,[status(thm)],[c_4633]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_6218,plain,
% 2.18/1.00      ( u1_struct_0(k1_tex_2(sK1,sK2)) != u1_struct_0(sK1)
% 2.18/1.00      | u1_struct_0(sK1) = u1_struct_0(k1_tex_2(sK1,sK2))
% 2.18/1.00      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 2.18/1.00      inference(instantiation,[status(thm)],[c_6216]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_3968,plain,
% 2.18/1.00      ( m1_pre_topc(k1_tex_2(X0_45,X0_46),X0_45) = iProver_top
% 2.18/1.00      | m1_subset_1(X0_46,u1_struct_0(X0_45)) != iProver_top
% 2.18/1.00      | v2_struct_0(X0_45) = iProver_top
% 2.18/1.00      | l1_pre_topc(X0_45) != iProver_top ),
% 2.18/1.00      inference(predicate_to_equality,[status(thm)],[c_3485]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_4342,plain,
% 2.18/1.00      ( u1_struct_0(X0_45) = u1_struct_0(X1_45)
% 2.18/1.00      | m1_pre_topc(X0_45,X1_45) != iProver_top
% 2.18/1.00      | v1_subset_1(u1_struct_0(X0_45),u1_struct_0(X1_45)) = iProver_top
% 2.18/1.00      | l1_pre_topc(X1_45) != iProver_top ),
% 2.18/1.00      inference(superposition,[status(thm)],[c_3965,c_3966]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_5303,plain,
% 2.18/1.00      ( u1_struct_0(X0_45) = u1_struct_0(X1_45)
% 2.18/1.00      | m1_pre_topc(X0_45,X1_45) != iProver_top
% 2.18/1.00      | v1_zfmisc_1(u1_struct_0(X1_45)) != iProver_top
% 2.18/1.00      | l1_pre_topc(X1_45) != iProver_top
% 2.18/1.00      | v1_xboole_0(u1_struct_0(X0_45)) = iProver_top ),
% 2.18/1.00      inference(superposition,[status(thm)],[c_4342,c_4620]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_5998,plain,
% 2.18/1.00      ( u1_struct_0(k1_tex_2(X0_45,X0_46)) = u1_struct_0(X0_45)
% 2.18/1.00      | m1_subset_1(X0_46,u1_struct_0(X0_45)) != iProver_top
% 2.18/1.00      | v1_zfmisc_1(u1_struct_0(X0_45)) != iProver_top
% 2.18/1.00      | v2_struct_0(X0_45) = iProver_top
% 2.18/1.00      | l1_pre_topc(X0_45) != iProver_top
% 2.18/1.00      | v1_xboole_0(u1_struct_0(k1_tex_2(X0_45,X0_46))) = iProver_top ),
% 2.18/1.00      inference(superposition,[status(thm)],[c_3968,c_5303]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_372,plain,
% 2.18/1.00      ( v2_struct_0(X0)
% 2.18/1.00      | ~ l1_pre_topc(X0)
% 2.18/1.00      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.18/1.00      inference(resolution,[status(thm)],[c_1,c_3]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_3477,plain,
% 2.18/1.00      ( v2_struct_0(X0_45)
% 2.18/1.00      | ~ l1_pre_topc(X0_45)
% 2.18/1.00      | ~ v1_xboole_0(u1_struct_0(X0_45)) ),
% 2.18/1.00      inference(subtyping,[status(esa)],[c_372]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_3976,plain,
% 2.18/1.00      ( v2_struct_0(X0_45) = iProver_top
% 2.18/1.00      | l1_pre_topc(X0_45) != iProver_top
% 2.18/1.00      | v1_xboole_0(u1_struct_0(X0_45)) != iProver_top ),
% 2.18/1.00      inference(predicate_to_equality,[status(thm)],[c_3477]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_6371,plain,
% 2.18/1.00      ( u1_struct_0(k1_tex_2(X0_45,X0_46)) = u1_struct_0(X0_45)
% 2.18/1.00      | m1_subset_1(X0_46,u1_struct_0(X0_45)) != iProver_top
% 2.18/1.00      | v1_zfmisc_1(u1_struct_0(X0_45)) != iProver_top
% 2.18/1.00      | v2_struct_0(X0_45) = iProver_top
% 2.18/1.00      | v2_struct_0(k1_tex_2(X0_45,X0_46)) = iProver_top
% 2.18/1.00      | l1_pre_topc(X0_45) != iProver_top
% 2.18/1.00      | l1_pre_topc(k1_tex_2(X0_45,X0_46)) != iProver_top ),
% 2.18/1.00      inference(superposition,[status(thm)],[c_5998,c_3976]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_6373,plain,
% 2.18/1.00      ( u1_struct_0(k1_tex_2(sK1,sK2)) = u1_struct_0(sK1)
% 2.18/1.00      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 2.18/1.00      | v1_zfmisc_1(u1_struct_0(sK1)) != iProver_top
% 2.18/1.00      | v2_struct_0(k1_tex_2(sK1,sK2)) = iProver_top
% 2.18/1.00      | v2_struct_0(sK1) = iProver_top
% 2.18/1.00      | l1_pre_topc(k1_tex_2(sK1,sK2)) != iProver_top
% 2.18/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.18/1.00      inference(instantiation,[status(thm)],[c_6371]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_7,plain,
% 2.18/1.00      ( v1_tex_2(X0,X1)
% 2.18/1.00      | ~ m1_pre_topc(X0,X1)
% 2.18/1.00      | ~ l1_pre_topc(X1)
% 2.18/1.00      | sK0(X1,X0) = u1_struct_0(X0) ),
% 2.18/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_717,plain,
% 2.18/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.18/1.00      | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
% 2.18/1.00      | ~ l1_pre_topc(X1)
% 2.18/1.00      | sK0(X1,X0) = u1_struct_0(X0) ),
% 2.18/1.00      inference(resolution,[status(thm)],[c_7,c_135]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_3474,plain,
% 2.18/1.00      ( ~ m1_pre_topc(X0_45,X1_45)
% 2.18/1.00      | v1_subset_1(u1_struct_0(X0_45),u1_struct_0(X1_45))
% 2.18/1.00      | ~ l1_pre_topc(X1_45)
% 2.18/1.00      | sK0(X1_45,X0_45) = u1_struct_0(X0_45) ),
% 2.18/1.00      inference(subtyping,[status(esa)],[c_717]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_3979,plain,
% 2.18/1.00      ( sK0(X0_45,X1_45) = u1_struct_0(X1_45)
% 2.18/1.00      | m1_pre_topc(X1_45,X0_45) != iProver_top
% 2.18/1.00      | v1_subset_1(u1_struct_0(X1_45),u1_struct_0(X0_45)) = iProver_top
% 2.18/1.00      | l1_pre_topc(X0_45) != iProver_top ),
% 2.18/1.00      inference(predicate_to_equality,[status(thm)],[c_3474]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_5304,plain,
% 2.18/1.00      ( sK0(X0_45,X1_45) = u1_struct_0(X1_45)
% 2.18/1.00      | m1_pre_topc(X1_45,X0_45) != iProver_top
% 2.18/1.00      | v1_zfmisc_1(u1_struct_0(X0_45)) != iProver_top
% 2.18/1.00      | l1_pre_topc(X0_45) != iProver_top
% 2.18/1.00      | v1_xboole_0(u1_struct_0(X1_45)) = iProver_top ),
% 2.18/1.00      inference(superposition,[status(thm)],[c_3979,c_4620]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_6116,plain,
% 2.18/1.00      ( sK0(X0_45,k1_tex_2(X0_45,X0_46)) = u1_struct_0(k1_tex_2(X0_45,X0_46))
% 2.18/1.00      | m1_subset_1(X0_46,u1_struct_0(X0_45)) != iProver_top
% 2.18/1.00      | v1_zfmisc_1(u1_struct_0(X0_45)) != iProver_top
% 2.18/1.00      | v2_struct_0(X0_45) = iProver_top
% 2.18/1.00      | l1_pre_topc(X0_45) != iProver_top
% 2.18/1.00      | v1_xboole_0(u1_struct_0(k1_tex_2(X0_45,X0_46))) = iProver_top ),
% 2.18/1.00      inference(superposition,[status(thm)],[c_3968,c_5304]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_6495,plain,
% 2.18/1.00      ( sK0(X0_45,k1_tex_2(X0_45,X0_46)) = u1_struct_0(k1_tex_2(X0_45,X0_46))
% 2.18/1.00      | m1_subset_1(X0_46,u1_struct_0(X0_45)) != iProver_top
% 2.18/1.00      | v1_zfmisc_1(u1_struct_0(X0_45)) != iProver_top
% 2.18/1.00      | v2_struct_0(X0_45) = iProver_top
% 2.18/1.00      | v2_struct_0(k1_tex_2(X0_45,X0_46)) = iProver_top
% 2.18/1.00      | l1_pre_topc(X0_45) != iProver_top
% 2.18/1.00      | l1_pre_topc(k1_tex_2(X0_45,X0_46)) != iProver_top ),
% 2.18/1.00      inference(superposition,[status(thm)],[c_6116,c_3976]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_6497,plain,
% 2.18/1.00      ( sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(k1_tex_2(sK1,sK2))
% 2.18/1.00      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 2.18/1.00      | v1_zfmisc_1(u1_struct_0(sK1)) != iProver_top
% 2.18/1.00      | v2_struct_0(k1_tex_2(sK1,sK2)) = iProver_top
% 2.18/1.00      | v2_struct_0(sK1) = iProver_top
% 2.18/1.00      | l1_pre_topc(k1_tex_2(sK1,sK2)) != iProver_top
% 2.18/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.18/1.00      inference(instantiation,[status(thm)],[c_6495]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_6613,plain,
% 2.18/1.00      ( sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(sK1) ),
% 2.18/1.00      inference(global_propositional_subsumption,
% 2.18/1.00                [status(thm)],
% 2.18/1.00                [c_5823,c_23,c_24,c_25,c_3513,c_3520,c_3533,c_3536,
% 2.18/1.00                 c_4330,c_4473,c_5694,c_6218,c_6373,c_6497]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_769,plain,
% 2.18/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.18/1.00      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 2.18/1.00      | ~ l1_pre_topc(X1)
% 2.18/1.00      | k1_tex_2(sK1,sK2) != X0
% 2.18/1.00      | sK0(X1,X0) = u1_struct_0(X0)
% 2.18/1.00      | sK1 != X1 ),
% 2.18/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_179]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_770,plain,
% 2.18/1.00      ( ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
% 2.18/1.00      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 2.18/1.00      | ~ l1_pre_topc(sK1)
% 2.18/1.00      | sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(k1_tex_2(sK1,sK2)) ),
% 2.18/1.00      inference(unflattening,[status(thm)],[c_769]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_772,plain,
% 2.18/1.00      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 2.18/1.00      | ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
% 2.18/1.00      | sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(k1_tex_2(sK1,sK2)) ),
% 2.18/1.00      inference(global_propositional_subsumption,
% 2.18/1.00                [status(thm)],
% 2.18/1.00                [c_770,c_21]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_773,plain,
% 2.18/1.00      ( ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
% 2.18/1.00      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 2.18/1.00      | sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(k1_tex_2(sK1,sK2)) ),
% 2.18/1.00      inference(renaming,[status(thm)],[c_772]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_3471,plain,
% 2.18/1.00      ( ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
% 2.18/1.00      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 2.18/1.00      | sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(k1_tex_2(sK1,sK2)) ),
% 2.18/1.00      inference(subtyping,[status(esa)],[c_773]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_3982,plain,
% 2.18/1.00      ( sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(k1_tex_2(sK1,sK2))
% 2.18/1.00      | m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top
% 2.18/1.00      | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top ),
% 2.18/1.00      inference(predicate_to_equality,[status(thm)],[c_3471]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_3620,plain,
% 2.18/1.00      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 2.18/1.00      | sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(k1_tex_2(sK1,sK2)) ),
% 2.18/1.00      inference(global_propositional_subsumption,
% 2.18/1.00                [status(thm)],
% 2.18/1.00                [c_3471,c_22,c_21,c_20,c_3532]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_3622,plain,
% 2.18/1.00      ( sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(k1_tex_2(sK1,sK2))
% 2.18/1.00      | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top ),
% 2.18/1.00      inference(predicate_to_equality,[status(thm)],[c_3620]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_4690,plain,
% 2.18/1.00      ( sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(k1_tex_2(sK1,sK2))
% 2.18/1.00      | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top ),
% 2.18/1.00      inference(global_propositional_subsumption,
% 2.18/1.00                [status(thm)],
% 2.18/1.00                [c_3982,c_3622]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_6620,plain,
% 2.18/1.00      ( u1_struct_0(k1_tex_2(sK1,sK2)) = u1_struct_0(sK1)
% 2.18/1.00      | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top ),
% 2.18/1.00      inference(demodulation,[status(thm)],[c_6613,c_4690]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_3535,plain,
% 2.18/1.00      ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 2.18/1.00      | ~ v2_struct_0(k1_tex_2(sK1,sK2))
% 2.18/1.00      | v2_struct_0(sK1)
% 2.18/1.00      | ~ l1_pre_topc(sK1) ),
% 2.18/1.00      inference(instantiation,[status(thm)],[c_3484]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_4329,plain,
% 2.18/1.00      ( ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
% 2.18/1.00      | l1_pre_topc(k1_tex_2(sK1,sK2))
% 2.18/1.00      | ~ l1_pre_topc(sK1) ),
% 2.18/1.00      inference(instantiation,[status(thm)],[c_4327]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_6372,plain,
% 2.18/1.00      ( ~ m1_subset_1(X0_46,u1_struct_0(X0_45))
% 2.18/1.00      | ~ v1_zfmisc_1(u1_struct_0(X0_45))
% 2.18/1.00      | v2_struct_0(X0_45)
% 2.18/1.00      | v2_struct_0(k1_tex_2(X0_45,X0_46))
% 2.18/1.00      | ~ l1_pre_topc(X0_45)
% 2.18/1.00      | ~ l1_pre_topc(k1_tex_2(X0_45,X0_46))
% 2.18/1.00      | u1_struct_0(k1_tex_2(X0_45,X0_46)) = u1_struct_0(X0_45) ),
% 2.18/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_6371]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_6374,plain,
% 2.18/1.00      ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 2.18/1.00      | ~ v1_zfmisc_1(u1_struct_0(sK1))
% 2.18/1.00      | v2_struct_0(k1_tex_2(sK1,sK2))
% 2.18/1.00      | v2_struct_0(sK1)
% 2.18/1.00      | ~ l1_pre_topc(k1_tex_2(sK1,sK2))
% 2.18/1.00      | ~ l1_pre_topc(sK1)
% 2.18/1.00      | u1_struct_0(k1_tex_2(sK1,sK2)) = u1_struct_0(sK1) ),
% 2.18/1.00      inference(instantiation,[status(thm)],[c_6372]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_4696,plain,
% 2.18/1.00      ( sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(k1_tex_2(sK1,sK2))
% 2.18/1.00      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 2.18/1.00      | v1_zfmisc_1(u1_struct_0(sK1)) = iProver_top
% 2.18/1.00      | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
% 2.18/1.00      inference(superposition,[status(thm)],[c_3971,c_4690]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_5587,plain,
% 2.18/1.00      ( v1_zfmisc_1(u1_struct_0(sK1)) = iProver_top
% 2.18/1.00      | sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(k1_tex_2(sK1,sK2)) ),
% 2.18/1.00      inference(global_propositional_subsumption,
% 2.18/1.00                [status(thm)],
% 2.18/1.00                [c_4696,c_23,c_24,c_25,c_68,c_72]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_5588,plain,
% 2.18/1.00      ( sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(k1_tex_2(sK1,sK2))
% 2.18/1.00      | v1_zfmisc_1(u1_struct_0(sK1)) = iProver_top ),
% 2.18/1.00      inference(renaming,[status(thm)],[c_5587]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_6617,plain,
% 2.18/1.00      ( u1_struct_0(k1_tex_2(sK1,sK2)) = u1_struct_0(sK1)
% 2.18/1.00      | v1_zfmisc_1(u1_struct_0(sK1)) = iProver_top ),
% 2.18/1.00      inference(demodulation,[status(thm)],[c_6613,c_5588]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_6642,plain,
% 2.18/1.00      ( v1_zfmisc_1(u1_struct_0(sK1))
% 2.18/1.00      | u1_struct_0(k1_tex_2(sK1,sK2)) = u1_struct_0(sK1) ),
% 2.18/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_6617]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_6803,plain,
% 2.18/1.00      ( u1_struct_0(k1_tex_2(sK1,sK2)) = u1_struct_0(sK1) ),
% 2.18/1.00      inference(global_propositional_subsumption,
% 2.18/1.00                [status(thm)],
% 2.18/1.00                [c_6620,c_22,c_21,c_20,c_3532,c_3535,c_4329,c_6374,
% 2.18/1.00                 c_6642]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_6823,plain,
% 2.18/1.00      ( m1_pre_topc(k1_tex_2(sK1,sK2),X0_45) != iProver_top
% 2.18/1.00      | v1_subset_1(u1_struct_0(sK1),u1_struct_0(X0_45)) != iProver_top
% 2.18/1.00      | v1_zfmisc_1(u1_struct_0(X0_45)) != iProver_top
% 2.18/1.00      | l1_pre_topc(X0_45) != iProver_top
% 2.18/1.00      | v1_xboole_0(u1_struct_0(k1_tex_2(sK1,sK2))) = iProver_top ),
% 2.18/1.00      inference(superposition,[status(thm)],[c_6803,c_4620]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_6922,plain,
% 2.18/1.00      ( m1_pre_topc(k1_tex_2(sK1,sK2),X0_45) != iProver_top
% 2.18/1.00      | v1_subset_1(u1_struct_0(sK1),u1_struct_0(X0_45)) != iProver_top
% 2.18/1.00      | v1_zfmisc_1(u1_struct_0(X0_45)) != iProver_top
% 2.18/1.00      | l1_pre_topc(X0_45) != iProver_top
% 2.18/1.00      | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
% 2.18/1.00      inference(light_normalisation,[status(thm)],[c_6823,c_6803]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_7040,plain,
% 2.18/1.00      ( m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top
% 2.18/1.00      | v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK1)) != iProver_top
% 2.18/1.00      | v1_zfmisc_1(u1_struct_0(sK1)) != iProver_top
% 2.18/1.00      | l1_pre_topc(sK1) != iProver_top
% 2.18/1.00      | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
% 2.18/1.00      inference(instantiation,[status(thm)],[c_6922]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_17,plain,
% 2.18/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.18/1.00      | ~ v1_subset_1(k6_domain_1(u1_struct_0(X1),X0),u1_struct_0(X1))
% 2.18/1.00      | ~ v7_struct_0(X1)
% 2.18/1.00      | v2_struct_0(X1)
% 2.18/1.00      | ~ l1_struct_0(X1) ),
% 2.18/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_386,plain,
% 2.18/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.18/1.00      | ~ v1_subset_1(k6_domain_1(u1_struct_0(X1),X0),u1_struct_0(X1))
% 2.18/1.00      | ~ v7_struct_0(X1)
% 2.18/1.00      | v2_struct_0(X1)
% 2.18/1.00      | ~ l1_pre_topc(X2)
% 2.18/1.00      | X2 != X1 ),
% 2.18/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_1]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_387,plain,
% 2.18/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.18/1.00      | ~ v1_subset_1(k6_domain_1(u1_struct_0(X1),X0),u1_struct_0(X1))
% 2.18/1.00      | ~ v7_struct_0(X1)
% 2.18/1.00      | v2_struct_0(X1)
% 2.18/1.00      | ~ l1_pre_topc(X1) ),
% 2.18/1.00      inference(unflattening,[status(thm)],[c_386]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_3476,plain,
% 2.18/1.00      ( ~ m1_subset_1(X0_46,u1_struct_0(X0_45))
% 2.18/1.00      | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0_45),X0_46),u1_struct_0(X0_45))
% 2.18/1.00      | ~ v7_struct_0(X0_45)
% 2.18/1.00      | v2_struct_0(X0_45)
% 2.18/1.00      | ~ l1_pre_topc(X0_45) ),
% 2.18/1.00      inference(subtyping,[status(esa)],[c_387]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_3977,plain,
% 2.18/1.00      ( m1_subset_1(X0_46,u1_struct_0(X0_45)) != iProver_top
% 2.18/1.00      | v1_subset_1(k6_domain_1(u1_struct_0(X0_45),X0_46),u1_struct_0(X0_45)) != iProver_top
% 2.18/1.00      | v7_struct_0(X0_45) != iProver_top
% 2.18/1.00      | v2_struct_0(X0_45) = iProver_top
% 2.18/1.00      | l1_pre_topc(X0_45) != iProver_top ),
% 2.18/1.00      inference(predicate_to_equality,[status(thm)],[c_3476]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_6827,plain,
% 2.18/1.00      ( m1_subset_1(X0_46,u1_struct_0(k1_tex_2(sK1,sK2))) != iProver_top
% 2.18/1.00      | v1_subset_1(k6_domain_1(u1_struct_0(sK1),X0_46),u1_struct_0(sK1)) != iProver_top
% 2.18/1.00      | v7_struct_0(k1_tex_2(sK1,sK2)) != iProver_top
% 2.18/1.00      | v2_struct_0(k1_tex_2(sK1,sK2)) = iProver_top
% 2.18/1.00      | l1_pre_topc(k1_tex_2(sK1,sK2)) != iProver_top ),
% 2.18/1.00      inference(superposition,[status(thm)],[c_6803,c_3977]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_6886,plain,
% 2.18/1.00      ( m1_subset_1(X0_46,u1_struct_0(sK1)) != iProver_top
% 2.18/1.00      | v1_subset_1(k6_domain_1(u1_struct_0(sK1),X0_46),u1_struct_0(sK1)) != iProver_top
% 2.18/1.00      | v7_struct_0(k1_tex_2(sK1,sK2)) != iProver_top
% 2.18/1.00      | v2_struct_0(k1_tex_2(sK1,sK2)) = iProver_top
% 2.18/1.00      | l1_pre_topc(k1_tex_2(sK1,sK2)) != iProver_top ),
% 2.18/1.00      inference(light_normalisation,[status(thm)],[c_6827,c_6803]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_7036,plain,
% 2.18/1.00      ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 2.18/1.00      | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top
% 2.18/1.00      | v7_struct_0(k1_tex_2(sK1,sK2)) != iProver_top
% 2.18/1.00      | v2_struct_0(k1_tex_2(sK1,sK2)) = iProver_top
% 2.18/1.00      | l1_pre_topc(k1_tex_2(sK1,sK2)) != iProver_top ),
% 2.18/1.00      inference(instantiation,[status(thm)],[c_6886]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_6807,plain,
% 2.18/1.00      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) = iProver_top
% 2.18/1.00      | v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK1)) = iProver_top ),
% 2.18/1.00      inference(demodulation,[status(thm)],[c_6803,c_5452]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_14,plain,
% 2.18/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.18/1.00      | v7_struct_0(k1_tex_2(X1,X0))
% 2.18/1.00      | v2_struct_0(X1)
% 2.18/1.00      | ~ l1_pre_topc(X1) ),
% 2.18/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_3483,plain,
% 2.18/1.00      ( ~ m1_subset_1(X0_46,u1_struct_0(X0_45))
% 2.18/1.00      | v7_struct_0(k1_tex_2(X0_45,X0_46))
% 2.18/1.00      | v2_struct_0(X0_45)
% 2.18/1.00      | ~ l1_pre_topc(X0_45) ),
% 2.18/1.00      inference(subtyping,[status(esa)],[c_14]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_3537,plain,
% 2.18/1.00      ( m1_subset_1(X0_46,u1_struct_0(X0_45)) != iProver_top
% 2.18/1.00      | v7_struct_0(k1_tex_2(X0_45,X0_46)) = iProver_top
% 2.18/1.00      | v2_struct_0(X0_45) = iProver_top
% 2.18/1.00      | l1_pre_topc(X0_45) != iProver_top ),
% 2.18/1.00      inference(predicate_to_equality,[status(thm)],[c_3483]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_3539,plain,
% 2.18/1.00      ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 2.18/1.00      | v7_struct_0(k1_tex_2(sK1,sK2)) = iProver_top
% 2.18/1.00      | v2_struct_0(sK1) = iProver_top
% 2.18/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.18/1.00      inference(instantiation,[status(thm)],[c_3537]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_1830,plain,
% 2.18/1.00      ( v1_subset_1(k6_domain_1(X0,X1),X0)
% 2.18/1.00      | v1_zfmisc_1(X0)
% 2.18/1.00      | v1_xboole_0(X0)
% 2.18/1.00      | u1_struct_0(sK1) != X0
% 2.18/1.00      | sK2 != X1 ),
% 2.18/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_20]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_1831,plain,
% 2.18/1.00      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 2.18/1.00      | v1_zfmisc_1(u1_struct_0(sK1))
% 2.18/1.00      | v1_xboole_0(u1_struct_0(sK1)) ),
% 2.18/1.00      inference(unflattening,[status(thm)],[c_1830]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(c_1832,plain,
% 2.18/1.00      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) = iProver_top
% 2.18/1.00      | v1_zfmisc_1(u1_struct_0(sK1)) = iProver_top
% 2.18/1.00      | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
% 2.18/1.00      inference(predicate_to_equality,[status(thm)],[c_1831]) ).
% 2.18/1.00  
% 2.18/1.00  cnf(contradiction,plain,
% 2.18/1.00      ( $false ),
% 2.18/1.00      inference(minisat,
% 2.18/1.00                [status(thm)],
% 2.18/1.00                [c_7040,c_7036,c_6807,c_4330,c_3539,c_3536,c_3533,c_1832,
% 2.18/1.00                 c_72,c_68,c_25,c_24,c_23]) ).
% 2.18/1.00  
% 2.18/1.00  
% 2.18/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.18/1.00  
% 2.18/1.00  ------                               Statistics
% 2.18/1.00  
% 2.18/1.00  ------ General
% 2.18/1.00  
% 2.18/1.00  abstr_ref_over_cycles:                  0
% 2.18/1.00  abstr_ref_under_cycles:                 0
% 2.18/1.00  gc_basic_clause_elim:                   0
% 2.18/1.00  forced_gc_time:                         0
% 2.18/1.00  parsing_time:                           0.012
% 2.18/1.00  unif_index_cands_time:                  0.
% 2.18/1.00  unif_index_add_time:                    0.
% 2.18/1.00  orderings_time:                         0.
% 2.18/1.00  out_proof_time:                         0.015
% 2.18/1.00  total_time:                             0.192
% 2.18/1.00  num_of_symbols:                         50
% 2.18/1.00  num_of_terms:                           4250
% 2.18/1.00  
% 2.18/1.00  ------ Preprocessing
% 2.18/1.00  
% 2.18/1.00  num_of_splits:                          0
% 2.18/1.00  num_of_split_atoms:                     0
% 2.18/1.00  num_of_reused_defs:                     0
% 2.18/1.00  num_eq_ax_congr_red:                    7
% 2.18/1.00  num_of_sem_filtered_clauses:            1
% 2.18/1.00  num_of_subtypes:                        2
% 2.18/1.00  monotx_restored_types:                  1
% 2.18/1.00  sat_num_of_epr_types:                   0
% 2.18/1.00  sat_num_of_non_cyclic_types:            0
% 2.18/1.00  sat_guarded_non_collapsed_types:        0
% 2.18/1.00  num_pure_diseq_elim:                    0
% 2.18/1.00  simp_replaced_by:                       0
% 2.18/1.00  res_preprocessed:                       119
% 2.18/1.00  prep_upred:                             0
% 2.18/1.00  prep_unflattend:                        138
% 2.18/1.00  smt_new_axioms:                         0
% 2.18/1.01  pred_elim_cands:                        8
% 2.18/1.01  pred_elim:                              2
% 2.18/1.01  pred_elim_cl:                           0
% 2.18/1.01  pred_elim_cycles:                       14
% 2.18/1.01  merged_defs:                            2
% 2.18/1.01  merged_defs_ncl:                        0
% 2.18/1.01  bin_hyper_res:                          2
% 2.18/1.01  prep_cycles:                            4
% 2.18/1.01  pred_elim_time:                         0.055
% 2.18/1.01  splitting_time:                         0.
% 2.18/1.01  sem_filter_time:                        0.
% 2.18/1.01  monotx_time:                            0.001
% 2.18/1.01  subtype_inf_time:                       0.001
% 2.18/1.01  
% 2.18/1.01  ------ Problem properties
% 2.18/1.01  
% 2.18/1.01  clauses:                                22
% 2.18/1.01  conjectures:                            3
% 2.18/1.01  epr:                                    3
% 2.18/1.01  horn:                                   15
% 2.18/1.01  ground:                                 7
% 2.18/1.01  unary:                                  3
% 2.18/1.01  binary:                                 1
% 2.18/1.01  lits:                                   69
% 2.18/1.01  lits_eq:                                3
% 2.18/1.01  fd_pure:                                0
% 2.18/1.01  fd_pseudo:                              0
% 2.18/1.01  fd_cond:                                0
% 2.18/1.01  fd_pseudo_cond:                         1
% 2.18/1.01  ac_symbols:                             0
% 2.18/1.01  
% 2.18/1.01  ------ Propositional Solver
% 2.18/1.01  
% 2.18/1.01  prop_solver_calls:                      29
% 2.18/1.01  prop_fast_solver_calls:                 1640
% 2.18/1.01  smt_solver_calls:                       0
% 2.18/1.01  smt_fast_solver_calls:                  0
% 2.18/1.01  prop_num_of_clauses:                    1423
% 2.18/1.01  prop_preprocess_simplified:             5788
% 2.18/1.01  prop_fo_subsumed:                       66
% 2.18/1.01  prop_solver_time:                       0.
% 2.18/1.01  smt_solver_time:                        0.
% 2.18/1.01  smt_fast_solver_time:                   0.
% 2.18/1.01  prop_fast_solver_time:                  0.
% 2.18/1.01  prop_unsat_core_time:                   0.
% 2.18/1.01  
% 2.18/1.01  ------ QBF
% 2.18/1.01  
% 2.18/1.01  qbf_q_res:                              0
% 2.18/1.01  qbf_num_tautologies:                    0
% 2.18/1.01  qbf_prep_cycles:                        0
% 2.18/1.01  
% 2.18/1.01  ------ BMC1
% 2.18/1.01  
% 2.18/1.01  bmc1_current_bound:                     -1
% 2.18/1.01  bmc1_last_solved_bound:                 -1
% 2.18/1.01  bmc1_unsat_core_size:                   -1
% 2.18/1.01  bmc1_unsat_core_parents_size:           -1
% 2.18/1.01  bmc1_merge_next_fun:                    0
% 2.18/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.18/1.01  
% 2.18/1.01  ------ Instantiation
% 2.18/1.01  
% 2.18/1.01  inst_num_of_clauses:                    431
% 2.18/1.01  inst_num_in_passive:                    69
% 2.18/1.01  inst_num_in_active:                     249
% 2.18/1.01  inst_num_in_unprocessed:                113
% 2.18/1.01  inst_num_of_loops:                      270
% 2.18/1.01  inst_num_of_learning_restarts:          0
% 2.18/1.01  inst_num_moves_active_passive:          17
% 2.18/1.01  inst_lit_activity:                      0
% 2.18/1.01  inst_lit_activity_moves:                0
% 2.18/1.01  inst_num_tautologies:                   0
% 2.18/1.01  inst_num_prop_implied:                  0
% 2.18/1.01  inst_num_existing_simplified:           0
% 2.18/1.01  inst_num_eq_res_simplified:             0
% 2.18/1.01  inst_num_child_elim:                    0
% 2.18/1.01  inst_num_of_dismatching_blockings:      289
% 2.18/1.01  inst_num_of_non_proper_insts:           547
% 2.18/1.01  inst_num_of_duplicates:                 0
% 2.18/1.01  inst_inst_num_from_inst_to_res:         0
% 2.18/1.01  inst_dismatching_checking_time:         0.
% 2.18/1.01  
% 2.18/1.01  ------ Resolution
% 2.18/1.01  
% 2.18/1.01  res_num_of_clauses:                     0
% 2.18/1.01  res_num_in_passive:                     0
% 2.18/1.01  res_num_in_active:                      0
% 2.18/1.01  res_num_of_loops:                       123
% 2.18/1.01  res_forward_subset_subsumed:            68
% 2.18/1.01  res_backward_subset_subsumed:           0
% 2.18/1.01  res_forward_subsumed:                   0
% 2.18/1.01  res_backward_subsumed:                  0
% 2.18/1.01  res_forward_subsumption_resolution:     1
% 2.18/1.01  res_backward_subsumption_resolution:    0
% 2.18/1.01  res_clause_to_clause_subsumption:       317
% 2.18/1.01  res_orphan_elimination:                 0
% 2.18/1.01  res_tautology_del:                      68
% 2.18/1.01  res_num_eq_res_simplified:              0
% 2.18/1.01  res_num_sel_changes:                    0
% 2.18/1.01  res_moves_from_active_to_pass:          0
% 2.18/1.01  
% 2.18/1.01  ------ Superposition
% 2.18/1.01  
% 2.18/1.01  sup_time_total:                         0.
% 2.18/1.01  sup_time_generating:                    0.
% 2.18/1.01  sup_time_sim_full:                      0.
% 2.18/1.01  sup_time_sim_immed:                     0.
% 2.18/1.01  
% 2.18/1.01  sup_num_of_clauses:                     62
% 2.18/1.01  sup_num_in_active:                      41
% 2.18/1.01  sup_num_in_passive:                     21
% 2.18/1.01  sup_num_of_loops:                       52
% 2.18/1.01  sup_fw_superposition:                   18
% 2.18/1.01  sup_bw_superposition:                   54
% 2.18/1.01  sup_immediate_simplified:               23
% 2.18/1.01  sup_given_eliminated:                   0
% 2.18/1.01  comparisons_done:                       0
% 2.18/1.01  comparisons_avoided:                    0
% 2.18/1.01  
% 2.18/1.01  ------ Simplifications
% 2.18/1.01  
% 2.18/1.01  
% 2.18/1.01  sim_fw_subset_subsumed:                 10
% 2.18/1.01  sim_bw_subset_subsumed:                 8
% 2.18/1.01  sim_fw_subsumed:                        2
% 2.18/1.01  sim_bw_subsumed:                        0
% 2.18/1.01  sim_fw_subsumption_res:                 1
% 2.18/1.01  sim_bw_subsumption_res:                 0
% 2.18/1.01  sim_tautology_del:                      0
% 2.18/1.01  sim_eq_tautology_del:                   2
% 2.18/1.01  sim_eq_res_simp:                        0
% 2.18/1.01  sim_fw_demodulated:                     2
% 2.18/1.01  sim_bw_demodulated:                     7
% 2.18/1.01  sim_light_normalised:                   10
% 2.18/1.01  sim_joinable_taut:                      0
% 2.18/1.01  sim_joinable_simp:                      0
% 2.18/1.01  sim_ac_normalised:                      0
% 2.18/1.01  sim_smt_subsumption:                    0
% 2.18/1.01  
%------------------------------------------------------------------------------
