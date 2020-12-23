%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:25:36 EST 2020

% Result     : Theorem 1.77s
% Output     : CNFRefutation 1.77s
% Verified   : 
% Statistics : Number of formulae       :  153 (1380 expanded)
%              Number of clauses        :   89 ( 383 expanded)
%              Number of leaves         :   15 ( 282 expanded)
%              Depth                    :   24
%              Number of atoms          :  611 (7222 expanded)
%              Number of equality atoms :  147 ( 476 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
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

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v1_subset_1(X2,u1_struct_0(X0))
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_subset_1(sK0(X0,X1),u1_struct_0(X0))
        & u1_struct_0(X1) = sK0(X0,X1)
        & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | u1_struct_0(X1) = sK0(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( v1_tex_2(k1_tex_2(X0,X1),X0)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f44,plain,(
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

fof(f43,plain,
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

fof(f45,plain,
    ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
      | ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1) )
    & ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
      | v1_tex_2(k1_tex_2(sK1,sK2),sK1) )
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l1_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f42,f44,f43])).

fof(f68,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f64,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f65,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f66,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f45])).

fof(f5,axiom,(
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

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tex_2(X1,X0)
            & ~ v2_struct_0(X1) )
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tex_2(X1,X0)
            & ~ v2_struct_0(X1) )
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v1_tex_2(X1,X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f67,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f47,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v7_struct_0(X0) )
     => ~ v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_zfmisc_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f46,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f10,axiom,(
    ! [X0] :
      ( ( ~ v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v1_subset_1(k6_domain_1(X0,X1),X0)
      | ~ m1_subset_1(X1,X0)
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | ~ v1_subset_1(sK0(X0,X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ~ ( v7_struct_0(X0)
              & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v7_struct_0(X0)
          | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v7_struct_0(X0)
          | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v7_struct_0(X0)
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f48,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v7_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_pre_topc(k1_tex_2(X1,X0),X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_3309,plain,
    ( ~ m1_subset_1(X0_45,u1_struct_0(X0_46))
    | m1_pre_topc(k1_tex_2(X0_46,X0_45),X0_46)
    | v2_struct_0(X0_46)
    | ~ l1_pre_topc(X0_46) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_3751,plain,
    ( m1_subset_1(X0_45,u1_struct_0(X0_46)) != iProver_top
    | m1_pre_topc(k1_tex_2(X0_46,X0_45),X0_46) = iProver_top
    | v2_struct_0(X0_46) = iProver_top
    | l1_pre_topc(X0_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3309])).

cnf(c_7,plain,
    ( v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK0(X1,X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_3314,plain,
    ( v1_tex_2(X0_46,X1_46)
    | ~ m1_pre_topc(X0_46,X1_46)
    | ~ l1_pre_topc(X1_46)
    | sK0(X1_46,X0_46) = u1_struct_0(X0_46) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_3746,plain,
    ( sK0(X0_46,X1_46) = u1_struct_0(X1_46)
    | v1_tex_2(X1_46,X0_46) = iProver_top
    | m1_pre_topc(X1_46,X0_46) != iProver_top
    | l1_pre_topc(X0_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3314])).

cnf(c_4237,plain,
    ( sK0(X0_46,k1_tex_2(X0_46,X0_45)) = u1_struct_0(k1_tex_2(X0_46,X0_45))
    | m1_subset_1(X0_45,u1_struct_0(X0_46)) != iProver_top
    | v1_tex_2(k1_tex_2(X0_46,X0_45),X0_46) = iProver_top
    | v2_struct_0(X0_46) = iProver_top
    | l1_pre_topc(X0_46) != iProver_top ),
    inference(superposition,[status(thm)],[c_3751,c_3746])).

cnf(c_18,negated_conjecture,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_3306,negated_conjecture,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_3754,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top
    | v1_tex_2(k1_tex_2(sK1,sK2),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3306])).

cnf(c_22,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_23,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_21,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_24,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_25,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_27,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top
    | v1_tex_2(k1_tex_2(sK1,sK2),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4,plain,
    ( ~ v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v7_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_19,negated_conjecture,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_172,plain,
    ( v1_tex_2(k1_tex_2(sK1,sK2),sK1)
    | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) ),
    inference(prop_impl,[status(thm)],[c_19])).

cnf(c_173,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
    inference(renaming,[status(thm)],[c_172])).

cnf(c_1329,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v7_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k1_tex_2(sK1,sK2) != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_173])).

cnf(c_1330,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
    | v2_struct_0(k1_tex_2(sK1,sK2))
    | v2_struct_0(sK1)
    | ~ v7_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_1329])).

cnf(c_1,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_3,plain,
    ( v7_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_zfmisc_1(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_339,plain,
    ( v7_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_zfmisc_1(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_1,c_3])).

cnf(c_341,plain,
    ( v7_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_339])).

cnf(c_0,plain,
    ( ~ v1_xboole_0(X0)
    | v1_zfmisc_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_subset_1(k6_domain_1(X1,X0),X1)
    | v1_xboole_0(X1)
    | v1_zfmisc_1(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_298,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_subset_1(k6_domain_1(X1,X0),X1)
    | v1_zfmisc_1(X2)
    | v1_zfmisc_1(X1)
    | X1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_16])).

cnf(c_299,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_subset_1(k6_domain_1(X1,X0),X1)
    | v1_zfmisc_1(X1) ),
    inference(unflattening,[status(thm)],[c_298])).

cnf(c_1030,plain,
    ( v1_subset_1(k6_domain_1(X0,X1),X0)
    | v1_zfmisc_1(X0)
    | u1_struct_0(sK1) != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_299,c_20])).

cnf(c_1031,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | v1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_1030])).

cnf(c_1332,plain,
    ( v2_struct_0(k1_tex_2(sK1,sK2))
    | ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
    | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1330,c_22,c_21,c_341,c_1031])).

cnf(c_1333,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
    | v2_struct_0(k1_tex_2(sK1,sK2)) ),
    inference(renaming,[status(thm)],[c_1332])).

cnf(c_1334,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) = iProver_top
    | m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top
    | v2_struct_0(k1_tex_2(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1333])).

cnf(c_3361,plain,
    ( m1_subset_1(X0_45,u1_struct_0(X0_46)) != iProver_top
    | m1_pre_topc(k1_tex_2(X0_46,X0_45),X0_46) = iProver_top
    | v2_struct_0(X0_46) = iProver_top
    | l1_pre_topc(X0_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3309])).

cnf(c_3363,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(k1_tex_2(sK1,sK2),sK1) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3361])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k1_tex_2(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_3308,plain,
    ( ~ m1_subset_1(X0_45,u1_struct_0(X0_46))
    | v2_struct_0(X0_46)
    | ~ v2_struct_0(k1_tex_2(X0_46,X0_45))
    | ~ l1_pre_topc(X0_46) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_3364,plain,
    ( m1_subset_1(X0_45,u1_struct_0(X0_46)) != iProver_top
    | v2_struct_0(X0_46) = iProver_top
    | v2_struct_0(k1_tex_2(X0_46,X0_45)) != iProver_top
    | l1_pre_topc(X0_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3308])).

cnf(c_3366,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | v2_struct_0(k1_tex_2(sK1,sK2)) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3364])).

cnf(c_3958,plain,
    ( v1_tex_2(k1_tex_2(sK1,sK2),sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3754,c_23,c_24,c_25,c_27,c_1334,c_3363,c_3366])).

cnf(c_5215,plain,
    ( sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(k1_tex_2(sK1,sK2))
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4237,c_3958])).

cnf(c_8,plain,
    ( m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | v1_tex_2(X1,X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_3313,plain,
    ( m1_subset_1(sK0(X0_46,X1_46),k1_zfmisc_1(u1_struct_0(X0_46)))
    | v1_tex_2(X1_46,X0_46)
    | ~ m1_pre_topc(X1_46,X0_46)
    | ~ l1_pre_topc(X0_46) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_3747,plain,
    ( m1_subset_1(sK0(X0_46,X1_46),k1_zfmisc_1(u1_struct_0(X0_46))) = iProver_top
    | v1_tex_2(X1_46,X0_46) = iProver_top
    | m1_pre_topc(X1_46,X0_46) != iProver_top
    | l1_pre_topc(X0_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3313])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | v1_subset_1(X0,X1)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_3311,plain,
    ( ~ m1_subset_1(X0_45,k1_zfmisc_1(X1_45))
    | v1_subset_1(X0_45,X1_45)
    | X0_45 = X1_45 ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_3749,plain,
    ( X0_45 = X1_45
    | m1_subset_1(X0_45,k1_zfmisc_1(X1_45)) != iProver_top
    | v1_subset_1(X0_45,X1_45) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3311])).

cnf(c_4652,plain,
    ( sK0(X0_46,X1_46) = u1_struct_0(X0_46)
    | v1_subset_1(sK0(X0_46,X1_46),u1_struct_0(X0_46)) = iProver_top
    | v1_tex_2(X1_46,X0_46) = iProver_top
    | m1_pre_topc(X1_46,X0_46) != iProver_top
    | l1_pre_topc(X0_46) != iProver_top ),
    inference(superposition,[status(thm)],[c_3747,c_3749])).

cnf(c_6,plain,
    ( ~ v1_subset_1(sK0(X0,X1),u1_struct_0(X0))
    | v1_tex_2(X1,X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_3315,plain,
    ( ~ v1_subset_1(sK0(X0_46,X1_46),u1_struct_0(X0_46))
    | v1_tex_2(X1_46,X0_46)
    | ~ m1_pre_topc(X1_46,X0_46)
    | ~ l1_pre_topc(X0_46) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_3351,plain,
    ( v1_subset_1(sK0(X0_46,X1_46),u1_struct_0(X0_46)) != iProver_top
    | v1_tex_2(X1_46,X0_46) = iProver_top
    | m1_pre_topc(X1_46,X0_46) != iProver_top
    | l1_pre_topc(X0_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3315])).

cnf(c_4817,plain,
    ( sK0(X0_46,X1_46) = u1_struct_0(X0_46)
    | v1_tex_2(X1_46,X0_46) = iProver_top
    | m1_pre_topc(X1_46,X0_46) != iProver_top
    | l1_pre_topc(X0_46) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4652,c_3351])).

cnf(c_4825,plain,
    ( sK0(X0_46,k1_tex_2(X0_46,X0_45)) = u1_struct_0(X0_46)
    | m1_subset_1(X0_45,u1_struct_0(X0_46)) != iProver_top
    | v1_tex_2(k1_tex_2(X0_46,X0_45),X0_46) = iProver_top
    | v2_struct_0(X0_46) = iProver_top
    | l1_pre_topc(X0_46) != iProver_top ),
    inference(superposition,[status(thm)],[c_3751,c_4817])).

cnf(c_4835,plain,
    ( sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(sK1)
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4825,c_3958])).

cnf(c_170,plain,
    ( ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) ),
    inference(prop_impl,[status(thm)],[c_18])).

cnf(c_171,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
    inference(renaming,[status(thm)],[c_170])).

cnf(c_1258,plain,
    ( m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0)
    | k1_tex_2(sK1,sK2) != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_171])).

cnf(c_1259,plain,
    ( m1_subset_1(sK0(sK1,k1_tex_2(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_1258])).

cnf(c_1275,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | ~ v1_subset_1(sK0(X0,X1),u1_struct_0(X0))
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0)
    | k1_tex_2(sK1,sK2) != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_171])).

cnf(c_1276,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | ~ v1_subset_1(sK0(sK1,k1_tex_2(sK1,sK2)),u1_struct_0(sK1))
    | ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_1275])).

cnf(c_3362,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_3309])).

cnf(c_3365,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ v2_struct_0(k1_tex_2(sK1,sK2))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_3308])).

cnf(c_3997,plain,
    ( ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_subset_1(X0_45,u1_struct_0(sK1))
    | X0_45 = u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_3311])).

cnf(c_4159,plain,
    ( ~ m1_subset_1(sK0(sK1,k1_tex_2(sK1,X0_45)),k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_subset_1(sK0(sK1,k1_tex_2(sK1,X0_45)),u1_struct_0(sK1))
    | sK0(sK1,k1_tex_2(sK1,X0_45)) = u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_3997])).

cnf(c_4162,plain,
    ( ~ m1_subset_1(sK0(sK1,k1_tex_2(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_subset_1(sK0(sK1,k1_tex_2(sK1,sK2)),u1_struct_0(sK1))
    | sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_4159])).

cnf(c_4984,plain,
    ( sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4835,c_22,c_21,c_20,c_1259,c_1276,c_1333,c_3362,c_3365,c_4162])).

cnf(c_5235,plain,
    ( u1_struct_0(k1_tex_2(sK1,sK2)) = u1_struct_0(sK1)
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5215,c_4984])).

cnf(c_5323,plain,
    ( u1_struct_0(k1_tex_2(sK1,sK2)) = u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5235,c_23,c_24,c_25])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(X1),X0),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v7_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_353,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(X1),X0),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v7_struct_0(X1)
    | ~ l1_pre_topc(X2)
    | X1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_17])).

cnf(c_354,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(X1),X0),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v7_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_353])).

cnf(c_3299,plain,
    ( ~ m1_subset_1(X0_45,u1_struct_0(X0_46))
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0_46),X0_45),u1_struct_0(X0_46))
    | v2_struct_0(X0_46)
    | ~ v7_struct_0(X0_46)
    | ~ l1_pre_topc(X0_46) ),
    inference(subtyping,[status(esa)],[c_354])).

cnf(c_3761,plain,
    ( m1_subset_1(X0_45,u1_struct_0(X0_46)) != iProver_top
    | v1_subset_1(k6_domain_1(u1_struct_0(X0_46),X0_45),u1_struct_0(X0_46)) != iProver_top
    | v2_struct_0(X0_46) = iProver_top
    | v7_struct_0(X0_46) != iProver_top
    | l1_pre_topc(X0_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3299])).

cnf(c_5331,plain,
    ( m1_subset_1(X0_45,u1_struct_0(k1_tex_2(sK1,sK2))) != iProver_top
    | v1_subset_1(k6_domain_1(u1_struct_0(sK1),X0_45),u1_struct_0(sK1)) != iProver_top
    | v2_struct_0(k1_tex_2(sK1,sK2)) = iProver_top
    | v7_struct_0(k1_tex_2(sK1,sK2)) != iProver_top
    | l1_pre_topc(k1_tex_2(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5323,c_3761])).

cnf(c_5366,plain,
    ( m1_subset_1(X0_45,u1_struct_0(sK1)) != iProver_top
    | v1_subset_1(k6_domain_1(u1_struct_0(sK1),X0_45),u1_struct_0(sK1)) != iProver_top
    | v2_struct_0(k1_tex_2(sK1,sK2)) = iProver_top
    | v7_struct_0(k1_tex_2(sK1,sK2)) != iProver_top
    | l1_pre_topc(k1_tex_2(sK1,sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5331,c_5323])).

cnf(c_5437,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top
    | v2_struct_0(k1_tex_2(sK1,sK2)) = iProver_top
    | v7_struct_0(k1_tex_2(sK1,sK2)) != iProver_top
    | l1_pre_topc(k1_tex_2(sK1,sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5366])).

cnf(c_2,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_3317,plain,
    ( ~ m1_pre_topc(X0_46,X1_46)
    | ~ l1_pre_topc(X1_46)
    | l1_pre_topc(X0_46) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_4051,plain,
    ( ~ m1_pre_topc(k1_tex_2(X0_46,X0_45),X1_46)
    | ~ l1_pre_topc(X1_46)
    | l1_pre_topc(k1_tex_2(X0_46,X0_45)) ),
    inference(instantiation,[status(thm)],[c_3317])).

cnf(c_4052,plain,
    ( m1_pre_topc(k1_tex_2(X0_46,X0_45),X1_46) != iProver_top
    | l1_pre_topc(X1_46) != iProver_top
    | l1_pre_topc(k1_tex_2(X0_46,X0_45)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4051])).

cnf(c_4054,plain,
    ( m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top
    | l1_pre_topc(k1_tex_2(sK1,sK2)) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4052])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v7_struct_0(k1_tex_2(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_3307,plain,
    ( ~ m1_subset_1(X0_45,u1_struct_0(X0_46))
    | v2_struct_0(X0_46)
    | v7_struct_0(k1_tex_2(X0_46,X0_45))
    | ~ l1_pre_topc(X0_46) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_3367,plain,
    ( m1_subset_1(X0_45,u1_struct_0(X0_46)) != iProver_top
    | v2_struct_0(X0_46) = iProver_top
    | v7_struct_0(k1_tex_2(X0_46,X0_45)) = iProver_top
    | l1_pre_topc(X0_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3307])).

cnf(c_3369,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v7_struct_0(k1_tex_2(sK1,sK2)) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3367])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5437,c_4054,c_3369,c_3366,c_3363,c_1334,c_25,c_24,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:24:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.77/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.77/1.00  
% 1.77/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.77/1.00  
% 1.77/1.00  ------  iProver source info
% 1.77/1.00  
% 1.77/1.00  git: date: 2020-06-30 10:37:57 +0100
% 1.77/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.77/1.00  git: non_committed_changes: false
% 1.77/1.00  git: last_make_outside_of_git: false
% 1.77/1.00  
% 1.77/1.00  ------ 
% 1.77/1.00  
% 1.77/1.00  ------ Input Options
% 1.77/1.00  
% 1.77/1.00  --out_options                           all
% 1.77/1.00  --tptp_safe_out                         true
% 1.77/1.00  --problem_path                          ""
% 1.77/1.00  --include_path                          ""
% 1.77/1.00  --clausifier                            res/vclausify_rel
% 1.77/1.00  --clausifier_options                    --mode clausify
% 1.77/1.00  --stdin                                 false
% 1.77/1.00  --stats_out                             all
% 1.77/1.00  
% 1.77/1.00  ------ General Options
% 1.77/1.00  
% 1.77/1.00  --fof                                   false
% 1.77/1.00  --time_out_real                         305.
% 1.77/1.00  --time_out_virtual                      -1.
% 1.77/1.00  --symbol_type_check                     false
% 1.77/1.00  --clausify_out                          false
% 1.77/1.00  --sig_cnt_out                           false
% 1.77/1.00  --trig_cnt_out                          false
% 1.77/1.00  --trig_cnt_out_tolerance                1.
% 1.77/1.00  --trig_cnt_out_sk_spl                   false
% 1.77/1.00  --abstr_cl_out                          false
% 1.77/1.00  
% 1.77/1.00  ------ Global Options
% 1.77/1.00  
% 1.77/1.00  --schedule                              default
% 1.77/1.00  --add_important_lit                     false
% 1.77/1.00  --prop_solver_per_cl                    1000
% 1.77/1.00  --min_unsat_core                        false
% 1.77/1.00  --soft_assumptions                      false
% 1.77/1.00  --soft_lemma_size                       3
% 1.77/1.00  --prop_impl_unit_size                   0
% 1.77/1.00  --prop_impl_unit                        []
% 1.77/1.00  --share_sel_clauses                     true
% 1.77/1.00  --reset_solvers                         false
% 1.77/1.00  --bc_imp_inh                            [conj_cone]
% 1.77/1.00  --conj_cone_tolerance                   3.
% 1.77/1.00  --extra_neg_conj                        none
% 1.77/1.00  --large_theory_mode                     true
% 1.77/1.00  --prolific_symb_bound                   200
% 1.77/1.00  --lt_threshold                          2000
% 1.77/1.00  --clause_weak_htbl                      true
% 1.77/1.00  --gc_record_bc_elim                     false
% 1.77/1.00  
% 1.77/1.00  ------ Preprocessing Options
% 1.77/1.00  
% 1.77/1.00  --preprocessing_flag                    true
% 1.77/1.00  --time_out_prep_mult                    0.1
% 1.77/1.00  --splitting_mode                        input
% 1.77/1.00  --splitting_grd                         true
% 1.77/1.00  --splitting_cvd                         false
% 1.77/1.00  --splitting_cvd_svl                     false
% 1.77/1.00  --splitting_nvd                         32
% 1.77/1.00  --sub_typing                            true
% 1.77/1.00  --prep_gs_sim                           true
% 1.77/1.00  --prep_unflatten                        true
% 1.77/1.00  --prep_res_sim                          true
% 1.77/1.00  --prep_upred                            true
% 1.77/1.00  --prep_sem_filter                       exhaustive
% 1.77/1.00  --prep_sem_filter_out                   false
% 1.77/1.00  --pred_elim                             true
% 1.77/1.00  --res_sim_input                         true
% 1.77/1.00  --eq_ax_congr_red                       true
% 1.77/1.00  --pure_diseq_elim                       true
% 1.77/1.00  --brand_transform                       false
% 1.77/1.00  --non_eq_to_eq                          false
% 1.77/1.00  --prep_def_merge                        true
% 1.77/1.00  --prep_def_merge_prop_impl              false
% 1.77/1.00  --prep_def_merge_mbd                    true
% 1.77/1.00  --prep_def_merge_tr_red                 false
% 1.77/1.00  --prep_def_merge_tr_cl                  false
% 1.77/1.00  --smt_preprocessing                     true
% 1.77/1.00  --smt_ac_axioms                         fast
% 1.77/1.00  --preprocessed_out                      false
% 1.77/1.00  --preprocessed_stats                    false
% 1.77/1.00  
% 1.77/1.00  ------ Abstraction refinement Options
% 1.77/1.00  
% 1.77/1.00  --abstr_ref                             []
% 1.77/1.00  --abstr_ref_prep                        false
% 1.77/1.00  --abstr_ref_until_sat                   false
% 1.77/1.00  --abstr_ref_sig_restrict                funpre
% 1.77/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.77/1.00  --abstr_ref_under                       []
% 1.77/1.00  
% 1.77/1.00  ------ SAT Options
% 1.77/1.00  
% 1.77/1.00  --sat_mode                              false
% 1.77/1.00  --sat_fm_restart_options                ""
% 1.77/1.00  --sat_gr_def                            false
% 1.77/1.00  --sat_epr_types                         true
% 1.77/1.00  --sat_non_cyclic_types                  false
% 1.77/1.00  --sat_finite_models                     false
% 1.77/1.00  --sat_fm_lemmas                         false
% 1.77/1.00  --sat_fm_prep                           false
% 1.77/1.00  --sat_fm_uc_incr                        true
% 1.77/1.00  --sat_out_model                         small
% 1.77/1.00  --sat_out_clauses                       false
% 1.77/1.00  
% 1.77/1.00  ------ QBF Options
% 1.77/1.00  
% 1.77/1.00  --qbf_mode                              false
% 1.77/1.00  --qbf_elim_univ                         false
% 1.77/1.00  --qbf_dom_inst                          none
% 1.77/1.00  --qbf_dom_pre_inst                      false
% 1.77/1.00  --qbf_sk_in                             false
% 1.77/1.00  --qbf_pred_elim                         true
% 1.77/1.00  --qbf_split                             512
% 1.77/1.00  
% 1.77/1.00  ------ BMC1 Options
% 1.77/1.00  
% 1.77/1.00  --bmc1_incremental                      false
% 1.77/1.00  --bmc1_axioms                           reachable_all
% 1.77/1.00  --bmc1_min_bound                        0
% 1.77/1.00  --bmc1_max_bound                        -1
% 1.77/1.00  --bmc1_max_bound_default                -1
% 1.77/1.00  --bmc1_symbol_reachability              true
% 1.77/1.00  --bmc1_property_lemmas                  false
% 1.77/1.00  --bmc1_k_induction                      false
% 1.77/1.00  --bmc1_non_equiv_states                 false
% 1.77/1.00  --bmc1_deadlock                         false
% 1.77/1.00  --bmc1_ucm                              false
% 1.77/1.00  --bmc1_add_unsat_core                   none
% 1.77/1.00  --bmc1_unsat_core_children              false
% 1.77/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.77/1.00  --bmc1_out_stat                         full
% 1.77/1.00  --bmc1_ground_init                      false
% 1.77/1.00  --bmc1_pre_inst_next_state              false
% 1.77/1.00  --bmc1_pre_inst_state                   false
% 1.77/1.00  --bmc1_pre_inst_reach_state             false
% 1.77/1.00  --bmc1_out_unsat_core                   false
% 1.77/1.00  --bmc1_aig_witness_out                  false
% 1.77/1.00  --bmc1_verbose                          false
% 1.77/1.00  --bmc1_dump_clauses_tptp                false
% 1.77/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.77/1.00  --bmc1_dump_file                        -
% 1.77/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.77/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.77/1.00  --bmc1_ucm_extend_mode                  1
% 1.77/1.00  --bmc1_ucm_init_mode                    2
% 1.77/1.00  --bmc1_ucm_cone_mode                    none
% 1.77/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.77/1.00  --bmc1_ucm_relax_model                  4
% 1.77/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.77/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.77/1.00  --bmc1_ucm_layered_model                none
% 1.77/1.00  --bmc1_ucm_max_lemma_size               10
% 1.77/1.00  
% 1.77/1.00  ------ AIG Options
% 1.77/1.00  
% 1.77/1.00  --aig_mode                              false
% 1.77/1.00  
% 1.77/1.00  ------ Instantiation Options
% 1.77/1.00  
% 1.77/1.00  --instantiation_flag                    true
% 1.77/1.00  --inst_sos_flag                         false
% 1.77/1.00  --inst_sos_phase                        true
% 1.77/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.77/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.77/1.00  --inst_lit_sel_side                     num_symb
% 1.77/1.00  --inst_solver_per_active                1400
% 1.77/1.00  --inst_solver_calls_frac                1.
% 1.77/1.00  --inst_passive_queue_type               priority_queues
% 1.77/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.77/1.00  --inst_passive_queues_freq              [25;2]
% 1.77/1.00  --inst_dismatching                      true
% 1.77/1.00  --inst_eager_unprocessed_to_passive     true
% 1.77/1.00  --inst_prop_sim_given                   true
% 1.77/1.00  --inst_prop_sim_new                     false
% 1.77/1.00  --inst_subs_new                         false
% 1.77/1.00  --inst_eq_res_simp                      false
% 1.77/1.00  --inst_subs_given                       false
% 1.77/1.00  --inst_orphan_elimination               true
% 1.77/1.00  --inst_learning_loop_flag               true
% 1.77/1.00  --inst_learning_start                   3000
% 1.77/1.00  --inst_learning_factor                  2
% 1.77/1.00  --inst_start_prop_sim_after_learn       3
% 1.77/1.00  --inst_sel_renew                        solver
% 1.77/1.00  --inst_lit_activity_flag                true
% 1.77/1.00  --inst_restr_to_given                   false
% 1.77/1.00  --inst_activity_threshold               500
% 1.77/1.00  --inst_out_proof                        true
% 1.77/1.00  
% 1.77/1.00  ------ Resolution Options
% 1.77/1.00  
% 1.77/1.00  --resolution_flag                       true
% 1.77/1.00  --res_lit_sel                           adaptive
% 1.77/1.00  --res_lit_sel_side                      none
% 1.77/1.00  --res_ordering                          kbo
% 1.77/1.00  --res_to_prop_solver                    active
% 1.77/1.00  --res_prop_simpl_new                    false
% 1.77/1.00  --res_prop_simpl_given                  true
% 1.77/1.00  --res_passive_queue_type                priority_queues
% 1.77/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.77/1.00  --res_passive_queues_freq               [15;5]
% 1.77/1.00  --res_forward_subs                      full
% 1.77/1.00  --res_backward_subs                     full
% 1.77/1.00  --res_forward_subs_resolution           true
% 1.77/1.00  --res_backward_subs_resolution          true
% 1.77/1.00  --res_orphan_elimination                true
% 1.77/1.00  --res_time_limit                        2.
% 1.77/1.00  --res_out_proof                         true
% 1.77/1.00  
% 1.77/1.00  ------ Superposition Options
% 1.77/1.00  
% 1.77/1.00  --superposition_flag                    true
% 1.77/1.00  --sup_passive_queue_type                priority_queues
% 1.77/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.77/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.77/1.00  --demod_completeness_check              fast
% 1.77/1.00  --demod_use_ground                      true
% 1.77/1.00  --sup_to_prop_solver                    passive
% 1.77/1.00  --sup_prop_simpl_new                    true
% 1.77/1.00  --sup_prop_simpl_given                  true
% 1.77/1.00  --sup_fun_splitting                     false
% 1.77/1.00  --sup_smt_interval                      50000
% 1.77/1.00  
% 1.77/1.00  ------ Superposition Simplification Setup
% 1.77/1.00  
% 1.77/1.00  --sup_indices_passive                   []
% 1.77/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.77/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.77/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.77/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.77/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.77/1.00  --sup_full_bw                           [BwDemod]
% 1.77/1.00  --sup_immed_triv                        [TrivRules]
% 1.77/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.77/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.77/1.00  --sup_immed_bw_main                     []
% 1.77/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.77/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.77/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.77/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.77/1.00  
% 1.77/1.00  ------ Combination Options
% 1.77/1.00  
% 1.77/1.00  --comb_res_mult                         3
% 1.77/1.00  --comb_sup_mult                         2
% 1.77/1.00  --comb_inst_mult                        10
% 1.77/1.00  
% 1.77/1.00  ------ Debug Options
% 1.77/1.00  
% 1.77/1.00  --dbg_backtrace                         false
% 1.77/1.00  --dbg_dump_prop_clauses                 false
% 1.77/1.00  --dbg_dump_prop_clauses_file            -
% 1.77/1.00  --dbg_out_stat                          false
% 1.77/1.00  ------ Parsing...
% 1.77/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.77/1.00  
% 1.77/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 1.77/1.00  
% 1.77/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.77/1.00  
% 1.77/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.77/1.00  ------ Proving...
% 1.77/1.00  ------ Problem Properties 
% 1.77/1.00  
% 1.77/1.00  
% 1.77/1.00  clauses                                 19
% 1.77/1.00  conjectures                             5
% 1.77/1.00  EPR                                     4
% 1.77/1.00  Horn                                    11
% 1.77/1.00  unary                                   3
% 1.77/1.00  binary                                  3
% 1.77/1.00  lits                                    61
% 1.77/1.00  lits eq                                 2
% 1.77/1.00  fd_pure                                 0
% 1.77/1.00  fd_pseudo                               0
% 1.77/1.00  fd_cond                                 0
% 1.77/1.00  fd_pseudo_cond                          1
% 1.77/1.00  AC symbols                              0
% 1.77/1.00  
% 1.77/1.00  ------ Schedule dynamic 5 is on 
% 1.77/1.00  
% 1.77/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.77/1.00  
% 1.77/1.00  
% 1.77/1.00  ------ 
% 1.77/1.00  Current options:
% 1.77/1.00  ------ 
% 1.77/1.00  
% 1.77/1.00  ------ Input Options
% 1.77/1.00  
% 1.77/1.00  --out_options                           all
% 1.77/1.00  --tptp_safe_out                         true
% 1.77/1.00  --problem_path                          ""
% 1.77/1.00  --include_path                          ""
% 1.77/1.00  --clausifier                            res/vclausify_rel
% 1.77/1.00  --clausifier_options                    --mode clausify
% 1.77/1.00  --stdin                                 false
% 1.77/1.00  --stats_out                             all
% 1.77/1.00  
% 1.77/1.00  ------ General Options
% 1.77/1.00  
% 1.77/1.00  --fof                                   false
% 1.77/1.00  --time_out_real                         305.
% 1.77/1.00  --time_out_virtual                      -1.
% 1.77/1.00  --symbol_type_check                     false
% 1.77/1.00  --clausify_out                          false
% 1.77/1.00  --sig_cnt_out                           false
% 1.77/1.00  --trig_cnt_out                          false
% 1.77/1.00  --trig_cnt_out_tolerance                1.
% 1.77/1.00  --trig_cnt_out_sk_spl                   false
% 1.77/1.00  --abstr_cl_out                          false
% 1.77/1.00  
% 1.77/1.00  ------ Global Options
% 1.77/1.00  
% 1.77/1.00  --schedule                              default
% 1.77/1.00  --add_important_lit                     false
% 1.77/1.00  --prop_solver_per_cl                    1000
% 1.77/1.00  --min_unsat_core                        false
% 1.77/1.00  --soft_assumptions                      false
% 1.77/1.00  --soft_lemma_size                       3
% 1.77/1.00  --prop_impl_unit_size                   0
% 1.77/1.00  --prop_impl_unit                        []
% 1.77/1.00  --share_sel_clauses                     true
% 1.77/1.00  --reset_solvers                         false
% 1.77/1.00  --bc_imp_inh                            [conj_cone]
% 1.77/1.00  --conj_cone_tolerance                   3.
% 1.77/1.00  --extra_neg_conj                        none
% 1.77/1.00  --large_theory_mode                     true
% 1.77/1.00  --prolific_symb_bound                   200
% 1.77/1.00  --lt_threshold                          2000
% 1.77/1.00  --clause_weak_htbl                      true
% 1.77/1.00  --gc_record_bc_elim                     false
% 1.77/1.00  
% 1.77/1.00  ------ Preprocessing Options
% 1.77/1.00  
% 1.77/1.00  --preprocessing_flag                    true
% 1.77/1.00  --time_out_prep_mult                    0.1
% 1.77/1.00  --splitting_mode                        input
% 1.77/1.00  --splitting_grd                         true
% 1.77/1.00  --splitting_cvd                         false
% 1.77/1.00  --splitting_cvd_svl                     false
% 1.77/1.00  --splitting_nvd                         32
% 1.77/1.00  --sub_typing                            true
% 1.77/1.00  --prep_gs_sim                           true
% 1.77/1.00  --prep_unflatten                        true
% 1.77/1.00  --prep_res_sim                          true
% 1.77/1.00  --prep_upred                            true
% 1.77/1.00  --prep_sem_filter                       exhaustive
% 1.77/1.00  --prep_sem_filter_out                   false
% 1.77/1.00  --pred_elim                             true
% 1.77/1.00  --res_sim_input                         true
% 1.77/1.00  --eq_ax_congr_red                       true
% 1.77/1.00  --pure_diseq_elim                       true
% 1.77/1.00  --brand_transform                       false
% 1.77/1.00  --non_eq_to_eq                          false
% 1.77/1.00  --prep_def_merge                        true
% 1.77/1.00  --prep_def_merge_prop_impl              false
% 1.77/1.00  --prep_def_merge_mbd                    true
% 1.77/1.00  --prep_def_merge_tr_red                 false
% 1.77/1.00  --prep_def_merge_tr_cl                  false
% 1.77/1.00  --smt_preprocessing                     true
% 1.77/1.00  --smt_ac_axioms                         fast
% 1.77/1.00  --preprocessed_out                      false
% 1.77/1.00  --preprocessed_stats                    false
% 1.77/1.00  
% 1.77/1.00  ------ Abstraction refinement Options
% 1.77/1.00  
% 1.77/1.00  --abstr_ref                             []
% 1.77/1.00  --abstr_ref_prep                        false
% 1.77/1.00  --abstr_ref_until_sat                   false
% 1.77/1.00  --abstr_ref_sig_restrict                funpre
% 1.77/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.77/1.00  --abstr_ref_under                       []
% 1.77/1.00  
% 1.77/1.00  ------ SAT Options
% 1.77/1.00  
% 1.77/1.00  --sat_mode                              false
% 1.77/1.00  --sat_fm_restart_options                ""
% 1.77/1.00  --sat_gr_def                            false
% 1.77/1.00  --sat_epr_types                         true
% 1.77/1.00  --sat_non_cyclic_types                  false
% 1.77/1.00  --sat_finite_models                     false
% 1.77/1.00  --sat_fm_lemmas                         false
% 1.77/1.00  --sat_fm_prep                           false
% 1.77/1.00  --sat_fm_uc_incr                        true
% 1.77/1.00  --sat_out_model                         small
% 1.77/1.00  --sat_out_clauses                       false
% 1.77/1.00  
% 1.77/1.00  ------ QBF Options
% 1.77/1.00  
% 1.77/1.00  --qbf_mode                              false
% 1.77/1.00  --qbf_elim_univ                         false
% 1.77/1.00  --qbf_dom_inst                          none
% 1.77/1.00  --qbf_dom_pre_inst                      false
% 1.77/1.00  --qbf_sk_in                             false
% 1.77/1.00  --qbf_pred_elim                         true
% 1.77/1.00  --qbf_split                             512
% 1.77/1.00  
% 1.77/1.00  ------ BMC1 Options
% 1.77/1.00  
% 1.77/1.00  --bmc1_incremental                      false
% 1.77/1.00  --bmc1_axioms                           reachable_all
% 1.77/1.00  --bmc1_min_bound                        0
% 1.77/1.00  --bmc1_max_bound                        -1
% 1.77/1.00  --bmc1_max_bound_default                -1
% 1.77/1.00  --bmc1_symbol_reachability              true
% 1.77/1.00  --bmc1_property_lemmas                  false
% 1.77/1.00  --bmc1_k_induction                      false
% 1.77/1.00  --bmc1_non_equiv_states                 false
% 1.77/1.00  --bmc1_deadlock                         false
% 1.77/1.00  --bmc1_ucm                              false
% 1.77/1.00  --bmc1_add_unsat_core                   none
% 1.77/1.00  --bmc1_unsat_core_children              false
% 1.77/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.77/1.00  --bmc1_out_stat                         full
% 1.77/1.00  --bmc1_ground_init                      false
% 1.77/1.00  --bmc1_pre_inst_next_state              false
% 1.77/1.00  --bmc1_pre_inst_state                   false
% 1.77/1.00  --bmc1_pre_inst_reach_state             false
% 1.77/1.00  --bmc1_out_unsat_core                   false
% 1.77/1.00  --bmc1_aig_witness_out                  false
% 1.77/1.00  --bmc1_verbose                          false
% 1.77/1.00  --bmc1_dump_clauses_tptp                false
% 1.77/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.77/1.00  --bmc1_dump_file                        -
% 1.77/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.77/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.77/1.00  --bmc1_ucm_extend_mode                  1
% 1.77/1.00  --bmc1_ucm_init_mode                    2
% 1.77/1.00  --bmc1_ucm_cone_mode                    none
% 1.77/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.77/1.00  --bmc1_ucm_relax_model                  4
% 1.77/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.77/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.77/1.00  --bmc1_ucm_layered_model                none
% 1.77/1.00  --bmc1_ucm_max_lemma_size               10
% 1.77/1.00  
% 1.77/1.00  ------ AIG Options
% 1.77/1.00  
% 1.77/1.00  --aig_mode                              false
% 1.77/1.00  
% 1.77/1.00  ------ Instantiation Options
% 1.77/1.00  
% 1.77/1.00  --instantiation_flag                    true
% 1.77/1.00  --inst_sos_flag                         false
% 1.77/1.00  --inst_sos_phase                        true
% 1.77/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.77/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.77/1.00  --inst_lit_sel_side                     none
% 1.77/1.00  --inst_solver_per_active                1400
% 1.77/1.00  --inst_solver_calls_frac                1.
% 1.77/1.00  --inst_passive_queue_type               priority_queues
% 1.77/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.77/1.00  --inst_passive_queues_freq              [25;2]
% 1.77/1.00  --inst_dismatching                      true
% 1.77/1.00  --inst_eager_unprocessed_to_passive     true
% 1.77/1.00  --inst_prop_sim_given                   true
% 1.77/1.00  --inst_prop_sim_new                     false
% 1.77/1.00  --inst_subs_new                         false
% 1.77/1.00  --inst_eq_res_simp                      false
% 1.77/1.00  --inst_subs_given                       false
% 1.77/1.00  --inst_orphan_elimination               true
% 1.77/1.00  --inst_learning_loop_flag               true
% 1.77/1.00  --inst_learning_start                   3000
% 1.77/1.00  --inst_learning_factor                  2
% 1.77/1.00  --inst_start_prop_sim_after_learn       3
% 1.77/1.00  --inst_sel_renew                        solver
% 1.77/1.00  --inst_lit_activity_flag                true
% 1.77/1.00  --inst_restr_to_given                   false
% 1.77/1.00  --inst_activity_threshold               500
% 1.77/1.00  --inst_out_proof                        true
% 1.77/1.00  
% 1.77/1.00  ------ Resolution Options
% 1.77/1.00  
% 1.77/1.00  --resolution_flag                       false
% 1.77/1.00  --res_lit_sel                           adaptive
% 1.77/1.00  --res_lit_sel_side                      none
% 1.77/1.00  --res_ordering                          kbo
% 1.77/1.00  --res_to_prop_solver                    active
% 1.77/1.00  --res_prop_simpl_new                    false
% 1.77/1.00  --res_prop_simpl_given                  true
% 1.77/1.00  --res_passive_queue_type                priority_queues
% 1.77/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.77/1.00  --res_passive_queues_freq               [15;5]
% 1.77/1.00  --res_forward_subs                      full
% 1.77/1.00  --res_backward_subs                     full
% 1.77/1.00  --res_forward_subs_resolution           true
% 1.77/1.00  --res_backward_subs_resolution          true
% 1.77/1.00  --res_orphan_elimination                true
% 1.77/1.00  --res_time_limit                        2.
% 1.77/1.00  --res_out_proof                         true
% 1.77/1.00  
% 1.77/1.00  ------ Superposition Options
% 1.77/1.00  
% 1.77/1.00  --superposition_flag                    true
% 1.77/1.00  --sup_passive_queue_type                priority_queues
% 1.77/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.77/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.77/1.00  --demod_completeness_check              fast
% 1.77/1.00  --demod_use_ground                      true
% 1.77/1.00  --sup_to_prop_solver                    passive
% 1.77/1.00  --sup_prop_simpl_new                    true
% 1.77/1.00  --sup_prop_simpl_given                  true
% 1.77/1.00  --sup_fun_splitting                     false
% 1.77/1.00  --sup_smt_interval                      50000
% 1.77/1.00  
% 1.77/1.00  ------ Superposition Simplification Setup
% 1.77/1.00  
% 1.77/1.00  --sup_indices_passive                   []
% 1.77/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.77/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.77/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.77/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.77/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.77/1.00  --sup_full_bw                           [BwDemod]
% 1.77/1.00  --sup_immed_triv                        [TrivRules]
% 1.77/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.77/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.77/1.00  --sup_immed_bw_main                     []
% 1.77/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.77/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.77/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.77/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.77/1.00  
% 1.77/1.00  ------ Combination Options
% 1.77/1.00  
% 1.77/1.00  --comb_res_mult                         3
% 1.77/1.00  --comb_sup_mult                         2
% 1.77/1.00  --comb_inst_mult                        10
% 1.77/1.00  
% 1.77/1.00  ------ Debug Options
% 1.77/1.00  
% 1.77/1.00  --dbg_backtrace                         false
% 1.77/1.00  --dbg_dump_prop_clauses                 false
% 1.77/1.00  --dbg_dump_prop_clauses_file            -
% 1.77/1.00  --dbg_out_stat                          false
% 1.77/1.00  
% 1.77/1.00  
% 1.77/1.00  
% 1.77/1.00  
% 1.77/1.00  ------ Proving...
% 1.77/1.00  
% 1.77/1.00  
% 1.77/1.00  % SZS status Theorem for theBenchmark.p
% 1.77/1.00  
% 1.77/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 1.77/1.00  
% 1.77/1.00  fof(f8,axiom,(
% 1.77/1.00    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 1.77/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.77/1.00  
% 1.77/1.00  fof(f14,plain,(
% 1.77/1.00    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 1.77/1.00    inference(pure_predicate_removal,[],[f8])).
% 1.77/1.00  
% 1.77/1.00  fof(f26,plain,(
% 1.77/1.00    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.77/1.00    inference(ennf_transformation,[],[f14])).
% 1.77/1.00  
% 1.77/1.00  fof(f27,plain,(
% 1.77/1.00    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.77/1.00    inference(flattening,[],[f26])).
% 1.77/1.00  
% 1.77/1.00  fof(f59,plain,(
% 1.77/1.00    ( ! [X0,X1] : (m1_pre_topc(k1_tex_2(X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.77/1.00    inference(cnf_transformation,[],[f27])).
% 1.77/1.00  
% 1.77/1.00  fof(f6,axiom,(
% 1.77/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v1_subset_1(X2,u1_struct_0(X0)))))))),
% 1.77/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.77/1.00  
% 1.77/1.00  fof(f23,plain,(
% 1.77/1.00    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : ((v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.77/1.00    inference(ennf_transformation,[],[f6])).
% 1.77/1.00  
% 1.77/1.00  fof(f24,plain,(
% 1.77/1.00    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.77/1.00    inference(flattening,[],[f23])).
% 1.77/1.00  
% 1.77/1.00  fof(f36,plain,(
% 1.77/1.00    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.77/1.00    inference(nnf_transformation,[],[f24])).
% 1.77/1.00  
% 1.77/1.00  fof(f37,plain,(
% 1.77/1.00    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.77/1.00    inference(rectify,[],[f36])).
% 1.77/1.00  
% 1.77/1.00  fof(f38,plain,(
% 1.77/1.00    ! [X1,X0] : (? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_subset_1(sK0(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK0(X0,X1) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.77/1.00    introduced(choice_axiom,[])).
% 1.77/1.00  
% 1.77/1.00  fof(f39,plain,(
% 1.77/1.00    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | (~v1_subset_1(sK0(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK0(X0,X1) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.77/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).
% 1.77/1.00  
% 1.77/1.00  fof(f54,plain,(
% 1.77/1.00    ( ! [X0,X1] : (v1_tex_2(X1,X0) | u1_struct_0(X1) = sK0(X0,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.77/1.00    inference(cnf_transformation,[],[f39])).
% 1.77/1.00  
% 1.77/1.00  fof(f12,conjecture,(
% 1.77/1.00    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 1.77/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.77/1.00  
% 1.77/1.00  fof(f13,negated_conjecture,(
% 1.77/1.00    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 1.77/1.00    inference(negated_conjecture,[],[f12])).
% 1.77/1.00  
% 1.77/1.00  fof(f34,plain,(
% 1.77/1.00    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.77/1.00    inference(ennf_transformation,[],[f13])).
% 1.77/1.00  
% 1.77/1.00  fof(f35,plain,(
% 1.77/1.00    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.77/1.00    inference(flattening,[],[f34])).
% 1.77/1.00  
% 1.77/1.00  fof(f41,plain,(
% 1.77/1.00    ? [X0] : (? [X1] : (((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.77/1.00    inference(nnf_transformation,[],[f35])).
% 1.77/1.00  
% 1.77/1.00  fof(f42,plain,(
% 1.77/1.00    ? [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.77/1.00    inference(flattening,[],[f41])).
% 1.77/1.00  
% 1.77/1.00  fof(f44,plain,(
% 1.77/1.00    ( ! [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) => ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),sK2),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,sK2),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),sK2),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,sK2),X0)) & m1_subset_1(sK2,u1_struct_0(X0)))) )),
% 1.77/1.00    introduced(choice_axiom,[])).
% 1.77/1.00  
% 1.77/1.00  fof(f43,plain,(
% 1.77/1.00    ? [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(sK1),X1),u1_struct_0(sK1)) | ~v1_tex_2(k1_tex_2(sK1,X1),sK1)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK1),X1),u1_struct_0(sK1)) | v1_tex_2(k1_tex_2(sK1,X1),sK1)) & m1_subset_1(X1,u1_struct_0(sK1))) & l1_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 1.77/1.00    introduced(choice_axiom,[])).
% 1.77/1.00  
% 1.77/1.00  fof(f45,plain,(
% 1.77/1.00    ((~v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) | ~v1_tex_2(k1_tex_2(sK1,sK2),sK1)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) | v1_tex_2(k1_tex_2(sK1,sK2),sK1)) & m1_subset_1(sK2,u1_struct_0(sK1))) & l1_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 1.77/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f42,f44,f43])).
% 1.77/1.00  
% 1.77/1.00  fof(f68,plain,(
% 1.77/1.00    ~v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) | ~v1_tex_2(k1_tex_2(sK1,sK2),sK1)),
% 1.77/1.00    inference(cnf_transformation,[],[f45])).
% 1.77/1.00  
% 1.77/1.00  fof(f64,plain,(
% 1.77/1.00    ~v2_struct_0(sK1)),
% 1.77/1.00    inference(cnf_transformation,[],[f45])).
% 1.77/1.00  
% 1.77/1.00  fof(f65,plain,(
% 1.77/1.00    l1_pre_topc(sK1)),
% 1.77/1.00    inference(cnf_transformation,[],[f45])).
% 1.77/1.00  
% 1.77/1.00  fof(f66,plain,(
% 1.77/1.00    m1_subset_1(sK2,u1_struct_0(sK1))),
% 1.77/1.00    inference(cnf_transformation,[],[f45])).
% 1.77/1.00  
% 1.77/1.00  fof(f5,axiom,(
% 1.77/1.00    ! [X0] : ((l1_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (~v2_struct_0(X1) => (~v1_tex_2(X1,X0) & ~v2_struct_0(X1)))))),
% 1.77/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.77/1.00  
% 1.77/1.00  fof(f21,plain,(
% 1.77/1.00    ! [X0] : (! [X1] : (((~v1_tex_2(X1,X0) & ~v2_struct_0(X1)) | v2_struct_0(X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0)))),
% 1.77/1.00    inference(ennf_transformation,[],[f5])).
% 1.77/1.00  
% 1.77/1.00  fof(f22,plain,(
% 1.77/1.00    ! [X0] : (! [X1] : ((~v1_tex_2(X1,X0) & ~v2_struct_0(X1)) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0))),
% 1.77/1.00    inference(flattening,[],[f21])).
% 1.77/1.00  
% 1.77/1.00  fof(f51,plain,(
% 1.77/1.00    ( ! [X0,X1] : (~v1_tex_2(X1,X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0)) )),
% 1.77/1.00    inference(cnf_transformation,[],[f22])).
% 1.77/1.00  
% 1.77/1.00  fof(f67,plain,(
% 1.77/1.00    v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) | v1_tex_2(k1_tex_2(sK1,sK2),sK1)),
% 1.77/1.00    inference(cnf_transformation,[],[f45])).
% 1.77/1.00  
% 1.77/1.00  fof(f2,axiom,(
% 1.77/1.00    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.77/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.77/1.00  
% 1.77/1.00  fof(f17,plain,(
% 1.77/1.00    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.77/1.00    inference(ennf_transformation,[],[f2])).
% 1.77/1.00  
% 1.77/1.00  fof(f47,plain,(
% 1.77/1.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.77/1.00    inference(cnf_transformation,[],[f17])).
% 1.77/1.00  
% 1.77/1.00  fof(f4,axiom,(
% 1.77/1.00    ! [X0] : ((l1_struct_0(X0) & ~v7_struct_0(X0)) => ~v1_zfmisc_1(u1_struct_0(X0)))),
% 1.77/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.77/1.00  
% 1.77/1.00  fof(f19,plain,(
% 1.77/1.00    ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | v7_struct_0(X0)))),
% 1.77/1.00    inference(ennf_transformation,[],[f4])).
% 1.77/1.00  
% 1.77/1.00  fof(f20,plain,(
% 1.77/1.00    ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | v7_struct_0(X0))),
% 1.77/1.00    inference(flattening,[],[f19])).
% 1.77/1.00  
% 1.77/1.00  fof(f49,plain,(
% 1.77/1.00    ( ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | v7_struct_0(X0)) )),
% 1.77/1.00    inference(cnf_transformation,[],[f20])).
% 1.77/1.00  
% 1.77/1.00  fof(f1,axiom,(
% 1.77/1.00    ! [X0] : (v1_xboole_0(X0) => v1_zfmisc_1(X0))),
% 1.77/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.77/1.00  
% 1.77/1.00  fof(f16,plain,(
% 1.77/1.00    ! [X0] : (v1_zfmisc_1(X0) | ~v1_xboole_0(X0))),
% 1.77/1.00    inference(ennf_transformation,[],[f1])).
% 1.77/1.00  
% 1.77/1.00  fof(f46,plain,(
% 1.77/1.00    ( ! [X0] : (v1_zfmisc_1(X0) | ~v1_xboole_0(X0)) )),
% 1.77/1.00    inference(cnf_transformation,[],[f16])).
% 1.77/1.00  
% 1.77/1.00  fof(f10,axiom,(
% 1.77/1.00    ! [X0] : ((~v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,X0) => v1_subset_1(k6_domain_1(X0,X1),X0)))),
% 1.77/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.77/1.00  
% 1.77/1.00  fof(f30,plain,(
% 1.77/1.00    ! [X0] : (! [X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | (v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 1.77/1.00    inference(ennf_transformation,[],[f10])).
% 1.77/1.00  
% 1.77/1.00  fof(f31,plain,(
% 1.77/1.00    ! [X0] : (! [X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 1.77/1.00    inference(flattening,[],[f30])).
% 1.77/1.00  
% 1.77/1.00  fof(f62,plain,(
% 1.77/1.00    ( ! [X0,X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0) | v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 1.77/1.00    inference(cnf_transformation,[],[f31])).
% 1.77/1.00  
% 1.77/1.00  fof(f9,axiom,(
% 1.77/1.00    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 1.77/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.77/1.00  
% 1.77/1.00  fof(f15,plain,(
% 1.77/1.00    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 1.77/1.00    inference(pure_predicate_removal,[],[f9])).
% 1.77/1.00  
% 1.77/1.00  fof(f28,plain,(
% 1.77/1.00    ! [X0,X1] : ((v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.77/1.00    inference(ennf_transformation,[],[f15])).
% 1.77/1.00  
% 1.77/1.00  fof(f29,plain,(
% 1.77/1.00    ! [X0,X1] : ((v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.77/1.00    inference(flattening,[],[f28])).
% 1.77/1.00  
% 1.77/1.00  fof(f60,plain,(
% 1.77/1.00    ( ! [X0,X1] : (~v2_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.77/1.00    inference(cnf_transformation,[],[f29])).
% 1.77/1.00  
% 1.77/1.00  fof(f53,plain,(
% 1.77/1.00    ( ! [X0,X1] : (v1_tex_2(X1,X0) | m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.77/1.00    inference(cnf_transformation,[],[f39])).
% 1.77/1.00  
% 1.77/1.00  fof(f7,axiom,(
% 1.77/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 1.77/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.77/1.00  
% 1.77/1.00  fof(f25,plain,(
% 1.77/1.00    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.77/1.00    inference(ennf_transformation,[],[f7])).
% 1.77/1.00  
% 1.77/1.00  fof(f40,plain,(
% 1.77/1.00    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.77/1.00    inference(nnf_transformation,[],[f25])).
% 1.77/1.00  
% 1.77/1.00  fof(f57,plain,(
% 1.77/1.00    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.77/1.00    inference(cnf_transformation,[],[f40])).
% 1.77/1.00  
% 1.77/1.00  fof(f55,plain,(
% 1.77/1.00    ( ! [X0,X1] : (v1_tex_2(X1,X0) | ~v1_subset_1(sK0(X0,X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.77/1.00    inference(cnf_transformation,[],[f39])).
% 1.77/1.00  
% 1.77/1.00  fof(f11,axiom,(
% 1.77/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~(v7_struct_0(X0) & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 1.77/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.77/1.00  
% 1.77/1.00  fof(f32,plain,(
% 1.77/1.00    ! [X0] : (! [X1] : ((~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.77/1.00    inference(ennf_transformation,[],[f11])).
% 1.77/1.00  
% 1.77/1.00  fof(f33,plain,(
% 1.77/1.00    ! [X0] : (! [X1] : (~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.77/1.00    inference(flattening,[],[f32])).
% 1.77/1.00  
% 1.77/1.00  fof(f63,plain,(
% 1.77/1.00    ( ! [X0,X1] : (~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.77/1.00    inference(cnf_transformation,[],[f33])).
% 1.77/1.00  
% 1.77/1.00  fof(f3,axiom,(
% 1.77/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.77/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.77/1.00  
% 1.77/1.00  fof(f18,plain,(
% 1.77/1.00    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.77/1.00    inference(ennf_transformation,[],[f3])).
% 1.77/1.00  
% 1.77/1.00  fof(f48,plain,(
% 1.77/1.00    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.77/1.00    inference(cnf_transformation,[],[f18])).
% 1.77/1.00  
% 1.77/1.00  fof(f61,plain,(
% 1.77/1.00    ( ! [X0,X1] : (v7_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.77/1.00    inference(cnf_transformation,[],[f29])).
% 1.77/1.00  
% 1.77/1.00  cnf(c_12,plain,
% 1.77/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.77/1.00      | m1_pre_topc(k1_tex_2(X1,X0),X1)
% 1.77/1.00      | v2_struct_0(X1)
% 1.77/1.00      | ~ l1_pre_topc(X1) ),
% 1.77/1.00      inference(cnf_transformation,[],[f59]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_3309,plain,
% 1.77/1.00      ( ~ m1_subset_1(X0_45,u1_struct_0(X0_46))
% 1.77/1.00      | m1_pre_topc(k1_tex_2(X0_46,X0_45),X0_46)
% 1.77/1.00      | v2_struct_0(X0_46)
% 1.77/1.00      | ~ l1_pre_topc(X0_46) ),
% 1.77/1.00      inference(subtyping,[status(esa)],[c_12]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_3751,plain,
% 1.77/1.00      ( m1_subset_1(X0_45,u1_struct_0(X0_46)) != iProver_top
% 1.77/1.00      | m1_pre_topc(k1_tex_2(X0_46,X0_45),X0_46) = iProver_top
% 1.77/1.00      | v2_struct_0(X0_46) = iProver_top
% 1.77/1.00      | l1_pre_topc(X0_46) != iProver_top ),
% 1.77/1.00      inference(predicate_to_equality,[status(thm)],[c_3309]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_7,plain,
% 1.77/1.00      ( v1_tex_2(X0,X1)
% 1.77/1.00      | ~ m1_pre_topc(X0,X1)
% 1.77/1.00      | ~ l1_pre_topc(X1)
% 1.77/1.00      | sK0(X1,X0) = u1_struct_0(X0) ),
% 1.77/1.00      inference(cnf_transformation,[],[f54]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_3314,plain,
% 1.77/1.00      ( v1_tex_2(X0_46,X1_46)
% 1.77/1.00      | ~ m1_pre_topc(X0_46,X1_46)
% 1.77/1.00      | ~ l1_pre_topc(X1_46)
% 1.77/1.00      | sK0(X1_46,X0_46) = u1_struct_0(X0_46) ),
% 1.77/1.00      inference(subtyping,[status(esa)],[c_7]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_3746,plain,
% 1.77/1.00      ( sK0(X0_46,X1_46) = u1_struct_0(X1_46)
% 1.77/1.00      | v1_tex_2(X1_46,X0_46) = iProver_top
% 1.77/1.00      | m1_pre_topc(X1_46,X0_46) != iProver_top
% 1.77/1.00      | l1_pre_topc(X0_46) != iProver_top ),
% 1.77/1.00      inference(predicate_to_equality,[status(thm)],[c_3314]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_4237,plain,
% 1.77/1.00      ( sK0(X0_46,k1_tex_2(X0_46,X0_45)) = u1_struct_0(k1_tex_2(X0_46,X0_45))
% 1.77/1.00      | m1_subset_1(X0_45,u1_struct_0(X0_46)) != iProver_top
% 1.77/1.00      | v1_tex_2(k1_tex_2(X0_46,X0_45),X0_46) = iProver_top
% 1.77/1.00      | v2_struct_0(X0_46) = iProver_top
% 1.77/1.00      | l1_pre_topc(X0_46) != iProver_top ),
% 1.77/1.00      inference(superposition,[status(thm)],[c_3751,c_3746]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_18,negated_conjecture,
% 1.77/1.00      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 1.77/1.00      | ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
% 1.77/1.00      inference(cnf_transformation,[],[f68]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_3306,negated_conjecture,
% 1.77/1.00      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 1.77/1.00      | ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
% 1.77/1.00      inference(subtyping,[status(esa)],[c_18]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_3754,plain,
% 1.77/1.00      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top
% 1.77/1.00      | v1_tex_2(k1_tex_2(sK1,sK2),sK1) != iProver_top ),
% 1.77/1.00      inference(predicate_to_equality,[status(thm)],[c_3306]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_22,negated_conjecture,
% 1.77/1.00      ( ~ v2_struct_0(sK1) ),
% 1.77/1.00      inference(cnf_transformation,[],[f64]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_23,plain,
% 1.77/1.00      ( v2_struct_0(sK1) != iProver_top ),
% 1.77/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_21,negated_conjecture,
% 1.77/1.00      ( l1_pre_topc(sK1) ),
% 1.77/1.00      inference(cnf_transformation,[],[f65]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_24,plain,
% 1.77/1.00      ( l1_pre_topc(sK1) = iProver_top ),
% 1.77/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_20,negated_conjecture,
% 1.77/1.00      ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 1.77/1.00      inference(cnf_transformation,[],[f66]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_25,plain,
% 1.77/1.00      ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
% 1.77/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_27,plain,
% 1.77/1.00      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top
% 1.77/1.00      | v1_tex_2(k1_tex_2(sK1,sK2),sK1) != iProver_top ),
% 1.77/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_4,plain,
% 1.77/1.00      ( ~ v1_tex_2(X0,X1)
% 1.77/1.00      | ~ m1_pre_topc(X0,X1)
% 1.77/1.00      | v2_struct_0(X1)
% 1.77/1.00      | v2_struct_0(X0)
% 1.77/1.00      | ~ v7_struct_0(X1)
% 1.77/1.00      | ~ l1_pre_topc(X1) ),
% 1.77/1.00      inference(cnf_transformation,[],[f51]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_19,negated_conjecture,
% 1.77/1.00      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 1.77/1.00      | v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
% 1.77/1.00      inference(cnf_transformation,[],[f67]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_172,plain,
% 1.77/1.00      ( v1_tex_2(k1_tex_2(sK1,sK2),sK1)
% 1.77/1.00      | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) ),
% 1.77/1.00      inference(prop_impl,[status(thm)],[c_19]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_173,plain,
% 1.77/1.00      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 1.77/1.00      | v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
% 1.77/1.00      inference(renaming,[status(thm)],[c_172]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_1329,plain,
% 1.77/1.00      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 1.77/1.00      | ~ m1_pre_topc(X0,X1)
% 1.77/1.00      | v2_struct_0(X0)
% 1.77/1.00      | v2_struct_0(X1)
% 1.77/1.00      | ~ v7_struct_0(X1)
% 1.77/1.00      | ~ l1_pre_topc(X1)
% 1.77/1.00      | k1_tex_2(sK1,sK2) != X0
% 1.77/1.00      | sK1 != X1 ),
% 1.77/1.00      inference(resolution_lifted,[status(thm)],[c_4,c_173]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_1330,plain,
% 1.77/1.00      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 1.77/1.00      | ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
% 1.77/1.00      | v2_struct_0(k1_tex_2(sK1,sK2))
% 1.77/1.00      | v2_struct_0(sK1)
% 1.77/1.00      | ~ v7_struct_0(sK1)
% 1.77/1.00      | ~ l1_pre_topc(sK1) ),
% 1.77/1.00      inference(unflattening,[status(thm)],[c_1329]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_1,plain,
% 1.77/1.00      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 1.77/1.00      inference(cnf_transformation,[],[f47]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_3,plain,
% 1.77/1.00      ( v7_struct_0(X0)
% 1.77/1.00      | ~ l1_struct_0(X0)
% 1.77/1.00      | ~ v1_zfmisc_1(u1_struct_0(X0)) ),
% 1.77/1.00      inference(cnf_transformation,[],[f49]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_339,plain,
% 1.77/1.00      ( v7_struct_0(X0)
% 1.77/1.00      | ~ l1_pre_topc(X0)
% 1.77/1.00      | ~ v1_zfmisc_1(u1_struct_0(X0)) ),
% 1.77/1.00      inference(resolution,[status(thm)],[c_1,c_3]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_341,plain,
% 1.77/1.00      ( v7_struct_0(sK1)
% 1.77/1.00      | ~ l1_pre_topc(sK1)
% 1.77/1.00      | ~ v1_zfmisc_1(u1_struct_0(sK1)) ),
% 1.77/1.00      inference(instantiation,[status(thm)],[c_339]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_0,plain,
% 1.77/1.00      ( ~ v1_xboole_0(X0) | v1_zfmisc_1(X0) ),
% 1.77/1.00      inference(cnf_transformation,[],[f46]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_16,plain,
% 1.77/1.00      ( ~ m1_subset_1(X0,X1)
% 1.77/1.00      | v1_subset_1(k6_domain_1(X1,X0),X1)
% 1.77/1.00      | v1_xboole_0(X1)
% 1.77/1.00      | v1_zfmisc_1(X1) ),
% 1.77/1.00      inference(cnf_transformation,[],[f62]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_298,plain,
% 1.77/1.00      ( ~ m1_subset_1(X0,X1)
% 1.77/1.00      | v1_subset_1(k6_domain_1(X1,X0),X1)
% 1.77/1.00      | v1_zfmisc_1(X2)
% 1.77/1.00      | v1_zfmisc_1(X1)
% 1.77/1.00      | X1 != X2 ),
% 1.77/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_16]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_299,plain,
% 1.77/1.00      ( ~ m1_subset_1(X0,X1)
% 1.77/1.00      | v1_subset_1(k6_domain_1(X1,X0),X1)
% 1.77/1.00      | v1_zfmisc_1(X1) ),
% 1.77/1.00      inference(unflattening,[status(thm)],[c_298]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_1030,plain,
% 1.77/1.00      ( v1_subset_1(k6_domain_1(X0,X1),X0)
% 1.77/1.00      | v1_zfmisc_1(X0)
% 1.77/1.00      | u1_struct_0(sK1) != X0
% 1.77/1.00      | sK2 != X1 ),
% 1.77/1.00      inference(resolution_lifted,[status(thm)],[c_299,c_20]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_1031,plain,
% 1.77/1.00      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 1.77/1.00      | v1_zfmisc_1(u1_struct_0(sK1)) ),
% 1.77/1.00      inference(unflattening,[status(thm)],[c_1030]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_1332,plain,
% 1.77/1.00      ( v2_struct_0(k1_tex_2(sK1,sK2))
% 1.77/1.00      | ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
% 1.77/1.00      | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) ),
% 1.77/1.00      inference(global_propositional_subsumption,
% 1.77/1.00                [status(thm)],
% 1.77/1.00                [c_1330,c_22,c_21,c_341,c_1031]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_1333,plain,
% 1.77/1.00      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 1.77/1.00      | ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
% 1.77/1.00      | v2_struct_0(k1_tex_2(sK1,sK2)) ),
% 1.77/1.00      inference(renaming,[status(thm)],[c_1332]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_1334,plain,
% 1.77/1.00      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) = iProver_top
% 1.77/1.00      | m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top
% 1.77/1.00      | v2_struct_0(k1_tex_2(sK1,sK2)) = iProver_top ),
% 1.77/1.00      inference(predicate_to_equality,[status(thm)],[c_1333]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_3361,plain,
% 1.77/1.00      ( m1_subset_1(X0_45,u1_struct_0(X0_46)) != iProver_top
% 1.77/1.00      | m1_pre_topc(k1_tex_2(X0_46,X0_45),X0_46) = iProver_top
% 1.77/1.00      | v2_struct_0(X0_46) = iProver_top
% 1.77/1.00      | l1_pre_topc(X0_46) != iProver_top ),
% 1.77/1.00      inference(predicate_to_equality,[status(thm)],[c_3309]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_3363,plain,
% 1.77/1.00      ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 1.77/1.00      | m1_pre_topc(k1_tex_2(sK1,sK2),sK1) = iProver_top
% 1.77/1.00      | v2_struct_0(sK1) = iProver_top
% 1.77/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 1.77/1.00      inference(instantiation,[status(thm)],[c_3361]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_15,plain,
% 1.77/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.77/1.00      | v2_struct_0(X1)
% 1.77/1.00      | ~ v2_struct_0(k1_tex_2(X1,X0))
% 1.77/1.00      | ~ l1_pre_topc(X1) ),
% 1.77/1.00      inference(cnf_transformation,[],[f60]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_3308,plain,
% 1.77/1.00      ( ~ m1_subset_1(X0_45,u1_struct_0(X0_46))
% 1.77/1.00      | v2_struct_0(X0_46)
% 1.77/1.00      | ~ v2_struct_0(k1_tex_2(X0_46,X0_45))
% 1.77/1.00      | ~ l1_pre_topc(X0_46) ),
% 1.77/1.00      inference(subtyping,[status(esa)],[c_15]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_3364,plain,
% 1.77/1.00      ( m1_subset_1(X0_45,u1_struct_0(X0_46)) != iProver_top
% 1.77/1.00      | v2_struct_0(X0_46) = iProver_top
% 1.77/1.00      | v2_struct_0(k1_tex_2(X0_46,X0_45)) != iProver_top
% 1.77/1.00      | l1_pre_topc(X0_46) != iProver_top ),
% 1.77/1.00      inference(predicate_to_equality,[status(thm)],[c_3308]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_3366,plain,
% 1.77/1.00      ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 1.77/1.00      | v2_struct_0(k1_tex_2(sK1,sK2)) != iProver_top
% 1.77/1.00      | v2_struct_0(sK1) = iProver_top
% 1.77/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 1.77/1.00      inference(instantiation,[status(thm)],[c_3364]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_3958,plain,
% 1.77/1.00      ( v1_tex_2(k1_tex_2(sK1,sK2),sK1) != iProver_top ),
% 1.77/1.00      inference(global_propositional_subsumption,
% 1.77/1.00                [status(thm)],
% 1.77/1.00                [c_3754,c_23,c_24,c_25,c_27,c_1334,c_3363,c_3366]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_5215,plain,
% 1.77/1.00      ( sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(k1_tex_2(sK1,sK2))
% 1.77/1.00      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 1.77/1.00      | v2_struct_0(sK1) = iProver_top
% 1.77/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 1.77/1.00      inference(superposition,[status(thm)],[c_4237,c_3958]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_8,plain,
% 1.77/1.00      ( m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
% 1.77/1.00      | v1_tex_2(X1,X0)
% 1.77/1.00      | ~ m1_pre_topc(X1,X0)
% 1.77/1.00      | ~ l1_pre_topc(X0) ),
% 1.77/1.00      inference(cnf_transformation,[],[f53]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_3313,plain,
% 1.77/1.00      ( m1_subset_1(sK0(X0_46,X1_46),k1_zfmisc_1(u1_struct_0(X0_46)))
% 1.77/1.00      | v1_tex_2(X1_46,X0_46)
% 1.77/1.00      | ~ m1_pre_topc(X1_46,X0_46)
% 1.77/1.00      | ~ l1_pre_topc(X0_46) ),
% 1.77/1.00      inference(subtyping,[status(esa)],[c_8]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_3747,plain,
% 1.77/1.00      ( m1_subset_1(sK0(X0_46,X1_46),k1_zfmisc_1(u1_struct_0(X0_46))) = iProver_top
% 1.77/1.00      | v1_tex_2(X1_46,X0_46) = iProver_top
% 1.77/1.00      | m1_pre_topc(X1_46,X0_46) != iProver_top
% 1.77/1.00      | l1_pre_topc(X0_46) != iProver_top ),
% 1.77/1.00      inference(predicate_to_equality,[status(thm)],[c_3313]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_10,plain,
% 1.77/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.77/1.00      | v1_subset_1(X0,X1)
% 1.77/1.00      | X0 = X1 ),
% 1.77/1.00      inference(cnf_transformation,[],[f57]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_3311,plain,
% 1.77/1.00      ( ~ m1_subset_1(X0_45,k1_zfmisc_1(X1_45))
% 1.77/1.00      | v1_subset_1(X0_45,X1_45)
% 1.77/1.00      | X0_45 = X1_45 ),
% 1.77/1.00      inference(subtyping,[status(esa)],[c_10]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_3749,plain,
% 1.77/1.00      ( X0_45 = X1_45
% 1.77/1.00      | m1_subset_1(X0_45,k1_zfmisc_1(X1_45)) != iProver_top
% 1.77/1.00      | v1_subset_1(X0_45,X1_45) = iProver_top ),
% 1.77/1.00      inference(predicate_to_equality,[status(thm)],[c_3311]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_4652,plain,
% 1.77/1.00      ( sK0(X0_46,X1_46) = u1_struct_0(X0_46)
% 1.77/1.00      | v1_subset_1(sK0(X0_46,X1_46),u1_struct_0(X0_46)) = iProver_top
% 1.77/1.00      | v1_tex_2(X1_46,X0_46) = iProver_top
% 1.77/1.00      | m1_pre_topc(X1_46,X0_46) != iProver_top
% 1.77/1.00      | l1_pre_topc(X0_46) != iProver_top ),
% 1.77/1.00      inference(superposition,[status(thm)],[c_3747,c_3749]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_6,plain,
% 1.77/1.00      ( ~ v1_subset_1(sK0(X0,X1),u1_struct_0(X0))
% 1.77/1.00      | v1_tex_2(X1,X0)
% 1.77/1.00      | ~ m1_pre_topc(X1,X0)
% 1.77/1.00      | ~ l1_pre_topc(X0) ),
% 1.77/1.00      inference(cnf_transformation,[],[f55]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_3315,plain,
% 1.77/1.00      ( ~ v1_subset_1(sK0(X0_46,X1_46),u1_struct_0(X0_46))
% 1.77/1.00      | v1_tex_2(X1_46,X0_46)
% 1.77/1.00      | ~ m1_pre_topc(X1_46,X0_46)
% 1.77/1.00      | ~ l1_pre_topc(X0_46) ),
% 1.77/1.00      inference(subtyping,[status(esa)],[c_6]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_3351,plain,
% 1.77/1.00      ( v1_subset_1(sK0(X0_46,X1_46),u1_struct_0(X0_46)) != iProver_top
% 1.77/1.00      | v1_tex_2(X1_46,X0_46) = iProver_top
% 1.77/1.00      | m1_pre_topc(X1_46,X0_46) != iProver_top
% 1.77/1.00      | l1_pre_topc(X0_46) != iProver_top ),
% 1.77/1.00      inference(predicate_to_equality,[status(thm)],[c_3315]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_4817,plain,
% 1.77/1.00      ( sK0(X0_46,X1_46) = u1_struct_0(X0_46)
% 1.77/1.00      | v1_tex_2(X1_46,X0_46) = iProver_top
% 1.77/1.00      | m1_pre_topc(X1_46,X0_46) != iProver_top
% 1.77/1.00      | l1_pre_topc(X0_46) != iProver_top ),
% 1.77/1.00      inference(global_propositional_subsumption,
% 1.77/1.00                [status(thm)],
% 1.77/1.00                [c_4652,c_3351]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_4825,plain,
% 1.77/1.00      ( sK0(X0_46,k1_tex_2(X0_46,X0_45)) = u1_struct_0(X0_46)
% 1.77/1.00      | m1_subset_1(X0_45,u1_struct_0(X0_46)) != iProver_top
% 1.77/1.00      | v1_tex_2(k1_tex_2(X0_46,X0_45),X0_46) = iProver_top
% 1.77/1.00      | v2_struct_0(X0_46) = iProver_top
% 1.77/1.00      | l1_pre_topc(X0_46) != iProver_top ),
% 1.77/1.00      inference(superposition,[status(thm)],[c_3751,c_4817]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_4835,plain,
% 1.77/1.00      ( sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(sK1)
% 1.77/1.00      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 1.77/1.00      | v2_struct_0(sK1) = iProver_top
% 1.77/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 1.77/1.00      inference(superposition,[status(thm)],[c_4825,c_3958]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_170,plain,
% 1.77/1.00      ( ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1)
% 1.77/1.00      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) ),
% 1.77/1.00      inference(prop_impl,[status(thm)],[c_18]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_171,plain,
% 1.77/1.00      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 1.77/1.00      | ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
% 1.77/1.00      inference(renaming,[status(thm)],[c_170]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_1258,plain,
% 1.77/1.00      ( m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
% 1.77/1.00      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 1.77/1.00      | ~ m1_pre_topc(X1,X0)
% 1.77/1.00      | ~ l1_pre_topc(X0)
% 1.77/1.00      | k1_tex_2(sK1,sK2) != X1
% 1.77/1.00      | sK1 != X0 ),
% 1.77/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_171]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_1259,plain,
% 1.77/1.00      ( m1_subset_1(sK0(sK1,k1_tex_2(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.77/1.00      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 1.77/1.00      | ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
% 1.77/1.00      | ~ l1_pre_topc(sK1) ),
% 1.77/1.00      inference(unflattening,[status(thm)],[c_1258]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_1275,plain,
% 1.77/1.00      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 1.77/1.00      | ~ v1_subset_1(sK0(X0,X1),u1_struct_0(X0))
% 1.77/1.00      | ~ m1_pre_topc(X1,X0)
% 1.77/1.00      | ~ l1_pre_topc(X0)
% 1.77/1.00      | k1_tex_2(sK1,sK2) != X1
% 1.77/1.00      | sK1 != X0 ),
% 1.77/1.00      inference(resolution_lifted,[status(thm)],[c_6,c_171]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_1276,plain,
% 1.77/1.00      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 1.77/1.00      | ~ v1_subset_1(sK0(sK1,k1_tex_2(sK1,sK2)),u1_struct_0(sK1))
% 1.77/1.00      | ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
% 1.77/1.00      | ~ l1_pre_topc(sK1) ),
% 1.77/1.00      inference(unflattening,[status(thm)],[c_1275]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_3362,plain,
% 1.77/1.00      ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 1.77/1.00      | m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
% 1.77/1.00      | v2_struct_0(sK1)
% 1.77/1.00      | ~ l1_pre_topc(sK1) ),
% 1.77/1.00      inference(instantiation,[status(thm)],[c_3309]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_3365,plain,
% 1.77/1.00      ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 1.77/1.00      | ~ v2_struct_0(k1_tex_2(sK1,sK2))
% 1.77/1.00      | v2_struct_0(sK1)
% 1.77/1.00      | ~ l1_pre_topc(sK1) ),
% 1.77/1.00      inference(instantiation,[status(thm)],[c_3308]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_3997,plain,
% 1.77/1.00      ( ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.77/1.00      | v1_subset_1(X0_45,u1_struct_0(sK1))
% 1.77/1.00      | X0_45 = u1_struct_0(sK1) ),
% 1.77/1.00      inference(instantiation,[status(thm)],[c_3311]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_4159,plain,
% 1.77/1.00      ( ~ m1_subset_1(sK0(sK1,k1_tex_2(sK1,X0_45)),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.77/1.00      | v1_subset_1(sK0(sK1,k1_tex_2(sK1,X0_45)),u1_struct_0(sK1))
% 1.77/1.00      | sK0(sK1,k1_tex_2(sK1,X0_45)) = u1_struct_0(sK1) ),
% 1.77/1.00      inference(instantiation,[status(thm)],[c_3997]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_4162,plain,
% 1.77/1.00      ( ~ m1_subset_1(sK0(sK1,k1_tex_2(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.77/1.00      | v1_subset_1(sK0(sK1,k1_tex_2(sK1,sK2)),u1_struct_0(sK1))
% 1.77/1.00      | sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(sK1) ),
% 1.77/1.00      inference(instantiation,[status(thm)],[c_4159]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_4984,plain,
% 1.77/1.00      ( sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(sK1) ),
% 1.77/1.00      inference(global_propositional_subsumption,
% 1.77/1.00                [status(thm)],
% 1.77/1.00                [c_4835,c_22,c_21,c_20,c_1259,c_1276,c_1333,c_3362,
% 1.77/1.00                 c_3365,c_4162]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_5235,plain,
% 1.77/1.00      ( u1_struct_0(k1_tex_2(sK1,sK2)) = u1_struct_0(sK1)
% 1.77/1.00      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 1.77/1.00      | v2_struct_0(sK1) = iProver_top
% 1.77/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 1.77/1.00      inference(light_normalisation,[status(thm)],[c_5215,c_4984]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_5323,plain,
% 1.77/1.00      ( u1_struct_0(k1_tex_2(sK1,sK2)) = u1_struct_0(sK1) ),
% 1.77/1.00      inference(global_propositional_subsumption,
% 1.77/1.00                [status(thm)],
% 1.77/1.00                [c_5235,c_23,c_24,c_25]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_17,plain,
% 1.77/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.77/1.00      | ~ v1_subset_1(k6_domain_1(u1_struct_0(X1),X0),u1_struct_0(X1))
% 1.77/1.00      | v2_struct_0(X1)
% 1.77/1.00      | ~ v7_struct_0(X1)
% 1.77/1.00      | ~ l1_struct_0(X1) ),
% 1.77/1.00      inference(cnf_transformation,[],[f63]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_353,plain,
% 1.77/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.77/1.00      | ~ v1_subset_1(k6_domain_1(u1_struct_0(X1),X0),u1_struct_0(X1))
% 1.77/1.00      | v2_struct_0(X1)
% 1.77/1.00      | ~ v7_struct_0(X1)
% 1.77/1.00      | ~ l1_pre_topc(X2)
% 1.77/1.00      | X1 != X2 ),
% 1.77/1.00      inference(resolution_lifted,[status(thm)],[c_1,c_17]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_354,plain,
% 1.77/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.77/1.00      | ~ v1_subset_1(k6_domain_1(u1_struct_0(X1),X0),u1_struct_0(X1))
% 1.77/1.00      | v2_struct_0(X1)
% 1.77/1.00      | ~ v7_struct_0(X1)
% 1.77/1.00      | ~ l1_pre_topc(X1) ),
% 1.77/1.00      inference(unflattening,[status(thm)],[c_353]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_3299,plain,
% 1.77/1.00      ( ~ m1_subset_1(X0_45,u1_struct_0(X0_46))
% 1.77/1.00      | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0_46),X0_45),u1_struct_0(X0_46))
% 1.77/1.00      | v2_struct_0(X0_46)
% 1.77/1.00      | ~ v7_struct_0(X0_46)
% 1.77/1.00      | ~ l1_pre_topc(X0_46) ),
% 1.77/1.00      inference(subtyping,[status(esa)],[c_354]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_3761,plain,
% 1.77/1.00      ( m1_subset_1(X0_45,u1_struct_0(X0_46)) != iProver_top
% 1.77/1.00      | v1_subset_1(k6_domain_1(u1_struct_0(X0_46),X0_45),u1_struct_0(X0_46)) != iProver_top
% 1.77/1.00      | v2_struct_0(X0_46) = iProver_top
% 1.77/1.00      | v7_struct_0(X0_46) != iProver_top
% 1.77/1.00      | l1_pre_topc(X0_46) != iProver_top ),
% 1.77/1.00      inference(predicate_to_equality,[status(thm)],[c_3299]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_5331,plain,
% 1.77/1.00      ( m1_subset_1(X0_45,u1_struct_0(k1_tex_2(sK1,sK2))) != iProver_top
% 1.77/1.00      | v1_subset_1(k6_domain_1(u1_struct_0(sK1),X0_45),u1_struct_0(sK1)) != iProver_top
% 1.77/1.00      | v2_struct_0(k1_tex_2(sK1,sK2)) = iProver_top
% 1.77/1.00      | v7_struct_0(k1_tex_2(sK1,sK2)) != iProver_top
% 1.77/1.00      | l1_pre_topc(k1_tex_2(sK1,sK2)) != iProver_top ),
% 1.77/1.00      inference(superposition,[status(thm)],[c_5323,c_3761]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_5366,plain,
% 1.77/1.00      ( m1_subset_1(X0_45,u1_struct_0(sK1)) != iProver_top
% 1.77/1.00      | v1_subset_1(k6_domain_1(u1_struct_0(sK1),X0_45),u1_struct_0(sK1)) != iProver_top
% 1.77/1.00      | v2_struct_0(k1_tex_2(sK1,sK2)) = iProver_top
% 1.77/1.00      | v7_struct_0(k1_tex_2(sK1,sK2)) != iProver_top
% 1.77/1.00      | l1_pre_topc(k1_tex_2(sK1,sK2)) != iProver_top ),
% 1.77/1.00      inference(light_normalisation,[status(thm)],[c_5331,c_5323]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_5437,plain,
% 1.77/1.00      ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 1.77/1.00      | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top
% 1.77/1.00      | v2_struct_0(k1_tex_2(sK1,sK2)) = iProver_top
% 1.77/1.00      | v7_struct_0(k1_tex_2(sK1,sK2)) != iProver_top
% 1.77/1.00      | l1_pre_topc(k1_tex_2(sK1,sK2)) != iProver_top ),
% 1.77/1.00      inference(instantiation,[status(thm)],[c_5366]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_2,plain,
% 1.77/1.00      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 1.77/1.00      inference(cnf_transformation,[],[f48]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_3317,plain,
% 1.77/1.00      ( ~ m1_pre_topc(X0_46,X1_46)
% 1.77/1.00      | ~ l1_pre_topc(X1_46)
% 1.77/1.00      | l1_pre_topc(X0_46) ),
% 1.77/1.00      inference(subtyping,[status(esa)],[c_2]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_4051,plain,
% 1.77/1.00      ( ~ m1_pre_topc(k1_tex_2(X0_46,X0_45),X1_46)
% 1.77/1.00      | ~ l1_pre_topc(X1_46)
% 1.77/1.00      | l1_pre_topc(k1_tex_2(X0_46,X0_45)) ),
% 1.77/1.00      inference(instantiation,[status(thm)],[c_3317]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_4052,plain,
% 1.77/1.00      ( m1_pre_topc(k1_tex_2(X0_46,X0_45),X1_46) != iProver_top
% 1.77/1.00      | l1_pre_topc(X1_46) != iProver_top
% 1.77/1.00      | l1_pre_topc(k1_tex_2(X0_46,X0_45)) = iProver_top ),
% 1.77/1.00      inference(predicate_to_equality,[status(thm)],[c_4051]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_4054,plain,
% 1.77/1.00      ( m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top
% 1.77/1.00      | l1_pre_topc(k1_tex_2(sK1,sK2)) = iProver_top
% 1.77/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 1.77/1.00      inference(instantiation,[status(thm)],[c_4052]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_14,plain,
% 1.77/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.77/1.00      | v2_struct_0(X1)
% 1.77/1.00      | v7_struct_0(k1_tex_2(X1,X0))
% 1.77/1.00      | ~ l1_pre_topc(X1) ),
% 1.77/1.00      inference(cnf_transformation,[],[f61]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_3307,plain,
% 1.77/1.00      ( ~ m1_subset_1(X0_45,u1_struct_0(X0_46))
% 1.77/1.00      | v2_struct_0(X0_46)
% 1.77/1.00      | v7_struct_0(k1_tex_2(X0_46,X0_45))
% 1.77/1.00      | ~ l1_pre_topc(X0_46) ),
% 1.77/1.00      inference(subtyping,[status(esa)],[c_14]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_3367,plain,
% 1.77/1.00      ( m1_subset_1(X0_45,u1_struct_0(X0_46)) != iProver_top
% 1.77/1.00      | v2_struct_0(X0_46) = iProver_top
% 1.77/1.00      | v7_struct_0(k1_tex_2(X0_46,X0_45)) = iProver_top
% 1.77/1.00      | l1_pre_topc(X0_46) != iProver_top ),
% 1.77/1.00      inference(predicate_to_equality,[status(thm)],[c_3307]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_3369,plain,
% 1.77/1.00      ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 1.77/1.00      | v2_struct_0(sK1) = iProver_top
% 1.77/1.00      | v7_struct_0(k1_tex_2(sK1,sK2)) = iProver_top
% 1.77/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 1.77/1.00      inference(instantiation,[status(thm)],[c_3367]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(contradiction,plain,
% 1.77/1.00      ( $false ),
% 1.77/1.00      inference(minisat,
% 1.77/1.00                [status(thm)],
% 1.77/1.00                [c_5437,c_4054,c_3369,c_3366,c_3363,c_1334,c_25,c_24,
% 1.77/1.00                 c_23]) ).
% 1.77/1.00  
% 1.77/1.00  
% 1.77/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 1.77/1.00  
% 1.77/1.00  ------                               Statistics
% 1.77/1.00  
% 1.77/1.00  ------ General
% 1.77/1.00  
% 1.77/1.00  abstr_ref_over_cycles:                  0
% 1.77/1.00  abstr_ref_under_cycles:                 0
% 1.77/1.00  gc_basic_clause_elim:                   0
% 1.77/1.00  forced_gc_time:                         0
% 1.77/1.00  parsing_time:                           0.008
% 1.77/1.00  unif_index_cands_time:                  0.
% 1.77/1.00  unif_index_add_time:                    0.
% 1.77/1.00  orderings_time:                         0.
% 1.77/1.00  out_proof_time:                         0.008
% 1.77/1.00  total_time:                             0.158
% 1.77/1.00  num_of_symbols:                         50
% 1.77/1.00  num_of_terms:                           3198
% 1.77/1.00  
% 1.77/1.00  ------ Preprocessing
% 1.77/1.00  
% 1.77/1.00  num_of_splits:                          0
% 1.77/1.00  num_of_split_atoms:                     0
% 1.77/1.00  num_of_reused_defs:                     0
% 1.77/1.00  num_eq_ax_congr_red:                    11
% 1.77/1.00  num_of_sem_filtered_clauses:            1
% 1.77/1.00  num_of_subtypes:                        2
% 1.77/1.00  monotx_restored_types:                  1
% 1.77/1.00  sat_num_of_epr_types:                   0
% 1.77/1.00  sat_num_of_non_cyclic_types:            0
% 1.77/1.00  sat_guarded_non_collapsed_types:        0
% 1.77/1.00  num_pure_diseq_elim:                    0
% 1.77/1.00  simp_replaced_by:                       0
% 1.77/1.00  res_preprocessed:                       109
% 1.77/1.00  prep_upred:                             0
% 1.77/1.00  prep_unflattend:                        133
% 1.77/1.00  smt_new_axioms:                         0
% 1.77/1.00  pred_elim_cands:                        8
% 1.77/1.00  pred_elim:                              2
% 1.77/1.00  pred_elim_cl:                           2
% 1.77/1.00  pred_elim_cycles:                       15
% 1.77/1.00  merged_defs:                            4
% 1.77/1.00  merged_defs_ncl:                        0
% 1.77/1.00  bin_hyper_res:                          4
% 1.77/1.00  prep_cycles:                            4
% 1.77/1.00  pred_elim_time:                         0.049
% 1.77/1.00  splitting_time:                         0.
% 1.77/1.00  sem_filter_time:                        0.
% 1.77/1.00  monotx_time:                            0.001
% 1.77/1.00  subtype_inf_time:                       0.001
% 1.77/1.00  
% 1.77/1.00  ------ Problem properties
% 1.77/1.00  
% 1.77/1.00  clauses:                                19
% 1.77/1.00  conjectures:                            5
% 1.77/1.00  epr:                                    4
% 1.77/1.00  horn:                                   11
% 1.77/1.00  ground:                                 5
% 1.77/1.00  unary:                                  3
% 1.77/1.00  binary:                                 3
% 1.77/1.00  lits:                                   61
% 1.77/1.00  lits_eq:                                2
% 1.77/1.00  fd_pure:                                0
% 1.77/1.00  fd_pseudo:                              0
% 1.77/1.00  fd_cond:                                0
% 1.77/1.00  fd_pseudo_cond:                         1
% 1.77/1.00  ac_symbols:                             0
% 1.77/1.00  
% 1.77/1.00  ------ Propositional Solver
% 1.77/1.00  
% 1.77/1.00  prop_solver_calls:                      28
% 1.77/1.00  prop_fast_solver_calls:                 1463
% 1.77/1.00  smt_solver_calls:                       0
% 1.77/1.00  smt_fast_solver_calls:                  0
% 1.77/1.00  prop_num_of_clauses:                    988
% 1.77/1.00  prop_preprocess_simplified:             4688
% 1.77/1.00  prop_fo_subsumed:                       56
% 1.77/1.00  prop_solver_time:                       0.
% 1.77/1.00  smt_solver_time:                        0.
% 1.77/1.00  smt_fast_solver_time:                   0.
% 1.77/1.00  prop_fast_solver_time:                  0.
% 1.77/1.00  prop_unsat_core_time:                   0.
% 1.77/1.00  
% 1.77/1.00  ------ QBF
% 1.77/1.00  
% 1.77/1.00  qbf_q_res:                              0
% 1.77/1.00  qbf_num_tautologies:                    0
% 1.77/1.00  qbf_prep_cycles:                        0
% 1.77/1.00  
% 1.77/1.00  ------ BMC1
% 1.77/1.00  
% 1.77/1.00  bmc1_current_bound:                     -1
% 1.77/1.00  bmc1_last_solved_bound:                 -1
% 1.77/1.00  bmc1_unsat_core_size:                   -1
% 1.77/1.00  bmc1_unsat_core_parents_size:           -1
% 1.77/1.00  bmc1_merge_next_fun:                    0
% 1.77/1.00  bmc1_unsat_core_clauses_time:           0.
% 1.77/1.00  
% 1.77/1.00  ------ Instantiation
% 1.77/1.00  
% 1.77/1.00  inst_num_of_clauses:                    276
% 1.77/1.00  inst_num_in_passive:                    93
% 1.77/1.00  inst_num_in_active:                     161
% 1.77/1.00  inst_num_in_unprocessed:                22
% 1.77/1.00  inst_num_of_loops:                      170
% 1.77/1.00  inst_num_of_learning_restarts:          0
% 1.77/1.00  inst_num_moves_active_passive:          5
% 1.77/1.00  inst_lit_activity:                      0
% 1.77/1.00  inst_lit_activity_moves:                0
% 1.77/1.00  inst_num_tautologies:                   0
% 1.77/1.00  inst_num_prop_implied:                  0
% 1.77/1.00  inst_num_existing_simplified:           0
% 1.77/1.00  inst_num_eq_res_simplified:             0
% 1.77/1.00  inst_num_child_elim:                    0
% 1.77/1.00  inst_num_of_dismatching_blockings:      67
% 1.77/1.00  inst_num_of_non_proper_insts:           306
% 1.77/1.00  inst_num_of_duplicates:                 0
% 1.77/1.00  inst_inst_num_from_inst_to_res:         0
% 1.77/1.00  inst_dismatching_checking_time:         0.
% 1.77/1.00  
% 1.77/1.00  ------ Resolution
% 1.77/1.00  
% 1.77/1.00  res_num_of_clauses:                     0
% 1.77/1.00  res_num_in_passive:                     0
% 1.77/1.00  res_num_in_active:                      0
% 1.77/1.00  res_num_of_loops:                       113
% 1.77/1.00  res_forward_subset_subsumed:            43
% 1.77/1.00  res_backward_subset_subsumed:           0
% 1.77/1.00  res_forward_subsumed:                   0
% 1.77/1.00  res_backward_subsumed:                  0
% 1.77/1.00  res_forward_subsumption_resolution:     0
% 1.77/1.00  res_backward_subsumption_resolution:    0
% 1.77/1.00  res_clause_to_clause_subsumption:       146
% 1.77/1.00  res_orphan_elimination:                 0
% 1.77/1.00  res_tautology_del:                      47
% 1.77/1.00  res_num_eq_res_simplified:              0
% 1.77/1.00  res_num_sel_changes:                    0
% 1.77/1.00  res_moves_from_active_to_pass:          0
% 1.77/1.00  
% 1.77/1.00  ------ Superposition
% 1.77/1.00  
% 1.77/1.00  sup_time_total:                         0.
% 1.77/1.00  sup_time_generating:                    0.
% 1.77/1.00  sup_time_sim_full:                      0.
% 1.77/1.00  sup_time_sim_immed:                     0.
% 1.77/1.00  
% 1.77/1.00  sup_num_of_clauses:                     41
% 1.77/1.00  sup_num_in_active:                      33
% 1.77/1.00  sup_num_in_passive:                     8
% 1.77/1.00  sup_num_of_loops:                       32
% 1.77/1.00  sup_fw_superposition:                   6
% 1.77/1.00  sup_bw_superposition:                   24
% 1.77/1.00  sup_immediate_simplified:               7
% 1.77/1.00  sup_given_eliminated:                   0
% 1.77/1.00  comparisons_done:                       0
% 1.77/1.00  comparisons_avoided:                    0
% 1.77/1.00  
% 1.77/1.00  ------ Simplifications
% 1.77/1.00  
% 1.77/1.00  
% 1.77/1.00  sim_fw_subset_subsumed:                 2
% 1.77/1.00  sim_bw_subset_subsumed:                 0
% 1.77/1.00  sim_fw_subsumed:                        0
% 1.77/1.00  sim_bw_subsumed:                        0
% 1.77/1.00  sim_fw_subsumption_res:                 0
% 1.77/1.00  sim_bw_subsumption_res:                 0
% 1.77/1.00  sim_tautology_del:                      0
% 1.77/1.00  sim_eq_tautology_del:                   1
% 1.77/1.00  sim_eq_res_simp:                        0
% 1.77/1.00  sim_fw_demodulated:                     0
% 1.77/1.00  sim_bw_demodulated:                     0
% 1.77/1.00  sim_light_normalised:                   5
% 1.77/1.00  sim_joinable_taut:                      0
% 1.77/1.00  sim_joinable_simp:                      0
% 1.77/1.00  sim_ac_normalised:                      0
% 1.77/1.00  sim_smt_subsumption:                    0
% 1.77/1.00  
%------------------------------------------------------------------------------
