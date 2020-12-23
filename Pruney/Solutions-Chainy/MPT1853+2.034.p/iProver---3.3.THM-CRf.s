%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:25:41 EST 2020

% Result     : Theorem 3.62s
% Output     : CNFRefutation 3.62s
% Verified   : 
% Statistics : Number of formulae       :  189 (3414 expanded)
%              Number of clauses        :  112 ( 991 expanded)
%              Number of leaves         :   18 ( 685 expanded)
%              Depth                    :   26
%              Number of atoms          :  700 (17110 expanded)
%              Number of equality atoms :  176 (1363 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( v1_tex_2(k1_tex_2(X0,X1),X0)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f52,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f53,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f52])).

fof(f62,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f53])).

fof(f63,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f62])).

fof(f65,plain,(
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

fof(f64,plain,
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

fof(f66,plain,
    ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
      | ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2) )
    & ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
      | v1_tex_2(k1_tex_2(sK2,sK3),sK2) )
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l1_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f63,f65,f64])).

fof(f98,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f66])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f96,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f66])).

fof(f97,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f66])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f79,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f76,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f12,axiom,(
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
    inference(ennf_transformation,[],[f12])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f57,plain,(
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
    inference(nnf_transformation,[],[f39])).

fof(f58,plain,(
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
    inference(rectify,[],[f57])).

fof(f59,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v1_subset_1(X2,u1_struct_0(X0))
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_subset_1(sK1(X0,X1),u1_struct_0(X0))
        & u1_struct_0(X1) = sK1(X0,X1)
        & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f58,f59])).

fof(f83,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f100,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2) ),
    inference(cnf_transformation,[],[f66])).

fof(f14,axiom,(
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
    inference(pure_predicate_removal,[],[f14])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f89,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f18,axiom,(
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
    inference(ennf_transformation,[],[f18])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f94,plain,(
    ! [X0,X1] :
      ( v1_subset_1(k6_domain_1(X0,X1),X0)
      | ~ m1_subset_1(X1,X0)
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f17,axiom,(
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
    inference(ennf_transformation,[],[f17])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_zfmisc_1(X0)
          | ~ v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(X0)
      | ~ v1_subset_1(k6_domain_1(X0,X1),X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f82,plain,(
    ! [X0,X3,X1] :
      ( v1_subset_1(X3,u1_struct_0(X0))
      | u1_struct_0(X1) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f101,plain,(
    ! [X0,X1] :
      ( v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f82])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f92,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f99,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | v1_tex_2(k1_tex_2(sK2,sK3),sK2) ),
    inference(cnf_transformation,[],[f66])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f77,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( v1_subset_1(X1,X0)
           => v1_xboole_0(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f81,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ~ v1_subset_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f84,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | u1_struct_0(X1) = sK1(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f87,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f85,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | ~ v1_subset_1(sK1(X0,X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ~ ( v7_struct_0(X0)
              & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v7_struct_0(X0)
          | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v7_struct_0(X0)
          | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f50])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ v7_struct_0(X0)
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f91,plain,(
    ! [X0,X1] :
      ( v7_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_2240,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2249,plain,
    ( k6_domain_1(X0,X1) = k1_tarski(X1)
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2873,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK3) = k1_tarski(sK3)
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2240,c_2249])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_32,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_12,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_84,plain,
    ( v2_struct_0(sK2)
    | ~ l1_struct_0(sK2)
    | ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_9,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_91,plain,
    ( ~ l1_pre_topc(sK2)
    | l1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2545,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2))
    | k6_domain_1(u1_struct_0(sK2),sK3) = k1_tarski(sK3) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_2984,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK3) = k1_tarski(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2873,c_33,c_32,c_31,c_84,c_91,c_2545])).

cnf(c_17,plain,
    ( v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | m1_subset_1(sK1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_29,negated_conjecture,
    ( ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_266,plain,
    ( ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) ),
    inference(prop_impl,[status(thm)],[c_29])).

cnf(c_848,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | m1_subset_1(sK1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tex_2(sK2,sK3) != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_266])).

cnf(c_849,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | m1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_848])).

cnf(c_851,plain,
    ( m1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_849,c_32])).

cnf(c_852,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | m1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(renaming,[status(thm)],[c_851])).

cnf(c_2229,plain,
    ( m1_pre_topc(k1_tex_2(sK2,sK3),sK2) != iProver_top
    | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_852])).

cnf(c_34,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_35,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_36,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_83,plain,
    ( v2_struct_0(X0) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_85,plain,
    ( v2_struct_0(sK2) = iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_83])).

cnf(c_90,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_92,plain,
    ( l1_pre_topc(sK2) != iProver_top
    | l1_struct_0(sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_90])).

cnf(c_850,plain,
    ( m1_pre_topc(k1_tex_2(sK2,sK3),sK2) != iProver_top
    | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_849])).

cnf(c_21,plain,
    ( m1_pre_topc(k1_tex_2(X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2554,plain,
    ( m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_2555,plain,
    ( m1_pre_topc(k1_tex_2(sK2,sK3),sK2) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2554])).

cnf(c_27,plain,
    ( v1_subset_1(k6_domain_1(X0,X1),X0)
    | ~ m1_subset_1(X1,X0)
    | v1_zfmisc_1(X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_2567,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | v1_zfmisc_1(u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_2568,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK2)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2567])).

cnf(c_26,plain,
    ( ~ v1_subset_1(k6_domain_1(X0,X1),X0)
    | ~ m1_subset_1(X1,X0)
    | ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_2242,plain,
    ( v1_subset_1(k6_domain_1(X0,X1),X0) != iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | v1_zfmisc_1(X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3568,plain,
    ( v1_subset_1(k1_tarski(sK3),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK2)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2984,c_2242])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k1_tex_2(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_2551,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ v2_struct_0(k1_tex_2(sK2,sK3))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_2552,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | v2_struct_0(k1_tex_2(sK2,sK3)) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2551])).

cnf(c_18,plain,
    ( ~ v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_25,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_200,plain,
    ( v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X1)
    | ~ v1_tex_2(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_18,c_25])).

cnf(c_201,plain,
    ( ~ v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_200])).

cnf(c_30,negated_conjecture,
    ( v1_tex_2(k1_tex_2(sK2,sK3),sK2)
    | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_268,plain,
    ( v1_tex_2(k1_tex_2(sK2,sK3),sK2)
    | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) ),
    inference(prop_impl,[status(thm)],[c_30])).

cnf(c_899,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | k1_tex_2(sK2,sK3) != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_201,c_268])).

cnf(c_900,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
    | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | v1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_899])).

cnf(c_902,plain,
    ( v1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),u1_struct_0(sK2))
    | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_900,c_32])).

cnf(c_903,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
    | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | v1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_902])).

cnf(c_2226,plain,
    ( m1_pre_topc(k1_tex_2(sK2,sK3),sK2) != iProver_top
    | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) = iProver_top
    | v1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_903])).

cnf(c_901,plain,
    ( m1_pre_topc(k1_tex_2(sK2,sK3),sK2) != iProver_top
    | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) = iProver_top
    | v1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),u1_struct_0(sK2)) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_900])).

cnf(c_2616,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) = iProver_top
    | v1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),u1_struct_0(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2226,c_34,c_35,c_36,c_901,c_2555])).

cnf(c_2634,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
    | m1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_2635,plain,
    ( m1_pre_topc(k1_tex_2(sK2,sK3),sK2) != iProver_top
    | m1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2634])).

cnf(c_10,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2930,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK2,sK3),X0)
    | ~ l1_pre_topc(X0)
    | l1_pre_topc(k1_tex_2(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2931,plain,
    ( m1_pre_topc(k1_tex_2(sK2,sK3),X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(k1_tex_2(sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2930])).

cnf(c_2933,plain,
    ( m1_pre_topc(k1_tex_2(sK2,sK3),sK2) != iProver_top
    | l1_pre_topc(k1_tex_2(sK2,sK3)) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2931])).

cnf(c_2978,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),X0),u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ v1_zfmisc_1(u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_3286,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ v1_zfmisc_1(u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2978])).

cnf(c_3287,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK2)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3286])).

cnf(c_14,plain,
    ( ~ v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_5,plain,
    ( ~ v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_210,plain,
    ( v1_xboole_0(X0)
    | ~ v1_zfmisc_1(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_subset_1(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14,c_5])).

cnf(c_211,plain,
    ( ~ v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_210])).

cnf(c_2973,plain,
    ( ~ v1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_zfmisc_1(u1_struct_0(sK2))
    | v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_211])).

cnf(c_3323,plain,
    ( ~ v1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),u1_struct_0(sK2))
    | ~ m1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_zfmisc_1(u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(k1_tex_2(sK2,sK3))) ),
    inference(instantiation,[status(thm)],[c_2973])).

cnf(c_3324,plain,
    ( v1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK2)) != iProver_top
    | v1_xboole_0(u1_struct_0(k1_tex_2(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3323])).

cnf(c_499,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_9,c_12])).

cnf(c_3540,plain,
    ( v2_struct_0(k1_tex_2(sK2,sK3))
    | ~ l1_pre_topc(k1_tex_2(sK2,sK3))
    | ~ v1_xboole_0(u1_struct_0(k1_tex_2(sK2,sK3))) ),
    inference(instantiation,[status(thm)],[c_499])).

cnf(c_3541,plain,
    ( v2_struct_0(k1_tex_2(sK2,sK3)) = iProver_top
    | l1_pre_topc(k1_tex_2(sK2,sK3)) != iProver_top
    | v1_xboole_0(u1_struct_0(k1_tex_2(sK2,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3540])).

cnf(c_3641,plain,
    ( v1_zfmisc_1(u1_struct_0(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3568,c_34,c_35,c_36,c_85,c_92,c_2552,c_2555,c_2616,c_2635,c_2933,c_3287,c_3324,c_3541])).

cnf(c_5274,plain,
    ( m1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2229,c_34,c_35,c_36,c_85,c_92,c_850,c_2552,c_2555,c_2568,c_2616,c_2635,c_2933,c_3287,c_3324,c_3541])).

cnf(c_16,plain,
    ( v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK1(X1,X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_865,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | ~ l1_pre_topc(X1)
    | k1_tex_2(sK2,sK3) != X0
    | sK1(X1,X0) = u1_struct_0(X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_266])).

cnf(c_866,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2)
    | sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(k1_tex_2(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_865])).

cnf(c_868,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
    | sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(k1_tex_2(sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_866,c_32])).

cnf(c_869,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(k1_tex_2(sK2,sK3)) ),
    inference(renaming,[status(thm)],[c_868])).

cnf(c_2228,plain,
    ( sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(k1_tex_2(sK2,sK3))
    | m1_pre_topc(k1_tex_2(sK2,sK3),sK2) != iProver_top
    | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_869])).

cnf(c_867,plain,
    ( sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(k1_tex_2(sK2,sK3))
    | m1_pre_topc(k1_tex_2(sK2,sK3),sK2) != iProver_top
    | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_866])).

cnf(c_4110,plain,
    ( sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(k1_tex_2(sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2228,c_34,c_35,c_36,c_85,c_92,c_867,c_2552,c_2555,c_2568,c_2616,c_2635,c_2933,c_3287,c_3324,c_3541])).

cnf(c_5278,plain,
    ( m1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5274,c_4110])).

cnf(c_19,plain,
    ( v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X1 = X0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2248,plain,
    ( X0 = X1
    | v1_subset_1(X1,X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_5286,plain,
    ( u1_struct_0(k1_tex_2(sK2,sK3)) = u1_struct_0(sK2)
    | v1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5278,c_2248])).

cnf(c_2241,plain,
    ( v1_subset_1(k6_domain_1(X0,X1),X0) = iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | v1_zfmisc_1(X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3469,plain,
    ( v1_subset_1(k1_tarski(sK3),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK2)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2984,c_2241])).

cnf(c_15,plain,
    ( v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v1_subset_1(sK1(X1,X0),u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_882,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_subset_1(sK1(X1,X0),u1_struct_0(X1))
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | ~ l1_pre_topc(X1)
    | k1_tex_2(sK2,sK3) != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_266])).

cnf(c_883,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
    | ~ v1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),u1_struct_0(sK2))
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_882])).

cnf(c_885,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | ~ v1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),u1_struct_0(sK2))
    | ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_883,c_32])).

cnf(c_886,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
    | ~ v1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),u1_struct_0(sK2))
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_885])).

cnf(c_2227,plain,
    ( m1_pre_topc(k1_tex_2(sK2,sK3),sK2) != iProver_top
    | v1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),u1_struct_0(sK2)) != iProver_top
    | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_886])).

cnf(c_887,plain,
    ( m1_pre_topc(k1_tex_2(sK2,sK3),sK2) != iProver_top
    | v1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),u1_struct_0(sK2)) != iProver_top
    | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_886])).

cnf(c_3304,plain,
    ( v1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),u1_struct_0(sK2)) != iProver_top
    | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2227,c_34,c_35,c_36,c_887,c_2555])).

cnf(c_3308,plain,
    ( v1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),u1_struct_0(sK2)) != iProver_top
    | v1_subset_1(k1_tarski(sK3),u1_struct_0(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3304,c_2984])).

cnf(c_4113,plain,
    ( v1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),u1_struct_0(sK2)) != iProver_top
    | v1_subset_1(k1_tarski(sK3),u1_struct_0(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4110,c_3308])).

cnf(c_5392,plain,
    ( u1_struct_0(k1_tex_2(sK2,sK3)) = u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5286,c_34,c_35,c_36,c_85,c_92,c_2552,c_2555,c_2616,c_2635,c_2933,c_3287,c_3324,c_3469,c_3541,c_4113])).

cnf(c_28,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v7_struct_0(X0)
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_479,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v7_struct_0(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_9,c_28])).

cnf(c_2236,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v7_struct_0(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_479])).

cnf(c_9840,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),X0),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(k1_tex_2(sK2,sK3))) != iProver_top
    | v7_struct_0(k1_tex_2(sK2,sK3)) != iProver_top
    | v2_struct_0(k1_tex_2(sK2,sK3)) = iProver_top
    | l1_pre_topc(k1_tex_2(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5392,c_2236])).

cnf(c_9847,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),X0),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | v7_struct_0(k1_tex_2(sK2,sK3)) != iProver_top
    | v2_struct_0(k1_tex_2(sK2,sK3)) = iProver_top
    | l1_pre_topc(k1_tex_2(sK2,sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9840,c_5392])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v7_struct_0(k1_tex_2(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_2548,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | v7_struct_0(k1_tex_2(sK2,sK3))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_2549,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | v7_struct_0(k1_tex_2(sK2,sK3)) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2548])).

cnf(c_13460,plain,
    ( m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | v1_subset_1(k6_domain_1(u1_struct_0(sK2),X0),u1_struct_0(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9847,c_34,c_35,c_36,c_2549,c_2552,c_2555,c_2933])).

cnf(c_13461,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),X0),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_13460])).

cnf(c_13469,plain,
    ( v1_subset_1(k1_tarski(sK3),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2984,c_13461])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13469,c_3641,c_3469,c_92,c_85,c_36,c_35,c_34])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n024.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:25:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.62/1.02  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.62/1.02  
% 3.62/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.62/1.02  
% 3.62/1.02  ------  iProver source info
% 3.62/1.02  
% 3.62/1.02  git: date: 2020-06-30 10:37:57 +0100
% 3.62/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.62/1.02  git: non_committed_changes: false
% 3.62/1.02  git: last_make_outside_of_git: false
% 3.62/1.02  
% 3.62/1.02  ------ 
% 3.62/1.02  
% 3.62/1.02  ------ Input Options
% 3.62/1.02  
% 3.62/1.02  --out_options                           all
% 3.62/1.02  --tptp_safe_out                         true
% 3.62/1.02  --problem_path                          ""
% 3.62/1.02  --include_path                          ""
% 3.62/1.02  --clausifier                            res/vclausify_rel
% 3.62/1.02  --clausifier_options                    --mode clausify
% 3.62/1.02  --stdin                                 false
% 3.62/1.02  --stats_out                             all
% 3.62/1.02  
% 3.62/1.02  ------ General Options
% 3.62/1.02  
% 3.62/1.02  --fof                                   false
% 3.62/1.02  --time_out_real                         305.
% 3.62/1.02  --time_out_virtual                      -1.
% 3.62/1.02  --symbol_type_check                     false
% 3.62/1.02  --clausify_out                          false
% 3.62/1.02  --sig_cnt_out                           false
% 3.62/1.02  --trig_cnt_out                          false
% 3.62/1.02  --trig_cnt_out_tolerance                1.
% 3.62/1.02  --trig_cnt_out_sk_spl                   false
% 3.62/1.02  --abstr_cl_out                          false
% 3.62/1.02  
% 3.62/1.02  ------ Global Options
% 3.62/1.02  
% 3.62/1.02  --schedule                              default
% 3.62/1.02  --add_important_lit                     false
% 3.62/1.02  --prop_solver_per_cl                    1000
% 3.62/1.02  --min_unsat_core                        false
% 3.62/1.02  --soft_assumptions                      false
% 3.62/1.02  --soft_lemma_size                       3
% 3.62/1.02  --prop_impl_unit_size                   0
% 3.62/1.02  --prop_impl_unit                        []
% 3.62/1.02  --share_sel_clauses                     true
% 3.62/1.02  --reset_solvers                         false
% 3.62/1.02  --bc_imp_inh                            [conj_cone]
% 3.62/1.02  --conj_cone_tolerance                   3.
% 3.62/1.02  --extra_neg_conj                        none
% 3.62/1.02  --large_theory_mode                     true
% 3.62/1.02  --prolific_symb_bound                   200
% 3.62/1.02  --lt_threshold                          2000
% 3.62/1.02  --clause_weak_htbl                      true
% 3.62/1.02  --gc_record_bc_elim                     false
% 3.62/1.02  
% 3.62/1.02  ------ Preprocessing Options
% 3.62/1.02  
% 3.62/1.02  --preprocessing_flag                    true
% 3.62/1.02  --time_out_prep_mult                    0.1
% 3.62/1.02  --splitting_mode                        input
% 3.62/1.02  --splitting_grd                         true
% 3.62/1.02  --splitting_cvd                         false
% 3.62/1.02  --splitting_cvd_svl                     false
% 3.62/1.02  --splitting_nvd                         32
% 3.62/1.02  --sub_typing                            true
% 3.62/1.02  --prep_gs_sim                           true
% 3.62/1.02  --prep_unflatten                        true
% 3.62/1.02  --prep_res_sim                          true
% 3.62/1.02  --prep_upred                            true
% 3.62/1.02  --prep_sem_filter                       exhaustive
% 3.62/1.02  --prep_sem_filter_out                   false
% 3.62/1.02  --pred_elim                             true
% 3.62/1.02  --res_sim_input                         true
% 3.62/1.02  --eq_ax_congr_red                       true
% 3.62/1.02  --pure_diseq_elim                       true
% 3.62/1.02  --brand_transform                       false
% 3.62/1.02  --non_eq_to_eq                          false
% 3.62/1.02  --prep_def_merge                        true
% 3.62/1.02  --prep_def_merge_prop_impl              false
% 3.62/1.02  --prep_def_merge_mbd                    true
% 3.62/1.02  --prep_def_merge_tr_red                 false
% 3.62/1.02  --prep_def_merge_tr_cl                  false
% 3.62/1.02  --smt_preprocessing                     true
% 3.62/1.02  --smt_ac_axioms                         fast
% 3.62/1.02  --preprocessed_out                      false
% 3.62/1.02  --preprocessed_stats                    false
% 3.62/1.02  
% 3.62/1.02  ------ Abstraction refinement Options
% 3.62/1.02  
% 3.62/1.02  --abstr_ref                             []
% 3.62/1.02  --abstr_ref_prep                        false
% 3.62/1.02  --abstr_ref_until_sat                   false
% 3.62/1.02  --abstr_ref_sig_restrict                funpre
% 3.62/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.62/1.02  --abstr_ref_under                       []
% 3.62/1.02  
% 3.62/1.02  ------ SAT Options
% 3.62/1.02  
% 3.62/1.02  --sat_mode                              false
% 3.62/1.02  --sat_fm_restart_options                ""
% 3.62/1.02  --sat_gr_def                            false
% 3.62/1.02  --sat_epr_types                         true
% 3.62/1.02  --sat_non_cyclic_types                  false
% 3.62/1.02  --sat_finite_models                     false
% 3.62/1.02  --sat_fm_lemmas                         false
% 3.62/1.02  --sat_fm_prep                           false
% 3.62/1.02  --sat_fm_uc_incr                        true
% 3.62/1.02  --sat_out_model                         small
% 3.62/1.02  --sat_out_clauses                       false
% 3.62/1.02  
% 3.62/1.02  ------ QBF Options
% 3.62/1.02  
% 3.62/1.02  --qbf_mode                              false
% 3.62/1.02  --qbf_elim_univ                         false
% 3.62/1.02  --qbf_dom_inst                          none
% 3.62/1.02  --qbf_dom_pre_inst                      false
% 3.62/1.02  --qbf_sk_in                             false
% 3.62/1.02  --qbf_pred_elim                         true
% 3.62/1.02  --qbf_split                             512
% 3.62/1.02  
% 3.62/1.02  ------ BMC1 Options
% 3.62/1.02  
% 3.62/1.02  --bmc1_incremental                      false
% 3.62/1.02  --bmc1_axioms                           reachable_all
% 3.62/1.02  --bmc1_min_bound                        0
% 3.62/1.02  --bmc1_max_bound                        -1
% 3.62/1.02  --bmc1_max_bound_default                -1
% 3.62/1.02  --bmc1_symbol_reachability              true
% 3.62/1.02  --bmc1_property_lemmas                  false
% 3.62/1.02  --bmc1_k_induction                      false
% 3.62/1.02  --bmc1_non_equiv_states                 false
% 3.62/1.02  --bmc1_deadlock                         false
% 3.62/1.02  --bmc1_ucm                              false
% 3.62/1.02  --bmc1_add_unsat_core                   none
% 3.62/1.02  --bmc1_unsat_core_children              false
% 3.62/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.62/1.02  --bmc1_out_stat                         full
% 3.62/1.02  --bmc1_ground_init                      false
% 3.62/1.02  --bmc1_pre_inst_next_state              false
% 3.62/1.02  --bmc1_pre_inst_state                   false
% 3.62/1.02  --bmc1_pre_inst_reach_state             false
% 3.62/1.02  --bmc1_out_unsat_core                   false
% 3.62/1.02  --bmc1_aig_witness_out                  false
% 3.62/1.02  --bmc1_verbose                          false
% 3.62/1.02  --bmc1_dump_clauses_tptp                false
% 3.62/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.62/1.02  --bmc1_dump_file                        -
% 3.62/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.62/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.62/1.02  --bmc1_ucm_extend_mode                  1
% 3.62/1.02  --bmc1_ucm_init_mode                    2
% 3.62/1.02  --bmc1_ucm_cone_mode                    none
% 3.62/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.62/1.02  --bmc1_ucm_relax_model                  4
% 3.62/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.62/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.62/1.02  --bmc1_ucm_layered_model                none
% 3.62/1.02  --bmc1_ucm_max_lemma_size               10
% 3.62/1.02  
% 3.62/1.02  ------ AIG Options
% 3.62/1.02  
% 3.62/1.02  --aig_mode                              false
% 3.62/1.02  
% 3.62/1.02  ------ Instantiation Options
% 3.62/1.02  
% 3.62/1.02  --instantiation_flag                    true
% 3.62/1.02  --inst_sos_flag                         false
% 3.62/1.02  --inst_sos_phase                        true
% 3.62/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.62/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.62/1.02  --inst_lit_sel_side                     num_symb
% 3.62/1.02  --inst_solver_per_active                1400
% 3.62/1.02  --inst_solver_calls_frac                1.
% 3.62/1.02  --inst_passive_queue_type               priority_queues
% 3.62/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.62/1.02  --inst_passive_queues_freq              [25;2]
% 3.62/1.02  --inst_dismatching                      true
% 3.62/1.02  --inst_eager_unprocessed_to_passive     true
% 3.62/1.02  --inst_prop_sim_given                   true
% 3.62/1.02  --inst_prop_sim_new                     false
% 3.62/1.02  --inst_subs_new                         false
% 3.62/1.02  --inst_eq_res_simp                      false
% 3.62/1.02  --inst_subs_given                       false
% 3.62/1.02  --inst_orphan_elimination               true
% 3.62/1.02  --inst_learning_loop_flag               true
% 3.62/1.02  --inst_learning_start                   3000
% 3.62/1.02  --inst_learning_factor                  2
% 3.62/1.02  --inst_start_prop_sim_after_learn       3
% 3.62/1.02  --inst_sel_renew                        solver
% 3.62/1.02  --inst_lit_activity_flag                true
% 3.62/1.02  --inst_restr_to_given                   false
% 3.62/1.02  --inst_activity_threshold               500
% 3.62/1.02  --inst_out_proof                        true
% 3.62/1.02  
% 3.62/1.02  ------ Resolution Options
% 3.62/1.02  
% 3.62/1.02  --resolution_flag                       true
% 3.62/1.02  --res_lit_sel                           adaptive
% 3.62/1.02  --res_lit_sel_side                      none
% 3.62/1.02  --res_ordering                          kbo
% 3.62/1.02  --res_to_prop_solver                    active
% 3.62/1.02  --res_prop_simpl_new                    false
% 3.62/1.02  --res_prop_simpl_given                  true
% 3.62/1.02  --res_passive_queue_type                priority_queues
% 3.62/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.62/1.02  --res_passive_queues_freq               [15;5]
% 3.62/1.02  --res_forward_subs                      full
% 3.62/1.02  --res_backward_subs                     full
% 3.62/1.02  --res_forward_subs_resolution           true
% 3.62/1.02  --res_backward_subs_resolution          true
% 3.62/1.02  --res_orphan_elimination                true
% 3.62/1.02  --res_time_limit                        2.
% 3.62/1.02  --res_out_proof                         true
% 3.62/1.02  
% 3.62/1.02  ------ Superposition Options
% 3.62/1.02  
% 3.62/1.02  --superposition_flag                    true
% 3.62/1.02  --sup_passive_queue_type                priority_queues
% 3.62/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.62/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.62/1.02  --demod_completeness_check              fast
% 3.62/1.02  --demod_use_ground                      true
% 3.62/1.02  --sup_to_prop_solver                    passive
% 3.62/1.02  --sup_prop_simpl_new                    true
% 3.62/1.02  --sup_prop_simpl_given                  true
% 3.62/1.02  --sup_fun_splitting                     false
% 3.62/1.02  --sup_smt_interval                      50000
% 3.62/1.02  
% 3.62/1.02  ------ Superposition Simplification Setup
% 3.62/1.02  
% 3.62/1.02  --sup_indices_passive                   []
% 3.62/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.62/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.62/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.62/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.62/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.62/1.02  --sup_full_bw                           [BwDemod]
% 3.62/1.02  --sup_immed_triv                        [TrivRules]
% 3.62/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.62/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.62/1.02  --sup_immed_bw_main                     []
% 3.62/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.62/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.62/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.62/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.62/1.02  
% 3.62/1.02  ------ Combination Options
% 3.62/1.02  
% 3.62/1.02  --comb_res_mult                         3
% 3.62/1.02  --comb_sup_mult                         2
% 3.62/1.02  --comb_inst_mult                        10
% 3.62/1.02  
% 3.62/1.02  ------ Debug Options
% 3.62/1.02  
% 3.62/1.02  --dbg_backtrace                         false
% 3.62/1.02  --dbg_dump_prop_clauses                 false
% 3.62/1.02  --dbg_dump_prop_clauses_file            -
% 3.62/1.02  --dbg_out_stat                          false
% 3.62/1.02  ------ Parsing...
% 3.62/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.62/1.02  
% 3.62/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.62/1.02  
% 3.62/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.62/1.02  
% 3.62/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.62/1.02  ------ Proving...
% 3.62/1.02  ------ Problem Properties 
% 3.62/1.02  
% 3.62/1.02  
% 3.62/1.02  clauses                                 31
% 3.62/1.02  conjectures                             3
% 3.62/1.02  EPR                                     5
% 3.62/1.02  Horn                                    22
% 3.62/1.02  unary                                   5
% 3.62/1.02  binary                                  1
% 3.62/1.02  lits                                    94
% 3.62/1.02  lits eq                                 4
% 3.62/1.02  fd_pure                                 0
% 3.62/1.02  fd_pseudo                               0
% 3.62/1.02  fd_cond                                 0
% 3.62/1.02  fd_pseudo_cond                          1
% 3.62/1.02  AC symbols                              0
% 3.62/1.02  
% 3.62/1.02  ------ Schedule dynamic 5 is on 
% 3.62/1.02  
% 3.62/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.62/1.02  
% 3.62/1.02  
% 3.62/1.02  ------ 
% 3.62/1.02  Current options:
% 3.62/1.02  ------ 
% 3.62/1.02  
% 3.62/1.02  ------ Input Options
% 3.62/1.02  
% 3.62/1.02  --out_options                           all
% 3.62/1.02  --tptp_safe_out                         true
% 3.62/1.02  --problem_path                          ""
% 3.62/1.02  --include_path                          ""
% 3.62/1.02  --clausifier                            res/vclausify_rel
% 3.62/1.02  --clausifier_options                    --mode clausify
% 3.62/1.02  --stdin                                 false
% 3.62/1.02  --stats_out                             all
% 3.62/1.02  
% 3.62/1.02  ------ General Options
% 3.62/1.02  
% 3.62/1.02  --fof                                   false
% 3.62/1.02  --time_out_real                         305.
% 3.62/1.02  --time_out_virtual                      -1.
% 3.62/1.02  --symbol_type_check                     false
% 3.62/1.02  --clausify_out                          false
% 3.62/1.02  --sig_cnt_out                           false
% 3.62/1.02  --trig_cnt_out                          false
% 3.62/1.02  --trig_cnt_out_tolerance                1.
% 3.62/1.02  --trig_cnt_out_sk_spl                   false
% 3.62/1.02  --abstr_cl_out                          false
% 3.62/1.02  
% 3.62/1.02  ------ Global Options
% 3.62/1.02  
% 3.62/1.02  --schedule                              default
% 3.62/1.02  --add_important_lit                     false
% 3.62/1.02  --prop_solver_per_cl                    1000
% 3.62/1.02  --min_unsat_core                        false
% 3.62/1.02  --soft_assumptions                      false
% 3.62/1.02  --soft_lemma_size                       3
% 3.62/1.02  --prop_impl_unit_size                   0
% 3.62/1.02  --prop_impl_unit                        []
% 3.62/1.02  --share_sel_clauses                     true
% 3.62/1.02  --reset_solvers                         false
% 3.62/1.02  --bc_imp_inh                            [conj_cone]
% 3.62/1.02  --conj_cone_tolerance                   3.
% 3.62/1.02  --extra_neg_conj                        none
% 3.62/1.02  --large_theory_mode                     true
% 3.62/1.02  --prolific_symb_bound                   200
% 3.62/1.02  --lt_threshold                          2000
% 3.62/1.02  --clause_weak_htbl                      true
% 3.62/1.02  --gc_record_bc_elim                     false
% 3.62/1.02  
% 3.62/1.02  ------ Preprocessing Options
% 3.62/1.02  
% 3.62/1.02  --preprocessing_flag                    true
% 3.62/1.02  --time_out_prep_mult                    0.1
% 3.62/1.02  --splitting_mode                        input
% 3.62/1.02  --splitting_grd                         true
% 3.62/1.02  --splitting_cvd                         false
% 3.62/1.02  --splitting_cvd_svl                     false
% 3.62/1.02  --splitting_nvd                         32
% 3.62/1.02  --sub_typing                            true
% 3.62/1.02  --prep_gs_sim                           true
% 3.62/1.02  --prep_unflatten                        true
% 3.62/1.02  --prep_res_sim                          true
% 3.62/1.02  --prep_upred                            true
% 3.62/1.02  --prep_sem_filter                       exhaustive
% 3.62/1.02  --prep_sem_filter_out                   false
% 3.62/1.02  --pred_elim                             true
% 3.62/1.02  --res_sim_input                         true
% 3.62/1.02  --eq_ax_congr_red                       true
% 3.62/1.02  --pure_diseq_elim                       true
% 3.62/1.02  --brand_transform                       false
% 3.62/1.02  --non_eq_to_eq                          false
% 3.62/1.02  --prep_def_merge                        true
% 3.62/1.02  --prep_def_merge_prop_impl              false
% 3.62/1.02  --prep_def_merge_mbd                    true
% 3.62/1.02  --prep_def_merge_tr_red                 false
% 3.62/1.02  --prep_def_merge_tr_cl                  false
% 3.62/1.02  --smt_preprocessing                     true
% 3.62/1.02  --smt_ac_axioms                         fast
% 3.62/1.02  --preprocessed_out                      false
% 3.62/1.02  --preprocessed_stats                    false
% 3.62/1.02  
% 3.62/1.02  ------ Abstraction refinement Options
% 3.62/1.02  
% 3.62/1.02  --abstr_ref                             []
% 3.62/1.02  --abstr_ref_prep                        false
% 3.62/1.02  --abstr_ref_until_sat                   false
% 3.62/1.02  --abstr_ref_sig_restrict                funpre
% 3.62/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.62/1.02  --abstr_ref_under                       []
% 3.62/1.02  
% 3.62/1.02  ------ SAT Options
% 3.62/1.02  
% 3.62/1.02  --sat_mode                              false
% 3.62/1.02  --sat_fm_restart_options                ""
% 3.62/1.02  --sat_gr_def                            false
% 3.62/1.02  --sat_epr_types                         true
% 3.62/1.02  --sat_non_cyclic_types                  false
% 3.62/1.02  --sat_finite_models                     false
% 3.62/1.02  --sat_fm_lemmas                         false
% 3.62/1.02  --sat_fm_prep                           false
% 3.62/1.02  --sat_fm_uc_incr                        true
% 3.62/1.02  --sat_out_model                         small
% 3.62/1.02  --sat_out_clauses                       false
% 3.62/1.02  
% 3.62/1.02  ------ QBF Options
% 3.62/1.02  
% 3.62/1.02  --qbf_mode                              false
% 3.62/1.02  --qbf_elim_univ                         false
% 3.62/1.02  --qbf_dom_inst                          none
% 3.62/1.02  --qbf_dom_pre_inst                      false
% 3.62/1.02  --qbf_sk_in                             false
% 3.62/1.02  --qbf_pred_elim                         true
% 3.62/1.02  --qbf_split                             512
% 3.62/1.02  
% 3.62/1.02  ------ BMC1 Options
% 3.62/1.02  
% 3.62/1.02  --bmc1_incremental                      false
% 3.62/1.02  --bmc1_axioms                           reachable_all
% 3.62/1.02  --bmc1_min_bound                        0
% 3.62/1.02  --bmc1_max_bound                        -1
% 3.62/1.02  --bmc1_max_bound_default                -1
% 3.62/1.02  --bmc1_symbol_reachability              true
% 3.62/1.02  --bmc1_property_lemmas                  false
% 3.62/1.02  --bmc1_k_induction                      false
% 3.62/1.02  --bmc1_non_equiv_states                 false
% 3.62/1.02  --bmc1_deadlock                         false
% 3.62/1.02  --bmc1_ucm                              false
% 3.62/1.02  --bmc1_add_unsat_core                   none
% 3.62/1.02  --bmc1_unsat_core_children              false
% 3.62/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.62/1.02  --bmc1_out_stat                         full
% 3.62/1.02  --bmc1_ground_init                      false
% 3.62/1.02  --bmc1_pre_inst_next_state              false
% 3.62/1.02  --bmc1_pre_inst_state                   false
% 3.62/1.02  --bmc1_pre_inst_reach_state             false
% 3.62/1.02  --bmc1_out_unsat_core                   false
% 3.62/1.02  --bmc1_aig_witness_out                  false
% 3.62/1.02  --bmc1_verbose                          false
% 3.62/1.02  --bmc1_dump_clauses_tptp                false
% 3.62/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.62/1.02  --bmc1_dump_file                        -
% 3.62/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.62/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.62/1.02  --bmc1_ucm_extend_mode                  1
% 3.62/1.02  --bmc1_ucm_init_mode                    2
% 3.62/1.02  --bmc1_ucm_cone_mode                    none
% 3.62/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.62/1.02  --bmc1_ucm_relax_model                  4
% 3.62/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.62/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.62/1.02  --bmc1_ucm_layered_model                none
% 3.62/1.02  --bmc1_ucm_max_lemma_size               10
% 3.62/1.02  
% 3.62/1.02  ------ AIG Options
% 3.62/1.02  
% 3.62/1.02  --aig_mode                              false
% 3.62/1.02  
% 3.62/1.02  ------ Instantiation Options
% 3.62/1.02  
% 3.62/1.02  --instantiation_flag                    true
% 3.62/1.02  --inst_sos_flag                         false
% 3.62/1.02  --inst_sos_phase                        true
% 3.62/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.62/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.62/1.02  --inst_lit_sel_side                     none
% 3.62/1.02  --inst_solver_per_active                1400
% 3.62/1.02  --inst_solver_calls_frac                1.
% 3.62/1.02  --inst_passive_queue_type               priority_queues
% 3.62/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.62/1.02  --inst_passive_queues_freq              [25;2]
% 3.62/1.02  --inst_dismatching                      true
% 3.62/1.02  --inst_eager_unprocessed_to_passive     true
% 3.62/1.02  --inst_prop_sim_given                   true
% 3.62/1.02  --inst_prop_sim_new                     false
% 3.62/1.02  --inst_subs_new                         false
% 3.62/1.02  --inst_eq_res_simp                      false
% 3.62/1.02  --inst_subs_given                       false
% 3.62/1.02  --inst_orphan_elimination               true
% 3.62/1.02  --inst_learning_loop_flag               true
% 3.62/1.02  --inst_learning_start                   3000
% 3.62/1.02  --inst_learning_factor                  2
% 3.62/1.02  --inst_start_prop_sim_after_learn       3
% 3.62/1.02  --inst_sel_renew                        solver
% 3.62/1.02  --inst_lit_activity_flag                true
% 3.62/1.02  --inst_restr_to_given                   false
% 3.62/1.02  --inst_activity_threshold               500
% 3.62/1.02  --inst_out_proof                        true
% 3.62/1.02  
% 3.62/1.02  ------ Resolution Options
% 3.62/1.02  
% 3.62/1.02  --resolution_flag                       false
% 3.62/1.02  --res_lit_sel                           adaptive
% 3.62/1.02  --res_lit_sel_side                      none
% 3.62/1.02  --res_ordering                          kbo
% 3.62/1.02  --res_to_prop_solver                    active
% 3.62/1.02  --res_prop_simpl_new                    false
% 3.62/1.02  --res_prop_simpl_given                  true
% 3.62/1.02  --res_passive_queue_type                priority_queues
% 3.62/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.62/1.02  --res_passive_queues_freq               [15;5]
% 3.62/1.02  --res_forward_subs                      full
% 3.62/1.02  --res_backward_subs                     full
% 3.62/1.02  --res_forward_subs_resolution           true
% 3.62/1.02  --res_backward_subs_resolution          true
% 3.62/1.02  --res_orphan_elimination                true
% 3.62/1.02  --res_time_limit                        2.
% 3.62/1.02  --res_out_proof                         true
% 3.62/1.02  
% 3.62/1.02  ------ Superposition Options
% 3.62/1.02  
% 3.62/1.02  --superposition_flag                    true
% 3.62/1.02  --sup_passive_queue_type                priority_queues
% 3.62/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.62/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.62/1.02  --demod_completeness_check              fast
% 3.62/1.02  --demod_use_ground                      true
% 3.62/1.02  --sup_to_prop_solver                    passive
% 3.62/1.02  --sup_prop_simpl_new                    true
% 3.62/1.02  --sup_prop_simpl_given                  true
% 3.62/1.02  --sup_fun_splitting                     false
% 3.62/1.02  --sup_smt_interval                      50000
% 3.62/1.02  
% 3.62/1.02  ------ Superposition Simplification Setup
% 3.62/1.02  
% 3.62/1.02  --sup_indices_passive                   []
% 3.62/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.62/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.62/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.62/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.62/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.62/1.02  --sup_full_bw                           [BwDemod]
% 3.62/1.02  --sup_immed_triv                        [TrivRules]
% 3.62/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.62/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.62/1.02  --sup_immed_bw_main                     []
% 3.62/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.62/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.62/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.62/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.62/1.02  
% 3.62/1.02  ------ Combination Options
% 3.62/1.02  
% 3.62/1.02  --comb_res_mult                         3
% 3.62/1.02  --comb_sup_mult                         2
% 3.62/1.02  --comb_inst_mult                        10
% 3.62/1.02  
% 3.62/1.02  ------ Debug Options
% 3.62/1.02  
% 3.62/1.02  --dbg_backtrace                         false
% 3.62/1.02  --dbg_dump_prop_clauses                 false
% 3.62/1.02  --dbg_dump_prop_clauses_file            -
% 3.62/1.02  --dbg_out_stat                          false
% 3.62/1.02  
% 3.62/1.02  
% 3.62/1.02  
% 3.62/1.02  
% 3.62/1.02  ------ Proving...
% 3.62/1.02  
% 3.62/1.02  
% 3.62/1.02  % SZS status Theorem for theBenchmark.p
% 3.62/1.02  
% 3.62/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 3.62/1.02  
% 3.62/1.02  fof(f20,conjecture,(
% 3.62/1.02    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 3.62/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/1.02  
% 3.62/1.02  fof(f21,negated_conjecture,(
% 3.62/1.02    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 3.62/1.02    inference(negated_conjecture,[],[f20])).
% 3.62/1.02  
% 3.62/1.02  fof(f52,plain,(
% 3.62/1.02    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.62/1.02    inference(ennf_transformation,[],[f21])).
% 3.62/1.02  
% 3.62/1.02  fof(f53,plain,(
% 3.62/1.02    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.62/1.02    inference(flattening,[],[f52])).
% 3.62/1.02  
% 3.62/1.02  fof(f62,plain,(
% 3.62/1.02    ? [X0] : (? [X1] : (((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.62/1.02    inference(nnf_transformation,[],[f53])).
% 3.62/1.02  
% 3.62/1.02  fof(f63,plain,(
% 3.62/1.02    ? [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.62/1.02    inference(flattening,[],[f62])).
% 3.62/1.02  
% 3.62/1.02  fof(f65,plain,(
% 3.62/1.02    ( ! [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) => ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),sK3),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,sK3),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),sK3),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,sK3),X0)) & m1_subset_1(sK3,u1_struct_0(X0)))) )),
% 3.62/1.02    introduced(choice_axiom,[])).
% 3.62/1.02  
% 3.62/1.02  fof(f64,plain,(
% 3.62/1.02    ? [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(sK2),X1),u1_struct_0(sK2)) | ~v1_tex_2(k1_tex_2(sK2,X1),sK2)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK2),X1),u1_struct_0(sK2)) | v1_tex_2(k1_tex_2(sK2,X1),sK2)) & m1_subset_1(X1,u1_struct_0(sK2))) & l1_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 3.62/1.02    introduced(choice_axiom,[])).
% 3.62/1.02  
% 3.62/1.02  fof(f66,plain,(
% 3.62/1.02    ((~v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) | ~v1_tex_2(k1_tex_2(sK2,sK3),sK2)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) | v1_tex_2(k1_tex_2(sK2,sK3),sK2)) & m1_subset_1(sK3,u1_struct_0(sK2))) & l1_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 3.62/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f63,f65,f64])).
% 3.62/1.02  
% 3.62/1.02  fof(f98,plain,(
% 3.62/1.02    m1_subset_1(sK3,u1_struct_0(sK2))),
% 3.62/1.02    inference(cnf_transformation,[],[f66])).
% 3.62/1.02  
% 3.62/1.02  fof(f10,axiom,(
% 3.62/1.02    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 3.62/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/1.02  
% 3.62/1.02  fof(f34,plain,(
% 3.62/1.02    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 3.62/1.02    inference(ennf_transformation,[],[f10])).
% 3.62/1.02  
% 3.62/1.02  fof(f35,plain,(
% 3.62/1.02    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 3.62/1.02    inference(flattening,[],[f34])).
% 3.62/1.02  
% 3.62/1.02  fof(f80,plain,(
% 3.62/1.02    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.62/1.02    inference(cnf_transformation,[],[f35])).
% 3.62/1.02  
% 3.62/1.02  fof(f96,plain,(
% 3.62/1.02    ~v2_struct_0(sK2)),
% 3.62/1.02    inference(cnf_transformation,[],[f66])).
% 3.62/1.02  
% 3.62/1.02  fof(f97,plain,(
% 3.62/1.02    l1_pre_topc(sK2)),
% 3.62/1.02    inference(cnf_transformation,[],[f66])).
% 3.62/1.02  
% 3.62/1.02  fof(f9,axiom,(
% 3.62/1.02    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 3.62/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/1.02  
% 3.62/1.02  fof(f32,plain,(
% 3.62/1.02    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.62/1.02    inference(ennf_transformation,[],[f9])).
% 3.62/1.02  
% 3.62/1.02  fof(f33,plain,(
% 3.62/1.02    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.62/1.02    inference(flattening,[],[f32])).
% 3.62/1.02  
% 3.62/1.02  fof(f79,plain,(
% 3.62/1.02    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.62/1.02    inference(cnf_transformation,[],[f33])).
% 3.62/1.02  
% 3.62/1.02  fof(f6,axiom,(
% 3.62/1.02    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.62/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/1.02  
% 3.62/1.02  fof(f28,plain,(
% 3.62/1.02    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.62/1.02    inference(ennf_transformation,[],[f6])).
% 3.62/1.02  
% 3.62/1.02  fof(f76,plain,(
% 3.62/1.02    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.62/1.02    inference(cnf_transformation,[],[f28])).
% 3.62/1.02  
% 3.62/1.02  fof(f12,axiom,(
% 3.62/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v1_subset_1(X2,u1_struct_0(X0)))))))),
% 3.62/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/1.02  
% 3.62/1.02  fof(f38,plain,(
% 3.62/1.02    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : ((v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.62/1.02    inference(ennf_transformation,[],[f12])).
% 3.62/1.02  
% 3.62/1.02  fof(f39,plain,(
% 3.62/1.02    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.62/1.02    inference(flattening,[],[f38])).
% 3.62/1.02  
% 3.62/1.02  fof(f57,plain,(
% 3.62/1.02    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.62/1.02    inference(nnf_transformation,[],[f39])).
% 3.62/1.02  
% 3.62/1.02  fof(f58,plain,(
% 3.62/1.02    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.62/1.02    inference(rectify,[],[f57])).
% 3.62/1.02  
% 3.62/1.02  fof(f59,plain,(
% 3.62/1.02    ! [X1,X0] : (? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_subset_1(sK1(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK1(X0,X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.62/1.02    introduced(choice_axiom,[])).
% 3.62/1.02  
% 3.62/1.02  fof(f60,plain,(
% 3.62/1.02    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | (~v1_subset_1(sK1(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK1(X0,X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.62/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f58,f59])).
% 3.62/1.02  
% 3.62/1.02  fof(f83,plain,(
% 3.62/1.02    ( ! [X0,X1] : (v1_tex_2(X1,X0) | m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.62/1.02    inference(cnf_transformation,[],[f60])).
% 3.62/1.02  
% 3.62/1.02  fof(f100,plain,(
% 3.62/1.02    ~v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) | ~v1_tex_2(k1_tex_2(sK2,sK3),sK2)),
% 3.62/1.02    inference(cnf_transformation,[],[f66])).
% 3.62/1.02  
% 3.62/1.02  fof(f14,axiom,(
% 3.62/1.02    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 3.62/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/1.02  
% 3.62/1.02  fof(f22,plain,(
% 3.62/1.02    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 3.62/1.02    inference(pure_predicate_removal,[],[f14])).
% 3.62/1.02  
% 3.62/1.02  fof(f41,plain,(
% 3.62/1.02    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.62/1.02    inference(ennf_transformation,[],[f22])).
% 3.62/1.02  
% 3.62/1.02  fof(f42,plain,(
% 3.62/1.02    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.62/1.02    inference(flattening,[],[f41])).
% 3.62/1.02  
% 3.62/1.02  fof(f89,plain,(
% 3.62/1.02    ( ! [X0,X1] : (m1_pre_topc(k1_tex_2(X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.62/1.02    inference(cnf_transformation,[],[f42])).
% 3.62/1.02  
% 3.62/1.02  fof(f18,axiom,(
% 3.62/1.02    ! [X0] : ((~v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,X0) => v1_subset_1(k6_domain_1(X0,X1),X0)))),
% 3.62/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/1.02  
% 3.62/1.02  fof(f48,plain,(
% 3.62/1.02    ! [X0] : (! [X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | (v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 3.62/1.02    inference(ennf_transformation,[],[f18])).
% 3.62/1.02  
% 3.62/1.02  fof(f49,plain,(
% 3.62/1.02    ! [X0] : (! [X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 3.62/1.02    inference(flattening,[],[f48])).
% 3.62/1.02  
% 3.62/1.02  fof(f94,plain,(
% 3.62/1.02    ( ! [X0,X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0) | v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 3.62/1.02    inference(cnf_transformation,[],[f49])).
% 3.62/1.02  
% 3.62/1.02  fof(f17,axiom,(
% 3.62/1.02    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 3.62/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/1.02  
% 3.62/1.02  fof(f46,plain,(
% 3.62/1.02    ! [X0] : (! [X1] : ((~v1_zfmisc_1(X0) | ~v1_subset_1(k6_domain_1(X0,X1),X0)) | ~m1_subset_1(X1,X0)) | v1_xboole_0(X0))),
% 3.62/1.02    inference(ennf_transformation,[],[f17])).
% 3.62/1.02  
% 3.62/1.02  fof(f47,plain,(
% 3.62/1.02    ! [X0] : (! [X1] : (~v1_zfmisc_1(X0) | ~v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | v1_xboole_0(X0))),
% 3.62/1.02    inference(flattening,[],[f46])).
% 3.62/1.02  
% 3.62/1.02  fof(f93,plain,(
% 3.62/1.02    ( ! [X0,X1] : (~v1_zfmisc_1(X0) | ~v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.62/1.02    inference(cnf_transformation,[],[f47])).
% 3.62/1.02  
% 3.62/1.02  fof(f15,axiom,(
% 3.62/1.02    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 3.62/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/1.02  
% 3.62/1.02  fof(f23,plain,(
% 3.62/1.02    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 3.62/1.02    inference(pure_predicate_removal,[],[f15])).
% 3.62/1.02  
% 3.62/1.02  fof(f43,plain,(
% 3.62/1.02    ! [X0,X1] : ((v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.62/1.02    inference(ennf_transformation,[],[f23])).
% 3.62/1.02  
% 3.62/1.02  fof(f44,plain,(
% 3.62/1.02    ! [X0,X1] : ((v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.62/1.02    inference(flattening,[],[f43])).
% 3.62/1.02  
% 3.62/1.02  fof(f90,plain,(
% 3.62/1.02    ( ! [X0,X1] : (~v2_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.62/1.02    inference(cnf_transformation,[],[f44])).
% 3.62/1.02  
% 3.62/1.02  fof(f82,plain,(
% 3.62/1.02    ( ! [X0,X3,X1] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.62/1.02    inference(cnf_transformation,[],[f60])).
% 3.62/1.02  
% 3.62/1.02  fof(f101,plain,(
% 3.62/1.02    ( ! [X0,X1] : (v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.62/1.02    inference(equality_resolution,[],[f82])).
% 3.62/1.02  
% 3.62/1.02  fof(f16,axiom,(
% 3.62/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.62/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/1.02  
% 3.62/1.02  fof(f45,plain,(
% 3.62/1.02    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.62/1.02    inference(ennf_transformation,[],[f16])).
% 3.62/1.02  
% 3.62/1.02  fof(f92,plain,(
% 3.62/1.02    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.62/1.02    inference(cnf_transformation,[],[f45])).
% 3.62/1.02  
% 3.62/1.02  fof(f99,plain,(
% 3.62/1.02    v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) | v1_tex_2(k1_tex_2(sK2,sK3),sK2)),
% 3.62/1.02    inference(cnf_transformation,[],[f66])).
% 3.62/1.02  
% 3.62/1.02  fof(f7,axiom,(
% 3.62/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.62/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/1.02  
% 3.62/1.02  fof(f29,plain,(
% 3.62/1.02    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.62/1.02    inference(ennf_transformation,[],[f7])).
% 3.62/1.02  
% 3.62/1.02  fof(f77,plain,(
% 3.62/1.02    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.62/1.02    inference(cnf_transformation,[],[f29])).
% 3.62/1.02  
% 3.62/1.02  fof(f11,axiom,(
% 3.62/1.02    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) => v1_xboole_0(X1))))),
% 3.62/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/1.02  
% 3.62/1.02  fof(f36,plain,(
% 3.62/1.02    ! [X0] : (! [X1] : ((v1_xboole_0(X1) | ~v1_subset_1(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | (~v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 3.62/1.02    inference(ennf_transformation,[],[f11])).
% 3.62/1.02  
% 3.62/1.02  fof(f37,plain,(
% 3.62/1.02    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 3.62/1.02    inference(flattening,[],[f36])).
% 3.62/1.02  
% 3.62/1.02  fof(f81,plain,(
% 3.62/1.02    ( ! [X0,X1] : (v1_xboole_0(X1) | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 3.62/1.02    inference(cnf_transformation,[],[f37])).
% 3.62/1.02  
% 3.62/1.02  fof(f3,axiom,(
% 3.62/1.02    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~v1_subset_1(X1,X0)))),
% 3.62/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/1.02  
% 3.62/1.02  fof(f26,plain,(
% 3.62/1.02    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 3.62/1.02    inference(ennf_transformation,[],[f3])).
% 3.62/1.02  
% 3.62/1.02  fof(f72,plain,(
% 3.62/1.02    ( ! [X0,X1] : (~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 3.62/1.02    inference(cnf_transformation,[],[f26])).
% 3.62/1.02  
% 3.62/1.02  fof(f84,plain,(
% 3.62/1.02    ( ! [X0,X1] : (v1_tex_2(X1,X0) | u1_struct_0(X1) = sK1(X0,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.62/1.02    inference(cnf_transformation,[],[f60])).
% 3.62/1.02  
% 3.62/1.02  fof(f13,axiom,(
% 3.62/1.02    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 3.62/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/1.02  
% 3.62/1.02  fof(f40,plain,(
% 3.62/1.02    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.62/1.02    inference(ennf_transformation,[],[f13])).
% 3.62/1.02  
% 3.62/1.02  fof(f61,plain,(
% 3.62/1.02    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.62/1.02    inference(nnf_transformation,[],[f40])).
% 3.62/1.02  
% 3.62/1.02  fof(f87,plain,(
% 3.62/1.02    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.62/1.02    inference(cnf_transformation,[],[f61])).
% 3.62/1.02  
% 3.62/1.02  fof(f85,plain,(
% 3.62/1.02    ( ! [X0,X1] : (v1_tex_2(X1,X0) | ~v1_subset_1(sK1(X0,X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.62/1.02    inference(cnf_transformation,[],[f60])).
% 3.62/1.02  
% 3.62/1.02  fof(f19,axiom,(
% 3.62/1.02    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~(v7_struct_0(X0) & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 3.62/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/1.02  
% 3.62/1.02  fof(f50,plain,(
% 3.62/1.02    ! [X0] : (! [X1] : ((~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.62/1.02    inference(ennf_transformation,[],[f19])).
% 3.62/1.02  
% 3.62/1.02  fof(f51,plain,(
% 3.62/1.02    ! [X0] : (! [X1] : (~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.62/1.02    inference(flattening,[],[f50])).
% 3.62/1.02  
% 3.62/1.02  fof(f95,plain,(
% 3.62/1.02    ( ! [X0,X1] : (~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.62/1.02    inference(cnf_transformation,[],[f51])).
% 3.62/1.02  
% 3.62/1.02  fof(f91,plain,(
% 3.62/1.02    ( ! [X0,X1] : (v7_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.62/1.02    inference(cnf_transformation,[],[f44])).
% 3.62/1.02  
% 3.62/1.02  cnf(c_31,negated_conjecture,
% 3.62/1.02      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 3.62/1.02      inference(cnf_transformation,[],[f98]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_2240,plain,
% 3.62/1.02      ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_13,plain,
% 3.62/1.02      ( ~ m1_subset_1(X0,X1)
% 3.62/1.02      | v1_xboole_0(X1)
% 3.62/1.02      | k6_domain_1(X1,X0) = k1_tarski(X0) ),
% 3.62/1.02      inference(cnf_transformation,[],[f80]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_2249,plain,
% 3.62/1.02      ( k6_domain_1(X0,X1) = k1_tarski(X1)
% 3.62/1.02      | m1_subset_1(X1,X0) != iProver_top
% 3.62/1.02      | v1_xboole_0(X0) = iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_2873,plain,
% 3.62/1.02      ( k6_domain_1(u1_struct_0(sK2),sK3) = k1_tarski(sK3)
% 3.62/1.02      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 3.62/1.02      inference(superposition,[status(thm)],[c_2240,c_2249]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_33,negated_conjecture,
% 3.62/1.02      ( ~ v2_struct_0(sK2) ),
% 3.62/1.02      inference(cnf_transformation,[],[f96]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_32,negated_conjecture,
% 3.62/1.02      ( l1_pre_topc(sK2) ),
% 3.62/1.02      inference(cnf_transformation,[],[f97]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_12,plain,
% 3.62/1.02      ( v2_struct_0(X0)
% 3.62/1.02      | ~ l1_struct_0(X0)
% 3.62/1.02      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 3.62/1.02      inference(cnf_transformation,[],[f79]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_84,plain,
% 3.62/1.02      ( v2_struct_0(sK2)
% 3.62/1.02      | ~ l1_struct_0(sK2)
% 3.62/1.02      | ~ v1_xboole_0(u1_struct_0(sK2)) ),
% 3.62/1.02      inference(instantiation,[status(thm)],[c_12]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_9,plain,
% 3.62/1.02      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 3.62/1.02      inference(cnf_transformation,[],[f76]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_91,plain,
% 3.62/1.02      ( ~ l1_pre_topc(sK2) | l1_struct_0(sK2) ),
% 3.62/1.02      inference(instantiation,[status(thm)],[c_9]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_2545,plain,
% 3.62/1.02      ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 3.62/1.02      | v1_xboole_0(u1_struct_0(sK2))
% 3.62/1.02      | k6_domain_1(u1_struct_0(sK2),sK3) = k1_tarski(sK3) ),
% 3.62/1.02      inference(instantiation,[status(thm)],[c_13]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_2984,plain,
% 3.62/1.02      ( k6_domain_1(u1_struct_0(sK2),sK3) = k1_tarski(sK3) ),
% 3.62/1.02      inference(global_propositional_subsumption,
% 3.62/1.02                [status(thm)],
% 3.62/1.02                [c_2873,c_33,c_32,c_31,c_84,c_91,c_2545]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_17,plain,
% 3.62/1.02      ( v1_tex_2(X0,X1)
% 3.62/1.02      | ~ m1_pre_topc(X0,X1)
% 3.62/1.02      | m1_subset_1(sK1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.62/1.02      | ~ l1_pre_topc(X1) ),
% 3.62/1.02      inference(cnf_transformation,[],[f83]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_29,negated_conjecture,
% 3.62/1.02      ( ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2)
% 3.62/1.02      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) ),
% 3.62/1.02      inference(cnf_transformation,[],[f100]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_266,plain,
% 3.62/1.02      ( ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2)
% 3.62/1.02      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) ),
% 3.62/1.02      inference(prop_impl,[status(thm)],[c_29]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_848,plain,
% 3.62/1.02      ( ~ m1_pre_topc(X0,X1)
% 3.62/1.02      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 3.62/1.02      | m1_subset_1(sK1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.62/1.02      | ~ l1_pre_topc(X1)
% 3.62/1.02      | k1_tex_2(sK2,sK3) != X0
% 3.62/1.02      | sK2 != X1 ),
% 3.62/1.02      inference(resolution_lifted,[status(thm)],[c_17,c_266]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_849,plain,
% 3.62/1.02      ( ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
% 3.62/1.02      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 3.62/1.02      | m1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.62/1.02      | ~ l1_pre_topc(sK2) ),
% 3.62/1.02      inference(unflattening,[status(thm)],[c_848]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_851,plain,
% 3.62/1.02      ( m1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.62/1.02      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 3.62/1.02      | ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2) ),
% 3.62/1.02      inference(global_propositional_subsumption,
% 3.62/1.02                [status(thm)],
% 3.62/1.02                [c_849,c_32]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_852,plain,
% 3.62/1.02      ( ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
% 3.62/1.02      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 3.62/1.02      | m1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.62/1.02      inference(renaming,[status(thm)],[c_851]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_2229,plain,
% 3.62/1.02      ( m1_pre_topc(k1_tex_2(sK2,sK3),sK2) != iProver_top
% 3.62/1.02      | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) != iProver_top
% 3.62/1.02      | m1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_852]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_34,plain,
% 3.62/1.02      ( v2_struct_0(sK2) != iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_35,plain,
% 3.62/1.02      ( l1_pre_topc(sK2) = iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_36,plain,
% 3.62/1.02      ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_83,plain,
% 3.62/1.02      ( v2_struct_0(X0) = iProver_top
% 3.62/1.02      | l1_struct_0(X0) != iProver_top
% 3.62/1.02      | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_85,plain,
% 3.62/1.02      ( v2_struct_0(sK2) = iProver_top
% 3.62/1.02      | l1_struct_0(sK2) != iProver_top
% 3.62/1.02      | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 3.62/1.02      inference(instantiation,[status(thm)],[c_83]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_90,plain,
% 3.62/1.02      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_92,plain,
% 3.62/1.02      ( l1_pre_topc(sK2) != iProver_top
% 3.62/1.02      | l1_struct_0(sK2) = iProver_top ),
% 3.62/1.02      inference(instantiation,[status(thm)],[c_90]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_850,plain,
% 3.62/1.02      ( m1_pre_topc(k1_tex_2(sK2,sK3),sK2) != iProver_top
% 3.62/1.02      | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) != iProver_top
% 3.62/1.02      | m1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 3.62/1.02      | l1_pre_topc(sK2) != iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_849]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_21,plain,
% 3.62/1.02      ( m1_pre_topc(k1_tex_2(X0,X1),X0)
% 3.62/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.62/1.02      | v2_struct_0(X0)
% 3.62/1.02      | ~ l1_pre_topc(X0) ),
% 3.62/1.02      inference(cnf_transformation,[],[f89]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_2554,plain,
% 3.62/1.02      ( m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
% 3.62/1.02      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 3.62/1.02      | v2_struct_0(sK2)
% 3.62/1.02      | ~ l1_pre_topc(sK2) ),
% 3.62/1.02      inference(instantiation,[status(thm)],[c_21]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_2555,plain,
% 3.62/1.02      ( m1_pre_topc(k1_tex_2(sK2,sK3),sK2) = iProver_top
% 3.62/1.02      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 3.62/1.02      | v2_struct_0(sK2) = iProver_top
% 3.62/1.02      | l1_pre_topc(sK2) != iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_2554]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_27,plain,
% 3.62/1.02      ( v1_subset_1(k6_domain_1(X0,X1),X0)
% 3.62/1.02      | ~ m1_subset_1(X1,X0)
% 3.62/1.02      | v1_zfmisc_1(X0)
% 3.62/1.02      | v1_xboole_0(X0) ),
% 3.62/1.02      inference(cnf_transformation,[],[f94]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_2567,plain,
% 3.62/1.02      ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 3.62/1.02      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 3.62/1.02      | v1_zfmisc_1(u1_struct_0(sK2))
% 3.62/1.02      | v1_xboole_0(u1_struct_0(sK2)) ),
% 3.62/1.02      inference(instantiation,[status(thm)],[c_27]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_2568,plain,
% 3.62/1.02      ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) = iProver_top
% 3.62/1.02      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 3.62/1.02      | v1_zfmisc_1(u1_struct_0(sK2)) = iProver_top
% 3.62/1.02      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_2567]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_26,plain,
% 3.62/1.02      ( ~ v1_subset_1(k6_domain_1(X0,X1),X0)
% 3.62/1.02      | ~ m1_subset_1(X1,X0)
% 3.62/1.02      | ~ v1_zfmisc_1(X0)
% 3.62/1.02      | v1_xboole_0(X0) ),
% 3.62/1.02      inference(cnf_transformation,[],[f93]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_2242,plain,
% 3.62/1.02      ( v1_subset_1(k6_domain_1(X0,X1),X0) != iProver_top
% 3.62/1.02      | m1_subset_1(X1,X0) != iProver_top
% 3.62/1.02      | v1_zfmisc_1(X0) != iProver_top
% 3.62/1.02      | v1_xboole_0(X0) = iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_3568,plain,
% 3.62/1.02      ( v1_subset_1(k1_tarski(sK3),u1_struct_0(sK2)) != iProver_top
% 3.62/1.02      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 3.62/1.02      | v1_zfmisc_1(u1_struct_0(sK2)) != iProver_top
% 3.62/1.02      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 3.62/1.02      inference(superposition,[status(thm)],[c_2984,c_2242]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_24,plain,
% 3.62/1.02      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.62/1.02      | v2_struct_0(X1)
% 3.62/1.02      | ~ v2_struct_0(k1_tex_2(X1,X0))
% 3.62/1.02      | ~ l1_pre_topc(X1) ),
% 3.62/1.02      inference(cnf_transformation,[],[f90]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_2551,plain,
% 3.62/1.02      ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 3.62/1.02      | ~ v2_struct_0(k1_tex_2(sK2,sK3))
% 3.62/1.02      | v2_struct_0(sK2)
% 3.62/1.02      | ~ l1_pre_topc(sK2) ),
% 3.62/1.02      inference(instantiation,[status(thm)],[c_24]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_2552,plain,
% 3.62/1.02      ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 3.62/1.02      | v2_struct_0(k1_tex_2(sK2,sK3)) != iProver_top
% 3.62/1.02      | v2_struct_0(sK2) = iProver_top
% 3.62/1.02      | l1_pre_topc(sK2) != iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_2551]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_18,plain,
% 3.62/1.02      ( ~ v1_tex_2(X0,X1)
% 3.62/1.02      | ~ m1_pre_topc(X0,X1)
% 3.62/1.02      | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
% 3.62/1.02      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.62/1.02      | ~ l1_pre_topc(X1) ),
% 3.62/1.02      inference(cnf_transformation,[],[f101]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_25,plain,
% 3.62/1.02      ( ~ m1_pre_topc(X0,X1)
% 3.62/1.02      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.62/1.02      | ~ l1_pre_topc(X1) ),
% 3.62/1.02      inference(cnf_transformation,[],[f92]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_200,plain,
% 3.62/1.02      ( v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
% 3.62/1.02      | ~ m1_pre_topc(X0,X1)
% 3.62/1.02      | ~ v1_tex_2(X0,X1)
% 3.62/1.02      | ~ l1_pre_topc(X1) ),
% 3.62/1.02      inference(global_propositional_subsumption,
% 3.62/1.02                [status(thm)],
% 3.62/1.02                [c_18,c_25]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_201,plain,
% 3.62/1.02      ( ~ v1_tex_2(X0,X1)
% 3.62/1.02      | ~ m1_pre_topc(X0,X1)
% 3.62/1.02      | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
% 3.62/1.02      | ~ l1_pre_topc(X1) ),
% 3.62/1.02      inference(renaming,[status(thm)],[c_200]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_30,negated_conjecture,
% 3.62/1.02      ( v1_tex_2(k1_tex_2(sK2,sK3),sK2)
% 3.62/1.02      | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) ),
% 3.62/1.02      inference(cnf_transformation,[],[f99]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_268,plain,
% 3.62/1.02      ( v1_tex_2(k1_tex_2(sK2,sK3),sK2)
% 3.62/1.02      | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) ),
% 3.62/1.02      inference(prop_impl,[status(thm)],[c_30]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_899,plain,
% 3.62/1.02      ( ~ m1_pre_topc(X0,X1)
% 3.62/1.02      | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 3.62/1.02      | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
% 3.62/1.02      | ~ l1_pre_topc(X1)
% 3.62/1.02      | k1_tex_2(sK2,sK3) != X0
% 3.62/1.02      | sK2 != X1 ),
% 3.62/1.02      inference(resolution_lifted,[status(thm)],[c_201,c_268]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_900,plain,
% 3.62/1.02      ( ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
% 3.62/1.02      | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 3.62/1.02      | v1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),u1_struct_0(sK2))
% 3.62/1.02      | ~ l1_pre_topc(sK2) ),
% 3.62/1.02      inference(unflattening,[status(thm)],[c_899]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_902,plain,
% 3.62/1.02      ( v1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),u1_struct_0(sK2))
% 3.62/1.02      | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 3.62/1.02      | ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2) ),
% 3.62/1.02      inference(global_propositional_subsumption,
% 3.62/1.02                [status(thm)],
% 3.62/1.02                [c_900,c_32]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_903,plain,
% 3.62/1.02      ( ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
% 3.62/1.02      | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 3.62/1.02      | v1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),u1_struct_0(sK2)) ),
% 3.62/1.02      inference(renaming,[status(thm)],[c_902]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_2226,plain,
% 3.62/1.02      ( m1_pre_topc(k1_tex_2(sK2,sK3),sK2) != iProver_top
% 3.62/1.02      | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) = iProver_top
% 3.62/1.02      | v1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),u1_struct_0(sK2)) = iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_903]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_901,plain,
% 3.62/1.02      ( m1_pre_topc(k1_tex_2(sK2,sK3),sK2) != iProver_top
% 3.62/1.02      | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) = iProver_top
% 3.62/1.02      | v1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),u1_struct_0(sK2)) = iProver_top
% 3.62/1.02      | l1_pre_topc(sK2) != iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_900]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_2616,plain,
% 3.62/1.02      ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) = iProver_top
% 3.62/1.02      | v1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),u1_struct_0(sK2)) = iProver_top ),
% 3.62/1.02      inference(global_propositional_subsumption,
% 3.62/1.02                [status(thm)],
% 3.62/1.02                [c_2226,c_34,c_35,c_36,c_901,c_2555]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_2634,plain,
% 3.62/1.02      ( ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
% 3.62/1.02      | m1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.62/1.02      | ~ l1_pre_topc(sK2) ),
% 3.62/1.02      inference(instantiation,[status(thm)],[c_25]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_2635,plain,
% 3.62/1.02      ( m1_pre_topc(k1_tex_2(sK2,sK3),sK2) != iProver_top
% 3.62/1.02      | m1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 3.62/1.02      | l1_pre_topc(sK2) != iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_2634]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_10,plain,
% 3.62/1.02      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.62/1.02      inference(cnf_transformation,[],[f77]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_2930,plain,
% 3.62/1.02      ( ~ m1_pre_topc(k1_tex_2(sK2,sK3),X0)
% 3.62/1.02      | ~ l1_pre_topc(X0)
% 3.62/1.02      | l1_pre_topc(k1_tex_2(sK2,sK3)) ),
% 3.62/1.02      inference(instantiation,[status(thm)],[c_10]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_2931,plain,
% 3.62/1.02      ( m1_pre_topc(k1_tex_2(sK2,sK3),X0) != iProver_top
% 3.62/1.02      | l1_pre_topc(X0) != iProver_top
% 3.62/1.02      | l1_pre_topc(k1_tex_2(sK2,sK3)) = iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_2930]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_2933,plain,
% 3.62/1.02      ( m1_pre_topc(k1_tex_2(sK2,sK3),sK2) != iProver_top
% 3.62/1.02      | l1_pre_topc(k1_tex_2(sK2,sK3)) = iProver_top
% 3.62/1.02      | l1_pre_topc(sK2) != iProver_top ),
% 3.62/1.02      inference(instantiation,[status(thm)],[c_2931]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_2978,plain,
% 3.62/1.02      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),X0),u1_struct_0(sK2))
% 3.62/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.62/1.02      | ~ v1_zfmisc_1(u1_struct_0(sK2))
% 3.62/1.02      | v1_xboole_0(u1_struct_0(sK2)) ),
% 3.62/1.02      inference(instantiation,[status(thm)],[c_26]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_3286,plain,
% 3.62/1.02      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 3.62/1.02      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 3.62/1.02      | ~ v1_zfmisc_1(u1_struct_0(sK2))
% 3.62/1.02      | v1_xboole_0(u1_struct_0(sK2)) ),
% 3.62/1.02      inference(instantiation,[status(thm)],[c_2978]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_3287,plain,
% 3.62/1.02      ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) != iProver_top
% 3.62/1.02      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 3.62/1.02      | v1_zfmisc_1(u1_struct_0(sK2)) != iProver_top
% 3.62/1.02      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_3286]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_14,plain,
% 3.62/1.02      ( ~ v1_subset_1(X0,X1)
% 3.62/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.62/1.02      | ~ v1_zfmisc_1(X1)
% 3.62/1.02      | v1_xboole_0(X0)
% 3.62/1.02      | v1_xboole_0(X1) ),
% 3.62/1.02      inference(cnf_transformation,[],[f81]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_5,plain,
% 3.62/1.02      ( ~ v1_subset_1(X0,X1)
% 3.62/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.62/1.02      | ~ v1_xboole_0(X1) ),
% 3.62/1.02      inference(cnf_transformation,[],[f72]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_210,plain,
% 3.62/1.02      ( v1_xboole_0(X0)
% 3.62/1.02      | ~ v1_zfmisc_1(X1)
% 3.62/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.62/1.02      | ~ v1_subset_1(X0,X1) ),
% 3.62/1.02      inference(global_propositional_subsumption,
% 3.62/1.02                [status(thm)],
% 3.62/1.02                [c_14,c_5]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_211,plain,
% 3.62/1.02      ( ~ v1_subset_1(X0,X1)
% 3.62/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.62/1.02      | ~ v1_zfmisc_1(X1)
% 3.62/1.02      | v1_xboole_0(X0) ),
% 3.62/1.02      inference(renaming,[status(thm)],[c_210]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_2973,plain,
% 3.62/1.02      ( ~ v1_subset_1(X0,u1_struct_0(sK2))
% 3.62/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.62/1.02      | ~ v1_zfmisc_1(u1_struct_0(sK2))
% 3.62/1.02      | v1_xboole_0(X0) ),
% 3.62/1.02      inference(instantiation,[status(thm)],[c_211]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_3323,plain,
% 3.62/1.02      ( ~ v1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),u1_struct_0(sK2))
% 3.62/1.02      | ~ m1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.62/1.02      | ~ v1_zfmisc_1(u1_struct_0(sK2))
% 3.62/1.02      | v1_xboole_0(u1_struct_0(k1_tex_2(sK2,sK3))) ),
% 3.62/1.02      inference(instantiation,[status(thm)],[c_2973]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_3324,plain,
% 3.62/1.02      ( v1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),u1_struct_0(sK2)) != iProver_top
% 3.62/1.02      | m1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.62/1.02      | v1_zfmisc_1(u1_struct_0(sK2)) != iProver_top
% 3.62/1.02      | v1_xboole_0(u1_struct_0(k1_tex_2(sK2,sK3))) = iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_3323]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_499,plain,
% 3.62/1.02      ( v2_struct_0(X0)
% 3.62/1.02      | ~ l1_pre_topc(X0)
% 3.62/1.02      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 3.62/1.02      inference(resolution,[status(thm)],[c_9,c_12]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_3540,plain,
% 3.62/1.02      ( v2_struct_0(k1_tex_2(sK2,sK3))
% 3.62/1.02      | ~ l1_pre_topc(k1_tex_2(sK2,sK3))
% 3.62/1.02      | ~ v1_xboole_0(u1_struct_0(k1_tex_2(sK2,sK3))) ),
% 3.62/1.02      inference(instantiation,[status(thm)],[c_499]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_3541,plain,
% 3.62/1.02      ( v2_struct_0(k1_tex_2(sK2,sK3)) = iProver_top
% 3.62/1.02      | l1_pre_topc(k1_tex_2(sK2,sK3)) != iProver_top
% 3.62/1.02      | v1_xboole_0(u1_struct_0(k1_tex_2(sK2,sK3))) != iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_3540]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_3641,plain,
% 3.62/1.02      ( v1_zfmisc_1(u1_struct_0(sK2)) != iProver_top ),
% 3.62/1.02      inference(global_propositional_subsumption,
% 3.62/1.02                [status(thm)],
% 3.62/1.02                [c_3568,c_34,c_35,c_36,c_85,c_92,c_2552,c_2555,c_2616,
% 3.62/1.02                 c_2635,c_2933,c_3287,c_3324,c_3541]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_5274,plain,
% 3.62/1.02      ( m1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.62/1.02      inference(global_propositional_subsumption,
% 3.62/1.02                [status(thm)],
% 3.62/1.02                [c_2229,c_34,c_35,c_36,c_85,c_92,c_850,c_2552,c_2555,
% 3.62/1.02                 c_2568,c_2616,c_2635,c_2933,c_3287,c_3324,c_3541]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_16,plain,
% 3.62/1.02      ( v1_tex_2(X0,X1)
% 3.62/1.02      | ~ m1_pre_topc(X0,X1)
% 3.62/1.02      | ~ l1_pre_topc(X1)
% 3.62/1.02      | sK1(X1,X0) = u1_struct_0(X0) ),
% 3.62/1.02      inference(cnf_transformation,[],[f84]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_865,plain,
% 3.62/1.02      ( ~ m1_pre_topc(X0,X1)
% 3.62/1.02      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 3.62/1.02      | ~ l1_pre_topc(X1)
% 3.62/1.02      | k1_tex_2(sK2,sK3) != X0
% 3.62/1.02      | sK1(X1,X0) = u1_struct_0(X0)
% 3.62/1.02      | sK2 != X1 ),
% 3.62/1.02      inference(resolution_lifted,[status(thm)],[c_16,c_266]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_866,plain,
% 3.62/1.02      ( ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
% 3.62/1.02      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 3.62/1.02      | ~ l1_pre_topc(sK2)
% 3.62/1.02      | sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(k1_tex_2(sK2,sK3)) ),
% 3.62/1.02      inference(unflattening,[status(thm)],[c_865]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_868,plain,
% 3.62/1.02      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 3.62/1.02      | ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
% 3.62/1.02      | sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(k1_tex_2(sK2,sK3)) ),
% 3.62/1.02      inference(global_propositional_subsumption,
% 3.62/1.02                [status(thm)],
% 3.62/1.02                [c_866,c_32]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_869,plain,
% 3.62/1.02      ( ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
% 3.62/1.02      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 3.62/1.02      | sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(k1_tex_2(sK2,sK3)) ),
% 3.62/1.02      inference(renaming,[status(thm)],[c_868]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_2228,plain,
% 3.62/1.02      ( sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(k1_tex_2(sK2,sK3))
% 3.62/1.02      | m1_pre_topc(k1_tex_2(sK2,sK3),sK2) != iProver_top
% 3.62/1.02      | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) != iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_869]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_867,plain,
% 3.62/1.02      ( sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(k1_tex_2(sK2,sK3))
% 3.62/1.02      | m1_pre_topc(k1_tex_2(sK2,sK3),sK2) != iProver_top
% 3.62/1.02      | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) != iProver_top
% 3.62/1.02      | l1_pre_topc(sK2) != iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_866]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_4110,plain,
% 3.62/1.02      ( sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(k1_tex_2(sK2,sK3)) ),
% 3.62/1.02      inference(global_propositional_subsumption,
% 3.62/1.02                [status(thm)],
% 3.62/1.02                [c_2228,c_34,c_35,c_36,c_85,c_92,c_867,c_2552,c_2555,
% 3.62/1.02                 c_2568,c_2616,c_2635,c_2933,c_3287,c_3324,c_3541]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_5278,plain,
% 3.62/1.02      ( m1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.62/1.02      inference(light_normalisation,[status(thm)],[c_5274,c_4110]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_19,plain,
% 3.62/1.02      ( v1_subset_1(X0,X1)
% 3.62/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.62/1.02      | X1 = X0 ),
% 3.62/1.02      inference(cnf_transformation,[],[f87]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_2248,plain,
% 3.62/1.02      ( X0 = X1
% 3.62/1.02      | v1_subset_1(X1,X0) = iProver_top
% 3.62/1.02      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_5286,plain,
% 3.62/1.02      ( u1_struct_0(k1_tex_2(sK2,sK3)) = u1_struct_0(sK2)
% 3.62/1.02      | v1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),u1_struct_0(sK2)) = iProver_top ),
% 3.62/1.02      inference(superposition,[status(thm)],[c_5278,c_2248]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_2241,plain,
% 3.62/1.02      ( v1_subset_1(k6_domain_1(X0,X1),X0) = iProver_top
% 3.62/1.02      | m1_subset_1(X1,X0) != iProver_top
% 3.62/1.02      | v1_zfmisc_1(X0) = iProver_top
% 3.62/1.02      | v1_xboole_0(X0) = iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_3469,plain,
% 3.62/1.02      ( v1_subset_1(k1_tarski(sK3),u1_struct_0(sK2)) = iProver_top
% 3.62/1.02      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 3.62/1.02      | v1_zfmisc_1(u1_struct_0(sK2)) = iProver_top
% 3.62/1.02      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 3.62/1.02      inference(superposition,[status(thm)],[c_2984,c_2241]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_15,plain,
% 3.62/1.02      ( v1_tex_2(X0,X1)
% 3.62/1.02      | ~ m1_pre_topc(X0,X1)
% 3.62/1.02      | ~ v1_subset_1(sK1(X1,X0),u1_struct_0(X1))
% 3.62/1.02      | ~ l1_pre_topc(X1) ),
% 3.62/1.02      inference(cnf_transformation,[],[f85]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_882,plain,
% 3.62/1.02      ( ~ m1_pre_topc(X0,X1)
% 3.62/1.02      | ~ v1_subset_1(sK1(X1,X0),u1_struct_0(X1))
% 3.62/1.02      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 3.62/1.02      | ~ l1_pre_topc(X1)
% 3.62/1.02      | k1_tex_2(sK2,sK3) != X0
% 3.62/1.02      | sK2 != X1 ),
% 3.62/1.02      inference(resolution_lifted,[status(thm)],[c_15,c_266]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_883,plain,
% 3.62/1.02      ( ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
% 3.62/1.02      | ~ v1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),u1_struct_0(sK2))
% 3.62/1.02      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 3.62/1.02      | ~ l1_pre_topc(sK2) ),
% 3.62/1.02      inference(unflattening,[status(thm)],[c_882]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_885,plain,
% 3.62/1.02      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 3.62/1.02      | ~ v1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),u1_struct_0(sK2))
% 3.62/1.02      | ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2) ),
% 3.62/1.02      inference(global_propositional_subsumption,
% 3.62/1.02                [status(thm)],
% 3.62/1.02                [c_883,c_32]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_886,plain,
% 3.62/1.02      ( ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
% 3.62/1.02      | ~ v1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),u1_struct_0(sK2))
% 3.62/1.02      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) ),
% 3.62/1.02      inference(renaming,[status(thm)],[c_885]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_2227,plain,
% 3.62/1.02      ( m1_pre_topc(k1_tex_2(sK2,sK3),sK2) != iProver_top
% 3.62/1.02      | v1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),u1_struct_0(sK2)) != iProver_top
% 3.62/1.02      | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) != iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_886]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_887,plain,
% 3.62/1.02      ( m1_pre_topc(k1_tex_2(sK2,sK3),sK2) != iProver_top
% 3.62/1.02      | v1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),u1_struct_0(sK2)) != iProver_top
% 3.62/1.02      | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) != iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_886]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_3304,plain,
% 3.62/1.02      ( v1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),u1_struct_0(sK2)) != iProver_top
% 3.62/1.02      | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) != iProver_top ),
% 3.62/1.02      inference(global_propositional_subsumption,
% 3.62/1.02                [status(thm)],
% 3.62/1.02                [c_2227,c_34,c_35,c_36,c_887,c_2555]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_3308,plain,
% 3.62/1.02      ( v1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),u1_struct_0(sK2)) != iProver_top
% 3.62/1.02      | v1_subset_1(k1_tarski(sK3),u1_struct_0(sK2)) != iProver_top ),
% 3.62/1.02      inference(light_normalisation,[status(thm)],[c_3304,c_2984]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_4113,plain,
% 3.62/1.02      ( v1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),u1_struct_0(sK2)) != iProver_top
% 3.62/1.02      | v1_subset_1(k1_tarski(sK3),u1_struct_0(sK2)) != iProver_top ),
% 3.62/1.02      inference(demodulation,[status(thm)],[c_4110,c_3308]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_5392,plain,
% 3.62/1.02      ( u1_struct_0(k1_tex_2(sK2,sK3)) = u1_struct_0(sK2) ),
% 3.62/1.02      inference(global_propositional_subsumption,
% 3.62/1.02                [status(thm)],
% 3.62/1.02                [c_5286,c_34,c_35,c_36,c_85,c_92,c_2552,c_2555,c_2616,
% 3.62/1.02                 c_2635,c_2933,c_3287,c_3324,c_3469,c_3541,c_4113]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_28,plain,
% 3.62/1.02      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
% 3.62/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.62/1.02      | ~ v7_struct_0(X0)
% 3.62/1.02      | v2_struct_0(X0)
% 3.62/1.02      | ~ l1_struct_0(X0) ),
% 3.62/1.02      inference(cnf_transformation,[],[f95]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_479,plain,
% 3.62/1.02      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
% 3.62/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.62/1.02      | ~ v7_struct_0(X0)
% 3.62/1.02      | v2_struct_0(X0)
% 3.62/1.02      | ~ l1_pre_topc(X0) ),
% 3.62/1.02      inference(resolution,[status(thm)],[c_9,c_28]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_2236,plain,
% 3.62/1.02      ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) != iProver_top
% 3.62/1.02      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 3.62/1.02      | v7_struct_0(X0) != iProver_top
% 3.62/1.02      | v2_struct_0(X0) = iProver_top
% 3.62/1.02      | l1_pre_topc(X0) != iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_479]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_9840,plain,
% 3.62/1.02      ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),X0),u1_struct_0(sK2)) != iProver_top
% 3.62/1.02      | m1_subset_1(X0,u1_struct_0(k1_tex_2(sK2,sK3))) != iProver_top
% 3.62/1.02      | v7_struct_0(k1_tex_2(sK2,sK3)) != iProver_top
% 3.62/1.02      | v2_struct_0(k1_tex_2(sK2,sK3)) = iProver_top
% 3.62/1.02      | l1_pre_topc(k1_tex_2(sK2,sK3)) != iProver_top ),
% 3.62/1.02      inference(superposition,[status(thm)],[c_5392,c_2236]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_9847,plain,
% 3.62/1.02      ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),X0),u1_struct_0(sK2)) != iProver_top
% 3.62/1.02      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 3.62/1.02      | v7_struct_0(k1_tex_2(sK2,sK3)) != iProver_top
% 3.62/1.02      | v2_struct_0(k1_tex_2(sK2,sK3)) = iProver_top
% 3.62/1.02      | l1_pre_topc(k1_tex_2(sK2,sK3)) != iProver_top ),
% 3.62/1.02      inference(light_normalisation,[status(thm)],[c_9840,c_5392]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_23,plain,
% 3.62/1.02      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.62/1.02      | v7_struct_0(k1_tex_2(X1,X0))
% 3.62/1.02      | v2_struct_0(X1)
% 3.62/1.02      | ~ l1_pre_topc(X1) ),
% 3.62/1.02      inference(cnf_transformation,[],[f91]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_2548,plain,
% 3.62/1.02      ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 3.62/1.02      | v7_struct_0(k1_tex_2(sK2,sK3))
% 3.62/1.02      | v2_struct_0(sK2)
% 3.62/1.02      | ~ l1_pre_topc(sK2) ),
% 3.62/1.02      inference(instantiation,[status(thm)],[c_23]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_2549,plain,
% 3.62/1.02      ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 3.62/1.02      | v7_struct_0(k1_tex_2(sK2,sK3)) = iProver_top
% 3.62/1.02      | v2_struct_0(sK2) = iProver_top
% 3.62/1.02      | l1_pre_topc(sK2) != iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_2548]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_13460,plain,
% 3.62/1.02      ( m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 3.62/1.02      | v1_subset_1(k6_domain_1(u1_struct_0(sK2),X0),u1_struct_0(sK2)) != iProver_top ),
% 3.62/1.02      inference(global_propositional_subsumption,
% 3.62/1.02                [status(thm)],
% 3.62/1.02                [c_9847,c_34,c_35,c_36,c_2549,c_2552,c_2555,c_2933]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_13461,plain,
% 3.62/1.02      ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),X0),u1_struct_0(sK2)) != iProver_top
% 3.62/1.02      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
% 3.62/1.02      inference(renaming,[status(thm)],[c_13460]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_13469,plain,
% 3.62/1.02      ( v1_subset_1(k1_tarski(sK3),u1_struct_0(sK2)) != iProver_top
% 3.62/1.02      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 3.62/1.02      inference(superposition,[status(thm)],[c_2984,c_13461]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(contradiction,plain,
% 3.62/1.02      ( $false ),
% 3.62/1.02      inference(minisat,
% 3.62/1.02                [status(thm)],
% 3.62/1.02                [c_13469,c_3641,c_3469,c_92,c_85,c_36,c_35,c_34]) ).
% 3.62/1.02  
% 3.62/1.02  
% 3.62/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 3.62/1.02  
% 3.62/1.02  ------                               Statistics
% 3.62/1.02  
% 3.62/1.02  ------ General
% 3.62/1.02  
% 3.62/1.02  abstr_ref_over_cycles:                  0
% 3.62/1.02  abstr_ref_under_cycles:                 0
% 3.62/1.02  gc_basic_clause_elim:                   0
% 3.62/1.02  forced_gc_time:                         0
% 3.62/1.02  parsing_time:                           0.013
% 3.62/1.02  unif_index_cands_time:                  0.
% 3.62/1.02  unif_index_add_time:                    0.
% 3.62/1.02  orderings_time:                         0.
% 3.62/1.02  out_proof_time:                         0.016
% 3.62/1.02  total_time:                             0.489
% 3.62/1.02  num_of_symbols:                         52
% 3.62/1.02  num_of_terms:                           7733
% 3.62/1.02  
% 3.62/1.02  ------ Preprocessing
% 3.62/1.02  
% 3.62/1.02  num_of_splits:                          0
% 3.62/1.02  num_of_split_atoms:                     0
% 3.62/1.02  num_of_reused_defs:                     0
% 3.62/1.02  num_eq_ax_congr_red:                    21
% 3.62/1.02  num_of_sem_filtered_clauses:            1
% 3.62/1.02  num_of_subtypes:                        0
% 3.62/1.02  monotx_restored_types:                  0
% 3.62/1.02  sat_num_of_epr_types:                   0
% 3.62/1.02  sat_num_of_non_cyclic_types:            0
% 3.62/1.02  sat_guarded_non_collapsed_types:        0
% 3.62/1.02  num_pure_diseq_elim:                    0
% 3.62/1.02  simp_replaced_by:                       0
% 3.62/1.02  res_preprocessed:                       155
% 3.62/1.02  prep_upred:                             0
% 3.62/1.02  prep_unflattend:                        53
% 3.62/1.02  smt_new_axioms:                         0
% 3.62/1.02  pred_elim_cands:                        8
% 3.62/1.02  pred_elim:                              3
% 3.62/1.02  pred_elim_cl:                           2
% 3.62/1.02  pred_elim_cycles:                       11
% 3.62/1.02  merged_defs:                            2
% 3.62/1.02  merged_defs_ncl:                        0
% 3.62/1.02  bin_hyper_res:                          2
% 3.62/1.02  prep_cycles:                            4
% 3.62/1.02  pred_elim_time:                         0.02
% 3.62/1.02  splitting_time:                         0.
% 3.62/1.02  sem_filter_time:                        0.
% 3.62/1.02  monotx_time:                            0.001
% 3.62/1.02  subtype_inf_time:                       0.
% 3.62/1.02  
% 3.62/1.02  ------ Problem properties
% 3.62/1.02  
% 3.62/1.02  clauses:                                31
% 3.62/1.02  conjectures:                            3
% 3.62/1.02  epr:                                    5
% 3.62/1.02  horn:                                   22
% 3.62/1.02  ground:                                 7
% 3.62/1.02  unary:                                  5
% 3.62/1.02  binary:                                 1
% 3.62/1.02  lits:                                   94
% 3.62/1.02  lits_eq:                                4
% 3.62/1.02  fd_pure:                                0
% 3.62/1.02  fd_pseudo:                              0
% 3.62/1.02  fd_cond:                                0
% 3.62/1.02  fd_pseudo_cond:                         1
% 3.62/1.02  ac_symbols:                             0
% 3.62/1.02  
% 3.62/1.02  ------ Propositional Solver
% 3.62/1.02  
% 3.62/1.02  prop_solver_calls:                      28
% 3.62/1.02  prop_fast_solver_calls:                 1783
% 3.62/1.02  smt_solver_calls:                       0
% 3.62/1.02  smt_fast_solver_calls:                  0
% 3.62/1.02  prop_num_of_clauses:                    4336
% 3.62/1.02  prop_preprocess_simplified:             11734
% 3.62/1.02  prop_fo_subsumed:                       107
% 3.62/1.02  prop_solver_time:                       0.
% 3.62/1.02  smt_solver_time:                        0.
% 3.62/1.02  smt_fast_solver_time:                   0.
% 3.62/1.02  prop_fast_solver_time:                  0.
% 3.62/1.02  prop_unsat_core_time:                   0.
% 3.62/1.02  
% 3.62/1.02  ------ QBF
% 3.62/1.02  
% 3.62/1.02  qbf_q_res:                              0
% 3.62/1.02  qbf_num_tautologies:                    0
% 3.62/1.02  qbf_prep_cycles:                        0
% 3.62/1.02  
% 3.62/1.02  ------ BMC1
% 3.62/1.02  
% 3.62/1.02  bmc1_current_bound:                     -1
% 3.62/1.02  bmc1_last_solved_bound:                 -1
% 3.62/1.02  bmc1_unsat_core_size:                   -1
% 3.62/1.02  bmc1_unsat_core_parents_size:           -1
% 3.62/1.02  bmc1_merge_next_fun:                    0
% 3.62/1.02  bmc1_unsat_core_clauses_time:           0.
% 3.62/1.02  
% 3.62/1.02  ------ Instantiation
% 3.62/1.02  
% 3.62/1.02  inst_num_of_clauses:                    1189
% 3.62/1.02  inst_num_in_passive:                    214
% 3.62/1.02  inst_num_in_active:                     557
% 3.62/1.02  inst_num_in_unprocessed:                418
% 3.62/1.02  inst_num_of_loops:                      700
% 3.62/1.02  inst_num_of_learning_restarts:          0
% 3.62/1.02  inst_num_moves_active_passive:          140
% 3.62/1.02  inst_lit_activity:                      0
% 3.62/1.02  inst_lit_activity_moves:                0
% 3.62/1.02  inst_num_tautologies:                   0
% 3.62/1.02  inst_num_prop_implied:                  0
% 3.62/1.02  inst_num_existing_simplified:           0
% 3.62/1.02  inst_num_eq_res_simplified:             0
% 3.62/1.02  inst_num_child_elim:                    0
% 3.62/1.02  inst_num_of_dismatching_blockings:      992
% 3.62/1.02  inst_num_of_non_proper_insts:           1240
% 3.62/1.02  inst_num_of_duplicates:                 0
% 3.62/1.02  inst_inst_num_from_inst_to_res:         0
% 3.62/1.02  inst_dismatching_checking_time:         0.
% 3.62/1.02  
% 3.62/1.02  ------ Resolution
% 3.62/1.02  
% 3.62/1.02  res_num_of_clauses:                     0
% 3.62/1.02  res_num_in_passive:                     0
% 3.62/1.02  res_num_in_active:                      0
% 3.62/1.02  res_num_of_loops:                       159
% 3.62/1.02  res_forward_subset_subsumed:            44
% 3.62/1.02  res_backward_subset_subsumed:           2
% 3.62/1.02  res_forward_subsumed:                   0
% 3.62/1.02  res_backward_subsumed:                  0
% 3.62/1.02  res_forward_subsumption_resolution:     2
% 3.62/1.02  res_backward_subsumption_resolution:    0
% 3.62/1.02  res_clause_to_clause_subsumption:       828
% 3.62/1.02  res_orphan_elimination:                 0
% 3.62/1.02  res_tautology_del:                      115
% 3.62/1.02  res_num_eq_res_simplified:              0
% 3.62/1.02  res_num_sel_changes:                    0
% 3.62/1.02  res_moves_from_active_to_pass:          0
% 3.62/1.02  
% 3.62/1.02  ------ Superposition
% 3.62/1.02  
% 3.62/1.02  sup_time_total:                         0.
% 3.62/1.02  sup_time_generating:                    0.
% 3.62/1.02  sup_time_sim_full:                      0.
% 3.62/1.02  sup_time_sim_immed:                     0.
% 3.62/1.02  
% 3.62/1.02  sup_num_of_clauses:                     202
% 3.62/1.02  sup_num_in_active:                      125
% 3.62/1.02  sup_num_in_passive:                     77
% 3.62/1.02  sup_num_of_loops:                       138
% 3.62/1.02  sup_fw_superposition:                   144
% 3.62/1.02  sup_bw_superposition:                   144
% 3.62/1.02  sup_immediate_simplified:               81
% 3.62/1.02  sup_given_eliminated:                   0
% 3.62/1.02  comparisons_done:                       0
% 3.62/1.02  comparisons_avoided:                    0
% 3.62/1.02  
% 3.62/1.02  ------ Simplifications
% 3.62/1.02  
% 3.62/1.02  
% 3.62/1.02  sim_fw_subset_subsumed:                 38
% 3.62/1.02  sim_bw_subset_subsumed:                 2
% 3.62/1.02  sim_fw_subsumed:                        27
% 3.62/1.02  sim_bw_subsumed:                        2
% 3.62/1.02  sim_fw_subsumption_res:                 4
% 3.62/1.02  sim_bw_subsumption_res:                 0
% 3.62/1.02  sim_tautology_del:                      20
% 3.62/1.02  sim_eq_tautology_del:                   6
% 3.62/1.02  sim_eq_res_simp:                        0
% 3.62/1.02  sim_fw_demodulated:                     4
% 3.62/1.02  sim_bw_demodulated:                     12
% 3.62/1.02  sim_light_normalised:                   24
% 3.62/1.02  sim_joinable_taut:                      0
% 3.62/1.02  sim_joinable_simp:                      0
% 3.62/1.02  sim_ac_normalised:                      0
% 3.62/1.02  sim_smt_subsumption:                    0
% 3.62/1.02  
%------------------------------------------------------------------------------
