%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:25:38 EST 2020

% Result     : Theorem 2.27s
% Output     : CNFRefutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :  229 (2373 expanded)
%              Number of clauses        :  141 ( 662 expanded)
%              Number of leaves         :   21 ( 492 expanded)
%              Depth                    :   20
%              Number of atoms          :  810 (11090 expanded)
%              Number of equality atoms :  246 (1039 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f83,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

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
    inference(ennf_transformation,[],[f12])).

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

fof(f52,plain,(
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

fof(f53,plain,(
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
    inference(rectify,[],[f52])).

fof(f54,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v1_subset_1(X2,u1_struct_0(X0))
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_subset_1(sK1(X0,X1),u1_struct_0(X0))
        & u1_struct_0(X1) = sK1(X0,X1)
        & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f53,f54])).

fof(f78,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | u1_struct_0(X1) = sK1(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f17,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( v1_tex_2(k1_tex_2(X0,X1),X0)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f57,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f47])).

fof(f58,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f57])).

fof(f60,plain,(
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

fof(f59,plain,
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

fof(f61,plain,
    ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
      | ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2) )
    & ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
      | v1_tex_2(k1_tex_2(sK2,sK3),sK2) )
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l1_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f58,f60,f59])).

fof(f89,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f61])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f93,plain,(
    ! [X0,X1] :
      ( k2_tarski(X1,X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f70,f62])).

fof(f87,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f61])).

fof(f88,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f61])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f67,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f65,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f91,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2) ),
    inference(cnf_transformation,[],[f61])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v7_struct_0(X0) )
     => ~ v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f68,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
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

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tex_2(X1,X0)
            & ~ v2_struct_0(X1) )
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ v1_tex_2(X1,X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f90,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | v1_tex_2(k1_tex_2(sK2,sK3),sK2) ),
    inference(cnf_transformation,[],[f61])).

fof(f15,axiom,(
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
    inference(pure_predicate_removal,[],[f15])).

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

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f92,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f63,f62])).

fof(f13,axiom,(
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
    inference(ennf_transformation,[],[f13])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f81,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f11,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f48,plain,(
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
    inference(nnf_transformation,[],[f36])).

fof(f49,plain,(
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
    inference(rectify,[],[f48])).

fof(f50,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k6_domain_1(X0,X2) = X0
          & m1_subset_1(X2,X0) )
     => ( k6_domain_1(X0,sK0(X0)) = X0
        & m1_subset_1(sK0(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ( k6_domain_1(X0,sK0(X0)) = X0
            & m1_subset_1(sK0(X0),X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f49,f50])).

fof(f75,plain,(
    ! [X0,X1] :
      ( v1_zfmisc_1(X0)
      | k6_domain_1(X0,X1) != X0
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | ~ v1_subset_1(sK1(X0,X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f85,plain,(
    ! [X0,X1] :
      ( v7_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

fof(f31,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f69,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f74,plain,(
    ! [X0] :
      ( k6_domain_1(X0,sK0(X0)) = X0
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f5,axiom,(
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
    inference(ennf_transformation,[],[f5])).

fof(f66,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f16,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_zfmisc_1(X0)
          | ~ v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_zfmisc_1(X0)
          | ~ v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(X0)
      | ~ v1_subset_1(k6_domain_1(X0,X1),X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_19,plain,
    ( m1_pre_topc(k1_tex_2(X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2855,plain,
    ( m1_pre_topc(k1_tex_2(X0_48,X0_49),X0_48)
    | ~ m1_subset_1(X0_49,u1_struct_0(X0_48))
    | v2_struct_0(X0_48)
    | ~ l1_pre_topc(X0_48) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_3571,plain,
    ( m1_pre_topc(k1_tex_2(X0_48,X0_49),X0_48) = iProver_top
    | m1_subset_1(X0_49,u1_struct_0(X0_48)) != iProver_top
    | v2_struct_0(X0_48) = iProver_top
    | l1_pre_topc(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2855])).

cnf(c_14,plain,
    ( v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK1(X1,X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2860,plain,
    ( v1_tex_2(X0_48,X1_48)
    | ~ m1_pre_topc(X0_48,X1_48)
    | ~ l1_pre_topc(X1_48)
    | sK1(X1_48,X0_48) = u1_struct_0(X0_48) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_3566,plain,
    ( sK1(X0_48,X1_48) = u1_struct_0(X1_48)
    | v1_tex_2(X1_48,X0_48) = iProver_top
    | m1_pre_topc(X1_48,X0_48) != iProver_top
    | l1_pre_topc(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2860])).

cnf(c_4486,plain,
    ( sK1(X0_48,k1_tex_2(X0_48,X0_49)) = u1_struct_0(k1_tex_2(X0_48,X0_49))
    | v1_tex_2(k1_tex_2(X0_48,X0_49),X0_48) = iProver_top
    | m1_subset_1(X0_49,u1_struct_0(X0_48)) != iProver_top
    | v2_struct_0(X0_48) = iProver_top
    | l1_pre_topc(X0_48) != iProver_top ),
    inference(superposition,[status(thm)],[c_3571,c_3566])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2849,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_3577,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2849])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_2866,plain,
    ( ~ m1_subset_1(X0_49,X1_49)
    | v1_xboole_0(X1_49)
    | k6_domain_1(X1_49,X0_49) = k2_tarski(X0_49,X0_49) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_3560,plain,
    ( k6_domain_1(X0_49,X1_49) = k2_tarski(X1_49,X1_49)
    | m1_subset_1(X1_49,X0_49) != iProver_top
    | v1_xboole_0(X0_49) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2866])).

cnf(c_3878,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK3) = k2_tarski(sK3,sK3)
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3577,c_3560])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_27,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_4,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_88,plain,
    ( v2_struct_0(sK2)
    | ~ l1_struct_0(sK2)
    | ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_92,plain,
    ( ~ l1_pre_topc(sK2)
    | l1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_3821,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2))
    | k6_domain_1(u1_struct_0(sK2),sK3) = k2_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_2866])).

cnf(c_4070,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK3) = k2_tarski(sK3,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3878,c_28,c_27,c_26,c_88,c_92,c_3821])).

cnf(c_24,negated_conjecture,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_2851,negated_conjecture,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_3575,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) != iProver_top
    | v1_tex_2(k1_tex_2(sK2,sK3),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2851])).

cnf(c_4074,plain,
    ( v1_subset_1(k2_tarski(sK3,sK3),u1_struct_0(sK2)) != iProver_top
    | v1_tex_2(k1_tex_2(sK2,sK3),sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4070,c_3575])).

cnf(c_29,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_30,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_31,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_33,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) != iProver_top
    | v1_tex_2(k1_tex_2(sK2,sK3),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_5,plain,
    ( v7_struct_0(X0)
    | ~ v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_84,plain,
    ( v7_struct_0(X0) = iProver_top
    | v1_zfmisc_1(u1_struct_0(X0)) != iProver_top
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_86,plain,
    ( v7_struct_0(sK2) = iProver_top
    | v1_zfmisc_1(u1_struct_0(sK2)) != iProver_top
    | l1_struct_0(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_84])).

cnf(c_87,plain,
    ( v2_struct_0(X0) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_89,plain,
    ( v2_struct_0(sK2) = iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_87])).

cnf(c_91,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_93,plain,
    ( l1_pre_topc(sK2) != iProver_top
    | l1_struct_0(sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_91])).

cnf(c_8,plain,
    ( ~ v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v7_struct_0(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_25,negated_conjecture,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | v1_tex_2(k1_tex_2(sK2,sK3),sK2) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_220,plain,
    ( v1_tex_2(k1_tex_2(sK2,sK3),sK2)
    | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) ),
    inference(prop_impl,[status(thm)],[c_25])).

cnf(c_221,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | v1_tex_2(k1_tex_2(sK2,sK3),sK2) ),
    inference(renaming,[status(thm)],[c_220])).

cnf(c_1499,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | ~ m1_pre_topc(X0,X1)
    | ~ v7_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k1_tex_2(sK2,sK3) != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_221])).

cnf(c_1500,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
    | ~ v7_struct_0(sK2)
    | v2_struct_0(k1_tex_2(sK2,sK3))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_1499])).

cnf(c_1502,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
    | ~ v7_struct_0(sK2)
    | v2_struct_0(k1_tex_2(sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1500,c_28,c_27])).

cnf(c_1504,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) = iProver_top
    | m1_pre_topc(k1_tex_2(sK2,sK3),sK2) != iProver_top
    | v7_struct_0(sK2) != iProver_top
    | v2_struct_0(k1_tex_2(sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1502])).

cnf(c_2925,plain,
    ( m1_pre_topc(k1_tex_2(X0_48,X0_49),X0_48) = iProver_top
    | m1_subset_1(X0_49,u1_struct_0(X0_48)) != iProver_top
    | v2_struct_0(X0_48) = iProver_top
    | l1_pre_topc(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2855])).

cnf(c_2927,plain,
    ( m1_pre_topc(k1_tex_2(sK2,sK3),sK2) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2925])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k1_tex_2(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2854,plain,
    ( ~ m1_subset_1(X0_49,u1_struct_0(X0_48))
    | v2_struct_0(X0_48)
    | ~ v2_struct_0(k1_tex_2(X0_48,X0_49))
    | ~ l1_pre_topc(X0_48) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_2928,plain,
    ( m1_subset_1(X0_49,u1_struct_0(X0_48)) != iProver_top
    | v2_struct_0(X0_48) = iProver_top
    | v2_struct_0(k1_tex_2(X0_48,X0_49)) != iProver_top
    | l1_pre_topc(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2854])).

cnf(c_2930,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | v2_struct_0(k1_tex_2(sK2,sK3)) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2928])).

cnf(c_1,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_375,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(resolution,[status(thm)],[c_1,c_0])).

cnf(c_2846,plain,
    ( ~ m1_subset_1(X0_49,X1_49)
    | m1_subset_1(k2_tarski(X0_49,X0_49),k1_zfmisc_1(X1_49))
    | v1_xboole_0(X1_49) ),
    inference(subtyping,[status(esa)],[c_375])).

cnf(c_3805,plain,
    ( m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2846])).

cnf(c_3806,plain,
    ( m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3805])).

cnf(c_17,plain,
    ( v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2857,plain,
    ( v1_subset_1(X0_49,X1_49)
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(X1_49))
    | X0_49 = X1_49 ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_3904,plain,
    ( v1_subset_1(X0_49,u1_struct_0(sK2))
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(u1_struct_0(sK2)))
    | X0_49 = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_2857])).

cnf(c_4029,plain,
    ( v1_subset_1(k2_tarski(sK3,sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | k2_tarski(sK3,sK3) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_3904])).

cnf(c_4030,plain,
    ( k2_tarski(sK3,sK3) = u1_struct_0(sK2)
    | v1_subset_1(k2_tarski(sK3,sK3),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4029])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_zfmisc_1(X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) != X1 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2864,plain,
    ( ~ m1_subset_1(X0_49,X1_49)
    | v1_zfmisc_1(X1_49)
    | v1_xboole_0(X1_49)
    | k6_domain_1(X1_49,X0_49) != X1_49 ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_3562,plain,
    ( k6_domain_1(X0_49,X1_49) != X0_49
    | m1_subset_1(X1_49,X0_49) != iProver_top
    | v1_zfmisc_1(X0_49) = iProver_top
    | v1_xboole_0(X0_49) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2864])).

cnf(c_4085,plain,
    ( k2_tarski(sK3,sK3) != u1_struct_0(sK2)
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK2)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4070,c_3562])).

cnf(c_4088,plain,
    ( v1_tex_2(k1_tex_2(sK2,sK3),sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4074,c_29,c_30,c_31,c_33,c_86,c_89,c_93,c_1504,c_2927,c_2930,c_3806,c_4030,c_4085])).

cnf(c_6578,plain,
    ( sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(k1_tex_2(sK2,sK3))
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4486,c_4088])).

cnf(c_3829,plain,
    ( v1_tex_2(k1_tex_2(X0_48,X0_49),X0_48)
    | ~ m1_pre_topc(k1_tex_2(X0_48,X0_49),X0_48)
    | ~ l1_pre_topc(X0_48)
    | sK1(X0_48,k1_tex_2(X0_48,X0_49)) = u1_struct_0(k1_tex_2(X0_48,X0_49)) ),
    inference(instantiation,[status(thm)],[c_2860])).

cnf(c_3830,plain,
    ( sK1(X0_48,k1_tex_2(X0_48,X0_49)) = u1_struct_0(k1_tex_2(X0_48,X0_49))
    | v1_tex_2(k1_tex_2(X0_48,X0_49),X0_48) = iProver_top
    | m1_pre_topc(k1_tex_2(X0_48,X0_49),X0_48) != iProver_top
    | l1_pre_topc(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3829])).

cnf(c_3832,plain,
    ( sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(k1_tex_2(sK2,sK3))
    | v1_tex_2(k1_tex_2(sK2,sK3),sK2) = iProver_top
    | m1_pre_topc(k1_tex_2(sK2,sK3),sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3830])).

cnf(c_7084,plain,
    ( sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(k1_tex_2(sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6578,c_29,c_30,c_31,c_33,c_86,c_89,c_93,c_1504,c_2927,c_2930,c_3806,c_3832,c_4030,c_4074,c_4085])).

cnf(c_15,plain,
    ( v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | m1_subset_1(sK1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2859,plain,
    ( v1_tex_2(X0_48,X1_48)
    | ~ m1_pre_topc(X0_48,X1_48)
    | m1_subset_1(sK1(X1_48,X0_48),k1_zfmisc_1(u1_struct_0(X1_48)))
    | ~ l1_pre_topc(X1_48) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_3567,plain,
    ( v1_tex_2(X0_48,X1_48) = iProver_top
    | m1_pre_topc(X0_48,X1_48) != iProver_top
    | m1_subset_1(sK1(X1_48,X0_48),k1_zfmisc_1(u1_struct_0(X1_48))) = iProver_top
    | l1_pre_topc(X1_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2859])).

cnf(c_3569,plain,
    ( X0_49 = X1_49
    | v1_subset_1(X0_49,X1_49) = iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(X1_49)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2857])).

cnf(c_5097,plain,
    ( sK1(X0_48,X1_48) = u1_struct_0(X0_48)
    | v1_subset_1(sK1(X0_48,X1_48),u1_struct_0(X0_48)) = iProver_top
    | v1_tex_2(X1_48,X0_48) = iProver_top
    | m1_pre_topc(X1_48,X0_48) != iProver_top
    | l1_pre_topc(X0_48) != iProver_top ),
    inference(superposition,[status(thm)],[c_3567,c_3569])).

cnf(c_13,plain,
    ( ~ v1_subset_1(sK1(X0,X1),u1_struct_0(X0))
    | v1_tex_2(X1,X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2861,plain,
    ( ~ v1_subset_1(sK1(X0_48,X1_48),u1_struct_0(X0_48))
    | v1_tex_2(X1_48,X0_48)
    | ~ m1_pre_topc(X1_48,X0_48)
    | ~ l1_pre_topc(X0_48) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_2915,plain,
    ( v1_subset_1(sK1(X0_48,X1_48),u1_struct_0(X0_48)) != iProver_top
    | v1_tex_2(X1_48,X0_48) = iProver_top
    | m1_pre_topc(X1_48,X0_48) != iProver_top
    | l1_pre_topc(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2861])).

cnf(c_6605,plain,
    ( sK1(X0_48,X1_48) = u1_struct_0(X0_48)
    | v1_tex_2(X1_48,X0_48) = iProver_top
    | m1_pre_topc(X1_48,X0_48) != iProver_top
    | l1_pre_topc(X0_48) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5097,c_2915])).

cnf(c_6613,plain,
    ( sK1(X0_48,k1_tex_2(X0_48,X0_49)) = u1_struct_0(X0_48)
    | v1_tex_2(k1_tex_2(X0_48,X0_49),X0_48) = iProver_top
    | m1_subset_1(X0_49,u1_struct_0(X0_48)) != iProver_top
    | v2_struct_0(X0_48) = iProver_top
    | l1_pre_topc(X0_48) != iProver_top ),
    inference(superposition,[status(thm)],[c_3571,c_6605])).

cnf(c_6726,plain,
    ( sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(sK2)
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_6613,c_4088])).

cnf(c_2926,plain,
    ( m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_2855])).

cnf(c_3824,plain,
    ( v1_tex_2(k1_tex_2(X0_48,X0_49),X0_48)
    | ~ m1_pre_topc(k1_tex_2(X0_48,X0_49),X0_48)
    | m1_subset_1(sK1(X0_48,k1_tex_2(X0_48,X0_49)),k1_zfmisc_1(u1_struct_0(X0_48)))
    | ~ l1_pre_topc(X0_48) ),
    inference(instantiation,[status(thm)],[c_2859])).

cnf(c_3826,plain,
    ( v1_tex_2(k1_tex_2(sK2,sK3),sK2)
    | ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
    | m1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_3824])).

cnf(c_3834,plain,
    ( ~ v1_subset_1(sK1(X0_48,k1_tex_2(X0_48,X0_49)),u1_struct_0(X0_48))
    | v1_tex_2(k1_tex_2(X0_48,X0_49),X0_48)
    | ~ m1_pre_topc(k1_tex_2(X0_48,X0_49),X0_48)
    | ~ l1_pre_topc(X0_48) ),
    inference(instantiation,[status(thm)],[c_2861])).

cnf(c_3836,plain,
    ( ~ v1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),u1_struct_0(sK2))
    | v1_tex_2(k1_tex_2(sK2,sK3),sK2)
    | ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_3834])).

cnf(c_4090,plain,
    ( ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4088])).

cnf(c_4419,plain,
    ( v1_subset_1(sK1(sK2,k1_tex_2(sK2,X0_49)),u1_struct_0(sK2))
    | ~ m1_subset_1(sK1(sK2,k1_tex_2(sK2,X0_49)),k1_zfmisc_1(u1_struct_0(sK2)))
    | sK1(sK2,k1_tex_2(sK2,X0_49)) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_3904])).

cnf(c_4423,plain,
    ( v1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),u1_struct_0(sK2))
    | ~ m1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
    | sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_4419])).

cnf(c_6968,plain,
    ( sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6726,c_28,c_27,c_26,c_2926,c_3826,c_3836,c_4090,c_4423])).

cnf(c_7086,plain,
    ( u1_struct_0(k1_tex_2(sK2,sK3)) = u1_struct_0(sK2) ),
    inference(light_normalisation,[status(thm)],[c_7084,c_6968])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v7_struct_0(k1_tex_2(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_2853,plain,
    ( ~ m1_subset_1(X0_49,u1_struct_0(X0_48))
    | v7_struct_0(k1_tex_2(X0_48,X0_49))
    | v2_struct_0(X0_48)
    | ~ l1_pre_topc(X0_48) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_3573,plain,
    ( m1_subset_1(X0_49,u1_struct_0(X0_48)) != iProver_top
    | v7_struct_0(k1_tex_2(X0_48,X0_49)) = iProver_top
    | v2_struct_0(X0_48) = iProver_top
    | l1_pre_topc(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2853])).

cnf(c_4436,plain,
    ( v7_struct_0(k1_tex_2(sK2,sK3)) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3577,c_3573])).

cnf(c_2931,plain,
    ( m1_subset_1(X0_49,u1_struct_0(X0_48)) != iProver_top
    | v7_struct_0(k1_tex_2(X0_48,X0_49)) = iProver_top
    | v2_struct_0(X0_48) = iProver_top
    | l1_pre_topc(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2853])).

cnf(c_2933,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | v7_struct_0(k1_tex_2(sK2,sK3)) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2931])).

cnf(c_4628,plain,
    ( v7_struct_0(k1_tex_2(sK2,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4436,c_29,c_30,c_31,c_2933])).

cnf(c_6,plain,
    ( ~ v7_struct_0(X0)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_393,plain,
    ( ~ v7_struct_0(X0)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_2,c_6])).

cnf(c_2845,plain,
    ( ~ v7_struct_0(X0_48)
    | v1_zfmisc_1(u1_struct_0(X0_48))
    | ~ l1_pre_topc(X0_48) ),
    inference(subtyping,[status(esa)],[c_393])).

cnf(c_3581,plain,
    ( v7_struct_0(X0_48) != iProver_top
    | v1_zfmisc_1(u1_struct_0(X0_48)) = iProver_top
    | l1_pre_topc(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2845])).

cnf(c_11,plain,
    ( ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0)
    | k6_domain_1(X0,sK0(X0)) = X0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2863,plain,
    ( ~ v1_zfmisc_1(X0_49)
    | v1_xboole_0(X0_49)
    | k6_domain_1(X0_49,sK0(X0_49)) = X0_49 ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_3563,plain,
    ( k6_domain_1(X0_49,sK0(X0_49)) = X0_49
    | v1_zfmisc_1(X0_49) != iProver_top
    | v1_xboole_0(X0_49) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2863])).

cnf(c_4265,plain,
    ( k6_domain_1(u1_struct_0(X0_48),sK0(u1_struct_0(X0_48))) = u1_struct_0(X0_48)
    | v7_struct_0(X0_48) != iProver_top
    | l1_pre_topc(X0_48) != iProver_top
    | v1_xboole_0(u1_struct_0(X0_48)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3581,c_3563])).

cnf(c_421,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_2,c_4])).

cnf(c_2843,plain,
    ( v2_struct_0(X0_48)
    | ~ l1_pre_topc(X0_48)
    | ~ v1_xboole_0(u1_struct_0(X0_48)) ),
    inference(subtyping,[status(esa)],[c_421])).

cnf(c_3583,plain,
    ( v2_struct_0(X0_48) = iProver_top
    | l1_pre_topc(X0_48) != iProver_top
    | v1_xboole_0(u1_struct_0(X0_48)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2843])).

cnf(c_5407,plain,
    ( k6_domain_1(u1_struct_0(X0_48),sK0(u1_struct_0(X0_48))) = u1_struct_0(X0_48)
    | v7_struct_0(X0_48) != iProver_top
    | v2_struct_0(X0_48) = iProver_top
    | l1_pre_topc(X0_48) != iProver_top ),
    inference(superposition,[status(thm)],[c_4265,c_3583])).

cnf(c_5520,plain,
    ( k6_domain_1(u1_struct_0(k1_tex_2(sK2,sK3)),sK0(u1_struct_0(k1_tex_2(sK2,sK3)))) = u1_struct_0(k1_tex_2(sK2,sK3))
    | v2_struct_0(k1_tex_2(sK2,sK3)) = iProver_top
    | l1_pre_topc(k1_tex_2(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4628,c_5407])).

cnf(c_2929,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ v2_struct_0(k1_tex_2(sK2,sK3))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_2854])).

cnf(c_2932,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | v7_struct_0(k1_tex_2(sK2,sK3))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_2853])).

cnf(c_3808,plain,
    ( ~ v7_struct_0(k1_tex_2(X0_48,X0_49))
    | v1_zfmisc_1(u1_struct_0(k1_tex_2(X0_48,X0_49)))
    | ~ l1_pre_topc(k1_tex_2(X0_48,X0_49)) ),
    inference(instantiation,[status(thm)],[c_2845])).

cnf(c_3810,plain,
    ( ~ v7_struct_0(k1_tex_2(sK2,sK3))
    | v1_zfmisc_1(u1_struct_0(k1_tex_2(sK2,sK3)))
    | ~ l1_pre_topc(k1_tex_2(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_3808])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2867,plain,
    ( ~ m1_pre_topc(X0_48,X1_48)
    | ~ l1_pre_topc(X1_48)
    | l1_pre_topc(X0_48) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_3927,plain,
    ( ~ m1_pre_topc(k1_tex_2(X0_48,X0_49),X1_48)
    | ~ l1_pre_topc(X1_48)
    | l1_pre_topc(k1_tex_2(X0_48,X0_49)) ),
    inference(instantiation,[status(thm)],[c_2867])).

cnf(c_3929,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
    | l1_pre_topc(k1_tex_2(sK2,sK3))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_3927])).

cnf(c_4200,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(k1_tex_2(X0_48,X0_49)))
    | v1_xboole_0(u1_struct_0(k1_tex_2(X0_48,X0_49)))
    | k6_domain_1(u1_struct_0(k1_tex_2(X0_48,X0_49)),sK0(u1_struct_0(k1_tex_2(X0_48,X0_49)))) = u1_struct_0(k1_tex_2(X0_48,X0_49)) ),
    inference(instantiation,[status(thm)],[c_2863])).

cnf(c_4207,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(k1_tex_2(sK2,sK3)))
    | v1_xboole_0(u1_struct_0(k1_tex_2(sK2,sK3)))
    | k6_domain_1(u1_struct_0(k1_tex_2(sK2,sK3)),sK0(u1_struct_0(k1_tex_2(sK2,sK3)))) = u1_struct_0(k1_tex_2(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_4200])).

cnf(c_5177,plain,
    ( v2_struct_0(k1_tex_2(X0_48,X0_49))
    | ~ l1_pre_topc(k1_tex_2(X0_48,X0_49))
    | ~ v1_xboole_0(u1_struct_0(k1_tex_2(X0_48,X0_49))) ),
    inference(instantiation,[status(thm)],[c_2843])).

cnf(c_5179,plain,
    ( v2_struct_0(k1_tex_2(sK2,sK3))
    | ~ l1_pre_topc(k1_tex_2(sK2,sK3))
    | ~ v1_xboole_0(u1_struct_0(k1_tex_2(sK2,sK3))) ),
    inference(instantiation,[status(thm)],[c_5177])).

cnf(c_5523,plain,
    ( k6_domain_1(u1_struct_0(k1_tex_2(sK2,sK3)),sK0(u1_struct_0(k1_tex_2(sK2,sK3)))) = u1_struct_0(k1_tex_2(sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5520,c_28,c_27,c_26,c_2926,c_2929,c_2932,c_3810,c_3929,c_4207,c_5179])).

cnf(c_5527,plain,
    ( m1_subset_1(sK0(u1_struct_0(k1_tex_2(sK2,sK3))),u1_struct_0(k1_tex_2(sK2,sK3))) != iProver_top
    | v1_zfmisc_1(u1_struct_0(k1_tex_2(sK2,sK3))) = iProver_top
    | v1_xboole_0(u1_struct_0(k1_tex_2(sK2,sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5523,c_3562])).

cnf(c_3809,plain,
    ( v7_struct_0(k1_tex_2(X0_48,X0_49)) != iProver_top
    | v1_zfmisc_1(u1_struct_0(k1_tex_2(X0_48,X0_49))) = iProver_top
    | l1_pre_topc(k1_tex_2(X0_48,X0_49)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3808])).

cnf(c_3811,plain,
    ( v7_struct_0(k1_tex_2(sK2,sK3)) != iProver_top
    | v1_zfmisc_1(u1_struct_0(k1_tex_2(sK2,sK3))) = iProver_top
    | l1_pre_topc(k1_tex_2(sK2,sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3809])).

cnf(c_3928,plain,
    ( m1_pre_topc(k1_tex_2(X0_48,X0_49),X1_48) != iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | l1_pre_topc(k1_tex_2(X0_48,X0_49)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3927])).

cnf(c_3930,plain,
    ( m1_pre_topc(k1_tex_2(sK2,sK3),sK2) != iProver_top
    | l1_pre_topc(k1_tex_2(sK2,sK3)) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3928])).

cnf(c_5601,plain,
    ( v1_zfmisc_1(u1_struct_0(k1_tex_2(sK2,sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5527,c_29,c_30,c_31,c_2927,c_2933,c_3811,c_3930])).

cnf(c_7095,plain,
    ( v1_zfmisc_1(u1_struct_0(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7086,c_5601])).

cnf(c_23,plain,
    ( ~ v1_subset_1(k6_domain_1(X0,X1),X0)
    | ~ m1_subset_1(X1,X0)
    | ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_2852,plain,
    ( ~ v1_subset_1(k6_domain_1(X0_49,X1_49),X0_49)
    | ~ m1_subset_1(X1_49,X0_49)
    | ~ v1_zfmisc_1(X0_49)
    | v1_xboole_0(X0_49) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_3574,plain,
    ( v1_subset_1(k6_domain_1(X0_49,X1_49),X0_49) != iProver_top
    | m1_subset_1(X1_49,X0_49) != iProver_top
    | v1_zfmisc_1(X0_49) != iProver_top
    | v1_xboole_0(X0_49) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2852])).

cnf(c_4762,plain,
    ( v1_subset_1(k2_tarski(sK3,sK3),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK2)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4070,c_3574])).

cnf(c_2850,negated_conjecture,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | v1_tex_2(k1_tex_2(sK2,sK3),sK2) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_3576,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) = iProver_top
    | v1_tex_2(k1_tex_2(sK2,sK3),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2850])).

cnf(c_4073,plain,
    ( v1_subset_1(k2_tarski(sK3,sK3),u1_struct_0(sK2)) = iProver_top
    | v1_tex_2(k1_tex_2(sK2,sK3),sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4070,c_3576])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7095,c_4762,c_4088,c_4073,c_93,c_89,c_31,c_30,c_29])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:39:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.27/1.07  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.27/1.07  
% 2.27/1.07  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.27/1.07  
% 2.27/1.07  ------  iProver source info
% 2.27/1.07  
% 2.27/1.07  git: date: 2020-06-30 10:37:57 +0100
% 2.27/1.07  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.27/1.07  git: non_committed_changes: false
% 2.27/1.07  git: last_make_outside_of_git: false
% 2.27/1.07  
% 2.27/1.07  ------ 
% 2.27/1.07  
% 2.27/1.07  ------ Input Options
% 2.27/1.07  
% 2.27/1.07  --out_options                           all
% 2.27/1.07  --tptp_safe_out                         true
% 2.27/1.07  --problem_path                          ""
% 2.27/1.07  --include_path                          ""
% 2.27/1.07  --clausifier                            res/vclausify_rel
% 2.27/1.07  --clausifier_options                    --mode clausify
% 2.27/1.07  --stdin                                 false
% 2.27/1.07  --stats_out                             all
% 2.27/1.07  
% 2.27/1.07  ------ General Options
% 2.27/1.07  
% 2.27/1.07  --fof                                   false
% 2.27/1.07  --time_out_real                         305.
% 2.27/1.07  --time_out_virtual                      -1.
% 2.27/1.07  --symbol_type_check                     false
% 2.27/1.07  --clausify_out                          false
% 2.27/1.07  --sig_cnt_out                           false
% 2.27/1.07  --trig_cnt_out                          false
% 2.27/1.07  --trig_cnt_out_tolerance                1.
% 2.27/1.07  --trig_cnt_out_sk_spl                   false
% 2.27/1.07  --abstr_cl_out                          false
% 2.27/1.07  
% 2.27/1.07  ------ Global Options
% 2.27/1.07  
% 2.27/1.07  --schedule                              default
% 2.27/1.07  --add_important_lit                     false
% 2.27/1.07  --prop_solver_per_cl                    1000
% 2.27/1.07  --min_unsat_core                        false
% 2.27/1.07  --soft_assumptions                      false
% 2.27/1.07  --soft_lemma_size                       3
% 2.27/1.07  --prop_impl_unit_size                   0
% 2.27/1.07  --prop_impl_unit                        []
% 2.27/1.07  --share_sel_clauses                     true
% 2.27/1.07  --reset_solvers                         false
% 2.27/1.07  --bc_imp_inh                            [conj_cone]
% 2.27/1.07  --conj_cone_tolerance                   3.
% 2.27/1.07  --extra_neg_conj                        none
% 2.27/1.07  --large_theory_mode                     true
% 2.27/1.07  --prolific_symb_bound                   200
% 2.27/1.07  --lt_threshold                          2000
% 2.27/1.07  --clause_weak_htbl                      true
% 2.27/1.07  --gc_record_bc_elim                     false
% 2.27/1.07  
% 2.27/1.07  ------ Preprocessing Options
% 2.27/1.07  
% 2.27/1.07  --preprocessing_flag                    true
% 2.27/1.07  --time_out_prep_mult                    0.1
% 2.27/1.07  --splitting_mode                        input
% 2.27/1.07  --splitting_grd                         true
% 2.27/1.07  --splitting_cvd                         false
% 2.27/1.07  --splitting_cvd_svl                     false
% 2.27/1.07  --splitting_nvd                         32
% 2.27/1.07  --sub_typing                            true
% 2.27/1.07  --prep_gs_sim                           true
% 2.27/1.07  --prep_unflatten                        true
% 2.27/1.07  --prep_res_sim                          true
% 2.27/1.07  --prep_upred                            true
% 2.27/1.07  --prep_sem_filter                       exhaustive
% 2.27/1.07  --prep_sem_filter_out                   false
% 2.27/1.07  --pred_elim                             true
% 2.27/1.07  --res_sim_input                         true
% 2.27/1.07  --eq_ax_congr_red                       true
% 2.27/1.07  --pure_diseq_elim                       true
% 2.27/1.07  --brand_transform                       false
% 2.27/1.07  --non_eq_to_eq                          false
% 2.27/1.07  --prep_def_merge                        true
% 2.27/1.07  --prep_def_merge_prop_impl              false
% 2.27/1.07  --prep_def_merge_mbd                    true
% 2.27/1.07  --prep_def_merge_tr_red                 false
% 2.27/1.07  --prep_def_merge_tr_cl                  false
% 2.27/1.07  --smt_preprocessing                     true
% 2.27/1.07  --smt_ac_axioms                         fast
% 2.27/1.07  --preprocessed_out                      false
% 2.27/1.07  --preprocessed_stats                    false
% 2.27/1.07  
% 2.27/1.07  ------ Abstraction refinement Options
% 2.27/1.07  
% 2.27/1.07  --abstr_ref                             []
% 2.27/1.07  --abstr_ref_prep                        false
% 2.27/1.07  --abstr_ref_until_sat                   false
% 2.27/1.07  --abstr_ref_sig_restrict                funpre
% 2.27/1.07  --abstr_ref_af_restrict_to_split_sk     false
% 2.27/1.07  --abstr_ref_under                       []
% 2.27/1.07  
% 2.27/1.07  ------ SAT Options
% 2.27/1.07  
% 2.27/1.07  --sat_mode                              false
% 2.27/1.07  --sat_fm_restart_options                ""
% 2.27/1.07  --sat_gr_def                            false
% 2.27/1.07  --sat_epr_types                         true
% 2.27/1.07  --sat_non_cyclic_types                  false
% 2.27/1.07  --sat_finite_models                     false
% 2.27/1.07  --sat_fm_lemmas                         false
% 2.27/1.07  --sat_fm_prep                           false
% 2.27/1.07  --sat_fm_uc_incr                        true
% 2.27/1.07  --sat_out_model                         small
% 2.27/1.07  --sat_out_clauses                       false
% 2.27/1.07  
% 2.27/1.07  ------ QBF Options
% 2.27/1.07  
% 2.27/1.07  --qbf_mode                              false
% 2.27/1.07  --qbf_elim_univ                         false
% 2.27/1.07  --qbf_dom_inst                          none
% 2.27/1.07  --qbf_dom_pre_inst                      false
% 2.27/1.07  --qbf_sk_in                             false
% 2.27/1.07  --qbf_pred_elim                         true
% 2.27/1.07  --qbf_split                             512
% 2.27/1.07  
% 2.27/1.07  ------ BMC1 Options
% 2.27/1.07  
% 2.27/1.07  --bmc1_incremental                      false
% 2.27/1.07  --bmc1_axioms                           reachable_all
% 2.27/1.07  --bmc1_min_bound                        0
% 2.27/1.07  --bmc1_max_bound                        -1
% 2.27/1.07  --bmc1_max_bound_default                -1
% 2.27/1.07  --bmc1_symbol_reachability              true
% 2.27/1.07  --bmc1_property_lemmas                  false
% 2.27/1.07  --bmc1_k_induction                      false
% 2.27/1.07  --bmc1_non_equiv_states                 false
% 2.27/1.07  --bmc1_deadlock                         false
% 2.27/1.07  --bmc1_ucm                              false
% 2.27/1.07  --bmc1_add_unsat_core                   none
% 2.27/1.07  --bmc1_unsat_core_children              false
% 2.27/1.07  --bmc1_unsat_core_extrapolate_axioms    false
% 2.27/1.07  --bmc1_out_stat                         full
% 2.27/1.07  --bmc1_ground_init                      false
% 2.27/1.07  --bmc1_pre_inst_next_state              false
% 2.27/1.07  --bmc1_pre_inst_state                   false
% 2.27/1.07  --bmc1_pre_inst_reach_state             false
% 2.27/1.07  --bmc1_out_unsat_core                   false
% 2.27/1.07  --bmc1_aig_witness_out                  false
% 2.27/1.07  --bmc1_verbose                          false
% 2.27/1.07  --bmc1_dump_clauses_tptp                false
% 2.27/1.07  --bmc1_dump_unsat_core_tptp             false
% 2.27/1.07  --bmc1_dump_file                        -
% 2.27/1.07  --bmc1_ucm_expand_uc_limit              128
% 2.27/1.07  --bmc1_ucm_n_expand_iterations          6
% 2.27/1.07  --bmc1_ucm_extend_mode                  1
% 2.27/1.07  --bmc1_ucm_init_mode                    2
% 2.27/1.07  --bmc1_ucm_cone_mode                    none
% 2.27/1.07  --bmc1_ucm_reduced_relation_type        0
% 2.27/1.07  --bmc1_ucm_relax_model                  4
% 2.27/1.07  --bmc1_ucm_full_tr_after_sat            true
% 2.27/1.07  --bmc1_ucm_expand_neg_assumptions       false
% 2.27/1.07  --bmc1_ucm_layered_model                none
% 2.27/1.07  --bmc1_ucm_max_lemma_size               10
% 2.27/1.07  
% 2.27/1.07  ------ AIG Options
% 2.27/1.07  
% 2.27/1.07  --aig_mode                              false
% 2.27/1.07  
% 2.27/1.07  ------ Instantiation Options
% 2.27/1.07  
% 2.27/1.07  --instantiation_flag                    true
% 2.27/1.07  --inst_sos_flag                         false
% 2.27/1.07  --inst_sos_phase                        true
% 2.27/1.07  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.27/1.07  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.27/1.07  --inst_lit_sel_side                     num_symb
% 2.27/1.07  --inst_solver_per_active                1400
% 2.27/1.07  --inst_solver_calls_frac                1.
% 2.27/1.07  --inst_passive_queue_type               priority_queues
% 2.27/1.07  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.27/1.07  --inst_passive_queues_freq              [25;2]
% 2.27/1.07  --inst_dismatching                      true
% 2.27/1.07  --inst_eager_unprocessed_to_passive     true
% 2.27/1.07  --inst_prop_sim_given                   true
% 2.27/1.07  --inst_prop_sim_new                     false
% 2.27/1.07  --inst_subs_new                         false
% 2.27/1.07  --inst_eq_res_simp                      false
% 2.27/1.07  --inst_subs_given                       false
% 2.27/1.07  --inst_orphan_elimination               true
% 2.27/1.07  --inst_learning_loop_flag               true
% 2.27/1.07  --inst_learning_start                   3000
% 2.27/1.07  --inst_learning_factor                  2
% 2.27/1.07  --inst_start_prop_sim_after_learn       3
% 2.27/1.07  --inst_sel_renew                        solver
% 2.27/1.07  --inst_lit_activity_flag                true
% 2.27/1.07  --inst_restr_to_given                   false
% 2.27/1.07  --inst_activity_threshold               500
% 2.27/1.07  --inst_out_proof                        true
% 2.27/1.07  
% 2.27/1.07  ------ Resolution Options
% 2.27/1.07  
% 2.27/1.07  --resolution_flag                       true
% 2.27/1.07  --res_lit_sel                           adaptive
% 2.27/1.07  --res_lit_sel_side                      none
% 2.27/1.07  --res_ordering                          kbo
% 2.27/1.07  --res_to_prop_solver                    active
% 2.27/1.07  --res_prop_simpl_new                    false
% 2.27/1.07  --res_prop_simpl_given                  true
% 2.27/1.07  --res_passive_queue_type                priority_queues
% 2.27/1.07  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.27/1.07  --res_passive_queues_freq               [15;5]
% 2.27/1.07  --res_forward_subs                      full
% 2.27/1.07  --res_backward_subs                     full
% 2.27/1.07  --res_forward_subs_resolution           true
% 2.27/1.07  --res_backward_subs_resolution          true
% 2.27/1.07  --res_orphan_elimination                true
% 2.27/1.07  --res_time_limit                        2.
% 2.27/1.07  --res_out_proof                         true
% 2.27/1.07  
% 2.27/1.07  ------ Superposition Options
% 2.27/1.07  
% 2.27/1.07  --superposition_flag                    true
% 2.27/1.07  --sup_passive_queue_type                priority_queues
% 2.27/1.07  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.27/1.07  --sup_passive_queues_freq               [8;1;4]
% 2.27/1.07  --demod_completeness_check              fast
% 2.27/1.07  --demod_use_ground                      true
% 2.27/1.07  --sup_to_prop_solver                    passive
% 2.27/1.07  --sup_prop_simpl_new                    true
% 2.27/1.07  --sup_prop_simpl_given                  true
% 2.27/1.07  --sup_fun_splitting                     false
% 2.27/1.07  --sup_smt_interval                      50000
% 2.27/1.07  
% 2.27/1.07  ------ Superposition Simplification Setup
% 2.27/1.07  
% 2.27/1.07  --sup_indices_passive                   []
% 2.27/1.07  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.27/1.07  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.27/1.07  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.27/1.07  --sup_full_triv                         [TrivRules;PropSubs]
% 2.27/1.07  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.27/1.07  --sup_full_bw                           [BwDemod]
% 2.27/1.07  --sup_immed_triv                        [TrivRules]
% 2.27/1.07  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.27/1.07  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.27/1.07  --sup_immed_bw_main                     []
% 2.27/1.07  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.27/1.07  --sup_input_triv                        [Unflattening;TrivRules]
% 2.27/1.07  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.27/1.07  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.27/1.07  
% 2.27/1.07  ------ Combination Options
% 2.27/1.07  
% 2.27/1.07  --comb_res_mult                         3
% 2.27/1.07  --comb_sup_mult                         2
% 2.27/1.07  --comb_inst_mult                        10
% 2.27/1.07  
% 2.27/1.07  ------ Debug Options
% 2.27/1.07  
% 2.27/1.07  --dbg_backtrace                         false
% 2.27/1.07  --dbg_dump_prop_clauses                 false
% 2.27/1.07  --dbg_dump_prop_clauses_file            -
% 2.27/1.07  --dbg_out_stat                          false
% 2.27/1.07  ------ Parsing...
% 2.27/1.07  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.27/1.07  
% 2.27/1.07  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.27/1.07  
% 2.27/1.07  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.27/1.07  
% 2.27/1.07  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.27/1.07  ------ Proving...
% 2.27/1.07  ------ Problem Properties 
% 2.27/1.07  
% 2.27/1.07  
% 2.27/1.07  clauses                                 25
% 2.27/1.07  conjectures                             5
% 2.27/1.07  EPR                                     4
% 2.27/1.07  Horn                                    13
% 2.27/1.07  unary                                   3
% 2.27/1.07  binary                                  3
% 2.27/1.07  lits                                    79
% 2.27/1.07  lits eq                                 5
% 2.27/1.07  fd_pure                                 0
% 2.27/1.07  fd_pseudo                               0
% 2.27/1.07  fd_cond                                 0
% 2.27/1.07  fd_pseudo_cond                          1
% 2.27/1.07  AC symbols                              0
% 2.27/1.07  
% 2.27/1.07  ------ Schedule dynamic 5 is on 
% 2.27/1.07  
% 2.27/1.07  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.27/1.07  
% 2.27/1.07  
% 2.27/1.07  ------ 
% 2.27/1.07  Current options:
% 2.27/1.07  ------ 
% 2.27/1.07  
% 2.27/1.07  ------ Input Options
% 2.27/1.07  
% 2.27/1.07  --out_options                           all
% 2.27/1.07  --tptp_safe_out                         true
% 2.27/1.07  --problem_path                          ""
% 2.27/1.07  --include_path                          ""
% 2.27/1.07  --clausifier                            res/vclausify_rel
% 2.27/1.07  --clausifier_options                    --mode clausify
% 2.27/1.07  --stdin                                 false
% 2.27/1.07  --stats_out                             all
% 2.27/1.08  
% 2.27/1.08  ------ General Options
% 2.27/1.08  
% 2.27/1.08  --fof                                   false
% 2.27/1.08  --time_out_real                         305.
% 2.27/1.08  --time_out_virtual                      -1.
% 2.27/1.08  --symbol_type_check                     false
% 2.27/1.08  --clausify_out                          false
% 2.27/1.08  --sig_cnt_out                           false
% 2.27/1.08  --trig_cnt_out                          false
% 2.27/1.08  --trig_cnt_out_tolerance                1.
% 2.27/1.08  --trig_cnt_out_sk_spl                   false
% 2.27/1.08  --abstr_cl_out                          false
% 2.27/1.08  
% 2.27/1.08  ------ Global Options
% 2.27/1.08  
% 2.27/1.08  --schedule                              default
% 2.27/1.08  --add_important_lit                     false
% 2.27/1.08  --prop_solver_per_cl                    1000
% 2.27/1.08  --min_unsat_core                        false
% 2.27/1.08  --soft_assumptions                      false
% 2.27/1.08  --soft_lemma_size                       3
% 2.27/1.08  --prop_impl_unit_size                   0
% 2.27/1.08  --prop_impl_unit                        []
% 2.27/1.08  --share_sel_clauses                     true
% 2.27/1.08  --reset_solvers                         false
% 2.27/1.08  --bc_imp_inh                            [conj_cone]
% 2.27/1.08  --conj_cone_tolerance                   3.
% 2.27/1.08  --extra_neg_conj                        none
% 2.27/1.08  --large_theory_mode                     true
% 2.27/1.08  --prolific_symb_bound                   200
% 2.27/1.08  --lt_threshold                          2000
% 2.27/1.08  --clause_weak_htbl                      true
% 2.27/1.08  --gc_record_bc_elim                     false
% 2.27/1.08  
% 2.27/1.08  ------ Preprocessing Options
% 2.27/1.08  
% 2.27/1.08  --preprocessing_flag                    true
% 2.27/1.08  --time_out_prep_mult                    0.1
% 2.27/1.08  --splitting_mode                        input
% 2.27/1.08  --splitting_grd                         true
% 2.27/1.08  --splitting_cvd                         false
% 2.27/1.08  --splitting_cvd_svl                     false
% 2.27/1.08  --splitting_nvd                         32
% 2.27/1.08  --sub_typing                            true
% 2.27/1.08  --prep_gs_sim                           true
% 2.27/1.08  --prep_unflatten                        true
% 2.27/1.08  --prep_res_sim                          true
% 2.27/1.08  --prep_upred                            true
% 2.27/1.08  --prep_sem_filter                       exhaustive
% 2.27/1.08  --prep_sem_filter_out                   false
% 2.27/1.08  --pred_elim                             true
% 2.27/1.08  --res_sim_input                         true
% 2.27/1.08  --eq_ax_congr_red                       true
% 2.27/1.08  --pure_diseq_elim                       true
% 2.27/1.08  --brand_transform                       false
% 2.27/1.08  --non_eq_to_eq                          false
% 2.27/1.08  --prep_def_merge                        true
% 2.27/1.08  --prep_def_merge_prop_impl              false
% 2.27/1.08  --prep_def_merge_mbd                    true
% 2.27/1.08  --prep_def_merge_tr_red                 false
% 2.27/1.08  --prep_def_merge_tr_cl                  false
% 2.27/1.08  --smt_preprocessing                     true
% 2.27/1.08  --smt_ac_axioms                         fast
% 2.27/1.08  --preprocessed_out                      false
% 2.27/1.08  --preprocessed_stats                    false
% 2.27/1.08  
% 2.27/1.08  ------ Abstraction refinement Options
% 2.27/1.08  
% 2.27/1.08  --abstr_ref                             []
% 2.27/1.08  --abstr_ref_prep                        false
% 2.27/1.08  --abstr_ref_until_sat                   false
% 2.27/1.08  --abstr_ref_sig_restrict                funpre
% 2.27/1.08  --abstr_ref_af_restrict_to_split_sk     false
% 2.27/1.08  --abstr_ref_under                       []
% 2.27/1.08  
% 2.27/1.08  ------ SAT Options
% 2.27/1.08  
% 2.27/1.08  --sat_mode                              false
% 2.27/1.08  --sat_fm_restart_options                ""
% 2.27/1.08  --sat_gr_def                            false
% 2.27/1.08  --sat_epr_types                         true
% 2.27/1.08  --sat_non_cyclic_types                  false
% 2.27/1.08  --sat_finite_models                     false
% 2.27/1.08  --sat_fm_lemmas                         false
% 2.27/1.08  --sat_fm_prep                           false
% 2.27/1.08  --sat_fm_uc_incr                        true
% 2.27/1.08  --sat_out_model                         small
% 2.27/1.08  --sat_out_clauses                       false
% 2.27/1.08  
% 2.27/1.08  ------ QBF Options
% 2.27/1.08  
% 2.27/1.08  --qbf_mode                              false
% 2.27/1.08  --qbf_elim_univ                         false
% 2.27/1.08  --qbf_dom_inst                          none
% 2.27/1.08  --qbf_dom_pre_inst                      false
% 2.27/1.08  --qbf_sk_in                             false
% 2.27/1.08  --qbf_pred_elim                         true
% 2.27/1.08  --qbf_split                             512
% 2.27/1.08  
% 2.27/1.08  ------ BMC1 Options
% 2.27/1.08  
% 2.27/1.08  --bmc1_incremental                      false
% 2.27/1.08  --bmc1_axioms                           reachable_all
% 2.27/1.08  --bmc1_min_bound                        0
% 2.27/1.08  --bmc1_max_bound                        -1
% 2.27/1.08  --bmc1_max_bound_default                -1
% 2.27/1.08  --bmc1_symbol_reachability              true
% 2.27/1.08  --bmc1_property_lemmas                  false
% 2.27/1.08  --bmc1_k_induction                      false
% 2.27/1.08  --bmc1_non_equiv_states                 false
% 2.27/1.08  --bmc1_deadlock                         false
% 2.27/1.08  --bmc1_ucm                              false
% 2.27/1.08  --bmc1_add_unsat_core                   none
% 2.27/1.08  --bmc1_unsat_core_children              false
% 2.27/1.08  --bmc1_unsat_core_extrapolate_axioms    false
% 2.27/1.08  --bmc1_out_stat                         full
% 2.27/1.08  --bmc1_ground_init                      false
% 2.27/1.08  --bmc1_pre_inst_next_state              false
% 2.27/1.08  --bmc1_pre_inst_state                   false
% 2.27/1.08  --bmc1_pre_inst_reach_state             false
% 2.27/1.08  --bmc1_out_unsat_core                   false
% 2.27/1.08  --bmc1_aig_witness_out                  false
% 2.27/1.08  --bmc1_verbose                          false
% 2.27/1.08  --bmc1_dump_clauses_tptp                false
% 2.27/1.08  --bmc1_dump_unsat_core_tptp             false
% 2.27/1.08  --bmc1_dump_file                        -
% 2.27/1.08  --bmc1_ucm_expand_uc_limit              128
% 2.27/1.08  --bmc1_ucm_n_expand_iterations          6
% 2.27/1.08  --bmc1_ucm_extend_mode                  1
% 2.27/1.08  --bmc1_ucm_init_mode                    2
% 2.27/1.08  --bmc1_ucm_cone_mode                    none
% 2.27/1.08  --bmc1_ucm_reduced_relation_type        0
% 2.27/1.08  --bmc1_ucm_relax_model                  4
% 2.27/1.08  --bmc1_ucm_full_tr_after_sat            true
% 2.27/1.08  --bmc1_ucm_expand_neg_assumptions       false
% 2.27/1.08  --bmc1_ucm_layered_model                none
% 2.27/1.08  --bmc1_ucm_max_lemma_size               10
% 2.27/1.08  
% 2.27/1.08  ------ AIG Options
% 2.27/1.08  
% 2.27/1.08  --aig_mode                              false
% 2.27/1.08  
% 2.27/1.08  ------ Instantiation Options
% 2.27/1.08  
% 2.27/1.08  --instantiation_flag                    true
% 2.27/1.08  --inst_sos_flag                         false
% 2.27/1.08  --inst_sos_phase                        true
% 2.27/1.08  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.27/1.08  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.27/1.08  --inst_lit_sel_side                     none
% 2.27/1.08  --inst_solver_per_active                1400
% 2.27/1.08  --inst_solver_calls_frac                1.
% 2.27/1.08  --inst_passive_queue_type               priority_queues
% 2.27/1.08  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.27/1.08  --inst_passive_queues_freq              [25;2]
% 2.27/1.08  --inst_dismatching                      true
% 2.27/1.08  --inst_eager_unprocessed_to_passive     true
% 2.27/1.08  --inst_prop_sim_given                   true
% 2.27/1.08  --inst_prop_sim_new                     false
% 2.27/1.08  --inst_subs_new                         false
% 2.27/1.08  --inst_eq_res_simp                      false
% 2.27/1.08  --inst_subs_given                       false
% 2.27/1.08  --inst_orphan_elimination               true
% 2.27/1.08  --inst_learning_loop_flag               true
% 2.27/1.08  --inst_learning_start                   3000
% 2.27/1.08  --inst_learning_factor                  2
% 2.27/1.08  --inst_start_prop_sim_after_learn       3
% 2.27/1.08  --inst_sel_renew                        solver
% 2.27/1.08  --inst_lit_activity_flag                true
% 2.27/1.08  --inst_restr_to_given                   false
% 2.27/1.08  --inst_activity_threshold               500
% 2.27/1.08  --inst_out_proof                        true
% 2.27/1.08  
% 2.27/1.08  ------ Resolution Options
% 2.27/1.08  
% 2.27/1.08  --resolution_flag                       false
% 2.27/1.08  --res_lit_sel                           adaptive
% 2.27/1.08  --res_lit_sel_side                      none
% 2.27/1.08  --res_ordering                          kbo
% 2.27/1.08  --res_to_prop_solver                    active
% 2.27/1.08  --res_prop_simpl_new                    false
% 2.27/1.08  --res_prop_simpl_given                  true
% 2.27/1.08  --res_passive_queue_type                priority_queues
% 2.27/1.08  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.27/1.08  --res_passive_queues_freq               [15;5]
% 2.27/1.08  --res_forward_subs                      full
% 2.27/1.08  --res_backward_subs                     full
% 2.27/1.08  --res_forward_subs_resolution           true
% 2.27/1.08  --res_backward_subs_resolution          true
% 2.27/1.08  --res_orphan_elimination                true
% 2.27/1.08  --res_time_limit                        2.
% 2.27/1.08  --res_out_proof                         true
% 2.27/1.08  
% 2.27/1.08  ------ Superposition Options
% 2.27/1.08  
% 2.27/1.08  --superposition_flag                    true
% 2.27/1.08  --sup_passive_queue_type                priority_queues
% 2.27/1.08  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.27/1.08  --sup_passive_queues_freq               [8;1;4]
% 2.27/1.08  --demod_completeness_check              fast
% 2.27/1.08  --demod_use_ground                      true
% 2.27/1.08  --sup_to_prop_solver                    passive
% 2.27/1.08  --sup_prop_simpl_new                    true
% 2.27/1.08  --sup_prop_simpl_given                  true
% 2.27/1.08  --sup_fun_splitting                     false
% 2.27/1.08  --sup_smt_interval                      50000
% 2.27/1.08  
% 2.27/1.08  ------ Superposition Simplification Setup
% 2.27/1.08  
% 2.27/1.08  --sup_indices_passive                   []
% 2.27/1.08  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.27/1.08  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.27/1.08  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.27/1.08  --sup_full_triv                         [TrivRules;PropSubs]
% 2.27/1.08  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.27/1.08  --sup_full_bw                           [BwDemod]
% 2.27/1.08  --sup_immed_triv                        [TrivRules]
% 2.27/1.08  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.27/1.08  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.27/1.08  --sup_immed_bw_main                     []
% 2.27/1.08  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.27/1.08  --sup_input_triv                        [Unflattening;TrivRules]
% 2.27/1.08  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.27/1.08  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.27/1.08  
% 2.27/1.08  ------ Combination Options
% 2.27/1.08  
% 2.27/1.08  --comb_res_mult                         3
% 2.27/1.08  --comb_sup_mult                         2
% 2.27/1.08  --comb_inst_mult                        10
% 2.27/1.08  
% 2.27/1.08  ------ Debug Options
% 2.27/1.08  
% 2.27/1.08  --dbg_backtrace                         false
% 2.27/1.08  --dbg_dump_prop_clauses                 false
% 2.27/1.08  --dbg_dump_prop_clauses_file            -
% 2.27/1.08  --dbg_out_stat                          false
% 2.27/1.08  
% 2.27/1.08  
% 2.27/1.08  
% 2.27/1.08  
% 2.27/1.08  ------ Proving...
% 2.27/1.08  
% 2.27/1.08  
% 2.27/1.08  % SZS status Theorem for theBenchmark.p
% 2.27/1.08  
% 2.27/1.08  % SZS output start CNFRefutation for theBenchmark.p
% 2.27/1.08  
% 2.27/1.08  fof(f14,axiom,(
% 2.27/1.08    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 2.27/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/1.08  
% 2.27/1.08  fof(f19,plain,(
% 2.27/1.08    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 2.27/1.08    inference(pure_predicate_removal,[],[f14])).
% 2.27/1.08  
% 2.27/1.08  fof(f40,plain,(
% 2.27/1.08    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.27/1.08    inference(ennf_transformation,[],[f19])).
% 2.27/1.08  
% 2.27/1.08  fof(f41,plain,(
% 2.27/1.08    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.27/1.08    inference(flattening,[],[f40])).
% 2.27/1.08  
% 2.27/1.08  fof(f83,plain,(
% 2.27/1.08    ( ! [X0,X1] : (m1_pre_topc(k1_tex_2(X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.27/1.08    inference(cnf_transformation,[],[f41])).
% 2.27/1.08  
% 2.27/1.08  fof(f12,axiom,(
% 2.27/1.08    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v1_subset_1(X2,u1_struct_0(X0)))))))),
% 2.27/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/1.08  
% 2.27/1.08  fof(f37,plain,(
% 2.27/1.08    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : ((v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.27/1.08    inference(ennf_transformation,[],[f12])).
% 2.27/1.08  
% 2.27/1.08  fof(f38,plain,(
% 2.27/1.08    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.27/1.08    inference(flattening,[],[f37])).
% 2.27/1.08  
% 2.27/1.08  fof(f52,plain,(
% 2.27/1.08    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.27/1.08    inference(nnf_transformation,[],[f38])).
% 2.27/1.08  
% 2.27/1.08  fof(f53,plain,(
% 2.27/1.08    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.27/1.08    inference(rectify,[],[f52])).
% 2.27/1.08  
% 2.27/1.08  fof(f54,plain,(
% 2.27/1.08    ! [X1,X0] : (? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_subset_1(sK1(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK1(X0,X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.27/1.08    introduced(choice_axiom,[])).
% 2.27/1.08  
% 2.27/1.08  fof(f55,plain,(
% 2.27/1.08    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | (~v1_subset_1(sK1(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK1(X0,X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.27/1.08    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f53,f54])).
% 2.27/1.08  
% 2.27/1.08  fof(f78,plain,(
% 2.27/1.08    ( ! [X0,X1] : (v1_tex_2(X1,X0) | u1_struct_0(X1) = sK1(X0,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.27/1.08    inference(cnf_transformation,[],[f55])).
% 2.27/1.08  
% 2.27/1.08  fof(f17,conjecture,(
% 2.27/1.08    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 2.27/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/1.08  
% 2.27/1.08  fof(f18,negated_conjecture,(
% 2.27/1.08    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 2.27/1.08    inference(negated_conjecture,[],[f17])).
% 2.27/1.08  
% 2.27/1.08  fof(f46,plain,(
% 2.27/1.08    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.27/1.08    inference(ennf_transformation,[],[f18])).
% 2.27/1.08  
% 2.27/1.08  fof(f47,plain,(
% 2.27/1.08    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.27/1.08    inference(flattening,[],[f46])).
% 2.27/1.08  
% 2.27/1.08  fof(f57,plain,(
% 2.27/1.08    ? [X0] : (? [X1] : (((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.27/1.08    inference(nnf_transformation,[],[f47])).
% 2.27/1.08  
% 2.27/1.08  fof(f58,plain,(
% 2.27/1.08    ? [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.27/1.08    inference(flattening,[],[f57])).
% 2.27/1.08  
% 2.27/1.08  fof(f60,plain,(
% 2.27/1.08    ( ! [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) => ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),sK3),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,sK3),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),sK3),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,sK3),X0)) & m1_subset_1(sK3,u1_struct_0(X0)))) )),
% 2.27/1.08    introduced(choice_axiom,[])).
% 2.27/1.08  
% 2.27/1.08  fof(f59,plain,(
% 2.27/1.08    ? [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(sK2),X1),u1_struct_0(sK2)) | ~v1_tex_2(k1_tex_2(sK2,X1),sK2)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK2),X1),u1_struct_0(sK2)) | v1_tex_2(k1_tex_2(sK2,X1),sK2)) & m1_subset_1(X1,u1_struct_0(sK2))) & l1_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 2.27/1.08    introduced(choice_axiom,[])).
% 2.27/1.08  
% 2.27/1.08  fof(f61,plain,(
% 2.27/1.08    ((~v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) | ~v1_tex_2(k1_tex_2(sK2,sK3),sK2)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) | v1_tex_2(k1_tex_2(sK2,sK3),sK2)) & m1_subset_1(sK3,u1_struct_0(sK2))) & l1_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 2.27/1.08    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f58,f60,f59])).
% 2.27/1.08  
% 2.27/1.08  fof(f89,plain,(
% 2.27/1.08    m1_subset_1(sK3,u1_struct_0(sK2))),
% 2.27/1.08    inference(cnf_transformation,[],[f61])).
% 2.27/1.08  
% 2.27/1.08  fof(f9,axiom,(
% 2.27/1.08    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 2.27/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/1.08  
% 2.27/1.08  fof(f32,plain,(
% 2.27/1.08    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.27/1.08    inference(ennf_transformation,[],[f9])).
% 2.27/1.08  
% 2.27/1.08  fof(f33,plain,(
% 2.27/1.08    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.27/1.08    inference(flattening,[],[f32])).
% 2.27/1.08  
% 2.27/1.08  fof(f70,plain,(
% 2.27/1.08    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.27/1.08    inference(cnf_transformation,[],[f33])).
% 2.27/1.08  
% 2.27/1.08  fof(f1,axiom,(
% 2.27/1.08    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.27/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/1.08  
% 2.27/1.08  fof(f62,plain,(
% 2.27/1.08    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.27/1.08    inference(cnf_transformation,[],[f1])).
% 2.27/1.08  
% 2.27/1.08  fof(f93,plain,(
% 2.27/1.08    ( ! [X0,X1] : (k2_tarski(X1,X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.27/1.08    inference(definition_unfolding,[],[f70,f62])).
% 2.27/1.08  
% 2.27/1.08  fof(f87,plain,(
% 2.27/1.08    ~v2_struct_0(sK2)),
% 2.27/1.08    inference(cnf_transformation,[],[f61])).
% 2.27/1.08  
% 2.27/1.08  fof(f88,plain,(
% 2.27/1.08    l1_pre_topc(sK2)),
% 2.27/1.08    inference(cnf_transformation,[],[f61])).
% 2.27/1.08  
% 2.27/1.08  fof(f6,axiom,(
% 2.27/1.08    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.27/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/1.08  
% 2.27/1.08  fof(f26,plain,(
% 2.27/1.08    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.27/1.08    inference(ennf_transformation,[],[f6])).
% 2.27/1.08  
% 2.27/1.08  fof(f27,plain,(
% 2.27/1.08    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.27/1.08    inference(flattening,[],[f26])).
% 2.27/1.08  
% 2.27/1.08  fof(f67,plain,(
% 2.27/1.08    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.27/1.08    inference(cnf_transformation,[],[f27])).
% 2.27/1.08  
% 2.27/1.08  fof(f4,axiom,(
% 2.27/1.08    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.27/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/1.08  
% 2.27/1.08  fof(f24,plain,(
% 2.27/1.08    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.27/1.08    inference(ennf_transformation,[],[f4])).
% 2.27/1.08  
% 2.27/1.08  fof(f65,plain,(
% 2.27/1.08    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.27/1.08    inference(cnf_transformation,[],[f24])).
% 2.27/1.08  
% 2.27/1.08  fof(f91,plain,(
% 2.27/1.08    ~v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) | ~v1_tex_2(k1_tex_2(sK2,sK3),sK2)),
% 2.27/1.08    inference(cnf_transformation,[],[f61])).
% 2.27/1.08  
% 2.27/1.08  fof(f7,axiom,(
% 2.27/1.08    ! [X0] : ((l1_struct_0(X0) & ~v7_struct_0(X0)) => ~v1_zfmisc_1(u1_struct_0(X0)))),
% 2.27/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/1.08  
% 2.27/1.08  fof(f28,plain,(
% 2.27/1.08    ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | v7_struct_0(X0)))),
% 2.27/1.08    inference(ennf_transformation,[],[f7])).
% 2.27/1.08  
% 2.27/1.08  fof(f29,plain,(
% 2.27/1.08    ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | v7_struct_0(X0))),
% 2.27/1.08    inference(flattening,[],[f28])).
% 2.27/1.08  
% 2.27/1.08  fof(f68,plain,(
% 2.27/1.08    ( ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | v7_struct_0(X0)) )),
% 2.27/1.08    inference(cnf_transformation,[],[f29])).
% 2.27/1.08  
% 2.27/1.08  fof(f10,axiom,(
% 2.27/1.08    ! [X0] : ((l1_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (~v2_struct_0(X1) => (~v1_tex_2(X1,X0) & ~v2_struct_0(X1)))))),
% 2.27/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/1.08  
% 2.27/1.08  fof(f34,plain,(
% 2.27/1.08    ! [X0] : (! [X1] : (((~v1_tex_2(X1,X0) & ~v2_struct_0(X1)) | v2_struct_0(X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0)))),
% 2.27/1.08    inference(ennf_transformation,[],[f10])).
% 2.27/1.08  
% 2.27/1.08  fof(f35,plain,(
% 2.27/1.08    ! [X0] : (! [X1] : ((~v1_tex_2(X1,X0) & ~v2_struct_0(X1)) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0))),
% 2.27/1.08    inference(flattening,[],[f34])).
% 2.27/1.08  
% 2.27/1.08  fof(f72,plain,(
% 2.27/1.08    ( ! [X0,X1] : (~v1_tex_2(X1,X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0)) )),
% 2.27/1.08    inference(cnf_transformation,[],[f35])).
% 2.27/1.08  
% 2.27/1.08  fof(f90,plain,(
% 2.27/1.08    v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) | v1_tex_2(k1_tex_2(sK2,sK3),sK2)),
% 2.27/1.08    inference(cnf_transformation,[],[f61])).
% 2.27/1.08  
% 2.27/1.08  fof(f15,axiom,(
% 2.27/1.08    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 2.27/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/1.08  
% 2.27/1.08  fof(f20,plain,(
% 2.27/1.08    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 2.27/1.08    inference(pure_predicate_removal,[],[f15])).
% 2.27/1.08  
% 2.27/1.08  fof(f42,plain,(
% 2.27/1.08    ! [X0,X1] : ((v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.27/1.08    inference(ennf_transformation,[],[f20])).
% 2.27/1.08  
% 2.27/1.08  fof(f43,plain,(
% 2.27/1.08    ! [X0,X1] : ((v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.27/1.08    inference(flattening,[],[f42])).
% 2.27/1.08  
% 2.27/1.08  fof(f84,plain,(
% 2.27/1.08    ( ! [X0,X1] : (~v2_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.27/1.08    inference(cnf_transformation,[],[f43])).
% 2.27/1.08  
% 2.27/1.08  fof(f3,axiom,(
% 2.27/1.08    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.27/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/1.08  
% 2.27/1.08  fof(f22,plain,(
% 2.27/1.08    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.27/1.08    inference(ennf_transformation,[],[f3])).
% 2.27/1.08  
% 2.27/1.08  fof(f23,plain,(
% 2.27/1.08    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.27/1.08    inference(flattening,[],[f22])).
% 2.27/1.08  
% 2.27/1.08  fof(f64,plain,(
% 2.27/1.08    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.27/1.08    inference(cnf_transformation,[],[f23])).
% 2.27/1.08  
% 2.27/1.08  fof(f2,axiom,(
% 2.27/1.08    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 2.27/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/1.08  
% 2.27/1.08  fof(f21,plain,(
% 2.27/1.08    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 2.27/1.08    inference(ennf_transformation,[],[f2])).
% 2.27/1.08  
% 2.27/1.08  fof(f63,plain,(
% 2.27/1.08    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 2.27/1.08    inference(cnf_transformation,[],[f21])).
% 2.27/1.08  
% 2.27/1.08  fof(f92,plain,(
% 2.27/1.08    ( ! [X0,X1] : (m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 2.27/1.08    inference(definition_unfolding,[],[f63,f62])).
% 2.27/1.08  
% 2.27/1.08  fof(f13,axiom,(
% 2.27/1.08    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 2.27/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/1.08  
% 2.27/1.08  fof(f39,plain,(
% 2.27/1.08    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.27/1.08    inference(ennf_transformation,[],[f13])).
% 2.27/1.08  
% 2.27/1.08  fof(f56,plain,(
% 2.27/1.08    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.27/1.08    inference(nnf_transformation,[],[f39])).
% 2.27/1.08  
% 2.27/1.08  fof(f81,plain,(
% 2.27/1.08    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.27/1.08    inference(cnf_transformation,[],[f56])).
% 2.27/1.08  
% 2.27/1.08  fof(f11,axiom,(
% 2.27/1.08    ! [X0] : (~v1_xboole_0(X0) => (v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))))),
% 2.27/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/1.08  
% 2.27/1.08  fof(f36,plain,(
% 2.27/1.08    ! [X0] : ((v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))) | v1_xboole_0(X0))),
% 2.27/1.08    inference(ennf_transformation,[],[f11])).
% 2.27/1.08  
% 2.27/1.08  fof(f48,plain,(
% 2.27/1.08    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 2.27/1.08    inference(nnf_transformation,[],[f36])).
% 2.27/1.08  
% 2.27/1.08  fof(f49,plain,(
% 2.27/1.08    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 2.27/1.08    inference(rectify,[],[f48])).
% 2.27/1.08  
% 2.27/1.08  fof(f50,plain,(
% 2.27/1.08    ! [X0] : (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) => (k6_domain_1(X0,sK0(X0)) = X0 & m1_subset_1(sK0(X0),X0)))),
% 2.27/1.08    introduced(choice_axiom,[])).
% 2.27/1.08  
% 2.27/1.08  fof(f51,plain,(
% 2.27/1.08    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & ((k6_domain_1(X0,sK0(X0)) = X0 & m1_subset_1(sK0(X0),X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 2.27/1.08    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f49,f50])).
% 2.27/1.08  
% 2.27/1.08  fof(f75,plain,(
% 2.27/1.08    ( ! [X0,X1] : (v1_zfmisc_1(X0) | k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.27/1.08    inference(cnf_transformation,[],[f51])).
% 2.27/1.08  
% 2.27/1.08  fof(f77,plain,(
% 2.27/1.08    ( ! [X0,X1] : (v1_tex_2(X1,X0) | m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.27/1.08    inference(cnf_transformation,[],[f55])).
% 2.27/1.08  
% 2.27/1.08  fof(f79,plain,(
% 2.27/1.08    ( ! [X0,X1] : (v1_tex_2(X1,X0) | ~v1_subset_1(sK1(X0,X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.27/1.08    inference(cnf_transformation,[],[f55])).
% 2.27/1.08  
% 2.27/1.08  fof(f85,plain,(
% 2.27/1.08    ( ! [X0,X1] : (v7_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.27/1.08    inference(cnf_transformation,[],[f43])).
% 2.27/1.08  
% 2.27/1.08  fof(f8,axiom,(
% 2.27/1.08    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 2.27/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/1.08  
% 2.27/1.08  fof(f30,plain,(
% 2.27/1.08    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 2.27/1.08    inference(ennf_transformation,[],[f8])).
% 2.27/1.08  
% 2.27/1.08  fof(f31,plain,(
% 2.27/1.08    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 2.27/1.08    inference(flattening,[],[f30])).
% 2.27/1.08  
% 2.27/1.08  fof(f69,plain,(
% 2.27/1.08    ( ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0)) )),
% 2.27/1.08    inference(cnf_transformation,[],[f31])).
% 2.27/1.08  
% 2.27/1.08  fof(f74,plain,(
% 2.27/1.08    ( ! [X0] : (k6_domain_1(X0,sK0(X0)) = X0 | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 2.27/1.08    inference(cnf_transformation,[],[f51])).
% 2.27/1.08  
% 2.27/1.08  fof(f5,axiom,(
% 2.27/1.08    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.27/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/1.08  
% 2.27/1.08  fof(f25,plain,(
% 2.27/1.08    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.27/1.08    inference(ennf_transformation,[],[f5])).
% 2.27/1.08  
% 2.27/1.08  fof(f66,plain,(
% 2.27/1.08    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.27/1.08    inference(cnf_transformation,[],[f25])).
% 2.27/1.08  
% 2.27/1.08  fof(f16,axiom,(
% 2.27/1.08    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 2.27/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/1.08  
% 2.27/1.08  fof(f44,plain,(
% 2.27/1.08    ! [X0] : (! [X1] : ((~v1_zfmisc_1(X0) | ~v1_subset_1(k6_domain_1(X0,X1),X0)) | ~m1_subset_1(X1,X0)) | v1_xboole_0(X0))),
% 2.27/1.08    inference(ennf_transformation,[],[f16])).
% 2.27/1.08  
% 2.27/1.08  fof(f45,plain,(
% 2.27/1.08    ! [X0] : (! [X1] : (~v1_zfmisc_1(X0) | ~v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | v1_xboole_0(X0))),
% 2.27/1.08    inference(flattening,[],[f44])).
% 2.27/1.08  
% 2.27/1.08  fof(f86,plain,(
% 2.27/1.08    ( ! [X0,X1] : (~v1_zfmisc_1(X0) | ~v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.27/1.08    inference(cnf_transformation,[],[f45])).
% 2.27/1.08  
% 2.27/1.08  cnf(c_19,plain,
% 2.27/1.08      ( m1_pre_topc(k1_tex_2(X0,X1),X0)
% 2.27/1.08      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.27/1.08      | v2_struct_0(X0)
% 2.27/1.08      | ~ l1_pre_topc(X0) ),
% 2.27/1.08      inference(cnf_transformation,[],[f83]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_2855,plain,
% 2.27/1.08      ( m1_pre_topc(k1_tex_2(X0_48,X0_49),X0_48)
% 2.27/1.08      | ~ m1_subset_1(X0_49,u1_struct_0(X0_48))
% 2.27/1.08      | v2_struct_0(X0_48)
% 2.27/1.08      | ~ l1_pre_topc(X0_48) ),
% 2.27/1.08      inference(subtyping,[status(esa)],[c_19]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_3571,plain,
% 2.27/1.08      ( m1_pre_topc(k1_tex_2(X0_48,X0_49),X0_48) = iProver_top
% 2.27/1.08      | m1_subset_1(X0_49,u1_struct_0(X0_48)) != iProver_top
% 2.27/1.08      | v2_struct_0(X0_48) = iProver_top
% 2.27/1.08      | l1_pre_topc(X0_48) != iProver_top ),
% 2.27/1.08      inference(predicate_to_equality,[status(thm)],[c_2855]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_14,plain,
% 2.27/1.08      ( v1_tex_2(X0,X1)
% 2.27/1.08      | ~ m1_pre_topc(X0,X1)
% 2.27/1.08      | ~ l1_pre_topc(X1)
% 2.27/1.08      | sK1(X1,X0) = u1_struct_0(X0) ),
% 2.27/1.08      inference(cnf_transformation,[],[f78]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_2860,plain,
% 2.27/1.08      ( v1_tex_2(X0_48,X1_48)
% 2.27/1.08      | ~ m1_pre_topc(X0_48,X1_48)
% 2.27/1.08      | ~ l1_pre_topc(X1_48)
% 2.27/1.08      | sK1(X1_48,X0_48) = u1_struct_0(X0_48) ),
% 2.27/1.08      inference(subtyping,[status(esa)],[c_14]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_3566,plain,
% 2.27/1.08      ( sK1(X0_48,X1_48) = u1_struct_0(X1_48)
% 2.27/1.08      | v1_tex_2(X1_48,X0_48) = iProver_top
% 2.27/1.08      | m1_pre_topc(X1_48,X0_48) != iProver_top
% 2.27/1.08      | l1_pre_topc(X0_48) != iProver_top ),
% 2.27/1.08      inference(predicate_to_equality,[status(thm)],[c_2860]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_4486,plain,
% 2.27/1.08      ( sK1(X0_48,k1_tex_2(X0_48,X0_49)) = u1_struct_0(k1_tex_2(X0_48,X0_49))
% 2.27/1.08      | v1_tex_2(k1_tex_2(X0_48,X0_49),X0_48) = iProver_top
% 2.27/1.08      | m1_subset_1(X0_49,u1_struct_0(X0_48)) != iProver_top
% 2.27/1.08      | v2_struct_0(X0_48) = iProver_top
% 2.27/1.08      | l1_pre_topc(X0_48) != iProver_top ),
% 2.27/1.08      inference(superposition,[status(thm)],[c_3571,c_3566]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_26,negated_conjecture,
% 2.27/1.08      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 2.27/1.08      inference(cnf_transformation,[],[f89]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_2849,negated_conjecture,
% 2.27/1.08      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 2.27/1.08      inference(subtyping,[status(esa)],[c_26]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_3577,plain,
% 2.27/1.08      ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
% 2.27/1.08      inference(predicate_to_equality,[status(thm)],[c_2849]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_7,plain,
% 2.27/1.08      ( ~ m1_subset_1(X0,X1)
% 2.27/1.08      | v1_xboole_0(X1)
% 2.27/1.08      | k6_domain_1(X1,X0) = k2_tarski(X0,X0) ),
% 2.27/1.08      inference(cnf_transformation,[],[f93]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_2866,plain,
% 2.27/1.08      ( ~ m1_subset_1(X0_49,X1_49)
% 2.27/1.08      | v1_xboole_0(X1_49)
% 2.27/1.08      | k6_domain_1(X1_49,X0_49) = k2_tarski(X0_49,X0_49) ),
% 2.27/1.08      inference(subtyping,[status(esa)],[c_7]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_3560,plain,
% 2.27/1.08      ( k6_domain_1(X0_49,X1_49) = k2_tarski(X1_49,X1_49)
% 2.27/1.08      | m1_subset_1(X1_49,X0_49) != iProver_top
% 2.27/1.08      | v1_xboole_0(X0_49) = iProver_top ),
% 2.27/1.08      inference(predicate_to_equality,[status(thm)],[c_2866]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_3878,plain,
% 2.27/1.08      ( k6_domain_1(u1_struct_0(sK2),sK3) = k2_tarski(sK3,sK3)
% 2.27/1.08      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 2.27/1.08      inference(superposition,[status(thm)],[c_3577,c_3560]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_28,negated_conjecture,
% 2.27/1.08      ( ~ v2_struct_0(sK2) ),
% 2.27/1.08      inference(cnf_transformation,[],[f87]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_27,negated_conjecture,
% 2.27/1.08      ( l1_pre_topc(sK2) ),
% 2.27/1.08      inference(cnf_transformation,[],[f88]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_4,plain,
% 2.27/1.08      ( v2_struct_0(X0)
% 2.27/1.08      | ~ l1_struct_0(X0)
% 2.27/1.08      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.27/1.08      inference(cnf_transformation,[],[f67]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_88,plain,
% 2.27/1.08      ( v2_struct_0(sK2)
% 2.27/1.08      | ~ l1_struct_0(sK2)
% 2.27/1.08      | ~ v1_xboole_0(u1_struct_0(sK2)) ),
% 2.27/1.08      inference(instantiation,[status(thm)],[c_4]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_2,plain,
% 2.27/1.08      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 2.27/1.08      inference(cnf_transformation,[],[f65]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_92,plain,
% 2.27/1.08      ( ~ l1_pre_topc(sK2) | l1_struct_0(sK2) ),
% 2.27/1.08      inference(instantiation,[status(thm)],[c_2]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_3821,plain,
% 2.27/1.08      ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 2.27/1.08      | v1_xboole_0(u1_struct_0(sK2))
% 2.27/1.08      | k6_domain_1(u1_struct_0(sK2),sK3) = k2_tarski(sK3,sK3) ),
% 2.27/1.08      inference(instantiation,[status(thm)],[c_2866]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_4070,plain,
% 2.27/1.08      ( k6_domain_1(u1_struct_0(sK2),sK3) = k2_tarski(sK3,sK3) ),
% 2.27/1.08      inference(global_propositional_subsumption,
% 2.27/1.08                [status(thm)],
% 2.27/1.08                [c_3878,c_28,c_27,c_26,c_88,c_92,c_3821]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_24,negated_conjecture,
% 2.27/1.08      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 2.27/1.08      | ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2) ),
% 2.27/1.08      inference(cnf_transformation,[],[f91]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_2851,negated_conjecture,
% 2.27/1.08      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 2.27/1.08      | ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2) ),
% 2.27/1.08      inference(subtyping,[status(esa)],[c_24]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_3575,plain,
% 2.27/1.08      ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) != iProver_top
% 2.27/1.08      | v1_tex_2(k1_tex_2(sK2,sK3),sK2) != iProver_top ),
% 2.27/1.08      inference(predicate_to_equality,[status(thm)],[c_2851]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_4074,plain,
% 2.27/1.08      ( v1_subset_1(k2_tarski(sK3,sK3),u1_struct_0(sK2)) != iProver_top
% 2.27/1.08      | v1_tex_2(k1_tex_2(sK2,sK3),sK2) != iProver_top ),
% 2.27/1.08      inference(demodulation,[status(thm)],[c_4070,c_3575]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_29,plain,
% 2.27/1.08      ( v2_struct_0(sK2) != iProver_top ),
% 2.27/1.08      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_30,plain,
% 2.27/1.08      ( l1_pre_topc(sK2) = iProver_top ),
% 2.27/1.08      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_31,plain,
% 2.27/1.08      ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
% 2.27/1.08      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_33,plain,
% 2.27/1.08      ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) != iProver_top
% 2.27/1.08      | v1_tex_2(k1_tex_2(sK2,sK3),sK2) != iProver_top ),
% 2.27/1.08      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_5,plain,
% 2.27/1.08      ( v7_struct_0(X0)
% 2.27/1.08      | ~ v1_zfmisc_1(u1_struct_0(X0))
% 2.27/1.08      | ~ l1_struct_0(X0) ),
% 2.27/1.08      inference(cnf_transformation,[],[f68]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_84,plain,
% 2.27/1.08      ( v7_struct_0(X0) = iProver_top
% 2.27/1.08      | v1_zfmisc_1(u1_struct_0(X0)) != iProver_top
% 2.27/1.08      | l1_struct_0(X0) != iProver_top ),
% 2.27/1.08      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_86,plain,
% 2.27/1.08      ( v7_struct_0(sK2) = iProver_top
% 2.27/1.08      | v1_zfmisc_1(u1_struct_0(sK2)) != iProver_top
% 2.27/1.08      | l1_struct_0(sK2) != iProver_top ),
% 2.27/1.08      inference(instantiation,[status(thm)],[c_84]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_87,plain,
% 2.27/1.08      ( v2_struct_0(X0) = iProver_top
% 2.27/1.08      | l1_struct_0(X0) != iProver_top
% 2.27/1.08      | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
% 2.27/1.08      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_89,plain,
% 2.27/1.08      ( v2_struct_0(sK2) = iProver_top
% 2.27/1.08      | l1_struct_0(sK2) != iProver_top
% 2.27/1.08      | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 2.27/1.08      inference(instantiation,[status(thm)],[c_87]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_91,plain,
% 2.27/1.08      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 2.27/1.08      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_93,plain,
% 2.27/1.08      ( l1_pre_topc(sK2) != iProver_top
% 2.27/1.08      | l1_struct_0(sK2) = iProver_top ),
% 2.27/1.08      inference(instantiation,[status(thm)],[c_91]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_8,plain,
% 2.27/1.08      ( ~ v1_tex_2(X0,X1)
% 2.27/1.08      | ~ m1_pre_topc(X0,X1)
% 2.27/1.08      | ~ v7_struct_0(X1)
% 2.27/1.08      | v2_struct_0(X1)
% 2.27/1.08      | v2_struct_0(X0)
% 2.27/1.08      | ~ l1_pre_topc(X1) ),
% 2.27/1.08      inference(cnf_transformation,[],[f72]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_25,negated_conjecture,
% 2.27/1.08      ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 2.27/1.08      | v1_tex_2(k1_tex_2(sK2,sK3),sK2) ),
% 2.27/1.08      inference(cnf_transformation,[],[f90]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_220,plain,
% 2.27/1.08      ( v1_tex_2(k1_tex_2(sK2,sK3),sK2)
% 2.27/1.08      | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) ),
% 2.27/1.08      inference(prop_impl,[status(thm)],[c_25]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_221,plain,
% 2.27/1.08      ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 2.27/1.08      | v1_tex_2(k1_tex_2(sK2,sK3),sK2) ),
% 2.27/1.08      inference(renaming,[status(thm)],[c_220]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_1499,plain,
% 2.27/1.08      ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 2.27/1.08      | ~ m1_pre_topc(X0,X1)
% 2.27/1.08      | ~ v7_struct_0(X1)
% 2.27/1.08      | v2_struct_0(X0)
% 2.27/1.08      | v2_struct_0(X1)
% 2.27/1.08      | ~ l1_pre_topc(X1)
% 2.27/1.08      | k1_tex_2(sK2,sK3) != X0
% 2.27/1.08      | sK2 != X1 ),
% 2.27/1.08      inference(resolution_lifted,[status(thm)],[c_8,c_221]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_1500,plain,
% 2.27/1.08      ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 2.27/1.08      | ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
% 2.27/1.08      | ~ v7_struct_0(sK2)
% 2.27/1.08      | v2_struct_0(k1_tex_2(sK2,sK3))
% 2.27/1.08      | v2_struct_0(sK2)
% 2.27/1.08      | ~ l1_pre_topc(sK2) ),
% 2.27/1.08      inference(unflattening,[status(thm)],[c_1499]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_1502,plain,
% 2.27/1.08      ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 2.27/1.08      | ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
% 2.27/1.08      | ~ v7_struct_0(sK2)
% 2.27/1.08      | v2_struct_0(k1_tex_2(sK2,sK3)) ),
% 2.27/1.08      inference(global_propositional_subsumption,
% 2.27/1.08                [status(thm)],
% 2.27/1.08                [c_1500,c_28,c_27]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_1504,plain,
% 2.27/1.08      ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) = iProver_top
% 2.27/1.08      | m1_pre_topc(k1_tex_2(sK2,sK3),sK2) != iProver_top
% 2.27/1.08      | v7_struct_0(sK2) != iProver_top
% 2.27/1.08      | v2_struct_0(k1_tex_2(sK2,sK3)) = iProver_top ),
% 2.27/1.08      inference(predicate_to_equality,[status(thm)],[c_1502]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_2925,plain,
% 2.27/1.08      ( m1_pre_topc(k1_tex_2(X0_48,X0_49),X0_48) = iProver_top
% 2.27/1.08      | m1_subset_1(X0_49,u1_struct_0(X0_48)) != iProver_top
% 2.27/1.08      | v2_struct_0(X0_48) = iProver_top
% 2.27/1.08      | l1_pre_topc(X0_48) != iProver_top ),
% 2.27/1.08      inference(predicate_to_equality,[status(thm)],[c_2855]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_2927,plain,
% 2.27/1.08      ( m1_pre_topc(k1_tex_2(sK2,sK3),sK2) = iProver_top
% 2.27/1.08      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 2.27/1.08      | v2_struct_0(sK2) = iProver_top
% 2.27/1.08      | l1_pre_topc(sK2) != iProver_top ),
% 2.27/1.08      inference(instantiation,[status(thm)],[c_2925]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_22,plain,
% 2.27/1.08      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.27/1.08      | v2_struct_0(X1)
% 2.27/1.08      | ~ v2_struct_0(k1_tex_2(X1,X0))
% 2.27/1.08      | ~ l1_pre_topc(X1) ),
% 2.27/1.08      inference(cnf_transformation,[],[f84]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_2854,plain,
% 2.27/1.08      ( ~ m1_subset_1(X0_49,u1_struct_0(X0_48))
% 2.27/1.08      | v2_struct_0(X0_48)
% 2.27/1.08      | ~ v2_struct_0(k1_tex_2(X0_48,X0_49))
% 2.27/1.08      | ~ l1_pre_topc(X0_48) ),
% 2.27/1.08      inference(subtyping,[status(esa)],[c_22]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_2928,plain,
% 2.27/1.08      ( m1_subset_1(X0_49,u1_struct_0(X0_48)) != iProver_top
% 2.27/1.08      | v2_struct_0(X0_48) = iProver_top
% 2.27/1.08      | v2_struct_0(k1_tex_2(X0_48,X0_49)) != iProver_top
% 2.27/1.08      | l1_pre_topc(X0_48) != iProver_top ),
% 2.27/1.08      inference(predicate_to_equality,[status(thm)],[c_2854]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_2930,plain,
% 2.27/1.08      ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 2.27/1.08      | v2_struct_0(k1_tex_2(sK2,sK3)) != iProver_top
% 2.27/1.08      | v2_struct_0(sK2) = iProver_top
% 2.27/1.08      | l1_pre_topc(sK2) != iProver_top ),
% 2.27/1.08      inference(instantiation,[status(thm)],[c_2928]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_1,plain,
% 2.27/1.08      ( r2_hidden(X0,X1) | ~ m1_subset_1(X0,X1) | v1_xboole_0(X1) ),
% 2.27/1.08      inference(cnf_transformation,[],[f64]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_0,plain,
% 2.27/1.08      ( ~ r2_hidden(X0,X1)
% 2.27/1.08      | m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1)) ),
% 2.27/1.08      inference(cnf_transformation,[],[f92]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_375,plain,
% 2.27/1.08      ( ~ m1_subset_1(X0,X1)
% 2.27/1.08      | m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1))
% 2.27/1.08      | v1_xboole_0(X1) ),
% 2.27/1.08      inference(resolution,[status(thm)],[c_1,c_0]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_2846,plain,
% 2.27/1.08      ( ~ m1_subset_1(X0_49,X1_49)
% 2.27/1.08      | m1_subset_1(k2_tarski(X0_49,X0_49),k1_zfmisc_1(X1_49))
% 2.27/1.08      | v1_xboole_0(X1_49) ),
% 2.27/1.08      inference(subtyping,[status(esa)],[c_375]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_3805,plain,
% 2.27/1.08      ( m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.27/1.08      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 2.27/1.08      | v1_xboole_0(u1_struct_0(sK2)) ),
% 2.27/1.08      inference(instantiation,[status(thm)],[c_2846]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_3806,plain,
% 2.27/1.08      ( m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 2.27/1.08      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 2.27/1.08      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 2.27/1.08      inference(predicate_to_equality,[status(thm)],[c_3805]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_17,plain,
% 2.27/1.08      ( v1_subset_1(X0,X1)
% 2.27/1.08      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.27/1.08      | X0 = X1 ),
% 2.27/1.08      inference(cnf_transformation,[],[f81]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_2857,plain,
% 2.27/1.08      ( v1_subset_1(X0_49,X1_49)
% 2.27/1.08      | ~ m1_subset_1(X0_49,k1_zfmisc_1(X1_49))
% 2.27/1.08      | X0_49 = X1_49 ),
% 2.27/1.08      inference(subtyping,[status(esa)],[c_17]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_3904,plain,
% 2.27/1.08      ( v1_subset_1(X0_49,u1_struct_0(sK2))
% 2.27/1.08      | ~ m1_subset_1(X0_49,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.27/1.08      | X0_49 = u1_struct_0(sK2) ),
% 2.27/1.08      inference(instantiation,[status(thm)],[c_2857]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_4029,plain,
% 2.27/1.08      ( v1_subset_1(k2_tarski(sK3,sK3),u1_struct_0(sK2))
% 2.27/1.08      | ~ m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.27/1.08      | k2_tarski(sK3,sK3) = u1_struct_0(sK2) ),
% 2.27/1.08      inference(instantiation,[status(thm)],[c_3904]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_4030,plain,
% 2.27/1.08      ( k2_tarski(sK3,sK3) = u1_struct_0(sK2)
% 2.27/1.08      | v1_subset_1(k2_tarski(sK3,sK3),u1_struct_0(sK2)) = iProver_top
% 2.27/1.08      | m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 2.27/1.08      inference(predicate_to_equality,[status(thm)],[c_4029]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_10,plain,
% 2.27/1.08      ( ~ m1_subset_1(X0,X1)
% 2.27/1.08      | v1_zfmisc_1(X1)
% 2.27/1.08      | v1_xboole_0(X1)
% 2.27/1.08      | k6_domain_1(X1,X0) != X1 ),
% 2.27/1.08      inference(cnf_transformation,[],[f75]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_2864,plain,
% 2.27/1.08      ( ~ m1_subset_1(X0_49,X1_49)
% 2.27/1.08      | v1_zfmisc_1(X1_49)
% 2.27/1.08      | v1_xboole_0(X1_49)
% 2.27/1.08      | k6_domain_1(X1_49,X0_49) != X1_49 ),
% 2.27/1.08      inference(subtyping,[status(esa)],[c_10]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_3562,plain,
% 2.27/1.08      ( k6_domain_1(X0_49,X1_49) != X0_49
% 2.27/1.08      | m1_subset_1(X1_49,X0_49) != iProver_top
% 2.27/1.08      | v1_zfmisc_1(X0_49) = iProver_top
% 2.27/1.08      | v1_xboole_0(X0_49) = iProver_top ),
% 2.27/1.08      inference(predicate_to_equality,[status(thm)],[c_2864]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_4085,plain,
% 2.27/1.08      ( k2_tarski(sK3,sK3) != u1_struct_0(sK2)
% 2.27/1.08      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 2.27/1.08      | v1_zfmisc_1(u1_struct_0(sK2)) = iProver_top
% 2.27/1.08      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 2.27/1.08      inference(superposition,[status(thm)],[c_4070,c_3562]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_4088,plain,
% 2.27/1.08      ( v1_tex_2(k1_tex_2(sK2,sK3),sK2) != iProver_top ),
% 2.27/1.08      inference(global_propositional_subsumption,
% 2.27/1.08                [status(thm)],
% 2.27/1.08                [c_4074,c_29,c_30,c_31,c_33,c_86,c_89,c_93,c_1504,c_2927,
% 2.27/1.08                 c_2930,c_3806,c_4030,c_4085]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_6578,plain,
% 2.27/1.08      ( sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(k1_tex_2(sK2,sK3))
% 2.27/1.08      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 2.27/1.08      | v2_struct_0(sK2) = iProver_top
% 2.27/1.08      | l1_pre_topc(sK2) != iProver_top ),
% 2.27/1.08      inference(superposition,[status(thm)],[c_4486,c_4088]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_3829,plain,
% 2.27/1.08      ( v1_tex_2(k1_tex_2(X0_48,X0_49),X0_48)
% 2.27/1.08      | ~ m1_pre_topc(k1_tex_2(X0_48,X0_49),X0_48)
% 2.27/1.08      | ~ l1_pre_topc(X0_48)
% 2.27/1.08      | sK1(X0_48,k1_tex_2(X0_48,X0_49)) = u1_struct_0(k1_tex_2(X0_48,X0_49)) ),
% 2.27/1.08      inference(instantiation,[status(thm)],[c_2860]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_3830,plain,
% 2.27/1.08      ( sK1(X0_48,k1_tex_2(X0_48,X0_49)) = u1_struct_0(k1_tex_2(X0_48,X0_49))
% 2.27/1.08      | v1_tex_2(k1_tex_2(X0_48,X0_49),X0_48) = iProver_top
% 2.27/1.08      | m1_pre_topc(k1_tex_2(X0_48,X0_49),X0_48) != iProver_top
% 2.27/1.08      | l1_pre_topc(X0_48) != iProver_top ),
% 2.27/1.08      inference(predicate_to_equality,[status(thm)],[c_3829]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_3832,plain,
% 2.27/1.08      ( sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(k1_tex_2(sK2,sK3))
% 2.27/1.08      | v1_tex_2(k1_tex_2(sK2,sK3),sK2) = iProver_top
% 2.27/1.08      | m1_pre_topc(k1_tex_2(sK2,sK3),sK2) != iProver_top
% 2.27/1.08      | l1_pre_topc(sK2) != iProver_top ),
% 2.27/1.08      inference(instantiation,[status(thm)],[c_3830]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_7084,plain,
% 2.27/1.08      ( sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(k1_tex_2(sK2,sK3)) ),
% 2.27/1.08      inference(global_propositional_subsumption,
% 2.27/1.08                [status(thm)],
% 2.27/1.08                [c_6578,c_29,c_30,c_31,c_33,c_86,c_89,c_93,c_1504,c_2927,
% 2.27/1.08                 c_2930,c_3806,c_3832,c_4030,c_4074,c_4085]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_15,plain,
% 2.27/1.08      ( v1_tex_2(X0,X1)
% 2.27/1.08      | ~ m1_pre_topc(X0,X1)
% 2.27/1.08      | m1_subset_1(sK1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.27/1.08      | ~ l1_pre_topc(X1) ),
% 2.27/1.08      inference(cnf_transformation,[],[f77]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_2859,plain,
% 2.27/1.08      ( v1_tex_2(X0_48,X1_48)
% 2.27/1.08      | ~ m1_pre_topc(X0_48,X1_48)
% 2.27/1.08      | m1_subset_1(sK1(X1_48,X0_48),k1_zfmisc_1(u1_struct_0(X1_48)))
% 2.27/1.08      | ~ l1_pre_topc(X1_48) ),
% 2.27/1.08      inference(subtyping,[status(esa)],[c_15]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_3567,plain,
% 2.27/1.08      ( v1_tex_2(X0_48,X1_48) = iProver_top
% 2.27/1.08      | m1_pre_topc(X0_48,X1_48) != iProver_top
% 2.27/1.08      | m1_subset_1(sK1(X1_48,X0_48),k1_zfmisc_1(u1_struct_0(X1_48))) = iProver_top
% 2.27/1.08      | l1_pre_topc(X1_48) != iProver_top ),
% 2.27/1.08      inference(predicate_to_equality,[status(thm)],[c_2859]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_3569,plain,
% 2.27/1.08      ( X0_49 = X1_49
% 2.27/1.08      | v1_subset_1(X0_49,X1_49) = iProver_top
% 2.27/1.08      | m1_subset_1(X0_49,k1_zfmisc_1(X1_49)) != iProver_top ),
% 2.27/1.08      inference(predicate_to_equality,[status(thm)],[c_2857]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_5097,plain,
% 2.27/1.08      ( sK1(X0_48,X1_48) = u1_struct_0(X0_48)
% 2.27/1.08      | v1_subset_1(sK1(X0_48,X1_48),u1_struct_0(X0_48)) = iProver_top
% 2.27/1.08      | v1_tex_2(X1_48,X0_48) = iProver_top
% 2.27/1.08      | m1_pre_topc(X1_48,X0_48) != iProver_top
% 2.27/1.08      | l1_pre_topc(X0_48) != iProver_top ),
% 2.27/1.08      inference(superposition,[status(thm)],[c_3567,c_3569]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_13,plain,
% 2.27/1.08      ( ~ v1_subset_1(sK1(X0,X1),u1_struct_0(X0))
% 2.27/1.08      | v1_tex_2(X1,X0)
% 2.27/1.08      | ~ m1_pre_topc(X1,X0)
% 2.27/1.08      | ~ l1_pre_topc(X0) ),
% 2.27/1.08      inference(cnf_transformation,[],[f79]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_2861,plain,
% 2.27/1.08      ( ~ v1_subset_1(sK1(X0_48,X1_48),u1_struct_0(X0_48))
% 2.27/1.08      | v1_tex_2(X1_48,X0_48)
% 2.27/1.08      | ~ m1_pre_topc(X1_48,X0_48)
% 2.27/1.08      | ~ l1_pre_topc(X0_48) ),
% 2.27/1.08      inference(subtyping,[status(esa)],[c_13]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_2915,plain,
% 2.27/1.08      ( v1_subset_1(sK1(X0_48,X1_48),u1_struct_0(X0_48)) != iProver_top
% 2.27/1.08      | v1_tex_2(X1_48,X0_48) = iProver_top
% 2.27/1.08      | m1_pre_topc(X1_48,X0_48) != iProver_top
% 2.27/1.08      | l1_pre_topc(X0_48) != iProver_top ),
% 2.27/1.08      inference(predicate_to_equality,[status(thm)],[c_2861]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_6605,plain,
% 2.27/1.08      ( sK1(X0_48,X1_48) = u1_struct_0(X0_48)
% 2.27/1.08      | v1_tex_2(X1_48,X0_48) = iProver_top
% 2.27/1.08      | m1_pre_topc(X1_48,X0_48) != iProver_top
% 2.27/1.08      | l1_pre_topc(X0_48) != iProver_top ),
% 2.27/1.08      inference(global_propositional_subsumption,
% 2.27/1.08                [status(thm)],
% 2.27/1.08                [c_5097,c_2915]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_6613,plain,
% 2.27/1.08      ( sK1(X0_48,k1_tex_2(X0_48,X0_49)) = u1_struct_0(X0_48)
% 2.27/1.08      | v1_tex_2(k1_tex_2(X0_48,X0_49),X0_48) = iProver_top
% 2.27/1.08      | m1_subset_1(X0_49,u1_struct_0(X0_48)) != iProver_top
% 2.27/1.08      | v2_struct_0(X0_48) = iProver_top
% 2.27/1.08      | l1_pre_topc(X0_48) != iProver_top ),
% 2.27/1.08      inference(superposition,[status(thm)],[c_3571,c_6605]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_6726,plain,
% 2.27/1.08      ( sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(sK2)
% 2.27/1.08      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 2.27/1.08      | v2_struct_0(sK2) = iProver_top
% 2.27/1.08      | l1_pre_topc(sK2) != iProver_top ),
% 2.27/1.08      inference(superposition,[status(thm)],[c_6613,c_4088]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_2926,plain,
% 2.27/1.08      ( m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
% 2.27/1.08      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 2.27/1.08      | v2_struct_0(sK2)
% 2.27/1.08      | ~ l1_pre_topc(sK2) ),
% 2.27/1.08      inference(instantiation,[status(thm)],[c_2855]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_3824,plain,
% 2.27/1.08      ( v1_tex_2(k1_tex_2(X0_48,X0_49),X0_48)
% 2.27/1.08      | ~ m1_pre_topc(k1_tex_2(X0_48,X0_49),X0_48)
% 2.27/1.08      | m1_subset_1(sK1(X0_48,k1_tex_2(X0_48,X0_49)),k1_zfmisc_1(u1_struct_0(X0_48)))
% 2.27/1.08      | ~ l1_pre_topc(X0_48) ),
% 2.27/1.08      inference(instantiation,[status(thm)],[c_2859]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_3826,plain,
% 2.27/1.08      ( v1_tex_2(k1_tex_2(sK2,sK3),sK2)
% 2.27/1.08      | ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
% 2.27/1.08      | m1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.27/1.08      | ~ l1_pre_topc(sK2) ),
% 2.27/1.08      inference(instantiation,[status(thm)],[c_3824]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_3834,plain,
% 2.27/1.08      ( ~ v1_subset_1(sK1(X0_48,k1_tex_2(X0_48,X0_49)),u1_struct_0(X0_48))
% 2.27/1.08      | v1_tex_2(k1_tex_2(X0_48,X0_49),X0_48)
% 2.27/1.08      | ~ m1_pre_topc(k1_tex_2(X0_48,X0_49),X0_48)
% 2.27/1.08      | ~ l1_pre_topc(X0_48) ),
% 2.27/1.08      inference(instantiation,[status(thm)],[c_2861]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_3836,plain,
% 2.27/1.08      ( ~ v1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),u1_struct_0(sK2))
% 2.27/1.08      | v1_tex_2(k1_tex_2(sK2,sK3),sK2)
% 2.27/1.08      | ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
% 2.27/1.08      | ~ l1_pre_topc(sK2) ),
% 2.27/1.08      inference(instantiation,[status(thm)],[c_3834]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_4090,plain,
% 2.27/1.08      ( ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2) ),
% 2.27/1.08      inference(predicate_to_equality_rev,[status(thm)],[c_4088]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_4419,plain,
% 2.27/1.08      ( v1_subset_1(sK1(sK2,k1_tex_2(sK2,X0_49)),u1_struct_0(sK2))
% 2.27/1.08      | ~ m1_subset_1(sK1(sK2,k1_tex_2(sK2,X0_49)),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.27/1.08      | sK1(sK2,k1_tex_2(sK2,X0_49)) = u1_struct_0(sK2) ),
% 2.27/1.08      inference(instantiation,[status(thm)],[c_3904]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_4423,plain,
% 2.27/1.08      ( v1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),u1_struct_0(sK2))
% 2.27/1.08      | ~ m1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.27/1.08      | sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(sK2) ),
% 2.27/1.08      inference(instantiation,[status(thm)],[c_4419]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_6968,plain,
% 2.27/1.08      ( sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(sK2) ),
% 2.27/1.08      inference(global_propositional_subsumption,
% 2.27/1.08                [status(thm)],
% 2.27/1.08                [c_6726,c_28,c_27,c_26,c_2926,c_3826,c_3836,c_4090,
% 2.27/1.08                 c_4423]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_7086,plain,
% 2.27/1.08      ( u1_struct_0(k1_tex_2(sK2,sK3)) = u1_struct_0(sK2) ),
% 2.27/1.08      inference(light_normalisation,[status(thm)],[c_7084,c_6968]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_21,plain,
% 2.27/1.08      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.27/1.08      | v7_struct_0(k1_tex_2(X1,X0))
% 2.27/1.08      | v2_struct_0(X1)
% 2.27/1.08      | ~ l1_pre_topc(X1) ),
% 2.27/1.08      inference(cnf_transformation,[],[f85]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_2853,plain,
% 2.27/1.08      ( ~ m1_subset_1(X0_49,u1_struct_0(X0_48))
% 2.27/1.08      | v7_struct_0(k1_tex_2(X0_48,X0_49))
% 2.27/1.08      | v2_struct_0(X0_48)
% 2.27/1.08      | ~ l1_pre_topc(X0_48) ),
% 2.27/1.08      inference(subtyping,[status(esa)],[c_21]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_3573,plain,
% 2.27/1.08      ( m1_subset_1(X0_49,u1_struct_0(X0_48)) != iProver_top
% 2.27/1.08      | v7_struct_0(k1_tex_2(X0_48,X0_49)) = iProver_top
% 2.27/1.08      | v2_struct_0(X0_48) = iProver_top
% 2.27/1.08      | l1_pre_topc(X0_48) != iProver_top ),
% 2.27/1.08      inference(predicate_to_equality,[status(thm)],[c_2853]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_4436,plain,
% 2.27/1.08      ( v7_struct_0(k1_tex_2(sK2,sK3)) = iProver_top
% 2.27/1.08      | v2_struct_0(sK2) = iProver_top
% 2.27/1.08      | l1_pre_topc(sK2) != iProver_top ),
% 2.27/1.08      inference(superposition,[status(thm)],[c_3577,c_3573]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_2931,plain,
% 2.27/1.08      ( m1_subset_1(X0_49,u1_struct_0(X0_48)) != iProver_top
% 2.27/1.08      | v7_struct_0(k1_tex_2(X0_48,X0_49)) = iProver_top
% 2.27/1.08      | v2_struct_0(X0_48) = iProver_top
% 2.27/1.08      | l1_pre_topc(X0_48) != iProver_top ),
% 2.27/1.08      inference(predicate_to_equality,[status(thm)],[c_2853]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_2933,plain,
% 2.27/1.08      ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 2.27/1.08      | v7_struct_0(k1_tex_2(sK2,sK3)) = iProver_top
% 2.27/1.08      | v2_struct_0(sK2) = iProver_top
% 2.27/1.08      | l1_pre_topc(sK2) != iProver_top ),
% 2.27/1.08      inference(instantiation,[status(thm)],[c_2931]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_4628,plain,
% 2.27/1.08      ( v7_struct_0(k1_tex_2(sK2,sK3)) = iProver_top ),
% 2.27/1.08      inference(global_propositional_subsumption,
% 2.27/1.08                [status(thm)],
% 2.27/1.08                [c_4436,c_29,c_30,c_31,c_2933]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_6,plain,
% 2.27/1.08      ( ~ v7_struct_0(X0)
% 2.27/1.08      | v1_zfmisc_1(u1_struct_0(X0))
% 2.27/1.08      | ~ l1_struct_0(X0) ),
% 2.27/1.08      inference(cnf_transformation,[],[f69]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_393,plain,
% 2.27/1.08      ( ~ v7_struct_0(X0)
% 2.27/1.08      | v1_zfmisc_1(u1_struct_0(X0))
% 2.27/1.08      | ~ l1_pre_topc(X0) ),
% 2.27/1.08      inference(resolution,[status(thm)],[c_2,c_6]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_2845,plain,
% 2.27/1.08      ( ~ v7_struct_0(X0_48)
% 2.27/1.08      | v1_zfmisc_1(u1_struct_0(X0_48))
% 2.27/1.08      | ~ l1_pre_topc(X0_48) ),
% 2.27/1.08      inference(subtyping,[status(esa)],[c_393]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_3581,plain,
% 2.27/1.08      ( v7_struct_0(X0_48) != iProver_top
% 2.27/1.08      | v1_zfmisc_1(u1_struct_0(X0_48)) = iProver_top
% 2.27/1.08      | l1_pre_topc(X0_48) != iProver_top ),
% 2.27/1.08      inference(predicate_to_equality,[status(thm)],[c_2845]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_11,plain,
% 2.27/1.08      ( ~ v1_zfmisc_1(X0)
% 2.27/1.08      | v1_xboole_0(X0)
% 2.27/1.08      | k6_domain_1(X0,sK0(X0)) = X0 ),
% 2.27/1.08      inference(cnf_transformation,[],[f74]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_2863,plain,
% 2.27/1.08      ( ~ v1_zfmisc_1(X0_49)
% 2.27/1.08      | v1_xboole_0(X0_49)
% 2.27/1.08      | k6_domain_1(X0_49,sK0(X0_49)) = X0_49 ),
% 2.27/1.08      inference(subtyping,[status(esa)],[c_11]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_3563,plain,
% 2.27/1.08      ( k6_domain_1(X0_49,sK0(X0_49)) = X0_49
% 2.27/1.08      | v1_zfmisc_1(X0_49) != iProver_top
% 2.27/1.08      | v1_xboole_0(X0_49) = iProver_top ),
% 2.27/1.08      inference(predicate_to_equality,[status(thm)],[c_2863]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_4265,plain,
% 2.27/1.08      ( k6_domain_1(u1_struct_0(X0_48),sK0(u1_struct_0(X0_48))) = u1_struct_0(X0_48)
% 2.27/1.08      | v7_struct_0(X0_48) != iProver_top
% 2.27/1.08      | l1_pre_topc(X0_48) != iProver_top
% 2.27/1.08      | v1_xboole_0(u1_struct_0(X0_48)) = iProver_top ),
% 2.27/1.08      inference(superposition,[status(thm)],[c_3581,c_3563]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_421,plain,
% 2.27/1.08      ( v2_struct_0(X0)
% 2.27/1.08      | ~ l1_pre_topc(X0)
% 2.27/1.08      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.27/1.08      inference(resolution,[status(thm)],[c_2,c_4]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_2843,plain,
% 2.27/1.08      ( v2_struct_0(X0_48)
% 2.27/1.08      | ~ l1_pre_topc(X0_48)
% 2.27/1.08      | ~ v1_xboole_0(u1_struct_0(X0_48)) ),
% 2.27/1.08      inference(subtyping,[status(esa)],[c_421]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_3583,plain,
% 2.27/1.08      ( v2_struct_0(X0_48) = iProver_top
% 2.27/1.08      | l1_pre_topc(X0_48) != iProver_top
% 2.27/1.08      | v1_xboole_0(u1_struct_0(X0_48)) != iProver_top ),
% 2.27/1.08      inference(predicate_to_equality,[status(thm)],[c_2843]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_5407,plain,
% 2.27/1.08      ( k6_domain_1(u1_struct_0(X0_48),sK0(u1_struct_0(X0_48))) = u1_struct_0(X0_48)
% 2.27/1.08      | v7_struct_0(X0_48) != iProver_top
% 2.27/1.08      | v2_struct_0(X0_48) = iProver_top
% 2.27/1.08      | l1_pre_topc(X0_48) != iProver_top ),
% 2.27/1.08      inference(superposition,[status(thm)],[c_4265,c_3583]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_5520,plain,
% 2.27/1.08      ( k6_domain_1(u1_struct_0(k1_tex_2(sK2,sK3)),sK0(u1_struct_0(k1_tex_2(sK2,sK3)))) = u1_struct_0(k1_tex_2(sK2,sK3))
% 2.27/1.08      | v2_struct_0(k1_tex_2(sK2,sK3)) = iProver_top
% 2.27/1.08      | l1_pre_topc(k1_tex_2(sK2,sK3)) != iProver_top ),
% 2.27/1.08      inference(superposition,[status(thm)],[c_4628,c_5407]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_2929,plain,
% 2.27/1.08      ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 2.27/1.08      | ~ v2_struct_0(k1_tex_2(sK2,sK3))
% 2.27/1.08      | v2_struct_0(sK2)
% 2.27/1.08      | ~ l1_pre_topc(sK2) ),
% 2.27/1.08      inference(instantiation,[status(thm)],[c_2854]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_2932,plain,
% 2.27/1.08      ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 2.27/1.08      | v7_struct_0(k1_tex_2(sK2,sK3))
% 2.27/1.08      | v2_struct_0(sK2)
% 2.27/1.08      | ~ l1_pre_topc(sK2) ),
% 2.27/1.08      inference(instantiation,[status(thm)],[c_2853]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_3808,plain,
% 2.27/1.08      ( ~ v7_struct_0(k1_tex_2(X0_48,X0_49))
% 2.27/1.08      | v1_zfmisc_1(u1_struct_0(k1_tex_2(X0_48,X0_49)))
% 2.27/1.08      | ~ l1_pre_topc(k1_tex_2(X0_48,X0_49)) ),
% 2.27/1.08      inference(instantiation,[status(thm)],[c_2845]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_3810,plain,
% 2.27/1.08      ( ~ v7_struct_0(k1_tex_2(sK2,sK3))
% 2.27/1.08      | v1_zfmisc_1(u1_struct_0(k1_tex_2(sK2,sK3)))
% 2.27/1.08      | ~ l1_pre_topc(k1_tex_2(sK2,sK3)) ),
% 2.27/1.08      inference(instantiation,[status(thm)],[c_3808]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_3,plain,
% 2.27/1.08      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.27/1.08      inference(cnf_transformation,[],[f66]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_2867,plain,
% 2.27/1.08      ( ~ m1_pre_topc(X0_48,X1_48)
% 2.27/1.08      | ~ l1_pre_topc(X1_48)
% 2.27/1.08      | l1_pre_topc(X0_48) ),
% 2.27/1.08      inference(subtyping,[status(esa)],[c_3]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_3927,plain,
% 2.27/1.08      ( ~ m1_pre_topc(k1_tex_2(X0_48,X0_49),X1_48)
% 2.27/1.08      | ~ l1_pre_topc(X1_48)
% 2.27/1.08      | l1_pre_topc(k1_tex_2(X0_48,X0_49)) ),
% 2.27/1.08      inference(instantiation,[status(thm)],[c_2867]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_3929,plain,
% 2.27/1.08      ( ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
% 2.27/1.08      | l1_pre_topc(k1_tex_2(sK2,sK3))
% 2.27/1.08      | ~ l1_pre_topc(sK2) ),
% 2.27/1.08      inference(instantiation,[status(thm)],[c_3927]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_4200,plain,
% 2.27/1.08      ( ~ v1_zfmisc_1(u1_struct_0(k1_tex_2(X0_48,X0_49)))
% 2.27/1.08      | v1_xboole_0(u1_struct_0(k1_tex_2(X0_48,X0_49)))
% 2.27/1.08      | k6_domain_1(u1_struct_0(k1_tex_2(X0_48,X0_49)),sK0(u1_struct_0(k1_tex_2(X0_48,X0_49)))) = u1_struct_0(k1_tex_2(X0_48,X0_49)) ),
% 2.27/1.08      inference(instantiation,[status(thm)],[c_2863]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_4207,plain,
% 2.27/1.08      ( ~ v1_zfmisc_1(u1_struct_0(k1_tex_2(sK2,sK3)))
% 2.27/1.08      | v1_xboole_0(u1_struct_0(k1_tex_2(sK2,sK3)))
% 2.27/1.08      | k6_domain_1(u1_struct_0(k1_tex_2(sK2,sK3)),sK0(u1_struct_0(k1_tex_2(sK2,sK3)))) = u1_struct_0(k1_tex_2(sK2,sK3)) ),
% 2.27/1.08      inference(instantiation,[status(thm)],[c_4200]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_5177,plain,
% 2.27/1.08      ( v2_struct_0(k1_tex_2(X0_48,X0_49))
% 2.27/1.08      | ~ l1_pre_topc(k1_tex_2(X0_48,X0_49))
% 2.27/1.08      | ~ v1_xboole_0(u1_struct_0(k1_tex_2(X0_48,X0_49))) ),
% 2.27/1.08      inference(instantiation,[status(thm)],[c_2843]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_5179,plain,
% 2.27/1.08      ( v2_struct_0(k1_tex_2(sK2,sK3))
% 2.27/1.08      | ~ l1_pre_topc(k1_tex_2(sK2,sK3))
% 2.27/1.08      | ~ v1_xboole_0(u1_struct_0(k1_tex_2(sK2,sK3))) ),
% 2.27/1.08      inference(instantiation,[status(thm)],[c_5177]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_5523,plain,
% 2.27/1.08      ( k6_domain_1(u1_struct_0(k1_tex_2(sK2,sK3)),sK0(u1_struct_0(k1_tex_2(sK2,sK3)))) = u1_struct_0(k1_tex_2(sK2,sK3)) ),
% 2.27/1.08      inference(global_propositional_subsumption,
% 2.27/1.08                [status(thm)],
% 2.27/1.08                [c_5520,c_28,c_27,c_26,c_2926,c_2929,c_2932,c_3810,
% 2.27/1.08                 c_3929,c_4207,c_5179]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_5527,plain,
% 2.27/1.08      ( m1_subset_1(sK0(u1_struct_0(k1_tex_2(sK2,sK3))),u1_struct_0(k1_tex_2(sK2,sK3))) != iProver_top
% 2.27/1.08      | v1_zfmisc_1(u1_struct_0(k1_tex_2(sK2,sK3))) = iProver_top
% 2.27/1.08      | v1_xboole_0(u1_struct_0(k1_tex_2(sK2,sK3))) = iProver_top ),
% 2.27/1.08      inference(superposition,[status(thm)],[c_5523,c_3562]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_3809,plain,
% 2.27/1.08      ( v7_struct_0(k1_tex_2(X0_48,X0_49)) != iProver_top
% 2.27/1.08      | v1_zfmisc_1(u1_struct_0(k1_tex_2(X0_48,X0_49))) = iProver_top
% 2.27/1.08      | l1_pre_topc(k1_tex_2(X0_48,X0_49)) != iProver_top ),
% 2.27/1.08      inference(predicate_to_equality,[status(thm)],[c_3808]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_3811,plain,
% 2.27/1.08      ( v7_struct_0(k1_tex_2(sK2,sK3)) != iProver_top
% 2.27/1.08      | v1_zfmisc_1(u1_struct_0(k1_tex_2(sK2,sK3))) = iProver_top
% 2.27/1.08      | l1_pre_topc(k1_tex_2(sK2,sK3)) != iProver_top ),
% 2.27/1.08      inference(instantiation,[status(thm)],[c_3809]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_3928,plain,
% 2.27/1.08      ( m1_pre_topc(k1_tex_2(X0_48,X0_49),X1_48) != iProver_top
% 2.27/1.08      | l1_pre_topc(X1_48) != iProver_top
% 2.27/1.08      | l1_pre_topc(k1_tex_2(X0_48,X0_49)) = iProver_top ),
% 2.27/1.08      inference(predicate_to_equality,[status(thm)],[c_3927]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_3930,plain,
% 2.27/1.08      ( m1_pre_topc(k1_tex_2(sK2,sK3),sK2) != iProver_top
% 2.27/1.08      | l1_pre_topc(k1_tex_2(sK2,sK3)) = iProver_top
% 2.27/1.08      | l1_pre_topc(sK2) != iProver_top ),
% 2.27/1.08      inference(instantiation,[status(thm)],[c_3928]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_5601,plain,
% 2.27/1.08      ( v1_zfmisc_1(u1_struct_0(k1_tex_2(sK2,sK3))) = iProver_top ),
% 2.27/1.08      inference(global_propositional_subsumption,
% 2.27/1.08                [status(thm)],
% 2.27/1.08                [c_5527,c_29,c_30,c_31,c_2927,c_2933,c_3811,c_3930]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_7095,plain,
% 2.27/1.08      ( v1_zfmisc_1(u1_struct_0(sK2)) = iProver_top ),
% 2.27/1.08      inference(demodulation,[status(thm)],[c_7086,c_5601]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_23,plain,
% 2.27/1.08      ( ~ v1_subset_1(k6_domain_1(X0,X1),X0)
% 2.27/1.08      | ~ m1_subset_1(X1,X0)
% 2.27/1.08      | ~ v1_zfmisc_1(X0)
% 2.27/1.08      | v1_xboole_0(X0) ),
% 2.27/1.08      inference(cnf_transformation,[],[f86]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_2852,plain,
% 2.27/1.08      ( ~ v1_subset_1(k6_domain_1(X0_49,X1_49),X0_49)
% 2.27/1.08      | ~ m1_subset_1(X1_49,X0_49)
% 2.27/1.08      | ~ v1_zfmisc_1(X0_49)
% 2.27/1.08      | v1_xboole_0(X0_49) ),
% 2.27/1.08      inference(subtyping,[status(esa)],[c_23]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_3574,plain,
% 2.27/1.08      ( v1_subset_1(k6_domain_1(X0_49,X1_49),X0_49) != iProver_top
% 2.27/1.08      | m1_subset_1(X1_49,X0_49) != iProver_top
% 2.27/1.08      | v1_zfmisc_1(X0_49) != iProver_top
% 2.27/1.08      | v1_xboole_0(X0_49) = iProver_top ),
% 2.27/1.08      inference(predicate_to_equality,[status(thm)],[c_2852]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_4762,plain,
% 2.27/1.08      ( v1_subset_1(k2_tarski(sK3,sK3),u1_struct_0(sK2)) != iProver_top
% 2.27/1.08      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 2.27/1.08      | v1_zfmisc_1(u1_struct_0(sK2)) != iProver_top
% 2.27/1.08      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 2.27/1.08      inference(superposition,[status(thm)],[c_4070,c_3574]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_2850,negated_conjecture,
% 2.27/1.08      ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 2.27/1.08      | v1_tex_2(k1_tex_2(sK2,sK3),sK2) ),
% 2.27/1.08      inference(subtyping,[status(esa)],[c_25]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_3576,plain,
% 2.27/1.08      ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) = iProver_top
% 2.27/1.08      | v1_tex_2(k1_tex_2(sK2,sK3),sK2) = iProver_top ),
% 2.27/1.08      inference(predicate_to_equality,[status(thm)],[c_2850]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(c_4073,plain,
% 2.27/1.08      ( v1_subset_1(k2_tarski(sK3,sK3),u1_struct_0(sK2)) = iProver_top
% 2.27/1.08      | v1_tex_2(k1_tex_2(sK2,sK3),sK2) = iProver_top ),
% 2.27/1.08      inference(demodulation,[status(thm)],[c_4070,c_3576]) ).
% 2.27/1.08  
% 2.27/1.08  cnf(contradiction,plain,
% 2.27/1.08      ( $false ),
% 2.27/1.08      inference(minisat,
% 2.27/1.08                [status(thm)],
% 2.27/1.08                [c_7095,c_4762,c_4088,c_4073,c_93,c_89,c_31,c_30,c_29]) ).
% 2.27/1.08  
% 2.27/1.08  
% 2.27/1.08  % SZS output end CNFRefutation for theBenchmark.p
% 2.27/1.08  
% 2.27/1.08  ------                               Statistics
% 2.27/1.08  
% 2.27/1.08  ------ General
% 2.27/1.08  
% 2.27/1.08  abstr_ref_over_cycles:                  0
% 2.27/1.08  abstr_ref_under_cycles:                 0
% 2.27/1.08  gc_basic_clause_elim:                   0
% 2.27/1.08  forced_gc_time:                         0
% 2.27/1.08  parsing_time:                           0.008
% 2.27/1.08  unif_index_cands_time:                  0.
% 2.27/1.08  unif_index_add_time:                    0.
% 2.27/1.08  orderings_time:                         0.
% 2.27/1.08  out_proof_time:                         0.011
% 2.27/1.08  total_time:                             0.205
% 2.27/1.08  num_of_symbols:                         53
% 2.27/1.08  num_of_terms:                           4368
% 2.27/1.08  
% 2.27/1.08  ------ Preprocessing
% 2.27/1.08  
% 2.27/1.08  num_of_splits:                          0
% 2.27/1.08  num_of_split_atoms:                     0
% 2.27/1.08  num_of_reused_defs:                     0
% 2.27/1.08  num_eq_ax_congr_red:                    21
% 2.27/1.08  num_of_sem_filtered_clauses:            1
% 2.27/1.08  num_of_subtypes:                        2
% 2.27/1.08  monotx_restored_types:                  1
% 2.27/1.08  sat_num_of_epr_types:                   0
% 2.27/1.08  sat_num_of_non_cyclic_types:            0
% 2.27/1.08  sat_guarded_non_collapsed_types:        0
% 2.27/1.08  num_pure_diseq_elim:                    0
% 2.27/1.08  simp_replaced_by:                       0
% 2.27/1.08  res_preprocessed:                       135
% 2.27/1.08  prep_upred:                             0
% 2.27/1.08  prep_unflattend:                        108
% 2.27/1.08  smt_new_axioms:                         0
% 2.27/1.08  pred_elim_cands:                        9
% 2.27/1.08  pred_elim:                              2
% 2.27/1.08  pred_elim_cl:                           2
% 2.27/1.08  pred_elim_cycles:                       14
% 2.27/1.08  merged_defs:                            8
% 2.27/1.08  merged_defs_ncl:                        0
% 2.27/1.08  bin_hyper_res:                          8
% 2.27/1.08  prep_cycles:                            4
% 2.27/1.08  pred_elim_time:                         0.039
% 2.27/1.08  splitting_time:                         0.
% 2.27/1.08  sem_filter_time:                        0.
% 2.27/1.08  monotx_time:                            0.
% 2.27/1.08  subtype_inf_time:                       0.001
% 2.27/1.08  
% 2.27/1.08  ------ Problem properties
% 2.27/1.08  
% 2.27/1.08  clauses:                                25
% 2.27/1.08  conjectures:                            5
% 2.27/1.08  epr:                                    4
% 2.27/1.08  horn:                                   13
% 2.27/1.08  ground:                                 5
% 2.27/1.08  unary:                                  3
% 2.27/1.08  binary:                                 3
% 2.27/1.08  lits:                                   79
% 2.27/1.08  lits_eq:                                5
% 2.27/1.08  fd_pure:                                0
% 2.27/1.08  fd_pseudo:                              0
% 2.27/1.08  fd_cond:                                0
% 2.27/1.08  fd_pseudo_cond:                         1
% 2.27/1.08  ac_symbols:                             0
% 2.27/1.08  
% 2.27/1.08  ------ Propositional Solver
% 2.27/1.08  
% 2.27/1.08  prop_solver_calls:                      29
% 2.27/1.08  prop_fast_solver_calls:                 1596
% 2.27/1.08  smt_solver_calls:                       0
% 2.27/1.08  smt_fast_solver_calls:                  0
% 2.27/1.08  prop_num_of_clauses:                    1781
% 2.27/1.08  prop_preprocess_simplified:             7005
% 2.27/1.08  prop_fo_subsumed:                       56
% 2.27/1.08  prop_solver_time:                       0.
% 2.27/1.08  smt_solver_time:                        0.
% 2.27/1.08  smt_fast_solver_time:                   0.
% 2.27/1.08  prop_fast_solver_time:                  0.
% 2.27/1.08  prop_unsat_core_time:                   0.
% 2.27/1.08  
% 2.27/1.08  ------ QBF
% 2.27/1.08  
% 2.27/1.08  qbf_q_res:                              0
% 2.27/1.08  qbf_num_tautologies:                    0
% 2.27/1.08  qbf_prep_cycles:                        0
% 2.27/1.08  
% 2.27/1.08  ------ BMC1
% 2.27/1.08  
% 2.27/1.08  bmc1_current_bound:                     -1
% 2.27/1.08  bmc1_last_solved_bound:                 -1
% 2.27/1.08  bmc1_unsat_core_size:                   -1
% 2.27/1.08  bmc1_unsat_core_parents_size:           -1
% 2.27/1.08  bmc1_merge_next_fun:                    0
% 2.27/1.08  bmc1_unsat_core_clauses_time:           0.
% 2.27/1.08  
% 2.27/1.08  ------ Instantiation
% 2.27/1.08  
% 2.27/1.08  inst_num_of_clauses:                    538
% 2.27/1.08  inst_num_in_passive:                    60
% 2.27/1.08  inst_num_in_active:                     286
% 2.27/1.08  inst_num_in_unprocessed:                192
% 2.27/1.08  inst_num_of_loops:                      320
% 2.27/1.08  inst_num_of_learning_restarts:          0
% 2.27/1.08  inst_num_moves_active_passive:          30
% 2.27/1.08  inst_lit_activity:                      0
% 2.27/1.08  inst_lit_activity_moves:                0
% 2.27/1.08  inst_num_tautologies:                   0
% 2.27/1.08  inst_num_prop_implied:                  0
% 2.27/1.08  inst_num_existing_simplified:           0
% 2.27/1.08  inst_num_eq_res_simplified:             0
% 2.27/1.08  inst_num_child_elim:                    0
% 2.27/1.08  inst_num_of_dismatching_blockings:      109
% 2.27/1.08  inst_num_of_non_proper_insts:           538
% 2.27/1.08  inst_num_of_duplicates:                 0
% 2.27/1.08  inst_inst_num_from_inst_to_res:         0
% 2.27/1.08  inst_dismatching_checking_time:         0.
% 2.27/1.08  
% 2.27/1.08  ------ Resolution
% 2.27/1.08  
% 2.27/1.08  res_num_of_clauses:                     0
% 2.27/1.08  res_num_in_passive:                     0
% 2.27/1.08  res_num_in_active:                      0
% 2.27/1.08  res_num_of_loops:                       139
% 2.27/1.08  res_forward_subset_subsumed:            24
% 2.27/1.08  res_backward_subset_subsumed:           0
% 2.27/1.08  res_forward_subsumed:                   0
% 2.27/1.08  res_backward_subsumed:                  0
% 2.27/1.08  res_forward_subsumption_resolution:     2
% 2.27/1.08  res_backward_subsumption_resolution:    0
% 2.27/1.08  res_clause_to_clause_subsumption:       152
% 2.27/1.08  res_orphan_elimination:                 0
% 2.27/1.08  res_tautology_del:                      99
% 2.27/1.08  res_num_eq_res_simplified:              0
% 2.27/1.08  res_num_sel_changes:                    0
% 2.27/1.08  res_moves_from_active_to_pass:          0
% 2.27/1.08  
% 2.27/1.08  ------ Superposition
% 2.27/1.08  
% 2.27/1.08  sup_time_total:                         0.
% 2.27/1.08  sup_time_generating:                    0.
% 2.27/1.08  sup_time_sim_full:                      0.
% 2.27/1.08  sup_time_sim_immed:                     0.
% 2.27/1.08  
% 2.27/1.08  sup_num_of_clauses:                     73
% 2.27/1.08  sup_num_in_active:                      51
% 2.27/1.08  sup_num_in_passive:                     22
% 2.27/1.08  sup_num_of_loops:                       62
% 2.27/1.08  sup_fw_superposition:                   21
% 2.27/1.08  sup_bw_superposition:                   36
% 2.27/1.08  sup_immediate_simplified:               6
% 2.27/1.08  sup_given_eliminated:                   0
% 2.27/1.08  comparisons_done:                       0
% 2.27/1.08  comparisons_avoided:                    0
% 2.27/1.08  
% 2.27/1.08  ------ Simplifications
% 2.27/1.08  
% 2.27/1.08  
% 2.27/1.08  sim_fw_subset_subsumed:                 2
% 2.27/1.08  sim_bw_subset_subsumed:                 2
% 2.27/1.08  sim_fw_subsumed:                        0
% 2.27/1.08  sim_bw_subsumed:                        0
% 2.27/1.08  sim_fw_subsumption_res:                 1
% 2.27/1.08  sim_bw_subsumption_res:                 0
% 2.27/1.08  sim_tautology_del:                      2
% 2.27/1.08  sim_eq_tautology_del:                   3
% 2.27/1.08  sim_eq_res_simp:                        0
% 2.27/1.08  sim_fw_demodulated:                     1
% 2.27/1.08  sim_bw_demodulated:                     11
% 2.27/1.08  sim_light_normalised:                   3
% 2.27/1.08  sim_joinable_taut:                      0
% 2.27/1.08  sim_joinable_simp:                      0
% 2.27/1.08  sim_ac_normalised:                      0
% 2.27/1.08  sim_smt_subsumption:                    0
% 2.27/1.08  
%------------------------------------------------------------------------------
