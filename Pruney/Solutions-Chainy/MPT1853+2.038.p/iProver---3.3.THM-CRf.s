%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:25:42 EST 2020

% Result     : Theorem 2.22s
% Output     : CNFRefutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :  200 (3900 expanded)
%              Number of clauses        :  122 (1201 expanded)
%              Number of leaves         :   21 ( 797 expanded)
%              Depth                    :   22
%              Number of atoms          :  735 (17460 expanded)
%              Number of equality atoms :  247 (1965 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f73,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f9,axiom,(
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

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

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
    inference(flattening,[],[f31])).

fof(f48,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f49,plain,(
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
    inference(rectify,[],[f48])).

fof(f50,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v1_subset_1(X2,u1_struct_0(X0))
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_subset_1(sK0(X0,X1),u1_struct_0(X0))
        & u1_struct_0(X1) = sK0(X0,X1)
        & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f49,f50])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | u1_struct_0(X1) = sK0(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

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
    inference(nnf_transformation,[],[f47])).

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
     => ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),sK2),u1_struct_0(X0))
          | ~ v1_tex_2(k1_tex_2(X0,sK2),X0) )
        & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),sK2),u1_struct_0(X0))
          | v1_tex_2(k1_tex_2(X0,sK2),X0) )
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
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
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),X1),u1_struct_0(sK1))
            | ~ v1_tex_2(k1_tex_2(sK1,X1),sK1) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),X1),u1_struct_0(sK1))
            | v1_tex_2(k1_tex_2(sK1,X1),sK1) )
          & m1_subset_1(X1,u1_struct_0(sK1)) )
      & l1_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,
    ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
      | ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1) )
    & ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
      | v1_tex_2(k1_tex_2(sK1,sK2),sK1) )
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l1_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f54,f56,f55])).

fof(f82,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f57])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k2_tarski(X1,X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f64,f58])).

fof(f80,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f81,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f57])).

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

fof(f63,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f60,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f15,axiom,(
    ! [X0] :
      ( ( ~ v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f78,plain,(
    ! [X0,X1] :
      ( v1_subset_1(k6_domain_1(X0,X1),X0)
      | ~ m1_subset_1(X1,X0)
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_zfmisc_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f59,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ~ ( v1_tex_2(X1,X0)
              & u1_struct_0(X0) = u1_struct_0(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_tex_2(X1,X0)
          | u1_struct_0(X0) != u1_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_tex_2(X1,X0)
          | u1_struct_0(X0) != u1_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ v1_tex_2(X1,X0)
      | u1_struct_0(X0) != u1_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f61,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f83,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f14,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f77,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X0,X1)
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f84,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | ~ v1_subset_1(sK0(X0,X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ~ ( v7_struct_0(X0)
              & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v7_struct_0(X0)
          | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v7_struct_0(X0)
          | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ v7_struct_0(X0)
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f75,plain,(
    ! [X0,X1] :
      ( v7_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_pre_topc(k1_tex_2(X1,X0),X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_3363,plain,
    ( ~ m1_subset_1(X0_48,u1_struct_0(X0_47))
    | m1_pre_topc(k1_tex_2(X0_47,X0_48),X0_47)
    | v2_struct_0(X0_47)
    | ~ l1_pre_topc(X0_47) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_4043,plain,
    ( m1_subset_1(X0_48,u1_struct_0(X0_47)) != iProver_top
    | m1_pre_topc(k1_tex_2(X0_47,X0_48),X0_47) = iProver_top
    | v2_struct_0(X0_47) = iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3363])).

cnf(c_8,plain,
    ( v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK0(X1,X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_3368,plain,
    ( v1_tex_2(X0_47,X1_47)
    | ~ m1_pre_topc(X0_47,X1_47)
    | ~ l1_pre_topc(X1_47)
    | sK0(X1_47,X0_47) = u1_struct_0(X0_47) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_4038,plain,
    ( sK0(X0_47,X1_47) = u1_struct_0(X1_47)
    | v1_tex_2(X1_47,X0_47) = iProver_top
    | m1_pre_topc(X1_47,X0_47) != iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3368])).

cnf(c_4815,plain,
    ( sK0(X0_47,k1_tex_2(X0_47,X0_48)) = u1_struct_0(k1_tex_2(X0_47,X0_48))
    | v1_tex_2(k1_tex_2(X0_47,X0_48),X0_47) = iProver_top
    | m1_subset_1(X0_48,u1_struct_0(X0_47)) != iProver_top
    | v2_struct_0(X0_47) = iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(superposition,[status(thm)],[c_4043,c_4038])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_3357,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_4049,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3357])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_3370,plain,
    ( ~ m1_subset_1(X0_48,X1_48)
    | v1_xboole_0(X1_48)
    | k6_domain_1(X1_48,X0_48) = k2_tarski(X0_48,X0_48) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_4036,plain,
    ( k6_domain_1(X0_48,X1_48) = k2_tarski(X1_48,X1_48)
    | m1_subset_1(X1_48,X0_48) != iProver_top
    | v1_xboole_0(X0_48) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3370])).

cnf(c_4399,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK2) = k2_tarski(sK2,sK2)
    | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4049,c_4036])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_4,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_78,plain,
    ( v2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_83,plain,
    ( ~ l1_pre_topc(sK1)
    | l1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_4268,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1))
    | k6_domain_1(u1_struct_0(sK1),sK2) = k2_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_3370])).

cnf(c_4512,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK2) = k2_tarski(sK2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4399,c_25,c_24,c_23,c_78,c_83,c_4268])).

cnf(c_19,plain,
    ( v1_subset_1(k6_domain_1(X0,X1),X0)
    | ~ m1_subset_1(X1,X0)
    | v1_xboole_0(X0)
    | v1_zfmisc_1(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_0,plain,
    ( ~ v1_xboole_0(X0)
    | v1_zfmisc_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_147,plain,
    ( ~ m1_subset_1(X1,X0)
    | v1_subset_1(k6_domain_1(X0,X1),X0)
    | v1_zfmisc_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19,c_0])).

cnf(c_148,plain,
    ( v1_subset_1(k6_domain_1(X0,X1),X0)
    | ~ m1_subset_1(X1,X0)
    | v1_zfmisc_1(X0) ),
    inference(renaming,[status(thm)],[c_147])).

cnf(c_3354,plain,
    ( v1_subset_1(k6_domain_1(X0_48,X1_48),X0_48)
    | ~ m1_subset_1(X1_48,X0_48)
    | v1_zfmisc_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_148])).

cnf(c_4052,plain,
    ( v1_subset_1(k6_domain_1(X0_48,X1_48),X0_48) = iProver_top
    | m1_subset_1(X1_48,X0_48) != iProver_top
    | v1_zfmisc_1(X0_48) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3354])).

cnf(c_5092,plain,
    ( v1_subset_1(k2_tarski(sK2,sK2),u1_struct_0(sK1)) = iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4512,c_4052])).

cnf(c_26,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_27,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_28,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_77,plain,
    ( v2_struct_0(X0) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_79,plain,
    ( v2_struct_0(sK1) = iProver_top
    | l1_struct_0(sK1) != iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_77])).

cnf(c_82,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_84,plain,
    ( l1_pre_topc(sK1) != iProver_top
    | l1_struct_0(sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_82])).

cnf(c_3423,plain,
    ( m1_subset_1(X0_48,u1_struct_0(X0_47)) != iProver_top
    | m1_pre_topc(k1_tex_2(X0_47,X0_48),X0_47) = iProver_top
    | v2_struct_0(X0_47) = iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3363])).

cnf(c_3425,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(k1_tex_2(sK1,sK2),sK1) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3423])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k1_tex_2(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_3362,plain,
    ( ~ m1_subset_1(X0_48,u1_struct_0(X0_47))
    | v2_struct_0(X0_47)
    | ~ v2_struct_0(k1_tex_2(X0_47,X0_48))
    | ~ l1_pre_topc(X0_47) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_3426,plain,
    ( m1_subset_1(X0_48,u1_struct_0(X0_47)) != iProver_top
    | v2_struct_0(X0_47) = iProver_top
    | v2_struct_0(k1_tex_2(X0_47,X0_48)) != iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3362])).

cnf(c_3428,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | v2_struct_0(k1_tex_2(sK1,sK2)) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3426])).

cnf(c_17,plain,
    ( ~ v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X0) != u1_struct_0(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_3360,plain,
    ( ~ v1_tex_2(X0_47,X1_47)
    | ~ m1_pre_topc(X0_47,X1_47)
    | ~ l1_pre_topc(X1_47)
    | u1_struct_0(X0_47) != u1_struct_0(X1_47) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_4265,plain,
    ( ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1)
    | ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
    | ~ l1_pre_topc(sK1)
    | u1_struct_0(k1_tex_2(sK1,sK2)) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_3360])).

cnf(c_4266,plain,
    ( u1_struct_0(k1_tex_2(sK1,sK2)) != u1_struct_0(sK1)
    | v1_tex_2(k1_tex_2(sK1,sK2),sK1) != iProver_top
    | m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4265])).

cnf(c_2,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_3371,plain,
    ( ~ m1_pre_topc(X0_47,X1_47)
    | ~ l1_pre_topc(X1_47)
    | l1_pre_topc(X0_47) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_4404,plain,
    ( ~ m1_pre_topc(k1_tex_2(X0_47,X0_48),X1_47)
    | ~ l1_pre_topc(X1_47)
    | l1_pre_topc(k1_tex_2(X0_47,X0_48)) ),
    inference(instantiation,[status(thm)],[c_3371])).

cnf(c_4405,plain,
    ( m1_pre_topc(k1_tex_2(X0_47,X0_48),X1_47) != iProver_top
    | l1_pre_topc(X1_47) != iProver_top
    | l1_pre_topc(k1_tex_2(X0_47,X0_48)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4404])).

cnf(c_4407,plain,
    ( m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top
    | l1_pre_topc(k1_tex_2(sK1,sK2)) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4405])).

cnf(c_437,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_1,c_4])).

cnf(c_3351,plain,
    ( v2_struct_0(X0_47)
    | ~ l1_pre_topc(X0_47)
    | ~ v1_xboole_0(u1_struct_0(X0_47)) ),
    inference(subtyping,[status(esa)],[c_437])).

cnf(c_4414,plain,
    ( v2_struct_0(k1_tex_2(sK1,sK2))
    | ~ l1_pre_topc(k1_tex_2(sK1,sK2))
    | ~ v1_xboole_0(u1_struct_0(k1_tex_2(sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_3351])).

cnf(c_4415,plain,
    ( v2_struct_0(k1_tex_2(sK1,sK2)) = iProver_top
    | l1_pre_topc(k1_tex_2(sK1,sK2)) != iProver_top
    | v1_xboole_0(u1_struct_0(k1_tex_2(sK1,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4414])).

cnf(c_22,negated_conjecture,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_3358,negated_conjecture,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_4048,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) = iProver_top
    | v1_tex_2(k1_tex_2(sK1,sK2),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3358])).

cnf(c_4515,plain,
    ( v1_subset_1(k2_tarski(sK2,sK2),u1_struct_0(sK1)) = iProver_top
    | v1_tex_2(k1_tex_2(sK1,sK2),sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4512,c_4048])).

cnf(c_3376,plain,
    ( X0_48 != X1_48
    | X2_48 != X1_48
    | X2_48 = X0_48 ),
    theory(equality)).

cnf(c_4346,plain,
    ( u1_struct_0(k1_tex_2(sK1,sK2)) != X0_48
    | u1_struct_0(k1_tex_2(sK1,sK2)) = u1_struct_0(sK1)
    | u1_struct_0(sK1) != X0_48 ),
    inference(instantiation,[status(thm)],[c_3376])).

cnf(c_4437,plain,
    ( u1_struct_0(k1_tex_2(sK1,sK2)) != u1_struct_0(X0_47)
    | u1_struct_0(k1_tex_2(sK1,sK2)) = u1_struct_0(sK1)
    | u1_struct_0(sK1) != u1_struct_0(X0_47) ),
    inference(instantiation,[status(thm)],[c_4346])).

cnf(c_4547,plain,
    ( u1_struct_0(k1_tex_2(sK1,sK2)) != u1_struct_0(k1_tex_2(sK1,sK2))
    | u1_struct_0(k1_tex_2(sK1,sK2)) = u1_struct_0(sK1)
    | u1_struct_0(sK1) != u1_struct_0(k1_tex_2(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_4437])).

cnf(c_3375,plain,
    ( X0_48 = X0_48 ),
    theory(equality)).

cnf(c_4548,plain,
    ( u1_struct_0(k1_tex_2(sK1,sK2)) = u1_struct_0(k1_tex_2(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_3375])).

cnf(c_6,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_18,plain,
    ( ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | ~ v1_zfmisc_1(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_351,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ v1_zfmisc_1(X3)
    | X3 = X2
    | u1_struct_0(X0) != X2
    | u1_struct_0(X1) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_18])).

cnf(c_352,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(u1_struct_0(X0))
    | v1_xboole_0(u1_struct_0(X1))
    | ~ v1_zfmisc_1(u1_struct_0(X1))
    | u1_struct_0(X1) = u1_struct_0(X0) ),
    inference(unflattening,[status(thm)],[c_351])).

cnf(c_3353,plain,
    ( ~ m1_pre_topc(X0_47,X1_47)
    | ~ l1_pre_topc(X1_47)
    | v1_xboole_0(u1_struct_0(X0_47))
    | v1_xboole_0(u1_struct_0(X1_47))
    | ~ v1_zfmisc_1(u1_struct_0(X1_47))
    | u1_struct_0(X1_47) = u1_struct_0(X0_47) ),
    inference(subtyping,[status(esa)],[c_352])).

cnf(c_4438,plain,
    ( ~ m1_pre_topc(X0_47,sK1)
    | ~ l1_pre_topc(sK1)
    | v1_xboole_0(u1_struct_0(X0_47))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ v1_zfmisc_1(u1_struct_0(sK1))
    | u1_struct_0(sK1) = u1_struct_0(X0_47) ),
    inference(instantiation,[status(thm)],[c_3353])).

cnf(c_4720,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
    | ~ l1_pre_topc(sK1)
    | v1_xboole_0(u1_struct_0(k1_tex_2(sK1,sK2)))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ v1_zfmisc_1(u1_struct_0(sK1))
    | u1_struct_0(sK1) = u1_struct_0(k1_tex_2(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_4438])).

cnf(c_4721,plain,
    ( u1_struct_0(sK1) = u1_struct_0(k1_tex_2(sK1,sK2))
    | m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_xboole_0(u1_struct_0(k1_tex_2(sK1,sK2))) = iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) = iProver_top
    | v1_zfmisc_1(u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4720])).

cnf(c_5171,plain,
    ( v1_subset_1(k2_tarski(sK2,sK2),u1_struct_0(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5092,c_26,c_27,c_28,c_79,c_84,c_3425,c_3428,c_4266,c_4407,c_4415,c_4515,c_4547,c_4548,c_4721])).

cnf(c_21,negated_conjecture,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_3359,negated_conjecture,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_4047,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top
    | v1_tex_2(k1_tex_2(sK1,sK2),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3359])).

cnf(c_4516,plain,
    ( v1_subset_1(k2_tarski(sK2,sK2),u1_struct_0(sK1)) != iProver_top
    | v1_tex_2(k1_tex_2(sK1,sK2),sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4512,c_4047])).

cnf(c_5176,plain,
    ( v1_tex_2(k1_tex_2(sK1,sK2),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5171,c_4516])).

cnf(c_5456,plain,
    ( sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(k1_tex_2(sK1,sK2))
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4815,c_5176])).

cnf(c_4286,plain,
    ( v1_tex_2(k1_tex_2(X0_47,X0_48),X0_47)
    | ~ m1_pre_topc(k1_tex_2(X0_47,X0_48),X0_47)
    | ~ l1_pre_topc(X0_47)
    | sK0(X0_47,k1_tex_2(X0_47,X0_48)) = u1_struct_0(k1_tex_2(X0_47,X0_48)) ),
    inference(instantiation,[status(thm)],[c_3368])).

cnf(c_4287,plain,
    ( sK0(X0_47,k1_tex_2(X0_47,X0_48)) = u1_struct_0(k1_tex_2(X0_47,X0_48))
    | v1_tex_2(k1_tex_2(X0_47,X0_48),X0_47) = iProver_top
    | m1_pre_topc(k1_tex_2(X0_47,X0_48),X0_47) != iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4286])).

cnf(c_4289,plain,
    ( sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(k1_tex_2(sK1,sK2))
    | v1_tex_2(k1_tex_2(sK1,sK2),sK1) = iProver_top
    | m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4287])).

cnf(c_5557,plain,
    ( sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(k1_tex_2(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5456,c_26,c_27,c_28,c_79,c_84,c_3425,c_3428,c_4266,c_4289,c_4407,c_4415,c_4515,c_4516,c_4547,c_4548,c_4721,c_5092])).

cnf(c_9,plain,
    ( v1_tex_2(X0,X1)
    | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_3367,plain,
    ( v1_tex_2(X0_47,X1_47)
    | m1_subset_1(sK0(X1_47,X0_47),k1_zfmisc_1(u1_struct_0(X1_47)))
    | ~ m1_pre_topc(X0_47,X1_47)
    | ~ l1_pre_topc(X1_47) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_4039,plain,
    ( v1_tex_2(X0_47,X1_47) = iProver_top
    | m1_subset_1(sK0(X1_47,X0_47),k1_zfmisc_1(u1_struct_0(X1_47))) = iProver_top
    | m1_pre_topc(X0_47,X1_47) != iProver_top
    | l1_pre_topc(X1_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3367])).

cnf(c_11,plain,
    ( v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_3365,plain,
    ( v1_subset_1(X0_48,X1_48)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(X1_48))
    | X0_48 = X1_48 ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_4041,plain,
    ( X0_48 = X1_48
    | v1_subset_1(X0_48,X1_48) = iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(X1_48)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3365])).

cnf(c_4902,plain,
    ( sK0(X0_47,X1_47) = u1_struct_0(X0_47)
    | v1_subset_1(sK0(X0_47,X1_47),u1_struct_0(X0_47)) = iProver_top
    | v1_tex_2(X1_47,X0_47) = iProver_top
    | m1_pre_topc(X1_47,X0_47) != iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(superposition,[status(thm)],[c_4039,c_4041])).

cnf(c_7,plain,
    ( ~ v1_subset_1(sK0(X0,X1),u1_struct_0(X0))
    | v1_tex_2(X1,X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_3369,plain,
    ( ~ v1_subset_1(sK0(X0_47,X1_47),u1_struct_0(X0_47))
    | v1_tex_2(X1_47,X0_47)
    | ~ m1_pre_topc(X1_47,X0_47)
    | ~ l1_pre_topc(X0_47) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_3413,plain,
    ( v1_subset_1(sK0(X0_47,X1_47),u1_struct_0(X0_47)) != iProver_top
    | v1_tex_2(X1_47,X0_47) = iProver_top
    | m1_pre_topc(X1_47,X0_47) != iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3369])).

cnf(c_5325,plain,
    ( sK0(X0_47,X1_47) = u1_struct_0(X0_47)
    | v1_tex_2(X1_47,X0_47) = iProver_top
    | m1_pre_topc(X1_47,X0_47) != iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4902,c_3413])).

cnf(c_5333,plain,
    ( sK0(X0_47,k1_tex_2(X0_47,X0_48)) = u1_struct_0(X0_47)
    | v1_tex_2(k1_tex_2(X0_47,X0_48),X0_47) = iProver_top
    | m1_subset_1(X0_48,u1_struct_0(X0_47)) != iProver_top
    | v2_struct_0(X0_47) = iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(superposition,[status(thm)],[c_4043,c_5325])).

cnf(c_5448,plain,
    ( sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(sK1)
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5333,c_5176])).

cnf(c_4281,plain,
    ( v1_tex_2(k1_tex_2(X0_47,X0_48),X0_47)
    | m1_subset_1(sK0(X0_47,k1_tex_2(X0_47,X0_48)),k1_zfmisc_1(u1_struct_0(X0_47)))
    | ~ m1_pre_topc(k1_tex_2(X0_47,X0_48),X0_47)
    | ~ l1_pre_topc(X0_47) ),
    inference(instantiation,[status(thm)],[c_3367])).

cnf(c_4282,plain,
    ( v1_tex_2(k1_tex_2(X0_47,X0_48),X0_47) = iProver_top
    | m1_subset_1(sK0(X0_47,k1_tex_2(X0_47,X0_48)),k1_zfmisc_1(u1_struct_0(X0_47))) = iProver_top
    | m1_pre_topc(k1_tex_2(X0_47,X0_48),X0_47) != iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4281])).

cnf(c_4284,plain,
    ( v1_tex_2(k1_tex_2(sK1,sK2),sK1) = iProver_top
    | m1_subset_1(sK0(sK1,k1_tex_2(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4282])).

cnf(c_4291,plain,
    ( ~ v1_subset_1(sK0(X0_47,k1_tex_2(X0_47,X0_48)),u1_struct_0(X0_47))
    | v1_tex_2(k1_tex_2(X0_47,X0_48),X0_47)
    | ~ m1_pre_topc(k1_tex_2(X0_47,X0_48),X0_47)
    | ~ l1_pre_topc(X0_47) ),
    inference(instantiation,[status(thm)],[c_3369])).

cnf(c_4292,plain,
    ( v1_subset_1(sK0(X0_47,k1_tex_2(X0_47,X0_48)),u1_struct_0(X0_47)) != iProver_top
    | v1_tex_2(k1_tex_2(X0_47,X0_48),X0_47) = iProver_top
    | m1_pre_topc(k1_tex_2(X0_47,X0_48),X0_47) != iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4291])).

cnf(c_4294,plain,
    ( v1_subset_1(sK0(sK1,k1_tex_2(sK1,sK2)),u1_struct_0(sK1)) != iProver_top
    | v1_tex_2(k1_tex_2(sK1,sK2),sK1) = iProver_top
    | m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4292])).

cnf(c_4355,plain,
    ( v1_subset_1(X0_48,u1_struct_0(sK1))
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK1)))
    | X0_48 = u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_3365])).

cnf(c_4989,plain,
    ( v1_subset_1(sK0(sK1,k1_tex_2(sK1,X0_48)),u1_struct_0(sK1))
    | ~ m1_subset_1(sK0(sK1,k1_tex_2(sK1,X0_48)),k1_zfmisc_1(u1_struct_0(sK1)))
    | sK0(sK1,k1_tex_2(sK1,X0_48)) = u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_4355])).

cnf(c_4992,plain,
    ( sK0(sK1,k1_tex_2(sK1,X0_48)) = u1_struct_0(sK1)
    | v1_subset_1(sK0(sK1,k1_tex_2(sK1,X0_48)),u1_struct_0(sK1)) = iProver_top
    | m1_subset_1(sK0(sK1,k1_tex_2(sK1,X0_48)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4989])).

cnf(c_4994,plain,
    ( sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(sK1)
    | v1_subset_1(sK0(sK1,k1_tex_2(sK1,sK2)),u1_struct_0(sK1)) = iProver_top
    | m1_subset_1(sK0(sK1,k1_tex_2(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4992])).

cnf(c_5533,plain,
    ( sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5448,c_26,c_27,c_28,c_79,c_84,c_3425,c_3428,c_4266,c_4284,c_4294,c_4407,c_4415,c_4515,c_4516,c_4547,c_4548,c_4721,c_4994,c_5092])).

cnf(c_5559,plain,
    ( u1_struct_0(k1_tex_2(sK1,sK2)) = u1_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_5557,c_5533])).

cnf(c_20,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v7_struct_0(X0)
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_417,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v7_struct_0(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_1,c_20])).

cnf(c_3352,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0_47),X0_48),u1_struct_0(X0_47))
    | ~ m1_subset_1(X0_48,u1_struct_0(X0_47))
    | ~ v7_struct_0(X0_47)
    | v2_struct_0(X0_47)
    | ~ l1_pre_topc(X0_47) ),
    inference(subtyping,[status(esa)],[c_417])).

cnf(c_4054,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(X0_47),X0_48),u1_struct_0(X0_47)) != iProver_top
    | m1_subset_1(X0_48,u1_struct_0(X0_47)) != iProver_top
    | v7_struct_0(X0_47) != iProver_top
    | v2_struct_0(X0_47) = iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3352])).

cnf(c_5562,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),X0_48),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_48,u1_struct_0(k1_tex_2(sK1,sK2))) != iProver_top
    | v7_struct_0(k1_tex_2(sK1,sK2)) != iProver_top
    | v2_struct_0(k1_tex_2(sK1,sK2)) = iProver_top
    | l1_pre_topc(k1_tex_2(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5559,c_4054])).

cnf(c_5656,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),X0_48),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_48,u1_struct_0(sK1)) != iProver_top
    | v7_struct_0(k1_tex_2(sK1,sK2)) != iProver_top
    | v2_struct_0(k1_tex_2(sK1,sK2)) = iProver_top
    | l1_pre_topc(k1_tex_2(sK1,sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5562,c_5559])).

cnf(c_5695,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | v7_struct_0(k1_tex_2(sK1,sK2)) != iProver_top
    | v2_struct_0(k1_tex_2(sK1,sK2)) = iProver_top
    | l1_pre_topc(k1_tex_2(sK1,sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5656])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v7_struct_0(k1_tex_2(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_3361,plain,
    ( ~ m1_subset_1(X0_48,u1_struct_0(X0_47))
    | v7_struct_0(k1_tex_2(X0_47,X0_48))
    | v2_struct_0(X0_47)
    | ~ l1_pre_topc(X0_47) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_3429,plain,
    ( m1_subset_1(X0_48,u1_struct_0(X0_47)) != iProver_top
    | v7_struct_0(k1_tex_2(X0_47,X0_48)) = iProver_top
    | v2_struct_0(X0_47) = iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3361])).

cnf(c_3431,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | v7_struct_0(k1_tex_2(sK1,sK2)) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3429])).

cnf(c_29,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) = iProver_top
    | v1_tex_2(k1_tex_2(sK1,sK2),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5695,c_5171,c_4516,c_4407,c_3431,c_3428,c_3425,c_29,c_28,c_27,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:25:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.22/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.00  
% 2.22/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.22/1.00  
% 2.22/1.00  ------  iProver source info
% 2.22/1.00  
% 2.22/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.22/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.22/1.00  git: non_committed_changes: false
% 2.22/1.00  git: last_make_outside_of_git: false
% 2.22/1.00  
% 2.22/1.00  ------ 
% 2.22/1.00  
% 2.22/1.00  ------ Input Options
% 2.22/1.00  
% 2.22/1.00  --out_options                           all
% 2.22/1.00  --tptp_safe_out                         true
% 2.22/1.00  --problem_path                          ""
% 2.22/1.00  --include_path                          ""
% 2.22/1.00  --clausifier                            res/vclausify_rel
% 2.22/1.00  --clausifier_options                    --mode clausify
% 2.22/1.00  --stdin                                 false
% 2.22/1.00  --stats_out                             all
% 2.22/1.00  
% 2.22/1.00  ------ General Options
% 2.22/1.00  
% 2.22/1.00  --fof                                   false
% 2.22/1.00  --time_out_real                         305.
% 2.22/1.00  --time_out_virtual                      -1.
% 2.22/1.00  --symbol_type_check                     false
% 2.22/1.00  --clausify_out                          false
% 2.22/1.00  --sig_cnt_out                           false
% 2.22/1.00  --trig_cnt_out                          false
% 2.22/1.00  --trig_cnt_out_tolerance                1.
% 2.22/1.00  --trig_cnt_out_sk_spl                   false
% 2.22/1.00  --abstr_cl_out                          false
% 2.22/1.00  
% 2.22/1.00  ------ Global Options
% 2.22/1.00  
% 2.22/1.00  --schedule                              default
% 2.22/1.00  --add_important_lit                     false
% 2.22/1.00  --prop_solver_per_cl                    1000
% 2.22/1.00  --min_unsat_core                        false
% 2.22/1.00  --soft_assumptions                      false
% 2.22/1.00  --soft_lemma_size                       3
% 2.22/1.00  --prop_impl_unit_size                   0
% 2.22/1.00  --prop_impl_unit                        []
% 2.22/1.00  --share_sel_clauses                     true
% 2.22/1.00  --reset_solvers                         false
% 2.22/1.00  --bc_imp_inh                            [conj_cone]
% 2.22/1.00  --conj_cone_tolerance                   3.
% 2.22/1.00  --extra_neg_conj                        none
% 2.22/1.00  --large_theory_mode                     true
% 2.22/1.00  --prolific_symb_bound                   200
% 2.22/1.00  --lt_threshold                          2000
% 2.22/1.00  --clause_weak_htbl                      true
% 2.22/1.00  --gc_record_bc_elim                     false
% 2.22/1.00  
% 2.22/1.00  ------ Preprocessing Options
% 2.22/1.00  
% 2.22/1.00  --preprocessing_flag                    true
% 2.22/1.00  --time_out_prep_mult                    0.1
% 2.22/1.00  --splitting_mode                        input
% 2.22/1.00  --splitting_grd                         true
% 2.22/1.00  --splitting_cvd                         false
% 2.22/1.00  --splitting_cvd_svl                     false
% 2.22/1.00  --splitting_nvd                         32
% 2.22/1.00  --sub_typing                            true
% 2.22/1.00  --prep_gs_sim                           true
% 2.22/1.00  --prep_unflatten                        true
% 2.22/1.00  --prep_res_sim                          true
% 2.22/1.00  --prep_upred                            true
% 2.22/1.00  --prep_sem_filter                       exhaustive
% 2.22/1.00  --prep_sem_filter_out                   false
% 2.22/1.00  --pred_elim                             true
% 2.22/1.00  --res_sim_input                         true
% 2.22/1.00  --eq_ax_congr_red                       true
% 2.22/1.00  --pure_diseq_elim                       true
% 2.22/1.00  --brand_transform                       false
% 2.22/1.00  --non_eq_to_eq                          false
% 2.22/1.00  --prep_def_merge                        true
% 2.22/1.00  --prep_def_merge_prop_impl              false
% 2.22/1.00  --prep_def_merge_mbd                    true
% 2.22/1.00  --prep_def_merge_tr_red                 false
% 2.22/1.00  --prep_def_merge_tr_cl                  false
% 2.22/1.00  --smt_preprocessing                     true
% 2.22/1.00  --smt_ac_axioms                         fast
% 2.22/1.00  --preprocessed_out                      false
% 2.22/1.00  --preprocessed_stats                    false
% 2.22/1.00  
% 2.22/1.00  ------ Abstraction refinement Options
% 2.22/1.00  
% 2.22/1.00  --abstr_ref                             []
% 2.22/1.00  --abstr_ref_prep                        false
% 2.22/1.00  --abstr_ref_until_sat                   false
% 2.22/1.00  --abstr_ref_sig_restrict                funpre
% 2.22/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.22/1.00  --abstr_ref_under                       []
% 2.22/1.00  
% 2.22/1.00  ------ SAT Options
% 2.22/1.00  
% 2.22/1.00  --sat_mode                              false
% 2.22/1.00  --sat_fm_restart_options                ""
% 2.22/1.00  --sat_gr_def                            false
% 2.22/1.00  --sat_epr_types                         true
% 2.22/1.00  --sat_non_cyclic_types                  false
% 2.22/1.00  --sat_finite_models                     false
% 2.22/1.00  --sat_fm_lemmas                         false
% 2.22/1.00  --sat_fm_prep                           false
% 2.22/1.00  --sat_fm_uc_incr                        true
% 2.22/1.00  --sat_out_model                         small
% 2.22/1.00  --sat_out_clauses                       false
% 2.22/1.00  
% 2.22/1.00  ------ QBF Options
% 2.22/1.00  
% 2.22/1.00  --qbf_mode                              false
% 2.22/1.00  --qbf_elim_univ                         false
% 2.22/1.00  --qbf_dom_inst                          none
% 2.22/1.00  --qbf_dom_pre_inst                      false
% 2.22/1.00  --qbf_sk_in                             false
% 2.22/1.00  --qbf_pred_elim                         true
% 2.22/1.00  --qbf_split                             512
% 2.22/1.00  
% 2.22/1.00  ------ BMC1 Options
% 2.22/1.00  
% 2.22/1.00  --bmc1_incremental                      false
% 2.22/1.00  --bmc1_axioms                           reachable_all
% 2.22/1.00  --bmc1_min_bound                        0
% 2.22/1.00  --bmc1_max_bound                        -1
% 2.22/1.00  --bmc1_max_bound_default                -1
% 2.22/1.00  --bmc1_symbol_reachability              true
% 2.22/1.00  --bmc1_property_lemmas                  false
% 2.22/1.00  --bmc1_k_induction                      false
% 2.22/1.00  --bmc1_non_equiv_states                 false
% 2.22/1.00  --bmc1_deadlock                         false
% 2.22/1.00  --bmc1_ucm                              false
% 2.22/1.00  --bmc1_add_unsat_core                   none
% 2.22/1.00  --bmc1_unsat_core_children              false
% 2.22/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.22/1.00  --bmc1_out_stat                         full
% 2.22/1.00  --bmc1_ground_init                      false
% 2.22/1.00  --bmc1_pre_inst_next_state              false
% 2.22/1.00  --bmc1_pre_inst_state                   false
% 2.22/1.00  --bmc1_pre_inst_reach_state             false
% 2.22/1.00  --bmc1_out_unsat_core                   false
% 2.22/1.00  --bmc1_aig_witness_out                  false
% 2.22/1.00  --bmc1_verbose                          false
% 2.22/1.00  --bmc1_dump_clauses_tptp                false
% 2.22/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.22/1.00  --bmc1_dump_file                        -
% 2.22/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.22/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.22/1.00  --bmc1_ucm_extend_mode                  1
% 2.22/1.00  --bmc1_ucm_init_mode                    2
% 2.22/1.00  --bmc1_ucm_cone_mode                    none
% 2.22/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.22/1.00  --bmc1_ucm_relax_model                  4
% 2.22/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.22/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.22/1.00  --bmc1_ucm_layered_model                none
% 2.22/1.00  --bmc1_ucm_max_lemma_size               10
% 2.22/1.00  
% 2.22/1.00  ------ AIG Options
% 2.22/1.00  
% 2.22/1.00  --aig_mode                              false
% 2.22/1.00  
% 2.22/1.00  ------ Instantiation Options
% 2.22/1.00  
% 2.22/1.00  --instantiation_flag                    true
% 2.22/1.00  --inst_sos_flag                         false
% 2.22/1.00  --inst_sos_phase                        true
% 2.22/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.22/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.22/1.00  --inst_lit_sel_side                     num_symb
% 2.22/1.00  --inst_solver_per_active                1400
% 2.22/1.00  --inst_solver_calls_frac                1.
% 2.22/1.00  --inst_passive_queue_type               priority_queues
% 2.22/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.22/1.00  --inst_passive_queues_freq              [25;2]
% 2.22/1.00  --inst_dismatching                      true
% 2.22/1.00  --inst_eager_unprocessed_to_passive     true
% 2.22/1.00  --inst_prop_sim_given                   true
% 2.22/1.00  --inst_prop_sim_new                     false
% 2.22/1.00  --inst_subs_new                         false
% 2.22/1.00  --inst_eq_res_simp                      false
% 2.22/1.00  --inst_subs_given                       false
% 2.22/1.00  --inst_orphan_elimination               true
% 2.22/1.00  --inst_learning_loop_flag               true
% 2.22/1.00  --inst_learning_start                   3000
% 2.22/1.00  --inst_learning_factor                  2
% 2.22/1.00  --inst_start_prop_sim_after_learn       3
% 2.22/1.00  --inst_sel_renew                        solver
% 2.22/1.00  --inst_lit_activity_flag                true
% 2.22/1.00  --inst_restr_to_given                   false
% 2.22/1.00  --inst_activity_threshold               500
% 2.22/1.00  --inst_out_proof                        true
% 2.22/1.00  
% 2.22/1.00  ------ Resolution Options
% 2.22/1.00  
% 2.22/1.00  --resolution_flag                       true
% 2.22/1.00  --res_lit_sel                           adaptive
% 2.22/1.00  --res_lit_sel_side                      none
% 2.22/1.00  --res_ordering                          kbo
% 2.22/1.00  --res_to_prop_solver                    active
% 2.22/1.00  --res_prop_simpl_new                    false
% 2.22/1.00  --res_prop_simpl_given                  true
% 2.22/1.00  --res_passive_queue_type                priority_queues
% 2.22/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.22/1.00  --res_passive_queues_freq               [15;5]
% 2.22/1.00  --res_forward_subs                      full
% 2.22/1.00  --res_backward_subs                     full
% 2.22/1.00  --res_forward_subs_resolution           true
% 2.22/1.00  --res_backward_subs_resolution          true
% 2.22/1.00  --res_orphan_elimination                true
% 2.22/1.00  --res_time_limit                        2.
% 2.22/1.00  --res_out_proof                         true
% 2.22/1.00  
% 2.22/1.00  ------ Superposition Options
% 2.22/1.00  
% 2.22/1.00  --superposition_flag                    true
% 2.22/1.00  --sup_passive_queue_type                priority_queues
% 2.22/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.22/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.22/1.00  --demod_completeness_check              fast
% 2.22/1.00  --demod_use_ground                      true
% 2.22/1.00  --sup_to_prop_solver                    passive
% 2.22/1.00  --sup_prop_simpl_new                    true
% 2.22/1.00  --sup_prop_simpl_given                  true
% 2.22/1.00  --sup_fun_splitting                     false
% 2.22/1.00  --sup_smt_interval                      50000
% 2.22/1.00  
% 2.22/1.00  ------ Superposition Simplification Setup
% 2.22/1.00  
% 2.22/1.00  --sup_indices_passive                   []
% 2.22/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.22/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.22/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.22/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.22/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.22/1.00  --sup_full_bw                           [BwDemod]
% 2.22/1.00  --sup_immed_triv                        [TrivRules]
% 2.22/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.22/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.22/1.00  --sup_immed_bw_main                     []
% 2.22/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.22/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.22/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.22/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.22/1.00  
% 2.22/1.00  ------ Combination Options
% 2.22/1.00  
% 2.22/1.00  --comb_res_mult                         3
% 2.22/1.00  --comb_sup_mult                         2
% 2.22/1.00  --comb_inst_mult                        10
% 2.22/1.00  
% 2.22/1.00  ------ Debug Options
% 2.22/1.00  
% 2.22/1.00  --dbg_backtrace                         false
% 2.22/1.00  --dbg_dump_prop_clauses                 false
% 2.22/1.00  --dbg_dump_prop_clauses_file            -
% 2.22/1.00  --dbg_out_stat                          false
% 2.22/1.00  ------ Parsing...
% 2.22/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.22/1.00  
% 2.22/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.22/1.00  
% 2.22/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.22/1.00  
% 2.22/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.22/1.00  ------ Proving...
% 2.22/1.00  ------ Problem Properties 
% 2.22/1.00  
% 2.22/1.00  
% 2.22/1.00  clauses                                 23
% 2.22/1.00  conjectures                             5
% 2.22/1.00  EPR                                     4
% 2.22/1.00  Horn                                    14
% 2.22/1.00  unary                                   3
% 2.22/1.00  binary                                  4
% 2.22/1.00  lits                                    73
% 2.22/1.00  lits eq                                 5
% 2.22/1.00  fd_pure                                 0
% 2.22/1.00  fd_pseudo                               0
% 2.22/1.00  fd_cond                                 0
% 2.22/1.00  fd_pseudo_cond                          1
% 2.22/1.00  AC symbols                              0
% 2.22/1.00  
% 2.22/1.00  ------ Schedule dynamic 5 is on 
% 2.22/1.00  
% 2.22/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.22/1.00  
% 2.22/1.00  
% 2.22/1.00  ------ 
% 2.22/1.00  Current options:
% 2.22/1.00  ------ 
% 2.22/1.00  
% 2.22/1.00  ------ Input Options
% 2.22/1.00  
% 2.22/1.00  --out_options                           all
% 2.22/1.00  --tptp_safe_out                         true
% 2.22/1.00  --problem_path                          ""
% 2.22/1.00  --include_path                          ""
% 2.22/1.00  --clausifier                            res/vclausify_rel
% 2.22/1.00  --clausifier_options                    --mode clausify
% 2.22/1.00  --stdin                                 false
% 2.22/1.00  --stats_out                             all
% 2.22/1.00  
% 2.22/1.00  ------ General Options
% 2.22/1.00  
% 2.22/1.00  --fof                                   false
% 2.22/1.00  --time_out_real                         305.
% 2.22/1.00  --time_out_virtual                      -1.
% 2.22/1.00  --symbol_type_check                     false
% 2.22/1.00  --clausify_out                          false
% 2.22/1.00  --sig_cnt_out                           false
% 2.22/1.00  --trig_cnt_out                          false
% 2.22/1.00  --trig_cnt_out_tolerance                1.
% 2.22/1.00  --trig_cnt_out_sk_spl                   false
% 2.22/1.00  --abstr_cl_out                          false
% 2.22/1.00  
% 2.22/1.00  ------ Global Options
% 2.22/1.00  
% 2.22/1.00  --schedule                              default
% 2.22/1.00  --add_important_lit                     false
% 2.22/1.00  --prop_solver_per_cl                    1000
% 2.22/1.00  --min_unsat_core                        false
% 2.22/1.00  --soft_assumptions                      false
% 2.22/1.00  --soft_lemma_size                       3
% 2.22/1.00  --prop_impl_unit_size                   0
% 2.22/1.00  --prop_impl_unit                        []
% 2.22/1.00  --share_sel_clauses                     true
% 2.22/1.00  --reset_solvers                         false
% 2.22/1.00  --bc_imp_inh                            [conj_cone]
% 2.22/1.00  --conj_cone_tolerance                   3.
% 2.22/1.00  --extra_neg_conj                        none
% 2.22/1.00  --large_theory_mode                     true
% 2.22/1.00  --prolific_symb_bound                   200
% 2.22/1.00  --lt_threshold                          2000
% 2.22/1.00  --clause_weak_htbl                      true
% 2.22/1.00  --gc_record_bc_elim                     false
% 2.22/1.00  
% 2.22/1.00  ------ Preprocessing Options
% 2.22/1.00  
% 2.22/1.00  --preprocessing_flag                    true
% 2.22/1.00  --time_out_prep_mult                    0.1
% 2.22/1.00  --splitting_mode                        input
% 2.22/1.00  --splitting_grd                         true
% 2.22/1.00  --splitting_cvd                         false
% 2.22/1.00  --splitting_cvd_svl                     false
% 2.22/1.00  --splitting_nvd                         32
% 2.22/1.00  --sub_typing                            true
% 2.22/1.00  --prep_gs_sim                           true
% 2.22/1.00  --prep_unflatten                        true
% 2.22/1.00  --prep_res_sim                          true
% 2.22/1.00  --prep_upred                            true
% 2.22/1.00  --prep_sem_filter                       exhaustive
% 2.22/1.00  --prep_sem_filter_out                   false
% 2.22/1.00  --pred_elim                             true
% 2.22/1.00  --res_sim_input                         true
% 2.22/1.00  --eq_ax_congr_red                       true
% 2.22/1.00  --pure_diseq_elim                       true
% 2.22/1.00  --brand_transform                       false
% 2.22/1.00  --non_eq_to_eq                          false
% 2.22/1.00  --prep_def_merge                        true
% 2.22/1.00  --prep_def_merge_prop_impl              false
% 2.22/1.00  --prep_def_merge_mbd                    true
% 2.22/1.00  --prep_def_merge_tr_red                 false
% 2.22/1.00  --prep_def_merge_tr_cl                  false
% 2.22/1.00  --smt_preprocessing                     true
% 2.22/1.00  --smt_ac_axioms                         fast
% 2.22/1.00  --preprocessed_out                      false
% 2.22/1.00  --preprocessed_stats                    false
% 2.22/1.00  
% 2.22/1.00  ------ Abstraction refinement Options
% 2.22/1.00  
% 2.22/1.00  --abstr_ref                             []
% 2.22/1.00  --abstr_ref_prep                        false
% 2.22/1.00  --abstr_ref_until_sat                   false
% 2.22/1.00  --abstr_ref_sig_restrict                funpre
% 2.22/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.22/1.00  --abstr_ref_under                       []
% 2.22/1.00  
% 2.22/1.00  ------ SAT Options
% 2.22/1.00  
% 2.22/1.00  --sat_mode                              false
% 2.22/1.00  --sat_fm_restart_options                ""
% 2.22/1.00  --sat_gr_def                            false
% 2.22/1.00  --sat_epr_types                         true
% 2.22/1.00  --sat_non_cyclic_types                  false
% 2.22/1.00  --sat_finite_models                     false
% 2.22/1.00  --sat_fm_lemmas                         false
% 2.22/1.00  --sat_fm_prep                           false
% 2.22/1.00  --sat_fm_uc_incr                        true
% 2.22/1.00  --sat_out_model                         small
% 2.22/1.00  --sat_out_clauses                       false
% 2.22/1.00  
% 2.22/1.00  ------ QBF Options
% 2.22/1.00  
% 2.22/1.00  --qbf_mode                              false
% 2.22/1.00  --qbf_elim_univ                         false
% 2.22/1.00  --qbf_dom_inst                          none
% 2.22/1.00  --qbf_dom_pre_inst                      false
% 2.22/1.00  --qbf_sk_in                             false
% 2.22/1.00  --qbf_pred_elim                         true
% 2.22/1.00  --qbf_split                             512
% 2.22/1.00  
% 2.22/1.00  ------ BMC1 Options
% 2.22/1.00  
% 2.22/1.00  --bmc1_incremental                      false
% 2.22/1.00  --bmc1_axioms                           reachable_all
% 2.22/1.00  --bmc1_min_bound                        0
% 2.22/1.00  --bmc1_max_bound                        -1
% 2.22/1.00  --bmc1_max_bound_default                -1
% 2.22/1.00  --bmc1_symbol_reachability              true
% 2.22/1.00  --bmc1_property_lemmas                  false
% 2.22/1.00  --bmc1_k_induction                      false
% 2.22/1.00  --bmc1_non_equiv_states                 false
% 2.22/1.00  --bmc1_deadlock                         false
% 2.22/1.00  --bmc1_ucm                              false
% 2.22/1.00  --bmc1_add_unsat_core                   none
% 2.22/1.00  --bmc1_unsat_core_children              false
% 2.22/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.22/1.00  --bmc1_out_stat                         full
% 2.22/1.00  --bmc1_ground_init                      false
% 2.22/1.00  --bmc1_pre_inst_next_state              false
% 2.22/1.00  --bmc1_pre_inst_state                   false
% 2.22/1.00  --bmc1_pre_inst_reach_state             false
% 2.22/1.00  --bmc1_out_unsat_core                   false
% 2.22/1.00  --bmc1_aig_witness_out                  false
% 2.22/1.00  --bmc1_verbose                          false
% 2.22/1.00  --bmc1_dump_clauses_tptp                false
% 2.22/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.22/1.00  --bmc1_dump_file                        -
% 2.22/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.22/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.22/1.00  --bmc1_ucm_extend_mode                  1
% 2.22/1.00  --bmc1_ucm_init_mode                    2
% 2.22/1.00  --bmc1_ucm_cone_mode                    none
% 2.22/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.22/1.00  --bmc1_ucm_relax_model                  4
% 2.22/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.22/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.22/1.00  --bmc1_ucm_layered_model                none
% 2.22/1.00  --bmc1_ucm_max_lemma_size               10
% 2.22/1.00  
% 2.22/1.00  ------ AIG Options
% 2.22/1.00  
% 2.22/1.00  --aig_mode                              false
% 2.22/1.00  
% 2.22/1.00  ------ Instantiation Options
% 2.22/1.00  
% 2.22/1.00  --instantiation_flag                    true
% 2.22/1.00  --inst_sos_flag                         false
% 2.22/1.00  --inst_sos_phase                        true
% 2.22/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.22/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.22/1.00  --inst_lit_sel_side                     none
% 2.22/1.00  --inst_solver_per_active                1400
% 2.22/1.00  --inst_solver_calls_frac                1.
% 2.22/1.00  --inst_passive_queue_type               priority_queues
% 2.22/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.22/1.00  --inst_passive_queues_freq              [25;2]
% 2.22/1.00  --inst_dismatching                      true
% 2.22/1.00  --inst_eager_unprocessed_to_passive     true
% 2.22/1.00  --inst_prop_sim_given                   true
% 2.22/1.00  --inst_prop_sim_new                     false
% 2.22/1.00  --inst_subs_new                         false
% 2.22/1.00  --inst_eq_res_simp                      false
% 2.22/1.00  --inst_subs_given                       false
% 2.22/1.00  --inst_orphan_elimination               true
% 2.22/1.00  --inst_learning_loop_flag               true
% 2.22/1.00  --inst_learning_start                   3000
% 2.22/1.00  --inst_learning_factor                  2
% 2.22/1.00  --inst_start_prop_sim_after_learn       3
% 2.22/1.00  --inst_sel_renew                        solver
% 2.22/1.00  --inst_lit_activity_flag                true
% 2.22/1.00  --inst_restr_to_given                   false
% 2.22/1.00  --inst_activity_threshold               500
% 2.22/1.00  --inst_out_proof                        true
% 2.22/1.00  
% 2.22/1.00  ------ Resolution Options
% 2.22/1.00  
% 2.22/1.00  --resolution_flag                       false
% 2.22/1.00  --res_lit_sel                           adaptive
% 2.22/1.00  --res_lit_sel_side                      none
% 2.22/1.00  --res_ordering                          kbo
% 2.22/1.00  --res_to_prop_solver                    active
% 2.22/1.00  --res_prop_simpl_new                    false
% 2.22/1.00  --res_prop_simpl_given                  true
% 2.22/1.00  --res_passive_queue_type                priority_queues
% 2.22/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.22/1.00  --res_passive_queues_freq               [15;5]
% 2.22/1.00  --res_forward_subs                      full
% 2.22/1.00  --res_backward_subs                     full
% 2.22/1.00  --res_forward_subs_resolution           true
% 2.22/1.00  --res_backward_subs_resolution          true
% 2.22/1.00  --res_orphan_elimination                true
% 2.22/1.00  --res_time_limit                        2.
% 2.22/1.00  --res_out_proof                         true
% 2.22/1.00  
% 2.22/1.00  ------ Superposition Options
% 2.22/1.00  
% 2.22/1.00  --superposition_flag                    true
% 2.22/1.00  --sup_passive_queue_type                priority_queues
% 2.22/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.22/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.22/1.00  --demod_completeness_check              fast
% 2.22/1.00  --demod_use_ground                      true
% 2.22/1.00  --sup_to_prop_solver                    passive
% 2.22/1.00  --sup_prop_simpl_new                    true
% 2.22/1.00  --sup_prop_simpl_given                  true
% 2.22/1.00  --sup_fun_splitting                     false
% 2.22/1.00  --sup_smt_interval                      50000
% 2.22/1.00  
% 2.22/1.00  ------ Superposition Simplification Setup
% 2.22/1.00  
% 2.22/1.00  --sup_indices_passive                   []
% 2.22/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.22/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.22/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.22/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.22/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.22/1.00  --sup_full_bw                           [BwDemod]
% 2.22/1.00  --sup_immed_triv                        [TrivRules]
% 2.22/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.22/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.22/1.00  --sup_immed_bw_main                     []
% 2.22/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.22/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.22/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.22/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.22/1.00  
% 2.22/1.00  ------ Combination Options
% 2.22/1.00  
% 2.22/1.00  --comb_res_mult                         3
% 2.22/1.00  --comb_sup_mult                         2
% 2.22/1.00  --comb_inst_mult                        10
% 2.22/1.00  
% 2.22/1.00  ------ Debug Options
% 2.22/1.00  
% 2.22/1.00  --dbg_backtrace                         false
% 2.22/1.00  --dbg_dump_prop_clauses                 false
% 2.22/1.00  --dbg_dump_prop_clauses_file            -
% 2.22/1.00  --dbg_out_stat                          false
% 2.22/1.00  
% 2.22/1.00  
% 2.22/1.00  
% 2.22/1.00  
% 2.22/1.00  ------ Proving...
% 2.22/1.00  
% 2.22/1.00  
% 2.22/1.00  % SZS status Theorem for theBenchmark.p
% 2.22/1.00  
% 2.22/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.22/1.00  
% 2.22/1.00  fof(f11,axiom,(
% 2.22/1.00    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 2.22/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.22/1.00  
% 2.22/1.00  fof(f20,plain,(
% 2.22/1.00    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 2.22/1.00    inference(pure_predicate_removal,[],[f11])).
% 2.22/1.00  
% 2.22/1.00  fof(f34,plain,(
% 2.22/1.00    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.22/1.00    inference(ennf_transformation,[],[f20])).
% 2.22/1.00  
% 2.22/1.00  fof(f35,plain,(
% 2.22/1.00    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.22/1.00    inference(flattening,[],[f34])).
% 2.22/1.00  
% 2.22/1.00  fof(f73,plain,(
% 2.22/1.00    ( ! [X0,X1] : (m1_pre_topc(k1_tex_2(X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.22/1.00    inference(cnf_transformation,[],[f35])).
% 2.22/1.00  
% 2.22/1.00  fof(f9,axiom,(
% 2.22/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v1_subset_1(X2,u1_struct_0(X0)))))))),
% 2.22/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.22/1.00  
% 2.22/1.00  fof(f31,plain,(
% 2.22/1.00    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : ((v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.22/1.00    inference(ennf_transformation,[],[f9])).
% 2.22/1.00  
% 2.22/1.00  fof(f32,plain,(
% 2.22/1.00    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.22/1.00    inference(flattening,[],[f31])).
% 2.22/1.00  
% 2.22/1.00  fof(f48,plain,(
% 2.22/1.00    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.22/1.00    inference(nnf_transformation,[],[f32])).
% 2.22/1.00  
% 2.22/1.00  fof(f49,plain,(
% 2.22/1.00    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.22/1.00    inference(rectify,[],[f48])).
% 2.22/1.00  
% 2.22/1.00  fof(f50,plain,(
% 2.22/1.00    ! [X1,X0] : (? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_subset_1(sK0(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK0(X0,X1) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.22/1.00    introduced(choice_axiom,[])).
% 2.22/1.00  
% 2.22/1.00  fof(f51,plain,(
% 2.22/1.00    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | (~v1_subset_1(sK0(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK0(X0,X1) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.22/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f49,f50])).
% 2.22/1.00  
% 2.22/1.00  fof(f68,plain,(
% 2.22/1.00    ( ! [X0,X1] : (v1_tex_2(X1,X0) | u1_struct_0(X1) = sK0(X0,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.22/1.00    inference(cnf_transformation,[],[f51])).
% 2.22/1.00  
% 2.22/1.00  fof(f17,conjecture,(
% 2.22/1.00    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 2.22/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.22/1.00  
% 2.22/1.00  fof(f18,negated_conjecture,(
% 2.22/1.00    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 2.22/1.00    inference(negated_conjecture,[],[f17])).
% 2.22/1.00  
% 2.22/1.00  fof(f46,plain,(
% 2.22/1.00    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.22/1.00    inference(ennf_transformation,[],[f18])).
% 2.22/1.00  
% 2.22/1.00  fof(f47,plain,(
% 2.22/1.00    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.22/1.00    inference(flattening,[],[f46])).
% 2.22/1.00  
% 2.22/1.00  fof(f53,plain,(
% 2.22/1.00    ? [X0] : (? [X1] : (((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.22/1.00    inference(nnf_transformation,[],[f47])).
% 2.22/1.00  
% 2.22/1.00  fof(f54,plain,(
% 2.22/1.00    ? [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.22/1.00    inference(flattening,[],[f53])).
% 2.22/1.00  
% 2.22/1.00  fof(f56,plain,(
% 2.22/1.00    ( ! [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) => ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),sK2),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,sK2),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),sK2),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,sK2),X0)) & m1_subset_1(sK2,u1_struct_0(X0)))) )),
% 2.22/1.00    introduced(choice_axiom,[])).
% 2.22/1.00  
% 2.22/1.00  fof(f55,plain,(
% 2.22/1.00    ? [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(sK1),X1),u1_struct_0(sK1)) | ~v1_tex_2(k1_tex_2(sK1,X1),sK1)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK1),X1),u1_struct_0(sK1)) | v1_tex_2(k1_tex_2(sK1,X1),sK1)) & m1_subset_1(X1,u1_struct_0(sK1))) & l1_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 2.22/1.00    introduced(choice_axiom,[])).
% 2.22/1.00  
% 2.22/1.00  fof(f57,plain,(
% 2.22/1.00    ((~v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) | ~v1_tex_2(k1_tex_2(sK1,sK2),sK1)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) | v1_tex_2(k1_tex_2(sK1,sK2),sK1)) & m1_subset_1(sK2,u1_struct_0(sK1))) & l1_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 2.22/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f54,f56,f55])).
% 2.22/1.00  
% 2.22/1.00  fof(f82,plain,(
% 2.22/1.00    m1_subset_1(sK2,u1_struct_0(sK1))),
% 2.22/1.00    inference(cnf_transformation,[],[f57])).
% 2.22/1.00  
% 2.22/1.00  fof(f7,axiom,(
% 2.22/1.00    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 2.22/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.22/1.00  
% 2.22/1.00  fof(f28,plain,(
% 2.22/1.00    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.22/1.00    inference(ennf_transformation,[],[f7])).
% 2.22/1.00  
% 2.22/1.00  fof(f29,plain,(
% 2.22/1.00    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.22/1.00    inference(flattening,[],[f28])).
% 2.22/1.00  
% 2.22/1.00  fof(f64,plain,(
% 2.22/1.00    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.22/1.00    inference(cnf_transformation,[],[f29])).
% 2.22/1.00  
% 2.22/1.00  fof(f1,axiom,(
% 2.22/1.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.22/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.22/1.00  
% 2.22/1.00  fof(f58,plain,(
% 2.22/1.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.22/1.00    inference(cnf_transformation,[],[f1])).
% 2.22/1.00  
% 2.22/1.00  fof(f85,plain,(
% 2.22/1.00    ( ! [X0,X1] : (k2_tarski(X1,X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.22/1.00    inference(definition_unfolding,[],[f64,f58])).
% 2.22/1.00  
% 2.22/1.00  fof(f80,plain,(
% 2.22/1.00    ~v2_struct_0(sK1)),
% 2.22/1.00    inference(cnf_transformation,[],[f57])).
% 2.22/1.00  
% 2.22/1.00  fof(f81,plain,(
% 2.22/1.00    l1_pre_topc(sK1)),
% 2.22/1.00    inference(cnf_transformation,[],[f57])).
% 2.22/1.00  
% 2.22/1.00  fof(f6,axiom,(
% 2.22/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.22/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.22/1.00  
% 2.22/1.00  fof(f26,plain,(
% 2.22/1.00    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.22/1.00    inference(ennf_transformation,[],[f6])).
% 2.22/1.00  
% 2.22/1.00  fof(f27,plain,(
% 2.22/1.00    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.22/1.00    inference(flattening,[],[f26])).
% 2.22/1.00  
% 2.22/1.00  fof(f63,plain,(
% 2.22/1.00    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.22/1.00    inference(cnf_transformation,[],[f27])).
% 2.22/1.00  
% 2.22/1.00  fof(f3,axiom,(
% 2.22/1.00    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.22/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.22/1.00  
% 2.22/1.00  fof(f22,plain,(
% 2.22/1.00    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.22/1.00    inference(ennf_transformation,[],[f3])).
% 2.22/1.00  
% 2.22/1.00  fof(f60,plain,(
% 2.22/1.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.22/1.00    inference(cnf_transformation,[],[f22])).
% 2.22/1.00  
% 2.22/1.00  fof(f15,axiom,(
% 2.22/1.00    ! [X0] : ((~v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,X0) => v1_subset_1(k6_domain_1(X0,X1),X0)))),
% 2.22/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.22/1.00  
% 2.22/1.00  fof(f42,plain,(
% 2.22/1.00    ! [X0] : (! [X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | (v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 2.22/1.00    inference(ennf_transformation,[],[f15])).
% 2.22/1.00  
% 2.22/1.00  fof(f43,plain,(
% 2.22/1.00    ! [X0] : (! [X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 2.22/1.00    inference(flattening,[],[f42])).
% 2.22/1.00  
% 2.22/1.00  fof(f78,plain,(
% 2.22/1.00    ( ! [X0,X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0) | v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 2.22/1.00    inference(cnf_transformation,[],[f43])).
% 2.22/1.00  
% 2.22/1.00  fof(f2,axiom,(
% 2.22/1.00    ! [X0] : (v1_xboole_0(X0) => v1_zfmisc_1(X0))),
% 2.22/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.22/1.00  
% 2.22/1.00  fof(f21,plain,(
% 2.22/1.00    ! [X0] : (v1_zfmisc_1(X0) | ~v1_xboole_0(X0))),
% 2.22/1.00    inference(ennf_transformation,[],[f2])).
% 2.22/1.00  
% 2.22/1.00  fof(f59,plain,(
% 2.22/1.00    ( ! [X0] : (v1_zfmisc_1(X0) | ~v1_xboole_0(X0)) )),
% 2.22/1.00    inference(cnf_transformation,[],[f21])).
% 2.22/1.00  
% 2.22/1.00  fof(f12,axiom,(
% 2.22/1.00    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 2.22/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.22/1.00  
% 2.22/1.00  fof(f19,plain,(
% 2.22/1.00    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 2.22/1.00    inference(pure_predicate_removal,[],[f12])).
% 2.22/1.00  
% 2.22/1.00  fof(f36,plain,(
% 2.22/1.00    ! [X0,X1] : ((v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.22/1.00    inference(ennf_transformation,[],[f19])).
% 2.22/1.00  
% 2.22/1.00  fof(f37,plain,(
% 2.22/1.00    ! [X0,X1] : ((v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.22/1.00    inference(flattening,[],[f36])).
% 2.22/1.00  
% 2.22/1.00  fof(f74,plain,(
% 2.22/1.00    ( ! [X0,X1] : (~v2_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.22/1.00    inference(cnf_transformation,[],[f37])).
% 2.22/1.00  
% 2.22/1.00  fof(f13,axiom,(
% 2.22/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ~(v1_tex_2(X1,X0) & u1_struct_0(X0) = u1_struct_0(X1))))),
% 2.22/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.22/1.00  
% 2.22/1.00  fof(f38,plain,(
% 2.22/1.00    ! [X0] : (! [X1] : ((~v1_tex_2(X1,X0) | u1_struct_0(X0) != u1_struct_0(X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.22/1.00    inference(ennf_transformation,[],[f13])).
% 2.22/1.00  
% 2.22/1.00  fof(f39,plain,(
% 2.22/1.00    ! [X0] : (! [X1] : (~v1_tex_2(X1,X0) | u1_struct_0(X0) != u1_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.22/1.00    inference(flattening,[],[f38])).
% 2.22/1.00  
% 2.22/1.00  fof(f76,plain,(
% 2.22/1.00    ( ! [X0,X1] : (~v1_tex_2(X1,X0) | u1_struct_0(X0) != u1_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.22/1.00    inference(cnf_transformation,[],[f39])).
% 2.22/1.00  
% 2.22/1.00  fof(f4,axiom,(
% 2.22/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.22/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.22/1.00  
% 2.22/1.00  fof(f23,plain,(
% 2.22/1.00    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.22/1.00    inference(ennf_transformation,[],[f4])).
% 2.22/1.00  
% 2.22/1.00  fof(f61,plain,(
% 2.22/1.00    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.22/1.00    inference(cnf_transformation,[],[f23])).
% 2.22/1.00  
% 2.22/1.00  fof(f83,plain,(
% 2.22/1.00    v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) | v1_tex_2(k1_tex_2(sK1,sK2),sK1)),
% 2.22/1.00    inference(cnf_transformation,[],[f57])).
% 2.22/1.00  
% 2.22/1.00  fof(f8,axiom,(
% 2.22/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))),
% 2.22/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.22/1.00  
% 2.22/1.00  fof(f30,plain,(
% 2.22/1.00    ! [X0] : (! [X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.22/1.00    inference(ennf_transformation,[],[f8])).
% 2.22/1.00  
% 2.22/1.00  fof(f65,plain,(
% 2.22/1.00    ( ! [X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.22/1.00    inference(cnf_transformation,[],[f30])).
% 2.22/1.00  
% 2.22/1.00  fof(f14,axiom,(
% 2.22/1.00    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 2.22/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.22/1.00  
% 2.22/1.00  fof(f40,plain,(
% 2.22/1.00    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 2.22/1.00    inference(ennf_transformation,[],[f14])).
% 2.22/1.00  
% 2.22/1.00  fof(f41,plain,(
% 2.22/1.00    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.22/1.00    inference(flattening,[],[f40])).
% 2.22/1.00  
% 2.22/1.00  fof(f77,plain,(
% 2.22/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.22/1.00    inference(cnf_transformation,[],[f41])).
% 2.22/1.00  
% 2.22/1.00  fof(f84,plain,(
% 2.22/1.00    ~v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) | ~v1_tex_2(k1_tex_2(sK1,sK2),sK1)),
% 2.22/1.00    inference(cnf_transformation,[],[f57])).
% 2.22/1.00  
% 2.22/1.00  fof(f67,plain,(
% 2.22/1.00    ( ! [X0,X1] : (v1_tex_2(X1,X0) | m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.22/1.00    inference(cnf_transformation,[],[f51])).
% 2.22/1.00  
% 2.22/1.00  fof(f10,axiom,(
% 2.22/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 2.22/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.22/1.00  
% 2.22/1.00  fof(f33,plain,(
% 2.22/1.00    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.22/1.00    inference(ennf_transformation,[],[f10])).
% 2.22/1.00  
% 2.22/1.00  fof(f52,plain,(
% 2.22/1.00    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.22/1.00    inference(nnf_transformation,[],[f33])).
% 2.22/1.00  
% 2.22/1.00  fof(f71,plain,(
% 2.22/1.00    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.22/1.00    inference(cnf_transformation,[],[f52])).
% 2.22/1.00  
% 2.22/1.00  fof(f69,plain,(
% 2.22/1.00    ( ! [X0,X1] : (v1_tex_2(X1,X0) | ~v1_subset_1(sK0(X0,X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.22/1.00    inference(cnf_transformation,[],[f51])).
% 2.22/1.00  
% 2.22/1.00  fof(f16,axiom,(
% 2.22/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~(v7_struct_0(X0) & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 2.22/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.22/1.00  
% 2.22/1.00  fof(f44,plain,(
% 2.22/1.00    ! [X0] : (! [X1] : ((~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.22/1.00    inference(ennf_transformation,[],[f16])).
% 2.22/1.00  
% 2.22/1.00  fof(f45,plain,(
% 2.22/1.00    ! [X0] : (! [X1] : (~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.22/1.00    inference(flattening,[],[f44])).
% 2.22/1.00  
% 2.22/1.00  fof(f79,plain,(
% 2.22/1.00    ( ! [X0,X1] : (~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.22/1.00    inference(cnf_transformation,[],[f45])).
% 2.22/1.00  
% 2.22/1.00  fof(f75,plain,(
% 2.22/1.00    ( ! [X0,X1] : (v7_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.22/1.00    inference(cnf_transformation,[],[f37])).
% 2.22/1.00  
% 2.22/1.00  cnf(c_13,plain,
% 2.22/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.22/1.00      | m1_pre_topc(k1_tex_2(X1,X0),X1)
% 2.22/1.00      | v2_struct_0(X1)
% 2.22/1.00      | ~ l1_pre_topc(X1) ),
% 2.22/1.00      inference(cnf_transformation,[],[f73]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_3363,plain,
% 2.22/1.00      ( ~ m1_subset_1(X0_48,u1_struct_0(X0_47))
% 2.22/1.00      | m1_pre_topc(k1_tex_2(X0_47,X0_48),X0_47)
% 2.22/1.00      | v2_struct_0(X0_47)
% 2.22/1.00      | ~ l1_pre_topc(X0_47) ),
% 2.22/1.00      inference(subtyping,[status(esa)],[c_13]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_4043,plain,
% 2.22/1.00      ( m1_subset_1(X0_48,u1_struct_0(X0_47)) != iProver_top
% 2.22/1.00      | m1_pre_topc(k1_tex_2(X0_47,X0_48),X0_47) = iProver_top
% 2.22/1.00      | v2_struct_0(X0_47) = iProver_top
% 2.22/1.00      | l1_pre_topc(X0_47) != iProver_top ),
% 2.22/1.00      inference(predicate_to_equality,[status(thm)],[c_3363]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_8,plain,
% 2.22/1.00      ( v1_tex_2(X0,X1)
% 2.22/1.00      | ~ m1_pre_topc(X0,X1)
% 2.22/1.00      | ~ l1_pre_topc(X1)
% 2.22/1.00      | sK0(X1,X0) = u1_struct_0(X0) ),
% 2.22/1.00      inference(cnf_transformation,[],[f68]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_3368,plain,
% 2.22/1.00      ( v1_tex_2(X0_47,X1_47)
% 2.22/1.00      | ~ m1_pre_topc(X0_47,X1_47)
% 2.22/1.00      | ~ l1_pre_topc(X1_47)
% 2.22/1.00      | sK0(X1_47,X0_47) = u1_struct_0(X0_47) ),
% 2.22/1.00      inference(subtyping,[status(esa)],[c_8]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_4038,plain,
% 2.22/1.00      ( sK0(X0_47,X1_47) = u1_struct_0(X1_47)
% 2.22/1.00      | v1_tex_2(X1_47,X0_47) = iProver_top
% 2.22/1.00      | m1_pre_topc(X1_47,X0_47) != iProver_top
% 2.22/1.00      | l1_pre_topc(X0_47) != iProver_top ),
% 2.22/1.00      inference(predicate_to_equality,[status(thm)],[c_3368]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_4815,plain,
% 2.22/1.00      ( sK0(X0_47,k1_tex_2(X0_47,X0_48)) = u1_struct_0(k1_tex_2(X0_47,X0_48))
% 2.22/1.00      | v1_tex_2(k1_tex_2(X0_47,X0_48),X0_47) = iProver_top
% 2.22/1.00      | m1_subset_1(X0_48,u1_struct_0(X0_47)) != iProver_top
% 2.22/1.00      | v2_struct_0(X0_47) = iProver_top
% 2.22/1.00      | l1_pre_topc(X0_47) != iProver_top ),
% 2.22/1.00      inference(superposition,[status(thm)],[c_4043,c_4038]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_23,negated_conjecture,
% 2.22/1.00      ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 2.22/1.00      inference(cnf_transformation,[],[f82]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_3357,negated_conjecture,
% 2.22/1.00      ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 2.22/1.00      inference(subtyping,[status(esa)],[c_23]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_4049,plain,
% 2.22/1.00      ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
% 2.22/1.00      inference(predicate_to_equality,[status(thm)],[c_3357]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_5,plain,
% 2.22/1.00      ( ~ m1_subset_1(X0,X1)
% 2.22/1.00      | v1_xboole_0(X1)
% 2.22/1.00      | k6_domain_1(X1,X0) = k2_tarski(X0,X0) ),
% 2.22/1.00      inference(cnf_transformation,[],[f85]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_3370,plain,
% 2.22/1.00      ( ~ m1_subset_1(X0_48,X1_48)
% 2.22/1.00      | v1_xboole_0(X1_48)
% 2.22/1.00      | k6_domain_1(X1_48,X0_48) = k2_tarski(X0_48,X0_48) ),
% 2.22/1.00      inference(subtyping,[status(esa)],[c_5]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_4036,plain,
% 2.22/1.00      ( k6_domain_1(X0_48,X1_48) = k2_tarski(X1_48,X1_48)
% 2.22/1.00      | m1_subset_1(X1_48,X0_48) != iProver_top
% 2.22/1.00      | v1_xboole_0(X0_48) = iProver_top ),
% 2.22/1.00      inference(predicate_to_equality,[status(thm)],[c_3370]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_4399,plain,
% 2.22/1.00      ( k6_domain_1(u1_struct_0(sK1),sK2) = k2_tarski(sK2,sK2)
% 2.22/1.00      | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
% 2.22/1.00      inference(superposition,[status(thm)],[c_4049,c_4036]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_25,negated_conjecture,
% 2.22/1.00      ( ~ v2_struct_0(sK1) ),
% 2.22/1.00      inference(cnf_transformation,[],[f80]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_24,negated_conjecture,
% 2.22/1.00      ( l1_pre_topc(sK1) ),
% 2.22/1.00      inference(cnf_transformation,[],[f81]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_4,plain,
% 2.22/1.00      ( v2_struct_0(X0)
% 2.22/1.00      | ~ l1_struct_0(X0)
% 2.22/1.00      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.22/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_78,plain,
% 2.22/1.00      ( v2_struct_0(sK1)
% 2.22/1.00      | ~ l1_struct_0(sK1)
% 2.22/1.00      | ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 2.22/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_1,plain,
% 2.22/1.00      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 2.22/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_83,plain,
% 2.22/1.00      ( ~ l1_pre_topc(sK1) | l1_struct_0(sK1) ),
% 2.22/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_4268,plain,
% 2.22/1.00      ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 2.22/1.00      | v1_xboole_0(u1_struct_0(sK1))
% 2.22/1.00      | k6_domain_1(u1_struct_0(sK1),sK2) = k2_tarski(sK2,sK2) ),
% 2.22/1.00      inference(instantiation,[status(thm)],[c_3370]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_4512,plain,
% 2.22/1.00      ( k6_domain_1(u1_struct_0(sK1),sK2) = k2_tarski(sK2,sK2) ),
% 2.22/1.00      inference(global_propositional_subsumption,
% 2.22/1.00                [status(thm)],
% 2.22/1.00                [c_4399,c_25,c_24,c_23,c_78,c_83,c_4268]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_19,plain,
% 2.22/1.00      ( v1_subset_1(k6_domain_1(X0,X1),X0)
% 2.22/1.00      | ~ m1_subset_1(X1,X0)
% 2.22/1.00      | v1_xboole_0(X0)
% 2.22/1.00      | v1_zfmisc_1(X0) ),
% 2.22/1.00      inference(cnf_transformation,[],[f78]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_0,plain,
% 2.22/1.00      ( ~ v1_xboole_0(X0) | v1_zfmisc_1(X0) ),
% 2.22/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_147,plain,
% 2.22/1.00      ( ~ m1_subset_1(X1,X0)
% 2.22/1.00      | v1_subset_1(k6_domain_1(X0,X1),X0)
% 2.22/1.00      | v1_zfmisc_1(X0) ),
% 2.22/1.00      inference(global_propositional_subsumption,
% 2.22/1.00                [status(thm)],
% 2.22/1.00                [c_19,c_0]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_148,plain,
% 2.22/1.00      ( v1_subset_1(k6_domain_1(X0,X1),X0)
% 2.22/1.00      | ~ m1_subset_1(X1,X0)
% 2.22/1.00      | v1_zfmisc_1(X0) ),
% 2.22/1.00      inference(renaming,[status(thm)],[c_147]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_3354,plain,
% 2.22/1.00      ( v1_subset_1(k6_domain_1(X0_48,X1_48),X0_48)
% 2.22/1.00      | ~ m1_subset_1(X1_48,X0_48)
% 2.22/1.00      | v1_zfmisc_1(X0_48) ),
% 2.22/1.00      inference(subtyping,[status(esa)],[c_148]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_4052,plain,
% 2.22/1.00      ( v1_subset_1(k6_domain_1(X0_48,X1_48),X0_48) = iProver_top
% 2.22/1.00      | m1_subset_1(X1_48,X0_48) != iProver_top
% 2.22/1.00      | v1_zfmisc_1(X0_48) = iProver_top ),
% 2.22/1.00      inference(predicate_to_equality,[status(thm)],[c_3354]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_5092,plain,
% 2.22/1.00      ( v1_subset_1(k2_tarski(sK2,sK2),u1_struct_0(sK1)) = iProver_top
% 2.22/1.00      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 2.22/1.00      | v1_zfmisc_1(u1_struct_0(sK1)) = iProver_top ),
% 2.22/1.00      inference(superposition,[status(thm)],[c_4512,c_4052]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_26,plain,
% 2.22/1.00      ( v2_struct_0(sK1) != iProver_top ),
% 2.22/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_27,plain,
% 2.22/1.00      ( l1_pre_topc(sK1) = iProver_top ),
% 2.22/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_28,plain,
% 2.22/1.00      ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
% 2.22/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_77,plain,
% 2.22/1.00      ( v2_struct_0(X0) = iProver_top
% 2.22/1.00      | l1_struct_0(X0) != iProver_top
% 2.22/1.00      | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
% 2.22/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_79,plain,
% 2.22/1.00      ( v2_struct_0(sK1) = iProver_top
% 2.22/1.00      | l1_struct_0(sK1) != iProver_top
% 2.22/1.00      | v1_xboole_0(u1_struct_0(sK1)) != iProver_top ),
% 2.22/1.00      inference(instantiation,[status(thm)],[c_77]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_82,plain,
% 2.22/1.00      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 2.22/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_84,plain,
% 2.22/1.00      ( l1_pre_topc(sK1) != iProver_top
% 2.22/1.00      | l1_struct_0(sK1) = iProver_top ),
% 2.22/1.00      inference(instantiation,[status(thm)],[c_82]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_3423,plain,
% 2.22/1.00      ( m1_subset_1(X0_48,u1_struct_0(X0_47)) != iProver_top
% 2.22/1.00      | m1_pre_topc(k1_tex_2(X0_47,X0_48),X0_47) = iProver_top
% 2.22/1.00      | v2_struct_0(X0_47) = iProver_top
% 2.22/1.00      | l1_pre_topc(X0_47) != iProver_top ),
% 2.22/1.00      inference(predicate_to_equality,[status(thm)],[c_3363]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_3425,plain,
% 2.22/1.00      ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 2.22/1.00      | m1_pre_topc(k1_tex_2(sK1,sK2),sK1) = iProver_top
% 2.22/1.00      | v2_struct_0(sK1) = iProver_top
% 2.22/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.22/1.00      inference(instantiation,[status(thm)],[c_3423]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_16,plain,
% 2.22/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.22/1.00      | v2_struct_0(X1)
% 2.22/1.00      | ~ v2_struct_0(k1_tex_2(X1,X0))
% 2.22/1.00      | ~ l1_pre_topc(X1) ),
% 2.22/1.00      inference(cnf_transformation,[],[f74]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_3362,plain,
% 2.22/1.00      ( ~ m1_subset_1(X0_48,u1_struct_0(X0_47))
% 2.22/1.00      | v2_struct_0(X0_47)
% 2.22/1.00      | ~ v2_struct_0(k1_tex_2(X0_47,X0_48))
% 2.22/1.00      | ~ l1_pre_topc(X0_47) ),
% 2.22/1.00      inference(subtyping,[status(esa)],[c_16]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_3426,plain,
% 2.22/1.00      ( m1_subset_1(X0_48,u1_struct_0(X0_47)) != iProver_top
% 2.22/1.00      | v2_struct_0(X0_47) = iProver_top
% 2.22/1.00      | v2_struct_0(k1_tex_2(X0_47,X0_48)) != iProver_top
% 2.22/1.00      | l1_pre_topc(X0_47) != iProver_top ),
% 2.22/1.00      inference(predicate_to_equality,[status(thm)],[c_3362]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_3428,plain,
% 2.22/1.00      ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 2.22/1.00      | v2_struct_0(k1_tex_2(sK1,sK2)) != iProver_top
% 2.22/1.00      | v2_struct_0(sK1) = iProver_top
% 2.22/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.22/1.00      inference(instantiation,[status(thm)],[c_3426]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_17,plain,
% 2.22/1.00      ( ~ v1_tex_2(X0,X1)
% 2.22/1.00      | ~ m1_pre_topc(X0,X1)
% 2.22/1.00      | ~ l1_pre_topc(X1)
% 2.22/1.00      | u1_struct_0(X0) != u1_struct_0(X1) ),
% 2.22/1.00      inference(cnf_transformation,[],[f76]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_3360,plain,
% 2.22/1.00      ( ~ v1_tex_2(X0_47,X1_47)
% 2.22/1.00      | ~ m1_pre_topc(X0_47,X1_47)
% 2.22/1.00      | ~ l1_pre_topc(X1_47)
% 2.22/1.00      | u1_struct_0(X0_47) != u1_struct_0(X1_47) ),
% 2.22/1.00      inference(subtyping,[status(esa)],[c_17]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_4265,plain,
% 2.22/1.00      ( ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1)
% 2.22/1.00      | ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
% 2.22/1.00      | ~ l1_pre_topc(sK1)
% 2.22/1.00      | u1_struct_0(k1_tex_2(sK1,sK2)) != u1_struct_0(sK1) ),
% 2.22/1.00      inference(instantiation,[status(thm)],[c_3360]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_4266,plain,
% 2.22/1.00      ( u1_struct_0(k1_tex_2(sK1,sK2)) != u1_struct_0(sK1)
% 2.22/1.00      | v1_tex_2(k1_tex_2(sK1,sK2),sK1) != iProver_top
% 2.22/1.00      | m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top
% 2.22/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.22/1.00      inference(predicate_to_equality,[status(thm)],[c_4265]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_2,plain,
% 2.22/1.00      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.22/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_3371,plain,
% 2.22/1.00      ( ~ m1_pre_topc(X0_47,X1_47)
% 2.22/1.00      | ~ l1_pre_topc(X1_47)
% 2.22/1.00      | l1_pre_topc(X0_47) ),
% 2.22/1.00      inference(subtyping,[status(esa)],[c_2]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_4404,plain,
% 2.22/1.00      ( ~ m1_pre_topc(k1_tex_2(X0_47,X0_48),X1_47)
% 2.22/1.00      | ~ l1_pre_topc(X1_47)
% 2.22/1.00      | l1_pre_topc(k1_tex_2(X0_47,X0_48)) ),
% 2.22/1.00      inference(instantiation,[status(thm)],[c_3371]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_4405,plain,
% 2.22/1.00      ( m1_pre_topc(k1_tex_2(X0_47,X0_48),X1_47) != iProver_top
% 2.22/1.00      | l1_pre_topc(X1_47) != iProver_top
% 2.22/1.00      | l1_pre_topc(k1_tex_2(X0_47,X0_48)) = iProver_top ),
% 2.22/1.00      inference(predicate_to_equality,[status(thm)],[c_4404]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_4407,plain,
% 2.22/1.00      ( m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top
% 2.22/1.00      | l1_pre_topc(k1_tex_2(sK1,sK2)) = iProver_top
% 2.22/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.22/1.00      inference(instantiation,[status(thm)],[c_4405]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_437,plain,
% 2.22/1.00      ( v2_struct_0(X0)
% 2.22/1.00      | ~ l1_pre_topc(X0)
% 2.22/1.00      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.22/1.00      inference(resolution,[status(thm)],[c_1,c_4]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_3351,plain,
% 2.22/1.00      ( v2_struct_0(X0_47)
% 2.22/1.00      | ~ l1_pre_topc(X0_47)
% 2.22/1.00      | ~ v1_xboole_0(u1_struct_0(X0_47)) ),
% 2.22/1.00      inference(subtyping,[status(esa)],[c_437]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_4414,plain,
% 2.22/1.00      ( v2_struct_0(k1_tex_2(sK1,sK2))
% 2.22/1.00      | ~ l1_pre_topc(k1_tex_2(sK1,sK2))
% 2.22/1.00      | ~ v1_xboole_0(u1_struct_0(k1_tex_2(sK1,sK2))) ),
% 2.22/1.00      inference(instantiation,[status(thm)],[c_3351]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_4415,plain,
% 2.22/1.00      ( v2_struct_0(k1_tex_2(sK1,sK2)) = iProver_top
% 2.22/1.00      | l1_pre_topc(k1_tex_2(sK1,sK2)) != iProver_top
% 2.22/1.00      | v1_xboole_0(u1_struct_0(k1_tex_2(sK1,sK2))) != iProver_top ),
% 2.22/1.00      inference(predicate_to_equality,[status(thm)],[c_4414]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_22,negated_conjecture,
% 2.22/1.00      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 2.22/1.00      | v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
% 2.22/1.00      inference(cnf_transformation,[],[f83]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_3358,negated_conjecture,
% 2.22/1.00      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 2.22/1.00      | v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
% 2.22/1.00      inference(subtyping,[status(esa)],[c_22]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_4048,plain,
% 2.22/1.00      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) = iProver_top
% 2.22/1.00      | v1_tex_2(k1_tex_2(sK1,sK2),sK1) = iProver_top ),
% 2.22/1.00      inference(predicate_to_equality,[status(thm)],[c_3358]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_4515,plain,
% 2.22/1.00      ( v1_subset_1(k2_tarski(sK2,sK2),u1_struct_0(sK1)) = iProver_top
% 2.22/1.00      | v1_tex_2(k1_tex_2(sK1,sK2),sK1) = iProver_top ),
% 2.22/1.00      inference(demodulation,[status(thm)],[c_4512,c_4048]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_3376,plain,
% 2.22/1.00      ( X0_48 != X1_48 | X2_48 != X1_48 | X2_48 = X0_48 ),
% 2.22/1.00      theory(equality) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_4346,plain,
% 2.22/1.00      ( u1_struct_0(k1_tex_2(sK1,sK2)) != X0_48
% 2.22/1.00      | u1_struct_0(k1_tex_2(sK1,sK2)) = u1_struct_0(sK1)
% 2.22/1.00      | u1_struct_0(sK1) != X0_48 ),
% 2.22/1.00      inference(instantiation,[status(thm)],[c_3376]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_4437,plain,
% 2.22/1.00      ( u1_struct_0(k1_tex_2(sK1,sK2)) != u1_struct_0(X0_47)
% 2.22/1.00      | u1_struct_0(k1_tex_2(sK1,sK2)) = u1_struct_0(sK1)
% 2.22/1.00      | u1_struct_0(sK1) != u1_struct_0(X0_47) ),
% 2.22/1.00      inference(instantiation,[status(thm)],[c_4346]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_4547,plain,
% 2.22/1.00      ( u1_struct_0(k1_tex_2(sK1,sK2)) != u1_struct_0(k1_tex_2(sK1,sK2))
% 2.22/1.00      | u1_struct_0(k1_tex_2(sK1,sK2)) = u1_struct_0(sK1)
% 2.22/1.00      | u1_struct_0(sK1) != u1_struct_0(k1_tex_2(sK1,sK2)) ),
% 2.22/1.00      inference(instantiation,[status(thm)],[c_4437]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_3375,plain,( X0_48 = X0_48 ),theory(equality) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_4548,plain,
% 2.22/1.00      ( u1_struct_0(k1_tex_2(sK1,sK2)) = u1_struct_0(k1_tex_2(sK1,sK2)) ),
% 2.22/1.00      inference(instantiation,[status(thm)],[c_3375]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_6,plain,
% 2.22/1.00      ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 2.22/1.00      | ~ m1_pre_topc(X0,X1)
% 2.22/1.00      | ~ l1_pre_topc(X1) ),
% 2.22/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_18,plain,
% 2.22/1.00      ( ~ r1_tarski(X0,X1)
% 2.22/1.00      | v1_xboole_0(X0)
% 2.22/1.00      | v1_xboole_0(X1)
% 2.22/1.00      | ~ v1_zfmisc_1(X1)
% 2.22/1.00      | X1 = X0 ),
% 2.22/1.00      inference(cnf_transformation,[],[f77]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_351,plain,
% 2.22/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.22/1.00      | ~ l1_pre_topc(X1)
% 2.22/1.00      | v1_xboole_0(X2)
% 2.22/1.00      | v1_xboole_0(X3)
% 2.22/1.00      | ~ v1_zfmisc_1(X3)
% 2.22/1.00      | X3 = X2
% 2.22/1.00      | u1_struct_0(X0) != X2
% 2.22/1.00      | u1_struct_0(X1) != X3 ),
% 2.22/1.00      inference(resolution_lifted,[status(thm)],[c_6,c_18]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_352,plain,
% 2.22/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.22/1.00      | ~ l1_pre_topc(X1)
% 2.22/1.00      | v1_xboole_0(u1_struct_0(X0))
% 2.22/1.00      | v1_xboole_0(u1_struct_0(X1))
% 2.22/1.00      | ~ v1_zfmisc_1(u1_struct_0(X1))
% 2.22/1.00      | u1_struct_0(X1) = u1_struct_0(X0) ),
% 2.22/1.00      inference(unflattening,[status(thm)],[c_351]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_3353,plain,
% 2.22/1.00      ( ~ m1_pre_topc(X0_47,X1_47)
% 2.22/1.00      | ~ l1_pre_topc(X1_47)
% 2.22/1.00      | v1_xboole_0(u1_struct_0(X0_47))
% 2.22/1.00      | v1_xboole_0(u1_struct_0(X1_47))
% 2.22/1.00      | ~ v1_zfmisc_1(u1_struct_0(X1_47))
% 2.22/1.00      | u1_struct_0(X1_47) = u1_struct_0(X0_47) ),
% 2.22/1.00      inference(subtyping,[status(esa)],[c_352]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_4438,plain,
% 2.22/1.00      ( ~ m1_pre_topc(X0_47,sK1)
% 2.22/1.00      | ~ l1_pre_topc(sK1)
% 2.22/1.00      | v1_xboole_0(u1_struct_0(X0_47))
% 2.22/1.00      | v1_xboole_0(u1_struct_0(sK1))
% 2.22/1.00      | ~ v1_zfmisc_1(u1_struct_0(sK1))
% 2.22/1.00      | u1_struct_0(sK1) = u1_struct_0(X0_47) ),
% 2.22/1.00      inference(instantiation,[status(thm)],[c_3353]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_4720,plain,
% 2.22/1.00      ( ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
% 2.22/1.00      | ~ l1_pre_topc(sK1)
% 2.22/1.00      | v1_xboole_0(u1_struct_0(k1_tex_2(sK1,sK2)))
% 2.22/1.00      | v1_xboole_0(u1_struct_0(sK1))
% 2.22/1.00      | ~ v1_zfmisc_1(u1_struct_0(sK1))
% 2.22/1.00      | u1_struct_0(sK1) = u1_struct_0(k1_tex_2(sK1,sK2)) ),
% 2.22/1.00      inference(instantiation,[status(thm)],[c_4438]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_4721,plain,
% 2.22/1.00      ( u1_struct_0(sK1) = u1_struct_0(k1_tex_2(sK1,sK2))
% 2.22/1.00      | m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top
% 2.22/1.00      | l1_pre_topc(sK1) != iProver_top
% 2.22/1.00      | v1_xboole_0(u1_struct_0(k1_tex_2(sK1,sK2))) = iProver_top
% 2.22/1.00      | v1_xboole_0(u1_struct_0(sK1)) = iProver_top
% 2.22/1.00      | v1_zfmisc_1(u1_struct_0(sK1)) != iProver_top ),
% 2.22/1.00      inference(predicate_to_equality,[status(thm)],[c_4720]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_5171,plain,
% 2.22/1.00      ( v1_subset_1(k2_tarski(sK2,sK2),u1_struct_0(sK1)) = iProver_top ),
% 2.22/1.00      inference(global_propositional_subsumption,
% 2.22/1.00                [status(thm)],
% 2.22/1.00                [c_5092,c_26,c_27,c_28,c_79,c_84,c_3425,c_3428,c_4266,
% 2.22/1.00                 c_4407,c_4415,c_4515,c_4547,c_4548,c_4721]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_21,negated_conjecture,
% 2.22/1.00      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 2.22/1.00      | ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
% 2.22/1.00      inference(cnf_transformation,[],[f84]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_3359,negated_conjecture,
% 2.22/1.00      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 2.22/1.00      | ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
% 2.22/1.00      inference(subtyping,[status(esa)],[c_21]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_4047,plain,
% 2.22/1.00      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top
% 2.22/1.00      | v1_tex_2(k1_tex_2(sK1,sK2),sK1) != iProver_top ),
% 2.22/1.00      inference(predicate_to_equality,[status(thm)],[c_3359]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_4516,plain,
% 2.22/1.00      ( v1_subset_1(k2_tarski(sK2,sK2),u1_struct_0(sK1)) != iProver_top
% 2.22/1.00      | v1_tex_2(k1_tex_2(sK1,sK2),sK1) != iProver_top ),
% 2.22/1.00      inference(demodulation,[status(thm)],[c_4512,c_4047]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_5176,plain,
% 2.22/1.00      ( v1_tex_2(k1_tex_2(sK1,sK2),sK1) != iProver_top ),
% 2.22/1.00      inference(superposition,[status(thm)],[c_5171,c_4516]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_5456,plain,
% 2.22/1.00      ( sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(k1_tex_2(sK1,sK2))
% 2.22/1.00      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 2.22/1.00      | v2_struct_0(sK1) = iProver_top
% 2.22/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.22/1.00      inference(superposition,[status(thm)],[c_4815,c_5176]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_4286,plain,
% 2.22/1.00      ( v1_tex_2(k1_tex_2(X0_47,X0_48),X0_47)
% 2.22/1.00      | ~ m1_pre_topc(k1_tex_2(X0_47,X0_48),X0_47)
% 2.22/1.00      | ~ l1_pre_topc(X0_47)
% 2.22/1.00      | sK0(X0_47,k1_tex_2(X0_47,X0_48)) = u1_struct_0(k1_tex_2(X0_47,X0_48)) ),
% 2.22/1.00      inference(instantiation,[status(thm)],[c_3368]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_4287,plain,
% 2.22/1.00      ( sK0(X0_47,k1_tex_2(X0_47,X0_48)) = u1_struct_0(k1_tex_2(X0_47,X0_48))
% 2.22/1.00      | v1_tex_2(k1_tex_2(X0_47,X0_48),X0_47) = iProver_top
% 2.22/1.00      | m1_pre_topc(k1_tex_2(X0_47,X0_48),X0_47) != iProver_top
% 2.22/1.00      | l1_pre_topc(X0_47) != iProver_top ),
% 2.22/1.00      inference(predicate_to_equality,[status(thm)],[c_4286]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_4289,plain,
% 2.22/1.00      ( sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(k1_tex_2(sK1,sK2))
% 2.22/1.00      | v1_tex_2(k1_tex_2(sK1,sK2),sK1) = iProver_top
% 2.22/1.00      | m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top
% 2.22/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.22/1.00      inference(instantiation,[status(thm)],[c_4287]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_5557,plain,
% 2.22/1.00      ( sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(k1_tex_2(sK1,sK2)) ),
% 2.22/1.00      inference(global_propositional_subsumption,
% 2.22/1.00                [status(thm)],
% 2.22/1.00                [c_5456,c_26,c_27,c_28,c_79,c_84,c_3425,c_3428,c_4266,
% 2.22/1.00                 c_4289,c_4407,c_4415,c_4515,c_4516,c_4547,c_4548,c_4721,
% 2.22/1.00                 c_5092]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_9,plain,
% 2.22/1.00      ( v1_tex_2(X0,X1)
% 2.22/1.00      | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.22/1.00      | ~ m1_pre_topc(X0,X1)
% 2.22/1.00      | ~ l1_pre_topc(X1) ),
% 2.22/1.00      inference(cnf_transformation,[],[f67]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_3367,plain,
% 2.22/1.00      ( v1_tex_2(X0_47,X1_47)
% 2.22/1.00      | m1_subset_1(sK0(X1_47,X0_47),k1_zfmisc_1(u1_struct_0(X1_47)))
% 2.22/1.00      | ~ m1_pre_topc(X0_47,X1_47)
% 2.22/1.00      | ~ l1_pre_topc(X1_47) ),
% 2.22/1.00      inference(subtyping,[status(esa)],[c_9]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_4039,plain,
% 2.22/1.00      ( v1_tex_2(X0_47,X1_47) = iProver_top
% 2.22/1.00      | m1_subset_1(sK0(X1_47,X0_47),k1_zfmisc_1(u1_struct_0(X1_47))) = iProver_top
% 2.22/1.00      | m1_pre_topc(X0_47,X1_47) != iProver_top
% 2.22/1.00      | l1_pre_topc(X1_47) != iProver_top ),
% 2.22/1.00      inference(predicate_to_equality,[status(thm)],[c_3367]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_11,plain,
% 2.22/1.00      ( v1_subset_1(X0,X1)
% 2.22/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.22/1.00      | X0 = X1 ),
% 2.22/1.00      inference(cnf_transformation,[],[f71]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_3365,plain,
% 2.22/1.00      ( v1_subset_1(X0_48,X1_48)
% 2.22/1.00      | ~ m1_subset_1(X0_48,k1_zfmisc_1(X1_48))
% 2.22/1.00      | X0_48 = X1_48 ),
% 2.22/1.00      inference(subtyping,[status(esa)],[c_11]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_4041,plain,
% 2.22/1.00      ( X0_48 = X1_48
% 2.22/1.00      | v1_subset_1(X0_48,X1_48) = iProver_top
% 2.22/1.00      | m1_subset_1(X0_48,k1_zfmisc_1(X1_48)) != iProver_top ),
% 2.22/1.00      inference(predicate_to_equality,[status(thm)],[c_3365]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_4902,plain,
% 2.22/1.00      ( sK0(X0_47,X1_47) = u1_struct_0(X0_47)
% 2.22/1.00      | v1_subset_1(sK0(X0_47,X1_47),u1_struct_0(X0_47)) = iProver_top
% 2.22/1.00      | v1_tex_2(X1_47,X0_47) = iProver_top
% 2.22/1.00      | m1_pre_topc(X1_47,X0_47) != iProver_top
% 2.22/1.00      | l1_pre_topc(X0_47) != iProver_top ),
% 2.22/1.00      inference(superposition,[status(thm)],[c_4039,c_4041]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_7,plain,
% 2.22/1.00      ( ~ v1_subset_1(sK0(X0,X1),u1_struct_0(X0))
% 2.22/1.00      | v1_tex_2(X1,X0)
% 2.22/1.00      | ~ m1_pre_topc(X1,X0)
% 2.22/1.00      | ~ l1_pre_topc(X0) ),
% 2.22/1.00      inference(cnf_transformation,[],[f69]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_3369,plain,
% 2.22/1.00      ( ~ v1_subset_1(sK0(X0_47,X1_47),u1_struct_0(X0_47))
% 2.22/1.00      | v1_tex_2(X1_47,X0_47)
% 2.22/1.00      | ~ m1_pre_topc(X1_47,X0_47)
% 2.22/1.00      | ~ l1_pre_topc(X0_47) ),
% 2.22/1.00      inference(subtyping,[status(esa)],[c_7]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_3413,plain,
% 2.22/1.00      ( v1_subset_1(sK0(X0_47,X1_47),u1_struct_0(X0_47)) != iProver_top
% 2.22/1.00      | v1_tex_2(X1_47,X0_47) = iProver_top
% 2.22/1.00      | m1_pre_topc(X1_47,X0_47) != iProver_top
% 2.22/1.00      | l1_pre_topc(X0_47) != iProver_top ),
% 2.22/1.00      inference(predicate_to_equality,[status(thm)],[c_3369]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_5325,plain,
% 2.22/1.00      ( sK0(X0_47,X1_47) = u1_struct_0(X0_47)
% 2.22/1.00      | v1_tex_2(X1_47,X0_47) = iProver_top
% 2.22/1.00      | m1_pre_topc(X1_47,X0_47) != iProver_top
% 2.22/1.00      | l1_pre_topc(X0_47) != iProver_top ),
% 2.22/1.00      inference(global_propositional_subsumption,
% 2.22/1.00                [status(thm)],
% 2.22/1.00                [c_4902,c_3413]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_5333,plain,
% 2.22/1.00      ( sK0(X0_47,k1_tex_2(X0_47,X0_48)) = u1_struct_0(X0_47)
% 2.22/1.00      | v1_tex_2(k1_tex_2(X0_47,X0_48),X0_47) = iProver_top
% 2.22/1.00      | m1_subset_1(X0_48,u1_struct_0(X0_47)) != iProver_top
% 2.22/1.00      | v2_struct_0(X0_47) = iProver_top
% 2.22/1.00      | l1_pre_topc(X0_47) != iProver_top ),
% 2.22/1.00      inference(superposition,[status(thm)],[c_4043,c_5325]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_5448,plain,
% 2.22/1.00      ( sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(sK1)
% 2.22/1.00      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 2.22/1.00      | v2_struct_0(sK1) = iProver_top
% 2.22/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.22/1.00      inference(superposition,[status(thm)],[c_5333,c_5176]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_4281,plain,
% 2.22/1.00      ( v1_tex_2(k1_tex_2(X0_47,X0_48),X0_47)
% 2.22/1.00      | m1_subset_1(sK0(X0_47,k1_tex_2(X0_47,X0_48)),k1_zfmisc_1(u1_struct_0(X0_47)))
% 2.22/1.00      | ~ m1_pre_topc(k1_tex_2(X0_47,X0_48),X0_47)
% 2.22/1.00      | ~ l1_pre_topc(X0_47) ),
% 2.22/1.00      inference(instantiation,[status(thm)],[c_3367]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_4282,plain,
% 2.22/1.00      ( v1_tex_2(k1_tex_2(X0_47,X0_48),X0_47) = iProver_top
% 2.22/1.00      | m1_subset_1(sK0(X0_47,k1_tex_2(X0_47,X0_48)),k1_zfmisc_1(u1_struct_0(X0_47))) = iProver_top
% 2.22/1.00      | m1_pre_topc(k1_tex_2(X0_47,X0_48),X0_47) != iProver_top
% 2.22/1.00      | l1_pre_topc(X0_47) != iProver_top ),
% 2.22/1.00      inference(predicate_to_equality,[status(thm)],[c_4281]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_4284,plain,
% 2.22/1.00      ( v1_tex_2(k1_tex_2(sK1,sK2),sK1) = iProver_top
% 2.22/1.00      | m1_subset_1(sK0(sK1,k1_tex_2(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 2.22/1.00      | m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top
% 2.22/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.22/1.00      inference(instantiation,[status(thm)],[c_4282]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_4291,plain,
% 2.22/1.00      ( ~ v1_subset_1(sK0(X0_47,k1_tex_2(X0_47,X0_48)),u1_struct_0(X0_47))
% 2.22/1.00      | v1_tex_2(k1_tex_2(X0_47,X0_48),X0_47)
% 2.22/1.00      | ~ m1_pre_topc(k1_tex_2(X0_47,X0_48),X0_47)
% 2.22/1.00      | ~ l1_pre_topc(X0_47) ),
% 2.22/1.00      inference(instantiation,[status(thm)],[c_3369]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_4292,plain,
% 2.22/1.00      ( v1_subset_1(sK0(X0_47,k1_tex_2(X0_47,X0_48)),u1_struct_0(X0_47)) != iProver_top
% 2.22/1.00      | v1_tex_2(k1_tex_2(X0_47,X0_48),X0_47) = iProver_top
% 2.22/1.00      | m1_pre_topc(k1_tex_2(X0_47,X0_48),X0_47) != iProver_top
% 2.22/1.00      | l1_pre_topc(X0_47) != iProver_top ),
% 2.22/1.00      inference(predicate_to_equality,[status(thm)],[c_4291]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_4294,plain,
% 2.22/1.00      ( v1_subset_1(sK0(sK1,k1_tex_2(sK1,sK2)),u1_struct_0(sK1)) != iProver_top
% 2.22/1.00      | v1_tex_2(k1_tex_2(sK1,sK2),sK1) = iProver_top
% 2.22/1.00      | m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top
% 2.22/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.22/1.00      inference(instantiation,[status(thm)],[c_4292]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_4355,plain,
% 2.22/1.00      ( v1_subset_1(X0_48,u1_struct_0(sK1))
% 2.22/1.00      | ~ m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.22/1.00      | X0_48 = u1_struct_0(sK1) ),
% 2.22/1.00      inference(instantiation,[status(thm)],[c_3365]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_4989,plain,
% 2.22/1.00      ( v1_subset_1(sK0(sK1,k1_tex_2(sK1,X0_48)),u1_struct_0(sK1))
% 2.22/1.00      | ~ m1_subset_1(sK0(sK1,k1_tex_2(sK1,X0_48)),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.22/1.00      | sK0(sK1,k1_tex_2(sK1,X0_48)) = u1_struct_0(sK1) ),
% 2.22/1.00      inference(instantiation,[status(thm)],[c_4355]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_4992,plain,
% 2.22/1.00      ( sK0(sK1,k1_tex_2(sK1,X0_48)) = u1_struct_0(sK1)
% 2.22/1.00      | v1_subset_1(sK0(sK1,k1_tex_2(sK1,X0_48)),u1_struct_0(sK1)) = iProver_top
% 2.22/1.00      | m1_subset_1(sK0(sK1,k1_tex_2(sK1,X0_48)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.22/1.00      inference(predicate_to_equality,[status(thm)],[c_4989]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_4994,plain,
% 2.22/1.00      ( sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(sK1)
% 2.22/1.00      | v1_subset_1(sK0(sK1,k1_tex_2(sK1,sK2)),u1_struct_0(sK1)) = iProver_top
% 2.22/1.00      | m1_subset_1(sK0(sK1,k1_tex_2(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.22/1.00      inference(instantiation,[status(thm)],[c_4992]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_5533,plain,
% 2.22/1.00      ( sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(sK1) ),
% 2.22/1.00      inference(global_propositional_subsumption,
% 2.22/1.00                [status(thm)],
% 2.22/1.00                [c_5448,c_26,c_27,c_28,c_79,c_84,c_3425,c_3428,c_4266,
% 2.22/1.00                 c_4284,c_4294,c_4407,c_4415,c_4515,c_4516,c_4547,c_4548,
% 2.22/1.00                 c_4721,c_4994,c_5092]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_5559,plain,
% 2.22/1.00      ( u1_struct_0(k1_tex_2(sK1,sK2)) = u1_struct_0(sK1) ),
% 2.22/1.00      inference(light_normalisation,[status(thm)],[c_5557,c_5533]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_20,plain,
% 2.22/1.00      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
% 2.22/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.22/1.00      | ~ v7_struct_0(X0)
% 2.22/1.00      | v2_struct_0(X0)
% 2.22/1.00      | ~ l1_struct_0(X0) ),
% 2.22/1.00      inference(cnf_transformation,[],[f79]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_417,plain,
% 2.22/1.00      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
% 2.22/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.22/1.00      | ~ v7_struct_0(X0)
% 2.22/1.00      | v2_struct_0(X0)
% 2.22/1.00      | ~ l1_pre_topc(X0) ),
% 2.22/1.00      inference(resolution,[status(thm)],[c_1,c_20]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_3352,plain,
% 2.22/1.00      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0_47),X0_48),u1_struct_0(X0_47))
% 2.22/1.00      | ~ m1_subset_1(X0_48,u1_struct_0(X0_47))
% 2.22/1.00      | ~ v7_struct_0(X0_47)
% 2.22/1.00      | v2_struct_0(X0_47)
% 2.22/1.00      | ~ l1_pre_topc(X0_47) ),
% 2.22/1.00      inference(subtyping,[status(esa)],[c_417]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_4054,plain,
% 2.22/1.00      ( v1_subset_1(k6_domain_1(u1_struct_0(X0_47),X0_48),u1_struct_0(X0_47)) != iProver_top
% 2.22/1.00      | m1_subset_1(X0_48,u1_struct_0(X0_47)) != iProver_top
% 2.22/1.00      | v7_struct_0(X0_47) != iProver_top
% 2.22/1.00      | v2_struct_0(X0_47) = iProver_top
% 2.22/1.00      | l1_pre_topc(X0_47) != iProver_top ),
% 2.22/1.00      inference(predicate_to_equality,[status(thm)],[c_3352]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_5562,plain,
% 2.22/1.00      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),X0_48),u1_struct_0(sK1)) != iProver_top
% 2.22/1.00      | m1_subset_1(X0_48,u1_struct_0(k1_tex_2(sK1,sK2))) != iProver_top
% 2.22/1.00      | v7_struct_0(k1_tex_2(sK1,sK2)) != iProver_top
% 2.22/1.00      | v2_struct_0(k1_tex_2(sK1,sK2)) = iProver_top
% 2.22/1.00      | l1_pre_topc(k1_tex_2(sK1,sK2)) != iProver_top ),
% 2.22/1.00      inference(superposition,[status(thm)],[c_5559,c_4054]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_5656,plain,
% 2.22/1.00      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),X0_48),u1_struct_0(sK1)) != iProver_top
% 2.22/1.00      | m1_subset_1(X0_48,u1_struct_0(sK1)) != iProver_top
% 2.22/1.00      | v7_struct_0(k1_tex_2(sK1,sK2)) != iProver_top
% 2.22/1.00      | v2_struct_0(k1_tex_2(sK1,sK2)) = iProver_top
% 2.22/1.00      | l1_pre_topc(k1_tex_2(sK1,sK2)) != iProver_top ),
% 2.22/1.00      inference(light_normalisation,[status(thm)],[c_5562,c_5559]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_5695,plain,
% 2.22/1.00      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top
% 2.22/1.00      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 2.22/1.00      | v7_struct_0(k1_tex_2(sK1,sK2)) != iProver_top
% 2.22/1.00      | v2_struct_0(k1_tex_2(sK1,sK2)) = iProver_top
% 2.22/1.00      | l1_pre_topc(k1_tex_2(sK1,sK2)) != iProver_top ),
% 2.22/1.00      inference(instantiation,[status(thm)],[c_5656]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_15,plain,
% 2.22/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.22/1.00      | v7_struct_0(k1_tex_2(X1,X0))
% 2.22/1.00      | v2_struct_0(X1)
% 2.22/1.00      | ~ l1_pre_topc(X1) ),
% 2.22/1.00      inference(cnf_transformation,[],[f75]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_3361,plain,
% 2.22/1.00      ( ~ m1_subset_1(X0_48,u1_struct_0(X0_47))
% 2.22/1.00      | v7_struct_0(k1_tex_2(X0_47,X0_48))
% 2.22/1.00      | v2_struct_0(X0_47)
% 2.22/1.00      | ~ l1_pre_topc(X0_47) ),
% 2.22/1.00      inference(subtyping,[status(esa)],[c_15]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_3429,plain,
% 2.22/1.00      ( m1_subset_1(X0_48,u1_struct_0(X0_47)) != iProver_top
% 2.22/1.00      | v7_struct_0(k1_tex_2(X0_47,X0_48)) = iProver_top
% 2.22/1.00      | v2_struct_0(X0_47) = iProver_top
% 2.22/1.00      | l1_pre_topc(X0_47) != iProver_top ),
% 2.22/1.00      inference(predicate_to_equality,[status(thm)],[c_3361]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_3431,plain,
% 2.22/1.00      ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 2.22/1.00      | v7_struct_0(k1_tex_2(sK1,sK2)) = iProver_top
% 2.22/1.00      | v2_struct_0(sK1) = iProver_top
% 2.22/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.22/1.00      inference(instantiation,[status(thm)],[c_3429]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(c_29,plain,
% 2.22/1.00      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) = iProver_top
% 2.22/1.00      | v1_tex_2(k1_tex_2(sK1,sK2),sK1) = iProver_top ),
% 2.22/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.22/1.00  
% 2.22/1.00  cnf(contradiction,plain,
% 2.22/1.00      ( $false ),
% 2.22/1.00      inference(minisat,
% 2.22/1.00                [status(thm)],
% 2.22/1.00                [c_5695,c_5171,c_4516,c_4407,c_3431,c_3428,c_3425,c_29,
% 2.22/1.00                 c_28,c_27,c_26]) ).
% 2.22/1.00  
% 2.22/1.00  
% 2.22/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.22/1.00  
% 2.22/1.00  ------                               Statistics
% 2.22/1.00  
% 2.22/1.00  ------ General
% 2.22/1.00  
% 2.22/1.00  abstr_ref_over_cycles:                  0
% 2.22/1.00  abstr_ref_under_cycles:                 0
% 2.22/1.00  gc_basic_clause_elim:                   0
% 2.22/1.00  forced_gc_time:                         0
% 2.22/1.00  parsing_time:                           0.008
% 2.22/1.00  unif_index_cands_time:                  0.
% 2.22/1.00  unif_index_add_time:                    0.
% 2.22/1.00  orderings_time:                         0.
% 2.22/1.00  out_proof_time:                         0.016
% 2.22/1.00  total_time:                             0.19
% 2.22/1.00  num_of_symbols:                         52
% 2.22/1.00  num_of_terms:                           3031
% 2.22/1.00  
% 2.22/1.00  ------ Preprocessing
% 2.22/1.00  
% 2.22/1.00  num_of_splits:                          0
% 2.22/1.00  num_of_split_atoms:                     0
% 2.22/1.00  num_of_reused_defs:                     0
% 2.22/1.00  num_eq_ax_congr_red:                    17
% 2.22/1.00  num_of_sem_filtered_clauses:            1
% 2.22/1.00  num_of_subtypes:                        2
% 2.22/1.00  monotx_restored_types:                  1
% 2.22/1.00  sat_num_of_epr_types:                   0
% 2.22/1.00  sat_num_of_non_cyclic_types:            0
% 2.22/1.00  sat_guarded_non_collapsed_types:        0
% 2.22/1.00  num_pure_diseq_elim:                    0
% 2.22/1.00  simp_replaced_by:                       0
% 2.22/1.00  res_preprocessed:                       127
% 2.22/1.00  prep_upred:                             0
% 2.22/1.00  prep_unflattend:                        133
% 2.22/1.00  smt_new_axioms:                         0
% 2.22/1.00  pred_elim_cands:                        9
% 2.22/1.00  pred_elim:                              2
% 2.22/1.00  pred_elim_cl:                           2
% 2.22/1.00  pred_elim_cycles:                       15
% 2.22/1.00  merged_defs:                            8
% 2.22/1.00  merged_defs_ncl:                        0
% 2.22/1.00  bin_hyper_res:                          8
% 2.22/1.00  prep_cycles:                            4
% 2.22/1.00  pred_elim_time:                         0.055
% 2.22/1.00  splitting_time:                         0.
% 2.22/1.00  sem_filter_time:                        0.
% 2.22/1.00  monotx_time:                            0.001
% 2.22/1.00  subtype_inf_time:                       0.001
% 2.22/1.00  
% 2.22/1.00  ------ Problem properties
% 2.22/1.00  
% 2.22/1.00  clauses:                                23
% 2.22/1.00  conjectures:                            5
% 2.22/1.00  epr:                                    4
% 2.22/1.00  horn:                                   14
% 2.22/1.00  ground:                                 5
% 2.22/1.00  unary:                                  3
% 2.22/1.00  binary:                                 4
% 2.22/1.00  lits:                                   73
% 2.22/1.00  lits_eq:                                5
% 2.22/1.00  fd_pure:                                0
% 2.22/1.00  fd_pseudo:                              0
% 2.22/1.00  fd_cond:                                0
% 2.22/1.00  fd_pseudo_cond:                         1
% 2.22/1.00  ac_symbols:                             0
% 2.22/1.00  
% 2.22/1.00  ------ Propositional Solver
% 2.22/1.00  
% 2.22/1.00  prop_solver_calls:                      28
% 2.22/1.00  prop_fast_solver_calls:                 1551
% 2.22/1.00  smt_solver_calls:                       0
% 2.22/1.00  smt_fast_solver_calls:                  0
% 2.22/1.00  prop_num_of_clauses:                    877
% 2.22/1.00  prop_preprocess_simplified:             4780
% 2.22/1.00  prop_fo_subsumed:                       39
% 2.22/1.00  prop_solver_time:                       0.
% 2.22/1.00  smt_solver_time:                        0.
% 2.22/1.00  smt_fast_solver_time:                   0.
% 2.22/1.00  prop_fast_solver_time:                  0.
% 2.22/1.00  prop_unsat_core_time:                   0.
% 2.22/1.00  
% 2.22/1.00  ------ QBF
% 2.22/1.00  
% 2.22/1.00  qbf_q_res:                              0
% 2.22/1.00  qbf_num_tautologies:                    0
% 2.22/1.00  qbf_prep_cycles:                        0
% 2.22/1.00  
% 2.22/1.00  ------ BMC1
% 2.22/1.00  
% 2.22/1.00  bmc1_current_bound:                     -1
% 2.22/1.00  bmc1_last_solved_bound:                 -1
% 2.22/1.00  bmc1_unsat_core_size:                   -1
% 2.22/1.00  bmc1_unsat_core_parents_size:           -1
% 2.22/1.00  bmc1_merge_next_fun:                    0
% 2.22/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.22/1.00  
% 2.22/1.00  ------ Instantiation
% 2.22/1.00  
% 2.22/1.00  inst_num_of_clauses:                    211
% 2.22/1.00  inst_num_in_passive:                    1
% 2.22/1.00  inst_num_in_active:                     161
% 2.22/1.00  inst_num_in_unprocessed:                49
% 2.22/1.00  inst_num_of_loops:                      200
% 2.22/1.00  inst_num_of_learning_restarts:          0
% 2.22/1.00  inst_num_moves_active_passive:          35
% 2.22/1.00  inst_lit_activity:                      0
% 2.22/1.00  inst_lit_activity_moves:                0
% 2.22/1.00  inst_num_tautologies:                   0
% 2.22/1.00  inst_num_prop_implied:                  0
% 2.22/1.00  inst_num_existing_simplified:           0
% 2.22/1.00  inst_num_eq_res_simplified:             0
% 2.22/1.00  inst_num_child_elim:                    0
% 2.22/1.00  inst_num_of_dismatching_blockings:      169
% 2.22/1.00  inst_num_of_non_proper_insts:           289
% 2.22/1.00  inst_num_of_duplicates:                 0
% 2.22/1.00  inst_inst_num_from_inst_to_res:         0
% 2.22/1.00  inst_dismatching_checking_time:         0.
% 2.22/1.00  
% 2.22/1.00  ------ Resolution
% 2.22/1.00  
% 2.22/1.00  res_num_of_clauses:                     0
% 2.22/1.00  res_num_in_passive:                     0
% 2.22/1.00  res_num_in_active:                      0
% 2.22/1.00  res_num_of_loops:                       131
% 2.22/1.00  res_forward_subset_subsumed:            27
% 2.22/1.00  res_backward_subset_subsumed:           0
% 2.22/1.00  res_forward_subsumed:                   0
% 2.22/1.00  res_backward_subsumed:                  0
% 2.22/1.00  res_forward_subsumption_resolution:     3
% 2.22/1.00  res_backward_subsumption_resolution:    0
% 2.22/1.00  res_clause_to_clause_subsumption:       225
% 2.22/1.00  res_orphan_elimination:                 0
% 2.22/1.00  res_tautology_del:                      66
% 2.22/1.00  res_num_eq_res_simplified:              0
% 2.22/1.00  res_num_sel_changes:                    0
% 2.22/1.00  res_moves_from_active_to_pass:          0
% 2.22/1.00  
% 2.22/1.00  ------ Superposition
% 2.22/1.00  
% 2.22/1.00  sup_time_total:                         0.
% 2.22/1.00  sup_time_generating:                    0.
% 2.22/1.00  sup_time_sim_full:                      0.
% 2.22/1.00  sup_time_sim_immed:                     0.
% 2.22/1.00  
% 2.22/1.00  sup_num_of_clauses:                     53
% 2.22/1.00  sup_num_in_active:                      37
% 2.22/1.00  sup_num_in_passive:                     16
% 2.22/1.00  sup_num_of_loops:                       39
% 2.22/1.00  sup_fw_superposition:                   8
% 2.22/1.00  sup_bw_superposition:                   28
% 2.22/1.00  sup_immediate_simplified:               5
% 2.22/1.00  sup_given_eliminated:                   0
% 2.22/1.00  comparisons_done:                       0
% 2.22/1.00  comparisons_avoided:                    0
% 2.22/1.00  
% 2.22/1.00  ------ Simplifications
% 2.22/1.00  
% 2.22/1.00  
% 2.22/1.00  sim_fw_subset_subsumed:                 2
% 2.22/1.00  sim_bw_subset_subsumed:                 2
% 2.22/1.00  sim_fw_subsumed:                        0
% 2.22/1.00  sim_bw_subsumed:                        0
% 2.22/1.00  sim_fw_subsumption_res:                 0
% 2.22/1.00  sim_bw_subsumption_res:                 0
% 2.22/1.00  sim_tautology_del:                      2
% 2.22/1.00  sim_eq_tautology_del:                   0
% 2.22/1.00  sim_eq_res_simp:                        0
% 2.22/1.00  sim_fw_demodulated:                     0
% 2.22/1.00  sim_bw_demodulated:                     2
% 2.22/1.00  sim_light_normalised:                   4
% 2.22/1.00  sim_joinable_taut:                      0
% 2.22/1.00  sim_joinable_simp:                      0
% 2.22/1.00  sim_ac_normalised:                      0
% 2.22/1.00  sim_smt_subsumption:                    0
% 2.22/1.00  
%------------------------------------------------------------------------------
