%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:25:44 EST 2020

% Result     : Theorem 3.87s
% Output     : CNFRefutation 3.87s
% Verified   : 
% Statistics : Number of formulae       :  213 (2776 expanded)
%              Number of clauses        :  124 ( 715 expanded)
%              Number of leaves         :   23 ( 610 expanded)
%              Depth                    :   23
%              Number of atoms          :  794 (14119 expanded)
%              Number of equality atoms :  291 (1837 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( v1_tex_2(k1_tex_2(X0,X1),X0)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f45,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

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
    inference(nnf_transformation,[],[f46])).

fof(f61,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f60])).

fof(f63,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),sK4),u1_struct_0(X0))
          | ~ v1_tex_2(k1_tex_2(X0,sK4),X0) )
        & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),sK4),u1_struct_0(X0))
          | v1_tex_2(k1_tex_2(X0,sK4),X0) )
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,
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
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK3),X1),u1_struct_0(sK3))
            | ~ v1_tex_2(k1_tex_2(sK3,X1),sK3) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(sK3),X1),u1_struct_0(sK3))
            | v1_tex_2(k1_tex_2(sK3,X1),sK3) )
          & m1_subset_1(X1,u1_struct_0(sK3)) )
      & l1_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,
    ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),u1_struct_0(sK3))
      | ~ v1_tex_2(k1_tex_2(sK3,sK4),sK3) )
    & ( v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),u1_struct_0(sK3))
      | v1_tex_2(k1_tex_2(sK3,sK4),sK3) )
    & m1_subset_1(sK4,u1_struct_0(sK3))
    & l1_pre_topc(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f61,f63,f62])).

fof(f96,plain,(
    m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f64])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f94,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f64])).

fof(f95,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f64])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f77,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f74,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f2,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f103,plain,(
    ! [X0,X1] :
      ( k2_tarski(X1,X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f78,f69])).

fof(f18,axiom,(
    ! [X0] :
      ( ( ~ v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f93,plain,(
    ! [X0,X1] :
      ( v1_subset_1(k6_domain_1(X0,X1),X0)
      | ~ m1_subset_1(X1,X0)
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f17,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_zfmisc_1(X0)
          | ~ v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_zfmisc_1(X0)
          | ~ v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(X0)
      | ~ v1_subset_1(k6_domain_1(X0,X1),X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f97,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),u1_struct_0(sK3))
    | v1_tex_2(k1_tex_2(sK3,sK4),sK3) ),
    inference(cnf_transformation,[],[f64])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f47])).

fof(f49,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK0(X0,X1) != X0
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( sK0(X0,X1) = X0
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK0(X0,X1) != X0
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( sK0(X0,X1) = X0
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f48,f49])).

fof(f65,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f102,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f65,f69])).

fof(f106,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k2_tarski(X0,X0)) ) ),
    inference(equality_resolution,[],[f102])).

fof(f66,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f101,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f66,f69])).

fof(f104,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_tarski(X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f101])).

fof(f105,plain,(
    ! [X3] : r2_hidden(X3,k2_tarski(X3,X3)) ),
    inference(equality_resolution,[],[f104])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f90,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_pre_topc(X2)
                & ~ v2_struct_0(X2) )
             => ( k1_tex_2(X0,X1) = X2
              <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_tex_2(X0,X1) = X2
              <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_tex_2(X0,X1) = X2
              <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k1_tex_2(X0,X1) = X2
                  | u1_struct_0(X2) != k6_domain_1(u1_struct_0(X0),X1) )
                & ( u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)
                  | k1_tex_2(X0,X1) != X2 ) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)
      | k1_tex_2(X0,X1) != X2
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f108,plain,(
    ! [X0,X1] :
      ( u1_struct_0(k1_tex_2(X0,X1)) = k6_domain_1(u1_struct_0(X0),X1)
      | ~ m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ v1_pre_topc(k1_tex_2(X0,X1))
      | v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f86])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f89,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f13,axiom,(
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
    inference(ennf_transformation,[],[f13])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f55,plain,(
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
    inference(nnf_transformation,[],[f34])).

fof(f56,plain,(
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
    inference(rectify,[],[f55])).

fof(f57,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v1_subset_1(X2,u1_struct_0(X0))
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_subset_1(sK2(X0,X1),u1_struct_0(X0))
        & u1_struct_0(X1) = sK2(X0,X1)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ( ~ v1_subset_1(sK2(X0,X1),u1_struct_0(X0))
                & u1_struct_0(X1) = sK2(X0,X1)
                & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v1_subset_1(X3,u1_struct_0(X0))
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f56,f57])).

fof(f85,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | ~ v1_subset_1(sK2(X0,X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f84,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | u1_struct_0(X1) = sK2(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f98,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),u1_struct_0(sK3))
    | ~ v1_tex_2(k1_tex_2(sK3,sK4),sK3) ),
    inference(cnf_transformation,[],[f64])).

fof(f12,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f51,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f52,plain,(
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
    inference(rectify,[],[f51])).

fof(f53,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k6_domain_1(X0,X2) = X0
          & m1_subset_1(X2,X0) )
     => ( k6_domain_1(X0,sK1(X0)) = X0
        & m1_subset_1(sK1(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ( k6_domain_1(X0,sK1(X0)) = X0
            & m1_subset_1(sK1(X0),X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f52,f53])).

fof(f79,plain,(
    ! [X0] :
      ( m1_subset_1(sK1(X0),X0)
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f80,plain,(
    ! [X0] :
      ( k6_domain_1(X0,sK1(X0)) = X0
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v2_struct_0(X0) )
     => v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f27,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f76,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ~ ( v1_tex_2(X1,X0)
              & u1_struct_0(X0) = u1_struct_0(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_tex_2(X1,X0)
          | u1_struct_0(X0) != u1_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_tex_2(X1,X0)
          | u1_struct_0(X0) != u1_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ v1_tex_2(X1,X0)
      | u1_struct_0(X0) != u1_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_6266,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_6286,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_7105,plain,
    ( r2_hidden(sK4,u1_struct_0(sK3)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6266,c_6286])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_33,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_31,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_34,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_11,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_86,plain,
    ( v2_struct_0(X0) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_88,plain,
    ( v2_struct_0(sK3) = iProver_top
    | l1_struct_0(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_86])).

cnf(c_8,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_91,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_93,plain,
    ( l1_pre_topc(sK3) != iProver_top
    | l1_struct_0(sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_91])).

cnf(c_2141,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | u1_struct_0(sK3) != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_30])).

cnf(c_2142,plain,
    ( r2_hidden(sK4,u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_2141])).

cnf(c_2143,plain,
    ( r2_hidden(sK4,u1_struct_0(sK3)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2142])).

cnf(c_7241,plain,
    ( r2_hidden(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7105,c_33,c_34,c_88,c_93,c_2143])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_6283,plain,
    ( k6_domain_1(X0,X1) = k2_tarski(X1,X1)
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_7136,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK4) = k2_tarski(sK4,sK4)
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6266,c_6283])).

cnf(c_87,plain,
    ( v2_struct_0(sK3)
    | ~ l1_struct_0(sK3)
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_92,plain,
    ( ~ l1_pre_topc(sK3)
    | l1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2133,plain,
    ( v1_xboole_0(X0)
    | k6_domain_1(X0,X1) = k2_tarski(X1,X1)
    | u1_struct_0(sK3) != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_30])).

cnf(c_2134,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
    | k6_domain_1(u1_struct_0(sK3),sK4) = k2_tarski(sK4,sK4) ),
    inference(unflattening,[status(thm)],[c_2133])).

cnf(c_7300,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK4) = k2_tarski(sK4,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7136,c_32,c_31,c_87,c_92,c_2134])).

cnf(c_27,plain,
    ( v1_subset_1(k6_domain_1(X0,X1),X0)
    | ~ m1_subset_1(X1,X0)
    | v1_zfmisc_1(X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_6269,plain,
    ( v1_subset_1(k6_domain_1(X0,X1),X0) = iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | v1_zfmisc_1(X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_7570,plain,
    ( v1_subset_1(k2_tarski(sK4,sK4),u1_struct_0(sK3)) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK3)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7300,c_6269])).

cnf(c_35,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_26,plain,
    ( ~ v1_subset_1(k6_domain_1(X0,X1),X0)
    | ~ m1_subset_1(X1,X0)
    | ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_6270,plain,
    ( v1_subset_1(k6_domain_1(X0,X1),X0) != iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | v1_zfmisc_1(X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_7775,plain,
    ( v1_subset_1(k2_tarski(sK4,sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7300,c_6270])).

cnf(c_29,negated_conjecture,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),u1_struct_0(sK3))
    | v1_tex_2(k1_tex_2(sK3,sK4),sK3) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_36,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),u1_struct_0(sK3)) = iProver_top
    | v1_tex_2(k1_tex_2(sK3,sK4),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k2_tarski(X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f106])).

cnf(c_105,plain,
    ( ~ r2_hidden(sK3,k2_tarski(sK3,sK3))
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2,plain,
    ( r2_hidden(X0,k2_tarski(X0,X0)) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_108,plain,
    ( r2_hidden(sK3,k2_tarski(sK3,sK3)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_22,plain,
    ( m1_pre_topc(k1_tex_2(X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_2658,plain,
    ( m1_pre_topc(k1_tex_2(X0,X1),X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_30])).

cnf(c_2659,plain,
    ( m1_pre_topc(k1_tex_2(X0,sK4),X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_2658])).

cnf(c_2660,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK3)
    | m1_pre_topc(k1_tex_2(X0,sK4),X0) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2659])).

cnf(c_2662,plain,
    ( u1_struct_0(sK3) != u1_struct_0(sK3)
    | m1_pre_topc(k1_tex_2(sK3,sK4),sK3) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2660])).

cnf(c_21,plain,
    ( ~ m1_pre_topc(k1_tex_2(X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v1_pre_topc(k1_tex_2(X0,X1))
    | v2_struct_0(X0)
    | v2_struct_0(k1_tex_2(X0,X1))
    | ~ l1_pre_topc(X0)
    | k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1)) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_192,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v1_pre_topc(k1_tex_2(X0,X1))
    | v2_struct_0(X0)
    | v2_struct_0(k1_tex_2(X0,X1))
    | ~ l1_pre_topc(X0)
    | k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_21,c_22])).

cnf(c_193,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v1_pre_topc(k1_tex_2(X1,X0))
    | v2_struct_0(X1)
    | v2_struct_0(k1_tex_2(X1,X0))
    | ~ l1_pre_topc(X1)
    | k6_domain_1(u1_struct_0(X1),X0) = u1_struct_0(k1_tex_2(X1,X0)) ),
    inference(renaming,[status(thm)],[c_192])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k1_tex_2(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v1_pre_topc(k1_tex_2(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_198,plain,
    ( v2_struct_0(X1)
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | k6_domain_1(u1_struct_0(X1),X0) = u1_struct_0(k1_tex_2(X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_193,c_24,c_23])).

cnf(c_199,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k6_domain_1(u1_struct_0(X1),X0) = u1_struct_0(k1_tex_2(X1,X0)) ),
    inference(renaming,[status(thm)],[c_198])).

cnf(c_2706,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1))
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_199,c_30])).

cnf(c_2707,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k6_domain_1(u1_struct_0(X0),sK4) = u1_struct_0(k1_tex_2(X0,sK4))
    | u1_struct_0(X0) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_2706])).

cnf(c_2709,plain,
    ( v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | k6_domain_1(u1_struct_0(sK3),sK4) = u1_struct_0(k1_tex_2(sK3,sK4))
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2707])).

cnf(c_5534,plain,
    ( X0 != X1
    | u1_struct_0(X0) = u1_struct_0(X1) ),
    theory(equality)).

cnf(c_5547,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_5534])).

cnf(c_16,plain,
    ( ~ v1_subset_1(sK2(X0,X1),u1_struct_0(X0))
    | v1_tex_2(X1,X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_6331,plain,
    ( ~ v1_subset_1(sK2(sK3,k1_tex_2(sK3,sK4)),u1_struct_0(sK3))
    | v1_tex_2(k1_tex_2(sK3,sK4),sK3)
    | ~ m1_pre_topc(k1_tex_2(sK3,sK4),sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_6332,plain,
    ( v1_subset_1(sK2(sK3,k1_tex_2(sK3,sK4)),u1_struct_0(sK3)) != iProver_top
    | v1_tex_2(k1_tex_2(sK3,sK4),sK3) = iProver_top
    | m1_pre_topc(k1_tex_2(sK3,sK4),sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6331])).

cnf(c_17,plain,
    ( v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK2(X1,X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_6334,plain,
    ( v1_tex_2(k1_tex_2(sK3,sK4),sK3)
    | ~ m1_pre_topc(k1_tex_2(sK3,sK4),sK3)
    | ~ l1_pre_topc(sK3)
    | sK2(sK3,k1_tex_2(sK3,sK4)) = u1_struct_0(k1_tex_2(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_6338,plain,
    ( sK2(sK3,k1_tex_2(sK3,sK4)) = u1_struct_0(k1_tex_2(sK3,sK4))
    | v1_tex_2(k1_tex_2(sK3,sK4),sK3) = iProver_top
    | m1_pre_topc(k1_tex_2(sK3,sK4),sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6334])).

cnf(c_28,negated_conjecture,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),u1_struct_0(sK3))
    | ~ v1_tex_2(k1_tex_2(sK3,sK4),sK3) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_6268,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),u1_struct_0(sK3)) != iProver_top
    | v1_tex_2(k1_tex_2(sK3,sK4),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_7303,plain,
    ( v1_subset_1(k2_tarski(sK4,sK4),u1_struct_0(sK3)) != iProver_top
    | v1_tex_2(k1_tex_2(sK3,sK4),sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7300,c_6268])).

cnf(c_5538,plain,
    ( ~ v1_subset_1(X0,X1)
    | v1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_6733,plain,
    ( ~ v1_subset_1(X0,X1)
    | v1_subset_1(sK2(X2,k1_tex_2(sK3,sK4)),u1_struct_0(X2))
    | sK2(X2,k1_tex_2(sK3,sK4)) != X0
    | u1_struct_0(X2) != X1 ),
    inference(instantiation,[status(thm)],[c_5538])).

cnf(c_7431,plain,
    ( v1_subset_1(sK2(X0,k1_tex_2(sK3,sK4)),u1_struct_0(X0))
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),u1_struct_0(sK3))
    | sK2(X0,k1_tex_2(sK3,sK4)) != k6_domain_1(u1_struct_0(sK3),sK4)
    | u1_struct_0(X0) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_6733])).

cnf(c_7432,plain,
    ( sK2(X0,k1_tex_2(sK3,sK4)) != k6_domain_1(u1_struct_0(sK3),sK4)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | v1_subset_1(sK2(X0,k1_tex_2(sK3,sK4)),u1_struct_0(X0)) = iProver_top
    | v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7431])).

cnf(c_7434,plain,
    ( sK2(sK3,k1_tex_2(sK3,sK4)) != k6_domain_1(u1_struct_0(sK3),sK4)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | v1_subset_1(sK2(sK3,k1_tex_2(sK3,sK4)),u1_struct_0(sK3)) = iProver_top
    | v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),u1_struct_0(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7432])).

cnf(c_5527,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_6717,plain,
    ( X0 != X1
    | sK2(sK3,k1_tex_2(sK3,sK4)) != X1
    | sK2(sK3,k1_tex_2(sK3,sK4)) = X0 ),
    inference(instantiation,[status(thm)],[c_5527])).

cnf(c_7344,plain,
    ( X0 != u1_struct_0(k1_tex_2(sK3,sK4))
    | sK2(sK3,k1_tex_2(sK3,sK4)) = X0
    | sK2(sK3,k1_tex_2(sK3,sK4)) != u1_struct_0(k1_tex_2(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_6717])).

cnf(c_7576,plain,
    ( sK2(sK3,k1_tex_2(sK3,sK4)) = k6_domain_1(u1_struct_0(sK3),sK4)
    | sK2(sK3,k1_tex_2(sK3,sK4)) != u1_struct_0(k1_tex_2(sK3,sK4))
    | k6_domain_1(u1_struct_0(sK3),sK4) != u1_struct_0(k1_tex_2(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_7344])).

cnf(c_7960,plain,
    ( v1_subset_1(k2_tarski(sK4,sK4),u1_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7775,c_32,c_33,c_31,c_34,c_36,c_105,c_108,c_2662,c_2709,c_5547,c_6332,c_6338,c_7303,c_7434,c_7576])).

cnf(c_8044,plain,
    ( v1_zfmisc_1(u1_struct_0(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7570,c_32,c_33,c_31,c_34,c_36,c_105,c_108,c_2662,c_2709,c_3667,c_5547,c_6332,c_6338,c_7434,c_7576])).

cnf(c_15,plain,
    ( m1_subset_1(sK1(X0),X0)
    | ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_6280,plain,
    ( m1_subset_1(sK1(X0),X0) = iProver_top
    | v1_zfmisc_1(X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_7135,plain,
    ( k2_tarski(sK1(X0),sK1(X0)) = k6_domain_1(X0,sK1(X0))
    | v1_zfmisc_1(X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6280,c_6283])).

cnf(c_10138,plain,
    ( k2_tarski(sK1(u1_struct_0(sK3)),sK1(u1_struct_0(sK3))) = k6_domain_1(u1_struct_0(sK3),sK1(u1_struct_0(sK3)))
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8044,c_7135])).

cnf(c_14,plain,
    ( ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0)
    | k6_domain_1(X0,sK1(X0)) = X0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_6281,plain,
    ( k6_domain_1(X0,sK1(X0)) = X0
    | v1_zfmisc_1(X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_8048,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK1(u1_struct_0(sK3))) = u1_struct_0(sK3)
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8044,c_6281])).

cnf(c_443,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_8,c_11])).

cnf(c_1728,plain,
    ( ~ v1_zfmisc_1(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k6_domain_1(X0,sK1(X0)) = X0
    | u1_struct_0(X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_443,c_14])).

cnf(c_1729,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k6_domain_1(u1_struct_0(X0),sK1(u1_struct_0(X0))) = u1_struct_0(X0) ),
    inference(unflattening,[status(thm)],[c_1728])).

cnf(c_1730,plain,
    ( k6_domain_1(u1_struct_0(X0),sK1(u1_struct_0(X0))) = u1_struct_0(X0)
    | v1_zfmisc_1(u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1729])).

cnf(c_1732,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK1(u1_struct_0(sK3))) = u1_struct_0(sK3)
    | v1_zfmisc_1(u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1730])).

cnf(c_3058,plain,
    ( ~ v1_tex_2(k1_tex_2(sK3,sK4),sK3)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),u1_struct_0(sK3)) ),
    inference(prop_impl,[status(thm)],[c_28])).

cnf(c_3059,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),u1_struct_0(sK3))
    | ~ v1_tex_2(k1_tex_2(sK3,sK4),sK3) ),
    inference(renaming,[status(thm)],[c_3058])).

cnf(c_3662,plain,
    ( ~ v1_tex_2(k1_tex_2(sK3,sK4),sK3)
    | ~ m1_subset_1(X0,X1)
    | v1_zfmisc_1(X1)
    | v1_xboole_0(X1)
    | k6_domain_1(u1_struct_0(sK3),sK4) != k6_domain_1(X1,X0)
    | u1_struct_0(sK3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_3059])).

cnf(c_3663,plain,
    ( ~ v1_tex_2(k1_tex_2(sK3,sK4),sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | v1_zfmisc_1(u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3))
    | k6_domain_1(u1_struct_0(sK3),sK4) != k6_domain_1(u1_struct_0(sK3),X0) ),
    inference(unflattening,[status(thm)],[c_3662])).

cnf(c_2274,plain,
    ( v1_subset_1(k6_domain_1(X0,X1),X0)
    | v1_zfmisc_1(X0)
    | v1_xboole_0(X0)
    | u1_struct_0(sK3) != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_30])).

cnf(c_2275,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),u1_struct_0(sK3))
    | v1_zfmisc_1(u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_2274])).

cnf(c_3665,plain,
    ( ~ v1_tex_2(k1_tex_2(sK3,sK4),sK3)
    | v1_zfmisc_1(u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3663,c_32,c_31,c_28,c_87,c_92,c_2275])).

cnf(c_3667,plain,
    ( v1_tex_2(k1_tex_2(sK3,sK4),sK3) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3665])).

cnf(c_8202,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK1(u1_struct_0(sK3))) = u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8048,c_32,c_33,c_31,c_34,c_36,c_105,c_108,c_1732,c_2662,c_2709,c_3667,c_5547,c_6332,c_6338,c_7434,c_7576])).

cnf(c_10139,plain,
    ( k2_tarski(sK1(u1_struct_0(sK3)),sK1(u1_struct_0(sK3))) = u1_struct_0(sK3)
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10138,c_8202])).

cnf(c_10791,plain,
    ( k2_tarski(sK1(u1_struct_0(sK3)),sK1(u1_struct_0(sK3))) = u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10139,c_33,c_34,c_88,c_93])).

cnf(c_6288,plain,
    ( X0 = X1
    | r2_hidden(X0,k2_tarski(X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_10806,plain,
    ( sK1(u1_struct_0(sK3)) = X0
    | r2_hidden(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10791,c_6288])).

cnf(c_11172,plain,
    ( sK1(u1_struct_0(sK3)) = sK4 ),
    inference(superposition,[status(thm)],[c_7241,c_10806])).

cnf(c_6263,plain,
    ( k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1))
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_199])).

cnf(c_7099,plain,
    ( k6_domain_1(u1_struct_0(X0),sK1(u1_struct_0(X0))) = u1_struct_0(k1_tex_2(X0,sK1(u1_struct_0(X0))))
    | v1_zfmisc_1(u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6280,c_6263])).

cnf(c_2386,plain,
    ( ~ v1_zfmisc_1(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0)
    | k6_domain_1(u1_struct_0(X1),X2) = u1_struct_0(k1_tex_2(X1,X2))
    | sK1(X0) != X2
    | u1_struct_0(X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_199])).

cnf(c_2387,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | v1_xboole_0(u1_struct_0(X0))
    | k6_domain_1(u1_struct_0(X0),sK1(u1_struct_0(X0))) = u1_struct_0(k1_tex_2(X0,sK1(u1_struct_0(X0)))) ),
    inference(unflattening,[status(thm)],[c_2386])).

cnf(c_10,plain,
    ( ~ v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_457,plain,
    ( ~ v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | v1_xboole_0(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_8,c_10])).

cnf(c_2391,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(X0)
    | v1_xboole_0(u1_struct_0(X0))
    | k6_domain_1(u1_struct_0(X0),sK1(u1_struct_0(X0))) = u1_struct_0(k1_tex_2(X0,sK1(u1_struct_0(X0)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2387,c_457])).

cnf(c_2393,plain,
    ( k6_domain_1(u1_struct_0(X0),sK1(u1_struct_0(X0))) = u1_struct_0(k1_tex_2(X0,sK1(u1_struct_0(X0))))
    | v1_zfmisc_1(u1_struct_0(X0)) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2391])).

cnf(c_10016,plain,
    ( v1_zfmisc_1(u1_struct_0(X0)) != iProver_top
    | k6_domain_1(u1_struct_0(X0),sK1(u1_struct_0(X0))) = u1_struct_0(k1_tex_2(X0,sK1(u1_struct_0(X0))))
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7099,c_2393])).

cnf(c_10017,plain,
    ( k6_domain_1(u1_struct_0(X0),sK1(u1_struct_0(X0))) = u1_struct_0(k1_tex_2(X0,sK1(u1_struct_0(X0))))
    | v1_zfmisc_1(u1_struct_0(X0)) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_10016])).

cnf(c_10020,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK1(u1_struct_0(sK3))) = u1_struct_0(k1_tex_2(sK3,sK1(u1_struct_0(sK3))))
    | l1_pre_topc(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8044,c_10017])).

cnf(c_10023,plain,
    ( u1_struct_0(k1_tex_2(sK3,sK1(u1_struct_0(sK3)))) = u1_struct_0(sK3)
    | l1_pre_topc(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10020,c_8202])).

cnf(c_10903,plain,
    ( u1_struct_0(k1_tex_2(sK3,sK1(u1_struct_0(sK3)))) = u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10023,c_33,c_34,c_88,c_93])).

cnf(c_11293,plain,
    ( u1_struct_0(k1_tex_2(sK3,sK4)) = u1_struct_0(sK3) ),
    inference(demodulation,[status(thm)],[c_11172,c_10903])).

cnf(c_25,plain,
    ( ~ v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X0) != u1_struct_0(X1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_6345,plain,
    ( ~ v1_tex_2(X0,sK3)
    | ~ m1_pre_topc(X0,sK3)
    | ~ l1_pre_topc(sK3)
    | u1_struct_0(X0) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_7910,plain,
    ( ~ v1_tex_2(k1_tex_2(sK3,sK4),sK3)
    | ~ m1_pre_topc(k1_tex_2(sK3,sK4),sK3)
    | ~ l1_pre_topc(sK3)
    | u1_struct_0(k1_tex_2(sK3,sK4)) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_6345])).

cnf(c_7911,plain,
    ( u1_struct_0(k1_tex_2(sK3,sK4)) != u1_struct_0(sK3)
    | v1_tex_2(k1_tex_2(sK3,sK4),sK3) != iProver_top
    | m1_pre_topc(k1_tex_2(sK3,sK4),sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7910])).

cnf(c_6267,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),u1_struct_0(sK3)) = iProver_top
    | v1_tex_2(k1_tex_2(sK3,sK4),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_7302,plain,
    ( v1_subset_1(k2_tarski(sK4,sK4),u1_struct_0(sK3)) = iProver_top
    | v1_tex_2(k1_tex_2(sK3,sK4),sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7300,c_6267])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11293,c_7960,c_7911,c_7302,c_5547,c_2662,c_108,c_105,c_34,c_33])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 12:28:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.87/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.87/0.99  
% 3.87/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.87/0.99  
% 3.87/0.99  ------  iProver source info
% 3.87/0.99  
% 3.87/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.87/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.87/0.99  git: non_committed_changes: false
% 3.87/0.99  git: last_make_outside_of_git: false
% 3.87/0.99  
% 3.87/0.99  ------ 
% 3.87/0.99  
% 3.87/0.99  ------ Input Options
% 3.87/0.99  
% 3.87/0.99  --out_options                           all
% 3.87/0.99  --tptp_safe_out                         true
% 3.87/0.99  --problem_path                          ""
% 3.87/0.99  --include_path                          ""
% 3.87/0.99  --clausifier                            res/vclausify_rel
% 3.87/0.99  --clausifier_options                    ""
% 3.87/0.99  --stdin                                 false
% 3.87/0.99  --stats_out                             all
% 3.87/0.99  
% 3.87/0.99  ------ General Options
% 3.87/0.99  
% 3.87/0.99  --fof                                   false
% 3.87/0.99  --time_out_real                         305.
% 3.87/0.99  --time_out_virtual                      -1.
% 3.87/0.99  --symbol_type_check                     false
% 3.87/0.99  --clausify_out                          false
% 3.87/0.99  --sig_cnt_out                           false
% 3.87/0.99  --trig_cnt_out                          false
% 3.87/0.99  --trig_cnt_out_tolerance                1.
% 3.87/0.99  --trig_cnt_out_sk_spl                   false
% 3.87/0.99  --abstr_cl_out                          false
% 3.87/0.99  
% 3.87/0.99  ------ Global Options
% 3.87/0.99  
% 3.87/0.99  --schedule                              default
% 3.87/0.99  --add_important_lit                     false
% 3.87/0.99  --prop_solver_per_cl                    1000
% 3.87/0.99  --min_unsat_core                        false
% 3.87/0.99  --soft_assumptions                      false
% 3.87/0.99  --soft_lemma_size                       3
% 3.87/0.99  --prop_impl_unit_size                   0
% 3.87/0.99  --prop_impl_unit                        []
% 3.87/0.99  --share_sel_clauses                     true
% 3.87/0.99  --reset_solvers                         false
% 3.87/0.99  --bc_imp_inh                            [conj_cone]
% 3.87/0.99  --conj_cone_tolerance                   3.
% 3.87/0.99  --extra_neg_conj                        none
% 3.87/0.99  --large_theory_mode                     true
% 3.87/0.99  --prolific_symb_bound                   200
% 3.87/0.99  --lt_threshold                          2000
% 3.87/0.99  --clause_weak_htbl                      true
% 3.87/0.99  --gc_record_bc_elim                     false
% 3.87/0.99  
% 3.87/0.99  ------ Preprocessing Options
% 3.87/0.99  
% 3.87/0.99  --preprocessing_flag                    true
% 3.87/0.99  --time_out_prep_mult                    0.1
% 3.87/0.99  --splitting_mode                        input
% 3.87/0.99  --splitting_grd                         true
% 3.87/0.99  --splitting_cvd                         false
% 3.87/0.99  --splitting_cvd_svl                     false
% 3.87/0.99  --splitting_nvd                         32
% 3.87/0.99  --sub_typing                            true
% 3.87/0.99  --prep_gs_sim                           true
% 3.87/0.99  --prep_unflatten                        true
% 3.87/0.99  --prep_res_sim                          true
% 3.87/0.99  --prep_upred                            true
% 3.87/0.99  --prep_sem_filter                       exhaustive
% 3.87/0.99  --prep_sem_filter_out                   false
% 3.87/0.99  --pred_elim                             true
% 3.87/0.99  --res_sim_input                         true
% 3.87/0.99  --eq_ax_congr_red                       true
% 3.87/0.99  --pure_diseq_elim                       true
% 3.87/0.99  --brand_transform                       false
% 3.87/0.99  --non_eq_to_eq                          false
% 3.87/0.99  --prep_def_merge                        true
% 3.87/0.99  --prep_def_merge_prop_impl              false
% 3.87/0.99  --prep_def_merge_mbd                    true
% 3.87/0.99  --prep_def_merge_tr_red                 false
% 3.87/0.99  --prep_def_merge_tr_cl                  false
% 3.87/0.99  --smt_preprocessing                     true
% 3.87/0.99  --smt_ac_axioms                         fast
% 3.87/0.99  --preprocessed_out                      false
% 3.87/0.99  --preprocessed_stats                    false
% 3.87/0.99  
% 3.87/0.99  ------ Abstraction refinement Options
% 3.87/0.99  
% 3.87/0.99  --abstr_ref                             []
% 3.87/0.99  --abstr_ref_prep                        false
% 3.87/0.99  --abstr_ref_until_sat                   false
% 3.87/0.99  --abstr_ref_sig_restrict                funpre
% 3.87/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.87/0.99  --abstr_ref_under                       []
% 3.87/0.99  
% 3.87/0.99  ------ SAT Options
% 3.87/0.99  
% 3.87/0.99  --sat_mode                              false
% 3.87/0.99  --sat_fm_restart_options                ""
% 3.87/0.99  --sat_gr_def                            false
% 3.87/0.99  --sat_epr_types                         true
% 3.87/0.99  --sat_non_cyclic_types                  false
% 3.87/0.99  --sat_finite_models                     false
% 3.87/0.99  --sat_fm_lemmas                         false
% 3.87/0.99  --sat_fm_prep                           false
% 3.87/0.99  --sat_fm_uc_incr                        true
% 3.87/0.99  --sat_out_model                         small
% 3.87/0.99  --sat_out_clauses                       false
% 3.87/0.99  
% 3.87/0.99  ------ QBF Options
% 3.87/0.99  
% 3.87/0.99  --qbf_mode                              false
% 3.87/0.99  --qbf_elim_univ                         false
% 3.87/0.99  --qbf_dom_inst                          none
% 3.87/0.99  --qbf_dom_pre_inst                      false
% 3.87/0.99  --qbf_sk_in                             false
% 3.87/0.99  --qbf_pred_elim                         true
% 3.87/0.99  --qbf_split                             512
% 3.87/0.99  
% 3.87/0.99  ------ BMC1 Options
% 3.87/0.99  
% 3.87/0.99  --bmc1_incremental                      false
% 3.87/0.99  --bmc1_axioms                           reachable_all
% 3.87/0.99  --bmc1_min_bound                        0
% 3.87/0.99  --bmc1_max_bound                        -1
% 3.87/0.99  --bmc1_max_bound_default                -1
% 3.87/0.99  --bmc1_symbol_reachability              true
% 3.87/0.99  --bmc1_property_lemmas                  false
% 3.87/0.99  --bmc1_k_induction                      false
% 3.87/0.99  --bmc1_non_equiv_states                 false
% 3.87/0.99  --bmc1_deadlock                         false
% 3.87/0.99  --bmc1_ucm                              false
% 3.87/0.99  --bmc1_add_unsat_core                   none
% 3.87/0.99  --bmc1_unsat_core_children              false
% 3.87/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.87/0.99  --bmc1_out_stat                         full
% 3.87/0.99  --bmc1_ground_init                      false
% 3.87/0.99  --bmc1_pre_inst_next_state              false
% 3.87/0.99  --bmc1_pre_inst_state                   false
% 3.87/0.99  --bmc1_pre_inst_reach_state             false
% 3.87/0.99  --bmc1_out_unsat_core                   false
% 3.87/0.99  --bmc1_aig_witness_out                  false
% 3.87/0.99  --bmc1_verbose                          false
% 3.87/0.99  --bmc1_dump_clauses_tptp                false
% 3.87/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.87/0.99  --bmc1_dump_file                        -
% 3.87/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.87/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.87/0.99  --bmc1_ucm_extend_mode                  1
% 3.87/0.99  --bmc1_ucm_init_mode                    2
% 3.87/0.99  --bmc1_ucm_cone_mode                    none
% 3.87/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.87/0.99  --bmc1_ucm_relax_model                  4
% 3.87/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.87/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.87/0.99  --bmc1_ucm_layered_model                none
% 3.87/0.99  --bmc1_ucm_max_lemma_size               10
% 3.87/0.99  
% 3.87/0.99  ------ AIG Options
% 3.87/0.99  
% 3.87/0.99  --aig_mode                              false
% 3.87/0.99  
% 3.87/0.99  ------ Instantiation Options
% 3.87/0.99  
% 3.87/0.99  --instantiation_flag                    true
% 3.87/0.99  --inst_sos_flag                         true
% 3.87/0.99  --inst_sos_phase                        true
% 3.87/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.87/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.87/0.99  --inst_lit_sel_side                     num_symb
% 3.87/0.99  --inst_solver_per_active                1400
% 3.87/0.99  --inst_solver_calls_frac                1.
% 3.87/0.99  --inst_passive_queue_type               priority_queues
% 3.87/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.87/0.99  --inst_passive_queues_freq              [25;2]
% 3.87/0.99  --inst_dismatching                      true
% 3.87/0.99  --inst_eager_unprocessed_to_passive     true
% 3.87/0.99  --inst_prop_sim_given                   true
% 3.87/0.99  --inst_prop_sim_new                     false
% 3.87/0.99  --inst_subs_new                         false
% 3.87/0.99  --inst_eq_res_simp                      false
% 3.87/0.99  --inst_subs_given                       false
% 3.87/0.99  --inst_orphan_elimination               true
% 3.87/0.99  --inst_learning_loop_flag               true
% 3.87/0.99  --inst_learning_start                   3000
% 3.87/0.99  --inst_learning_factor                  2
% 3.87/0.99  --inst_start_prop_sim_after_learn       3
% 3.87/0.99  --inst_sel_renew                        solver
% 3.87/0.99  --inst_lit_activity_flag                true
% 3.87/0.99  --inst_restr_to_given                   false
% 3.87/0.99  --inst_activity_threshold               500
% 3.87/0.99  --inst_out_proof                        true
% 3.87/0.99  
% 3.87/0.99  ------ Resolution Options
% 3.87/0.99  
% 3.87/0.99  --resolution_flag                       true
% 3.87/0.99  --res_lit_sel                           adaptive
% 3.87/0.99  --res_lit_sel_side                      none
% 3.87/0.99  --res_ordering                          kbo
% 3.87/0.99  --res_to_prop_solver                    active
% 3.87/0.99  --res_prop_simpl_new                    false
% 3.87/0.99  --res_prop_simpl_given                  true
% 3.87/0.99  --res_passive_queue_type                priority_queues
% 3.87/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.87/0.99  --res_passive_queues_freq               [15;5]
% 3.87/0.99  --res_forward_subs                      full
% 3.87/0.99  --res_backward_subs                     full
% 3.87/0.99  --res_forward_subs_resolution           true
% 3.87/0.99  --res_backward_subs_resolution          true
% 3.87/0.99  --res_orphan_elimination                true
% 3.87/0.99  --res_time_limit                        2.
% 3.87/0.99  --res_out_proof                         true
% 3.87/0.99  
% 3.87/0.99  ------ Superposition Options
% 3.87/0.99  
% 3.87/0.99  --superposition_flag                    true
% 3.87/0.99  --sup_passive_queue_type                priority_queues
% 3.87/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.87/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.87/0.99  --demod_completeness_check              fast
% 3.87/0.99  --demod_use_ground                      true
% 3.87/0.99  --sup_to_prop_solver                    passive
% 3.87/0.99  --sup_prop_simpl_new                    true
% 3.87/0.99  --sup_prop_simpl_given                  true
% 3.87/0.99  --sup_fun_splitting                     true
% 3.87/0.99  --sup_smt_interval                      50000
% 3.87/0.99  
% 3.87/0.99  ------ Superposition Simplification Setup
% 3.87/0.99  
% 3.87/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.87/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.87/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.87/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.87/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.87/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.87/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.87/0.99  --sup_immed_triv                        [TrivRules]
% 3.87/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.87/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.87/0.99  --sup_immed_bw_main                     []
% 3.87/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.87/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.87/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.87/0.99  --sup_input_bw                          []
% 3.87/0.99  
% 3.87/0.99  ------ Combination Options
% 3.87/0.99  
% 3.87/0.99  --comb_res_mult                         3
% 3.87/0.99  --comb_sup_mult                         2
% 3.87/0.99  --comb_inst_mult                        10
% 3.87/0.99  
% 3.87/0.99  ------ Debug Options
% 3.87/0.99  
% 3.87/0.99  --dbg_backtrace                         false
% 3.87/0.99  --dbg_dump_prop_clauses                 false
% 3.87/0.99  --dbg_dump_prop_clauses_file            -
% 3.87/0.99  --dbg_out_stat                          false
% 3.87/0.99  ------ Parsing...
% 3.87/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.87/0.99  
% 3.87/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.87/0.99  
% 3.87/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.87/0.99  
% 3.87/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.87/0.99  ------ Proving...
% 3.87/0.99  ------ Problem Properties 
% 3.87/0.99  
% 3.87/0.99  
% 3.87/0.99  clauses                                 32
% 3.87/0.99  conjectures                             5
% 3.87/0.99  EPR                                     4
% 3.87/0.99  Horn                                    18
% 3.87/0.99  unary                                   6
% 3.87/0.99  binary                                  3
% 3.87/0.99  lits                                    99
% 3.87/0.99  lits eq                                 14
% 3.87/0.99  fd_pure                                 0
% 3.87/0.99  fd_pseudo                               0
% 3.87/0.99  fd_cond                                 0
% 3.87/0.99  fd_pseudo_cond                          3
% 3.87/0.99  AC symbols                              0
% 3.87/0.99  
% 3.87/0.99  ------ Schedule dynamic 5 is on 
% 3.87/0.99  
% 3.87/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.87/0.99  
% 3.87/0.99  
% 3.87/0.99  ------ 
% 3.87/0.99  Current options:
% 3.87/0.99  ------ 
% 3.87/0.99  
% 3.87/0.99  ------ Input Options
% 3.87/0.99  
% 3.87/0.99  --out_options                           all
% 3.87/0.99  --tptp_safe_out                         true
% 3.87/0.99  --problem_path                          ""
% 3.87/0.99  --include_path                          ""
% 3.87/0.99  --clausifier                            res/vclausify_rel
% 3.87/0.99  --clausifier_options                    ""
% 3.87/0.99  --stdin                                 false
% 3.87/0.99  --stats_out                             all
% 3.87/0.99  
% 3.87/0.99  ------ General Options
% 3.87/0.99  
% 3.87/0.99  --fof                                   false
% 3.87/0.99  --time_out_real                         305.
% 3.87/0.99  --time_out_virtual                      -1.
% 3.87/0.99  --symbol_type_check                     false
% 3.87/0.99  --clausify_out                          false
% 3.87/0.99  --sig_cnt_out                           false
% 3.87/0.99  --trig_cnt_out                          false
% 3.87/0.99  --trig_cnt_out_tolerance                1.
% 3.87/0.99  --trig_cnt_out_sk_spl                   false
% 3.87/0.99  --abstr_cl_out                          false
% 3.87/0.99  
% 3.87/0.99  ------ Global Options
% 3.87/0.99  
% 3.87/0.99  --schedule                              default
% 3.87/0.99  --add_important_lit                     false
% 3.87/0.99  --prop_solver_per_cl                    1000
% 3.87/0.99  --min_unsat_core                        false
% 3.87/0.99  --soft_assumptions                      false
% 3.87/0.99  --soft_lemma_size                       3
% 3.87/0.99  --prop_impl_unit_size                   0
% 3.87/0.99  --prop_impl_unit                        []
% 3.87/0.99  --share_sel_clauses                     true
% 3.87/0.99  --reset_solvers                         false
% 3.87/0.99  --bc_imp_inh                            [conj_cone]
% 3.87/0.99  --conj_cone_tolerance                   3.
% 3.87/0.99  --extra_neg_conj                        none
% 3.87/0.99  --large_theory_mode                     true
% 3.87/0.99  --prolific_symb_bound                   200
% 3.87/0.99  --lt_threshold                          2000
% 3.87/0.99  --clause_weak_htbl                      true
% 3.87/0.99  --gc_record_bc_elim                     false
% 3.87/0.99  
% 3.87/0.99  ------ Preprocessing Options
% 3.87/0.99  
% 3.87/0.99  --preprocessing_flag                    true
% 3.87/0.99  --time_out_prep_mult                    0.1
% 3.87/0.99  --splitting_mode                        input
% 3.87/0.99  --splitting_grd                         true
% 3.87/0.99  --splitting_cvd                         false
% 3.87/0.99  --splitting_cvd_svl                     false
% 3.87/0.99  --splitting_nvd                         32
% 3.87/0.99  --sub_typing                            true
% 3.87/0.99  --prep_gs_sim                           true
% 3.87/0.99  --prep_unflatten                        true
% 3.87/0.99  --prep_res_sim                          true
% 3.87/0.99  --prep_upred                            true
% 3.87/0.99  --prep_sem_filter                       exhaustive
% 3.87/0.99  --prep_sem_filter_out                   false
% 3.87/0.99  --pred_elim                             true
% 3.87/0.99  --res_sim_input                         true
% 3.87/0.99  --eq_ax_congr_red                       true
% 3.87/0.99  --pure_diseq_elim                       true
% 3.87/0.99  --brand_transform                       false
% 3.87/0.99  --non_eq_to_eq                          false
% 3.87/0.99  --prep_def_merge                        true
% 3.87/0.99  --prep_def_merge_prop_impl              false
% 3.87/0.99  --prep_def_merge_mbd                    true
% 3.87/0.99  --prep_def_merge_tr_red                 false
% 3.87/0.99  --prep_def_merge_tr_cl                  false
% 3.87/0.99  --smt_preprocessing                     true
% 3.87/0.99  --smt_ac_axioms                         fast
% 3.87/0.99  --preprocessed_out                      false
% 3.87/0.99  --preprocessed_stats                    false
% 3.87/0.99  
% 3.87/0.99  ------ Abstraction refinement Options
% 3.87/0.99  
% 3.87/0.99  --abstr_ref                             []
% 3.87/0.99  --abstr_ref_prep                        false
% 3.87/0.99  --abstr_ref_until_sat                   false
% 3.87/0.99  --abstr_ref_sig_restrict                funpre
% 3.87/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.87/0.99  --abstr_ref_under                       []
% 3.87/0.99  
% 3.87/0.99  ------ SAT Options
% 3.87/0.99  
% 3.87/0.99  --sat_mode                              false
% 3.87/0.99  --sat_fm_restart_options                ""
% 3.87/0.99  --sat_gr_def                            false
% 3.87/0.99  --sat_epr_types                         true
% 3.87/0.99  --sat_non_cyclic_types                  false
% 3.87/0.99  --sat_finite_models                     false
% 3.87/0.99  --sat_fm_lemmas                         false
% 3.87/0.99  --sat_fm_prep                           false
% 3.87/0.99  --sat_fm_uc_incr                        true
% 3.87/0.99  --sat_out_model                         small
% 3.87/0.99  --sat_out_clauses                       false
% 3.87/0.99  
% 3.87/0.99  ------ QBF Options
% 3.87/0.99  
% 3.87/0.99  --qbf_mode                              false
% 3.87/0.99  --qbf_elim_univ                         false
% 3.87/0.99  --qbf_dom_inst                          none
% 3.87/0.99  --qbf_dom_pre_inst                      false
% 3.87/0.99  --qbf_sk_in                             false
% 3.87/0.99  --qbf_pred_elim                         true
% 3.87/0.99  --qbf_split                             512
% 3.87/0.99  
% 3.87/0.99  ------ BMC1 Options
% 3.87/0.99  
% 3.87/0.99  --bmc1_incremental                      false
% 3.87/0.99  --bmc1_axioms                           reachable_all
% 3.87/0.99  --bmc1_min_bound                        0
% 3.87/0.99  --bmc1_max_bound                        -1
% 3.87/0.99  --bmc1_max_bound_default                -1
% 3.87/0.99  --bmc1_symbol_reachability              true
% 3.87/0.99  --bmc1_property_lemmas                  false
% 3.87/0.99  --bmc1_k_induction                      false
% 3.87/0.99  --bmc1_non_equiv_states                 false
% 3.87/0.99  --bmc1_deadlock                         false
% 3.87/0.99  --bmc1_ucm                              false
% 3.87/0.99  --bmc1_add_unsat_core                   none
% 3.87/0.99  --bmc1_unsat_core_children              false
% 3.87/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.87/0.99  --bmc1_out_stat                         full
% 3.87/0.99  --bmc1_ground_init                      false
% 3.87/0.99  --bmc1_pre_inst_next_state              false
% 3.87/0.99  --bmc1_pre_inst_state                   false
% 3.87/0.99  --bmc1_pre_inst_reach_state             false
% 3.87/0.99  --bmc1_out_unsat_core                   false
% 3.87/0.99  --bmc1_aig_witness_out                  false
% 3.87/0.99  --bmc1_verbose                          false
% 3.87/0.99  --bmc1_dump_clauses_tptp                false
% 3.87/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.87/0.99  --bmc1_dump_file                        -
% 3.87/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.87/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.87/0.99  --bmc1_ucm_extend_mode                  1
% 3.87/0.99  --bmc1_ucm_init_mode                    2
% 3.87/0.99  --bmc1_ucm_cone_mode                    none
% 3.87/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.87/0.99  --bmc1_ucm_relax_model                  4
% 3.87/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.87/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.87/0.99  --bmc1_ucm_layered_model                none
% 3.87/0.99  --bmc1_ucm_max_lemma_size               10
% 3.87/0.99  
% 3.87/0.99  ------ AIG Options
% 3.87/0.99  
% 3.87/0.99  --aig_mode                              false
% 3.87/0.99  
% 3.87/0.99  ------ Instantiation Options
% 3.87/0.99  
% 3.87/0.99  --instantiation_flag                    true
% 3.87/0.99  --inst_sos_flag                         true
% 3.87/0.99  --inst_sos_phase                        true
% 3.87/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.87/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.87/0.99  --inst_lit_sel_side                     none
% 3.87/0.99  --inst_solver_per_active                1400
% 3.87/0.99  --inst_solver_calls_frac                1.
% 3.87/0.99  --inst_passive_queue_type               priority_queues
% 3.87/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.87/0.99  --inst_passive_queues_freq              [25;2]
% 3.87/0.99  --inst_dismatching                      true
% 3.87/0.99  --inst_eager_unprocessed_to_passive     true
% 3.87/0.99  --inst_prop_sim_given                   true
% 3.87/0.99  --inst_prop_sim_new                     false
% 3.87/0.99  --inst_subs_new                         false
% 3.87/0.99  --inst_eq_res_simp                      false
% 3.87/0.99  --inst_subs_given                       false
% 3.87/0.99  --inst_orphan_elimination               true
% 3.87/0.99  --inst_learning_loop_flag               true
% 3.87/0.99  --inst_learning_start                   3000
% 3.87/0.99  --inst_learning_factor                  2
% 3.87/0.99  --inst_start_prop_sim_after_learn       3
% 3.87/0.99  --inst_sel_renew                        solver
% 3.87/0.99  --inst_lit_activity_flag                true
% 3.87/0.99  --inst_restr_to_given                   false
% 3.87/0.99  --inst_activity_threshold               500
% 3.87/0.99  --inst_out_proof                        true
% 3.87/0.99  
% 3.87/0.99  ------ Resolution Options
% 3.87/0.99  
% 3.87/0.99  --resolution_flag                       false
% 3.87/0.99  --res_lit_sel                           adaptive
% 3.87/0.99  --res_lit_sel_side                      none
% 3.87/0.99  --res_ordering                          kbo
% 3.87/0.99  --res_to_prop_solver                    active
% 3.87/0.99  --res_prop_simpl_new                    false
% 3.87/0.99  --res_prop_simpl_given                  true
% 3.87/0.99  --res_passive_queue_type                priority_queues
% 3.87/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.87/0.99  --res_passive_queues_freq               [15;5]
% 3.87/0.99  --res_forward_subs                      full
% 3.87/0.99  --res_backward_subs                     full
% 3.87/0.99  --res_forward_subs_resolution           true
% 3.87/0.99  --res_backward_subs_resolution          true
% 3.87/0.99  --res_orphan_elimination                true
% 3.87/0.99  --res_time_limit                        2.
% 3.87/0.99  --res_out_proof                         true
% 3.87/0.99  
% 3.87/0.99  ------ Superposition Options
% 3.87/0.99  
% 3.87/0.99  --superposition_flag                    true
% 3.87/0.99  --sup_passive_queue_type                priority_queues
% 3.87/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.87/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.87/0.99  --demod_completeness_check              fast
% 3.87/0.99  --demod_use_ground                      true
% 3.87/0.99  --sup_to_prop_solver                    passive
% 3.87/0.99  --sup_prop_simpl_new                    true
% 3.87/0.99  --sup_prop_simpl_given                  true
% 3.87/0.99  --sup_fun_splitting                     true
% 3.87/0.99  --sup_smt_interval                      50000
% 3.87/0.99  
% 3.87/0.99  ------ Superposition Simplification Setup
% 3.87/0.99  
% 3.87/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.87/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.87/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.87/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.87/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.87/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.87/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.87/0.99  --sup_immed_triv                        [TrivRules]
% 3.87/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.87/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.87/0.99  --sup_immed_bw_main                     []
% 3.87/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.87/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.87/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.87/0.99  --sup_input_bw                          []
% 3.87/0.99  
% 3.87/0.99  ------ Combination Options
% 3.87/0.99  
% 3.87/0.99  --comb_res_mult                         3
% 3.87/0.99  --comb_sup_mult                         2
% 3.87/0.99  --comb_inst_mult                        10
% 3.87/0.99  
% 3.87/0.99  ------ Debug Options
% 3.87/0.99  
% 3.87/0.99  --dbg_backtrace                         false
% 3.87/0.99  --dbg_dump_prop_clauses                 false
% 3.87/0.99  --dbg_dump_prop_clauses_file            -
% 3.87/0.99  --dbg_out_stat                          false
% 3.87/0.99  
% 3.87/0.99  
% 3.87/0.99  
% 3.87/0.99  
% 3.87/0.99  ------ Proving...
% 3.87/0.99  
% 3.87/0.99  
% 3.87/0.99  % SZS status Theorem for theBenchmark.p
% 3.87/0.99  
% 3.87/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.87/0.99  
% 3.87/0.99  fof(f19,conjecture,(
% 3.87/0.99    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 3.87/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.87/0.99  
% 3.87/0.99  fof(f20,negated_conjecture,(
% 3.87/0.99    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 3.87/0.99    inference(negated_conjecture,[],[f19])).
% 3.87/0.99  
% 3.87/0.99  fof(f45,plain,(
% 3.87/0.99    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.87/0.99    inference(ennf_transformation,[],[f20])).
% 3.87/0.99  
% 3.87/0.99  fof(f46,plain,(
% 3.87/0.99    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.87/0.99    inference(flattening,[],[f45])).
% 3.87/0.99  
% 3.87/0.99  fof(f60,plain,(
% 3.87/0.99    ? [X0] : (? [X1] : (((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.87/0.99    inference(nnf_transformation,[],[f46])).
% 3.87/0.99  
% 3.87/0.99  fof(f61,plain,(
% 3.87/0.99    ? [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.87/0.99    inference(flattening,[],[f60])).
% 3.87/0.99  
% 3.87/0.99  fof(f63,plain,(
% 3.87/0.99    ( ! [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) => ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),sK4),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,sK4),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),sK4),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,sK4),X0)) & m1_subset_1(sK4,u1_struct_0(X0)))) )),
% 3.87/0.99    introduced(choice_axiom,[])).
% 3.87/0.99  
% 3.87/0.99  fof(f62,plain,(
% 3.87/0.99    ? [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(sK3),X1),u1_struct_0(sK3)) | ~v1_tex_2(k1_tex_2(sK3,X1),sK3)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK3),X1),u1_struct_0(sK3)) | v1_tex_2(k1_tex_2(sK3,X1),sK3)) & m1_subset_1(X1,u1_struct_0(sK3))) & l1_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 3.87/0.99    introduced(choice_axiom,[])).
% 3.87/0.99  
% 3.87/0.99  fof(f64,plain,(
% 3.87/0.99    ((~v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),u1_struct_0(sK3)) | ~v1_tex_2(k1_tex_2(sK3,sK4),sK3)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),u1_struct_0(sK3)) | v1_tex_2(k1_tex_2(sK3,sK4),sK3)) & m1_subset_1(sK4,u1_struct_0(sK3))) & l1_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 3.87/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f61,f63,f62])).
% 3.87/0.99  
% 3.87/0.99  fof(f96,plain,(
% 3.87/0.99    m1_subset_1(sK4,u1_struct_0(sK3))),
% 3.87/0.99    inference(cnf_transformation,[],[f64])).
% 3.87/0.99  
% 3.87/0.99  fof(f5,axiom,(
% 3.87/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.87/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.87/0.99  
% 3.87/0.99  fof(f21,plain,(
% 3.87/0.99    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.87/0.99    inference(ennf_transformation,[],[f5])).
% 3.87/0.99  
% 3.87/0.99  fof(f22,plain,(
% 3.87/0.99    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.87/0.99    inference(flattening,[],[f21])).
% 3.87/0.99  
% 3.87/0.99  fof(f72,plain,(
% 3.87/0.99    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.87/0.99    inference(cnf_transformation,[],[f22])).
% 3.87/0.99  
% 3.87/0.99  fof(f94,plain,(
% 3.87/0.99    ~v2_struct_0(sK3)),
% 3.87/0.99    inference(cnf_transformation,[],[f64])).
% 3.87/0.99  
% 3.87/0.99  fof(f95,plain,(
% 3.87/0.99    l1_pre_topc(sK3)),
% 3.87/0.99    inference(cnf_transformation,[],[f64])).
% 3.87/0.99  
% 3.87/0.99  fof(f10,axiom,(
% 3.87/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 3.87/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.87/0.99  
% 3.87/0.99  fof(f28,plain,(
% 3.87/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.87/0.99    inference(ennf_transformation,[],[f10])).
% 3.87/0.99  
% 3.87/0.99  fof(f29,plain,(
% 3.87/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.87/0.99    inference(flattening,[],[f28])).
% 3.87/0.99  
% 3.87/0.99  fof(f77,plain,(
% 3.87/0.99    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.87/0.99    inference(cnf_transformation,[],[f29])).
% 3.87/0.99  
% 3.87/0.99  fof(f7,axiom,(
% 3.87/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.87/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.87/0.99  
% 3.87/0.99  fof(f24,plain,(
% 3.87/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.87/0.99    inference(ennf_transformation,[],[f7])).
% 3.87/0.99  
% 3.87/0.99  fof(f74,plain,(
% 3.87/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.87/0.99    inference(cnf_transformation,[],[f24])).
% 3.87/0.99  
% 3.87/0.99  fof(f11,axiom,(
% 3.87/0.99    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 3.87/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.87/0.99  
% 3.87/0.99  fof(f30,plain,(
% 3.87/0.99    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 3.87/0.99    inference(ennf_transformation,[],[f11])).
% 3.87/0.99  
% 3.87/0.99  fof(f31,plain,(
% 3.87/0.99    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 3.87/0.99    inference(flattening,[],[f30])).
% 3.87/0.99  
% 3.87/0.99  fof(f78,plain,(
% 3.87/0.99    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.87/0.99    inference(cnf_transformation,[],[f31])).
% 3.87/0.99  
% 3.87/0.99  fof(f2,axiom,(
% 3.87/0.99    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.87/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.87/0.99  
% 3.87/0.99  fof(f69,plain,(
% 3.87/0.99    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.87/0.99    inference(cnf_transformation,[],[f2])).
% 3.87/0.99  
% 3.87/0.99  fof(f103,plain,(
% 3.87/0.99    ( ! [X0,X1] : (k2_tarski(X1,X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.87/0.99    inference(definition_unfolding,[],[f78,f69])).
% 3.87/0.99  
% 3.87/0.99  fof(f18,axiom,(
% 3.87/0.99    ! [X0] : ((~v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,X0) => v1_subset_1(k6_domain_1(X0,X1),X0)))),
% 3.87/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.87/0.99  
% 3.87/0.99  fof(f43,plain,(
% 3.87/0.99    ! [X0] : (! [X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | (v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 3.87/0.99    inference(ennf_transformation,[],[f18])).
% 3.87/0.99  
% 3.87/0.99  fof(f44,plain,(
% 3.87/0.99    ! [X0] : (! [X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 3.87/0.99    inference(flattening,[],[f43])).
% 3.87/0.99  
% 3.87/0.99  fof(f93,plain,(
% 3.87/0.99    ( ! [X0,X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0) | v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 3.87/0.99    inference(cnf_transformation,[],[f44])).
% 3.87/0.99  
% 3.87/0.99  fof(f17,axiom,(
% 3.87/0.99    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 3.87/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.87/0.99  
% 3.87/0.99  fof(f41,plain,(
% 3.87/0.99    ! [X0] : (! [X1] : ((~v1_zfmisc_1(X0) | ~v1_subset_1(k6_domain_1(X0,X1),X0)) | ~m1_subset_1(X1,X0)) | v1_xboole_0(X0))),
% 3.87/0.99    inference(ennf_transformation,[],[f17])).
% 3.87/0.99  
% 3.87/0.99  fof(f42,plain,(
% 3.87/0.99    ! [X0] : (! [X1] : (~v1_zfmisc_1(X0) | ~v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | v1_xboole_0(X0))),
% 3.87/0.99    inference(flattening,[],[f41])).
% 3.87/0.99  
% 3.87/0.99  fof(f92,plain,(
% 3.87/0.99    ( ! [X0,X1] : (~v1_zfmisc_1(X0) | ~v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.87/0.99    inference(cnf_transformation,[],[f42])).
% 3.87/0.99  
% 3.87/0.99  fof(f97,plain,(
% 3.87/0.99    v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),u1_struct_0(sK3)) | v1_tex_2(k1_tex_2(sK3,sK4),sK3)),
% 3.87/0.99    inference(cnf_transformation,[],[f64])).
% 3.87/0.99  
% 3.87/0.99  fof(f1,axiom,(
% 3.87/0.99    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 3.87/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.87/0.99  
% 3.87/0.99  fof(f47,plain,(
% 3.87/0.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 3.87/0.99    inference(nnf_transformation,[],[f1])).
% 3.87/0.99  
% 3.87/0.99  fof(f48,plain,(
% 3.87/0.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.87/0.99    inference(rectify,[],[f47])).
% 3.87/0.99  
% 3.87/0.99  fof(f49,plain,(
% 3.87/0.99    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1))))),
% 3.87/0.99    introduced(choice_axiom,[])).
% 3.87/0.99  
% 3.87/0.99  fof(f50,plain,(
% 3.87/0.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.87/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f48,f49])).
% 3.87/0.99  
% 3.87/0.99  fof(f65,plain,(
% 3.87/0.99    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 3.87/0.99    inference(cnf_transformation,[],[f50])).
% 3.87/0.99  
% 3.87/0.99  fof(f102,plain,(
% 3.87/0.99    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_tarski(X0,X0) != X1) )),
% 3.87/0.99    inference(definition_unfolding,[],[f65,f69])).
% 3.87/0.99  
% 3.87/0.99  fof(f106,plain,(
% 3.87/0.99    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k2_tarski(X0,X0))) )),
% 3.87/0.99    inference(equality_resolution,[],[f102])).
% 3.87/0.99  
% 3.87/0.99  fof(f66,plain,(
% 3.87/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 3.87/0.99    inference(cnf_transformation,[],[f50])).
% 3.87/0.99  
% 3.87/0.99  fof(f101,plain,(
% 3.87/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_tarski(X0,X0) != X1) )),
% 3.87/0.99    inference(definition_unfolding,[],[f66,f69])).
% 3.87/0.99  
% 3.87/0.99  fof(f104,plain,(
% 3.87/0.99    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_tarski(X3,X3) != X1) )),
% 3.87/0.99    inference(equality_resolution,[],[f101])).
% 3.87/0.99  
% 3.87/0.99  fof(f105,plain,(
% 3.87/0.99    ( ! [X3] : (r2_hidden(X3,k2_tarski(X3,X3))) )),
% 3.87/0.99    inference(equality_resolution,[],[f104])).
% 3.87/0.99  
% 3.87/0.99  fof(f15,axiom,(
% 3.87/0.99    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 3.87/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.87/0.99  
% 3.87/0.99  fof(f37,plain,(
% 3.87/0.99    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.87/0.99    inference(ennf_transformation,[],[f15])).
% 3.87/0.99  
% 3.87/0.99  fof(f38,plain,(
% 3.87/0.99    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.87/0.99    inference(flattening,[],[f37])).
% 3.87/0.99  
% 3.87/0.99  fof(f90,plain,(
% 3.87/0.99    ( ! [X0,X1] : (m1_pre_topc(k1_tex_2(X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.87/0.99    inference(cnf_transformation,[],[f38])).
% 3.87/0.99  
% 3.87/0.99  fof(f14,axiom,(
% 3.87/0.99    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => (k1_tex_2(X0,X1) = X2 <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)))))),
% 3.87/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.87/0.99  
% 3.87/0.99  fof(f35,plain,(
% 3.87/0.99    ! [X0] : (! [X1] : (! [X2] : ((k1_tex_2(X0,X1) = X2 <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)) | (~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.87/0.99    inference(ennf_transformation,[],[f14])).
% 3.87/0.99  
% 3.87/0.99  fof(f36,plain,(
% 3.87/0.99    ! [X0] : (! [X1] : (! [X2] : ((k1_tex_2(X0,X1) = X2 <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.87/0.99    inference(flattening,[],[f35])).
% 3.87/0.99  
% 3.87/0.99  fof(f59,plain,(
% 3.87/0.99    ! [X0] : (! [X1] : (! [X2] : (((k1_tex_2(X0,X1) = X2 | u1_struct_0(X2) != k6_domain_1(u1_struct_0(X0),X1)) & (u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) | k1_tex_2(X0,X1) != X2)) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.87/0.99    inference(nnf_transformation,[],[f36])).
% 3.87/0.99  
% 3.87/0.99  fof(f86,plain,(
% 3.87/0.99    ( ! [X2,X0,X1] : (u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) | k1_tex_2(X0,X1) != X2 | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.87/0.99    inference(cnf_transformation,[],[f59])).
% 3.87/0.99  
% 3.87/0.99  fof(f108,plain,(
% 3.87/0.99    ( ! [X0,X1] : (u1_struct_0(k1_tex_2(X0,X1)) = k6_domain_1(u1_struct_0(X0),X1) | ~m1_pre_topc(k1_tex_2(X0,X1),X0) | ~v1_pre_topc(k1_tex_2(X0,X1)) | v2_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.87/0.99    inference(equality_resolution,[],[f86])).
% 3.87/0.99  
% 3.87/0.99  fof(f88,plain,(
% 3.87/0.99    ( ! [X0,X1] : (~v2_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.87/0.99    inference(cnf_transformation,[],[f38])).
% 3.87/0.99  
% 3.87/0.99  fof(f89,plain,(
% 3.87/0.99    ( ! [X0,X1] : (v1_pre_topc(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.87/0.99    inference(cnf_transformation,[],[f38])).
% 3.87/0.99  
% 3.87/0.99  fof(f13,axiom,(
% 3.87/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v1_subset_1(X2,u1_struct_0(X0)))))))),
% 3.87/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.87/0.99  
% 3.87/0.99  fof(f33,plain,(
% 3.87/0.99    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : ((v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.87/0.99    inference(ennf_transformation,[],[f13])).
% 3.87/0.99  
% 3.87/0.99  fof(f34,plain,(
% 3.87/0.99    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.87/0.99    inference(flattening,[],[f33])).
% 3.87/0.99  
% 3.87/0.99  fof(f55,plain,(
% 3.87/0.99    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.87/0.99    inference(nnf_transformation,[],[f34])).
% 3.87/0.99  
% 3.87/0.99  fof(f56,plain,(
% 3.87/0.99    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.87/0.99    inference(rectify,[],[f55])).
% 3.87/0.99  
% 3.87/0.99  fof(f57,plain,(
% 3.87/0.99    ! [X1,X0] : (? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_subset_1(sK2(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK2(X0,X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.87/0.99    introduced(choice_axiom,[])).
% 3.87/0.99  
% 3.87/0.99  fof(f58,plain,(
% 3.87/0.99    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | (~v1_subset_1(sK2(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK2(X0,X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.87/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f56,f57])).
% 3.87/0.99  
% 3.87/0.99  fof(f85,plain,(
% 3.87/0.99    ( ! [X0,X1] : (v1_tex_2(X1,X0) | ~v1_subset_1(sK2(X0,X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.87/0.99    inference(cnf_transformation,[],[f58])).
% 3.87/0.99  
% 3.87/0.99  fof(f84,plain,(
% 3.87/0.99    ( ! [X0,X1] : (v1_tex_2(X1,X0) | u1_struct_0(X1) = sK2(X0,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.87/0.99    inference(cnf_transformation,[],[f58])).
% 3.87/0.99  
% 3.87/0.99  fof(f98,plain,(
% 3.87/0.99    ~v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),u1_struct_0(sK3)) | ~v1_tex_2(k1_tex_2(sK3,sK4),sK3)),
% 3.87/0.99    inference(cnf_transformation,[],[f64])).
% 3.87/0.99  
% 3.87/0.99  fof(f12,axiom,(
% 3.87/0.99    ! [X0] : (~v1_xboole_0(X0) => (v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))))),
% 3.87/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.87/0.99  
% 3.87/0.99  fof(f32,plain,(
% 3.87/0.99    ! [X0] : ((v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))) | v1_xboole_0(X0))),
% 3.87/0.99    inference(ennf_transformation,[],[f12])).
% 3.87/0.99  
% 3.87/0.99  fof(f51,plain,(
% 3.87/0.99    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 3.87/0.99    inference(nnf_transformation,[],[f32])).
% 3.87/0.99  
% 3.87/0.99  fof(f52,plain,(
% 3.87/0.99    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 3.87/0.99    inference(rectify,[],[f51])).
% 3.87/0.99  
% 3.87/0.99  fof(f53,plain,(
% 3.87/0.99    ! [X0] : (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) => (k6_domain_1(X0,sK1(X0)) = X0 & m1_subset_1(sK1(X0),X0)))),
% 3.87/0.99    introduced(choice_axiom,[])).
% 3.87/0.99  
% 3.87/0.99  fof(f54,plain,(
% 3.87/0.99    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & ((k6_domain_1(X0,sK1(X0)) = X0 & m1_subset_1(sK1(X0),X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 3.87/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f52,f53])).
% 3.87/0.99  
% 3.87/0.99  fof(f79,plain,(
% 3.87/0.99    ( ! [X0] : (m1_subset_1(sK1(X0),X0) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 3.87/0.99    inference(cnf_transformation,[],[f54])).
% 3.87/0.99  
% 3.87/0.99  fof(f80,plain,(
% 3.87/0.99    ( ! [X0] : (k6_domain_1(X0,sK1(X0)) = X0 | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 3.87/0.99    inference(cnf_transformation,[],[f54])).
% 3.87/0.99  
% 3.87/0.99  fof(f9,axiom,(
% 3.87/0.99    ! [X0] : ((l1_struct_0(X0) & v2_struct_0(X0)) => v1_xboole_0(u1_struct_0(X0)))),
% 3.87/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.87/0.99  
% 3.87/0.99  fof(f26,plain,(
% 3.87/0.99    ! [X0] : (v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v2_struct_0(X0)))),
% 3.87/0.99    inference(ennf_transformation,[],[f9])).
% 3.87/0.99  
% 3.87/0.99  fof(f27,plain,(
% 3.87/0.99    ! [X0] : (v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v2_struct_0(X0))),
% 3.87/0.99    inference(flattening,[],[f26])).
% 3.87/0.99  
% 3.87/0.99  fof(f76,plain,(
% 3.87/0.99    ( ! [X0] : (v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v2_struct_0(X0)) )),
% 3.87/0.99    inference(cnf_transformation,[],[f27])).
% 3.87/0.99  
% 3.87/0.99  fof(f16,axiom,(
% 3.87/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ~(v1_tex_2(X1,X0) & u1_struct_0(X0) = u1_struct_0(X1))))),
% 3.87/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.87/0.99  
% 3.87/0.99  fof(f39,plain,(
% 3.87/0.99    ! [X0] : (! [X1] : ((~v1_tex_2(X1,X0) | u1_struct_0(X0) != u1_struct_0(X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.87/0.99    inference(ennf_transformation,[],[f16])).
% 3.87/0.99  
% 3.87/0.99  fof(f40,plain,(
% 3.87/0.99    ! [X0] : (! [X1] : (~v1_tex_2(X1,X0) | u1_struct_0(X0) != u1_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.87/0.99    inference(flattening,[],[f39])).
% 3.87/0.99  
% 3.87/0.99  fof(f91,plain,(
% 3.87/0.99    ( ! [X0,X1] : (~v1_tex_2(X1,X0) | u1_struct_0(X0) != u1_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.87/0.99    inference(cnf_transformation,[],[f40])).
% 3.87/0.99  
% 3.87/0.99  cnf(c_30,negated_conjecture,
% 3.87/0.99      ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 3.87/0.99      inference(cnf_transformation,[],[f96]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_6266,plain,
% 3.87/0.99      ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_6,plain,
% 3.87/0.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.87/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_6286,plain,
% 3.87/0.99      ( m1_subset_1(X0,X1) != iProver_top
% 3.87/0.99      | r2_hidden(X0,X1) = iProver_top
% 3.87/0.99      | v1_xboole_0(X1) = iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_7105,plain,
% 3.87/0.99      ( r2_hidden(sK4,u1_struct_0(sK3)) = iProver_top
% 3.87/0.99      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 3.87/0.99      inference(superposition,[status(thm)],[c_6266,c_6286]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_32,negated_conjecture,
% 3.87/0.99      ( ~ v2_struct_0(sK3) ),
% 3.87/0.99      inference(cnf_transformation,[],[f94]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_33,plain,
% 3.87/0.99      ( v2_struct_0(sK3) != iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_31,negated_conjecture,
% 3.87/0.99      ( l1_pre_topc(sK3) ),
% 3.87/0.99      inference(cnf_transformation,[],[f95]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_34,plain,
% 3.87/0.99      ( l1_pre_topc(sK3) = iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_11,plain,
% 3.87/0.99      ( v2_struct_0(X0)
% 3.87/0.99      | ~ l1_struct_0(X0)
% 3.87/0.99      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 3.87/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_86,plain,
% 3.87/0.99      ( v2_struct_0(X0) = iProver_top
% 3.87/0.99      | l1_struct_0(X0) != iProver_top
% 3.87/0.99      | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_88,plain,
% 3.87/0.99      ( v2_struct_0(sK3) = iProver_top
% 3.87/0.99      | l1_struct_0(sK3) != iProver_top
% 3.87/0.99      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_86]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_8,plain,
% 3.87/0.99      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 3.87/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_91,plain,
% 3.87/0.99      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_93,plain,
% 3.87/0.99      ( l1_pre_topc(sK3) != iProver_top
% 3.87/0.99      | l1_struct_0(sK3) = iProver_top ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_91]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_2141,plain,
% 3.87/0.99      ( r2_hidden(X0,X1)
% 3.87/0.99      | v1_xboole_0(X1)
% 3.87/0.99      | u1_struct_0(sK3) != X1
% 3.87/0.99      | sK4 != X0 ),
% 3.87/0.99      inference(resolution_lifted,[status(thm)],[c_6,c_30]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_2142,plain,
% 3.87/0.99      ( r2_hidden(sK4,u1_struct_0(sK3)) | v1_xboole_0(u1_struct_0(sK3)) ),
% 3.87/0.99      inference(unflattening,[status(thm)],[c_2141]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_2143,plain,
% 3.87/0.99      ( r2_hidden(sK4,u1_struct_0(sK3)) = iProver_top
% 3.87/0.99      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_2142]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_7241,plain,
% 3.87/0.99      ( r2_hidden(sK4,u1_struct_0(sK3)) = iProver_top ),
% 3.87/0.99      inference(global_propositional_subsumption,
% 3.87/0.99                [status(thm)],
% 3.87/0.99                [c_7105,c_33,c_34,c_88,c_93,c_2143]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_12,plain,
% 3.87/0.99      ( ~ m1_subset_1(X0,X1)
% 3.87/0.99      | v1_xboole_0(X1)
% 3.87/0.99      | k6_domain_1(X1,X0) = k2_tarski(X0,X0) ),
% 3.87/0.99      inference(cnf_transformation,[],[f103]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_6283,plain,
% 3.87/0.99      ( k6_domain_1(X0,X1) = k2_tarski(X1,X1)
% 3.87/0.99      | m1_subset_1(X1,X0) != iProver_top
% 3.87/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_7136,plain,
% 3.87/0.99      ( k6_domain_1(u1_struct_0(sK3),sK4) = k2_tarski(sK4,sK4)
% 3.87/0.99      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 3.87/0.99      inference(superposition,[status(thm)],[c_6266,c_6283]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_87,plain,
% 3.87/0.99      ( v2_struct_0(sK3)
% 3.87/0.99      | ~ l1_struct_0(sK3)
% 3.87/0.99      | ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_11]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_92,plain,
% 3.87/0.99      ( ~ l1_pre_topc(sK3) | l1_struct_0(sK3) ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_2133,plain,
% 3.87/0.99      ( v1_xboole_0(X0)
% 3.87/0.99      | k6_domain_1(X0,X1) = k2_tarski(X1,X1)
% 3.87/0.99      | u1_struct_0(sK3) != X0
% 3.87/0.99      | sK4 != X1 ),
% 3.87/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_30]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_2134,plain,
% 3.87/0.99      ( v1_xboole_0(u1_struct_0(sK3))
% 3.87/0.99      | k6_domain_1(u1_struct_0(sK3),sK4) = k2_tarski(sK4,sK4) ),
% 3.87/0.99      inference(unflattening,[status(thm)],[c_2133]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_7300,plain,
% 3.87/0.99      ( k6_domain_1(u1_struct_0(sK3),sK4) = k2_tarski(sK4,sK4) ),
% 3.87/0.99      inference(global_propositional_subsumption,
% 3.87/0.99                [status(thm)],
% 3.87/0.99                [c_7136,c_32,c_31,c_87,c_92,c_2134]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_27,plain,
% 3.87/0.99      ( v1_subset_1(k6_domain_1(X0,X1),X0)
% 3.87/0.99      | ~ m1_subset_1(X1,X0)
% 3.87/0.99      | v1_zfmisc_1(X0)
% 3.87/0.99      | v1_xboole_0(X0) ),
% 3.87/0.99      inference(cnf_transformation,[],[f93]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_6269,plain,
% 3.87/0.99      ( v1_subset_1(k6_domain_1(X0,X1),X0) = iProver_top
% 3.87/0.99      | m1_subset_1(X1,X0) != iProver_top
% 3.87/0.99      | v1_zfmisc_1(X0) = iProver_top
% 3.87/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_7570,plain,
% 3.87/0.99      ( v1_subset_1(k2_tarski(sK4,sK4),u1_struct_0(sK3)) = iProver_top
% 3.87/0.99      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 3.87/0.99      | v1_zfmisc_1(u1_struct_0(sK3)) = iProver_top
% 3.87/0.99      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 3.87/0.99      inference(superposition,[status(thm)],[c_7300,c_6269]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_35,plain,
% 3.87/0.99      ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_26,plain,
% 3.87/0.99      ( ~ v1_subset_1(k6_domain_1(X0,X1),X0)
% 3.87/0.99      | ~ m1_subset_1(X1,X0)
% 3.87/0.99      | ~ v1_zfmisc_1(X0)
% 3.87/0.99      | v1_xboole_0(X0) ),
% 3.87/0.99      inference(cnf_transformation,[],[f92]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_6270,plain,
% 3.87/0.99      ( v1_subset_1(k6_domain_1(X0,X1),X0) != iProver_top
% 3.87/0.99      | m1_subset_1(X1,X0) != iProver_top
% 3.87/0.99      | v1_zfmisc_1(X0) != iProver_top
% 3.87/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_7775,plain,
% 3.87/0.99      ( v1_subset_1(k2_tarski(sK4,sK4),u1_struct_0(sK3)) != iProver_top
% 3.87/0.99      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 3.87/0.99      | v1_zfmisc_1(u1_struct_0(sK3)) != iProver_top
% 3.87/0.99      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 3.87/0.99      inference(superposition,[status(thm)],[c_7300,c_6270]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_29,negated_conjecture,
% 3.87/0.99      ( v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),u1_struct_0(sK3))
% 3.87/0.99      | v1_tex_2(k1_tex_2(sK3,sK4),sK3) ),
% 3.87/0.99      inference(cnf_transformation,[],[f97]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_36,plain,
% 3.87/0.99      ( v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),u1_struct_0(sK3)) = iProver_top
% 3.87/0.99      | v1_tex_2(k1_tex_2(sK3,sK4),sK3) = iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_3,plain,
% 3.87/0.99      ( ~ r2_hidden(X0,k2_tarski(X1,X1)) | X0 = X1 ),
% 3.87/0.99      inference(cnf_transformation,[],[f106]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_105,plain,
% 3.87/0.99      ( ~ r2_hidden(sK3,k2_tarski(sK3,sK3)) | sK3 = sK3 ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_2,plain,
% 3.87/0.99      ( r2_hidden(X0,k2_tarski(X0,X0)) ),
% 3.87/0.99      inference(cnf_transformation,[],[f105]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_108,plain,
% 3.87/0.99      ( r2_hidden(sK3,k2_tarski(sK3,sK3)) ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_22,plain,
% 3.87/0.99      ( m1_pre_topc(k1_tex_2(X0,X1),X0)
% 3.87/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.87/0.99      | v2_struct_0(X0)
% 3.87/0.99      | ~ l1_pre_topc(X0) ),
% 3.87/0.99      inference(cnf_transformation,[],[f90]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_2658,plain,
% 3.87/0.99      ( m1_pre_topc(k1_tex_2(X0,X1),X0)
% 3.87/0.99      | v2_struct_0(X0)
% 3.87/0.99      | ~ l1_pre_topc(X0)
% 3.87/0.99      | u1_struct_0(X0) != u1_struct_0(sK3)
% 3.87/0.99      | sK4 != X1 ),
% 3.87/0.99      inference(resolution_lifted,[status(thm)],[c_22,c_30]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_2659,plain,
% 3.87/0.99      ( m1_pre_topc(k1_tex_2(X0,sK4),X0)
% 3.87/0.99      | v2_struct_0(X0)
% 3.87/0.99      | ~ l1_pre_topc(X0)
% 3.87/0.99      | u1_struct_0(X0) != u1_struct_0(sK3) ),
% 3.87/0.99      inference(unflattening,[status(thm)],[c_2658]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_2660,plain,
% 3.87/0.99      ( u1_struct_0(X0) != u1_struct_0(sK3)
% 3.87/0.99      | m1_pre_topc(k1_tex_2(X0,sK4),X0) = iProver_top
% 3.87/0.99      | v2_struct_0(X0) = iProver_top
% 3.87/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_2659]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_2662,plain,
% 3.87/0.99      ( u1_struct_0(sK3) != u1_struct_0(sK3)
% 3.87/0.99      | m1_pre_topc(k1_tex_2(sK3,sK4),sK3) = iProver_top
% 3.87/0.99      | v2_struct_0(sK3) = iProver_top
% 3.87/0.99      | l1_pre_topc(sK3) != iProver_top ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_2660]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_21,plain,
% 3.87/0.99      ( ~ m1_pre_topc(k1_tex_2(X0,X1),X0)
% 3.87/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.87/0.99      | ~ v1_pre_topc(k1_tex_2(X0,X1))
% 3.87/0.99      | v2_struct_0(X0)
% 3.87/0.99      | v2_struct_0(k1_tex_2(X0,X1))
% 3.87/0.99      | ~ l1_pre_topc(X0)
% 3.87/0.99      | k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1)) ),
% 3.87/0.99      inference(cnf_transformation,[],[f108]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_192,plain,
% 3.87/0.99      ( ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.87/0.99      | ~ v1_pre_topc(k1_tex_2(X0,X1))
% 3.87/0.99      | v2_struct_0(X0)
% 3.87/0.99      | v2_struct_0(k1_tex_2(X0,X1))
% 3.87/0.99      | ~ l1_pre_topc(X0)
% 3.87/0.99      | k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1)) ),
% 3.87/0.99      inference(global_propositional_subsumption,
% 3.87/0.99                [status(thm)],
% 3.87/0.99                [c_21,c_22]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_193,plain,
% 3.87/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.87/0.99      | ~ v1_pre_topc(k1_tex_2(X1,X0))
% 3.87/0.99      | v2_struct_0(X1)
% 3.87/0.99      | v2_struct_0(k1_tex_2(X1,X0))
% 3.87/0.99      | ~ l1_pre_topc(X1)
% 3.87/0.99      | k6_domain_1(u1_struct_0(X1),X0) = u1_struct_0(k1_tex_2(X1,X0)) ),
% 3.87/0.99      inference(renaming,[status(thm)],[c_192]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_24,plain,
% 3.87/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.87/0.99      | v2_struct_0(X1)
% 3.87/0.99      | ~ v2_struct_0(k1_tex_2(X1,X0))
% 3.87/0.99      | ~ l1_pre_topc(X1) ),
% 3.87/0.99      inference(cnf_transformation,[],[f88]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_23,plain,
% 3.87/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.87/0.99      | v1_pre_topc(k1_tex_2(X1,X0))
% 3.87/0.99      | v2_struct_0(X1)
% 3.87/0.99      | ~ l1_pre_topc(X1) ),
% 3.87/0.99      inference(cnf_transformation,[],[f89]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_198,plain,
% 3.87/0.99      ( v2_struct_0(X1)
% 3.87/0.99      | ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.87/0.99      | ~ l1_pre_topc(X1)
% 3.87/0.99      | k6_domain_1(u1_struct_0(X1),X0) = u1_struct_0(k1_tex_2(X1,X0)) ),
% 3.87/0.99      inference(global_propositional_subsumption,
% 3.87/0.99                [status(thm)],
% 3.87/0.99                [c_193,c_24,c_23]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_199,plain,
% 3.87/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.87/0.99      | v2_struct_0(X1)
% 3.87/0.99      | ~ l1_pre_topc(X1)
% 3.87/0.99      | k6_domain_1(u1_struct_0(X1),X0) = u1_struct_0(k1_tex_2(X1,X0)) ),
% 3.87/0.99      inference(renaming,[status(thm)],[c_198]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_2706,plain,
% 3.87/0.99      ( v2_struct_0(X0)
% 3.87/0.99      | ~ l1_pre_topc(X0)
% 3.87/0.99      | k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1))
% 3.87/0.99      | u1_struct_0(X0) != u1_struct_0(sK3)
% 3.87/0.99      | sK4 != X1 ),
% 3.87/0.99      inference(resolution_lifted,[status(thm)],[c_199,c_30]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_2707,plain,
% 3.87/0.99      ( v2_struct_0(X0)
% 3.87/0.99      | ~ l1_pre_topc(X0)
% 3.87/0.99      | k6_domain_1(u1_struct_0(X0),sK4) = u1_struct_0(k1_tex_2(X0,sK4))
% 3.87/0.99      | u1_struct_0(X0) != u1_struct_0(sK3) ),
% 3.87/0.99      inference(unflattening,[status(thm)],[c_2706]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_2709,plain,
% 3.87/0.99      ( v2_struct_0(sK3)
% 3.87/0.99      | ~ l1_pre_topc(sK3)
% 3.87/0.99      | k6_domain_1(u1_struct_0(sK3),sK4) = u1_struct_0(k1_tex_2(sK3,sK4))
% 3.87/0.99      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_2707]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_5534,plain,
% 3.87/0.99      ( X0 != X1 | u1_struct_0(X0) = u1_struct_0(X1) ),
% 3.87/0.99      theory(equality) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_5547,plain,
% 3.87/0.99      ( u1_struct_0(sK3) = u1_struct_0(sK3) | sK3 != sK3 ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_5534]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_16,plain,
% 3.87/0.99      ( ~ v1_subset_1(sK2(X0,X1),u1_struct_0(X0))
% 3.87/0.99      | v1_tex_2(X1,X0)
% 3.87/0.99      | ~ m1_pre_topc(X1,X0)
% 3.87/0.99      | ~ l1_pre_topc(X0) ),
% 3.87/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_6331,plain,
% 3.87/0.99      ( ~ v1_subset_1(sK2(sK3,k1_tex_2(sK3,sK4)),u1_struct_0(sK3))
% 3.87/0.99      | v1_tex_2(k1_tex_2(sK3,sK4),sK3)
% 3.87/0.99      | ~ m1_pre_topc(k1_tex_2(sK3,sK4),sK3)
% 3.87/0.99      | ~ l1_pre_topc(sK3) ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_16]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_6332,plain,
% 3.87/0.99      ( v1_subset_1(sK2(sK3,k1_tex_2(sK3,sK4)),u1_struct_0(sK3)) != iProver_top
% 3.87/0.99      | v1_tex_2(k1_tex_2(sK3,sK4),sK3) = iProver_top
% 3.87/0.99      | m1_pre_topc(k1_tex_2(sK3,sK4),sK3) != iProver_top
% 3.87/0.99      | l1_pre_topc(sK3) != iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_6331]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_17,plain,
% 3.87/0.99      ( v1_tex_2(X0,X1)
% 3.87/0.99      | ~ m1_pre_topc(X0,X1)
% 3.87/0.99      | ~ l1_pre_topc(X1)
% 3.87/0.99      | sK2(X1,X0) = u1_struct_0(X0) ),
% 3.87/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_6334,plain,
% 3.87/0.99      ( v1_tex_2(k1_tex_2(sK3,sK4),sK3)
% 3.87/0.99      | ~ m1_pre_topc(k1_tex_2(sK3,sK4),sK3)
% 3.87/0.99      | ~ l1_pre_topc(sK3)
% 3.87/0.99      | sK2(sK3,k1_tex_2(sK3,sK4)) = u1_struct_0(k1_tex_2(sK3,sK4)) ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_17]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_6338,plain,
% 3.87/0.99      ( sK2(sK3,k1_tex_2(sK3,sK4)) = u1_struct_0(k1_tex_2(sK3,sK4))
% 3.87/0.99      | v1_tex_2(k1_tex_2(sK3,sK4),sK3) = iProver_top
% 3.87/0.99      | m1_pre_topc(k1_tex_2(sK3,sK4),sK3) != iProver_top
% 3.87/0.99      | l1_pre_topc(sK3) != iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_6334]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_28,negated_conjecture,
% 3.87/0.99      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),u1_struct_0(sK3))
% 3.87/0.99      | ~ v1_tex_2(k1_tex_2(sK3,sK4),sK3) ),
% 3.87/0.99      inference(cnf_transformation,[],[f98]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_6268,plain,
% 3.87/0.99      ( v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),u1_struct_0(sK3)) != iProver_top
% 3.87/0.99      | v1_tex_2(k1_tex_2(sK3,sK4),sK3) != iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_7303,plain,
% 3.87/0.99      ( v1_subset_1(k2_tarski(sK4,sK4),u1_struct_0(sK3)) != iProver_top
% 3.87/0.99      | v1_tex_2(k1_tex_2(sK3,sK4),sK3) != iProver_top ),
% 3.87/0.99      inference(demodulation,[status(thm)],[c_7300,c_6268]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_5538,plain,
% 3.87/0.99      ( ~ v1_subset_1(X0,X1) | v1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.87/0.99      theory(equality) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_6733,plain,
% 3.87/0.99      ( ~ v1_subset_1(X0,X1)
% 3.87/0.99      | v1_subset_1(sK2(X2,k1_tex_2(sK3,sK4)),u1_struct_0(X2))
% 3.87/0.99      | sK2(X2,k1_tex_2(sK3,sK4)) != X0
% 3.87/0.99      | u1_struct_0(X2) != X1 ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_5538]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_7431,plain,
% 3.87/0.99      ( v1_subset_1(sK2(X0,k1_tex_2(sK3,sK4)),u1_struct_0(X0))
% 3.87/0.99      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),u1_struct_0(sK3))
% 3.87/0.99      | sK2(X0,k1_tex_2(sK3,sK4)) != k6_domain_1(u1_struct_0(sK3),sK4)
% 3.87/0.99      | u1_struct_0(X0) != u1_struct_0(sK3) ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_6733]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_7432,plain,
% 3.87/0.99      ( sK2(X0,k1_tex_2(sK3,sK4)) != k6_domain_1(u1_struct_0(sK3),sK4)
% 3.87/0.99      | u1_struct_0(X0) != u1_struct_0(sK3)
% 3.87/0.99      | v1_subset_1(sK2(X0,k1_tex_2(sK3,sK4)),u1_struct_0(X0)) = iProver_top
% 3.87/0.99      | v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),u1_struct_0(sK3)) != iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_7431]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_7434,plain,
% 3.87/0.99      ( sK2(sK3,k1_tex_2(sK3,sK4)) != k6_domain_1(u1_struct_0(sK3),sK4)
% 3.87/0.99      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 3.87/0.99      | v1_subset_1(sK2(sK3,k1_tex_2(sK3,sK4)),u1_struct_0(sK3)) = iProver_top
% 3.87/0.99      | v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),u1_struct_0(sK3)) != iProver_top ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_7432]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_5527,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_6717,plain,
% 3.87/0.99      ( X0 != X1
% 3.87/0.99      | sK2(sK3,k1_tex_2(sK3,sK4)) != X1
% 3.87/0.99      | sK2(sK3,k1_tex_2(sK3,sK4)) = X0 ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_5527]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_7344,plain,
% 3.87/0.99      ( X0 != u1_struct_0(k1_tex_2(sK3,sK4))
% 3.87/0.99      | sK2(sK3,k1_tex_2(sK3,sK4)) = X0
% 3.87/0.99      | sK2(sK3,k1_tex_2(sK3,sK4)) != u1_struct_0(k1_tex_2(sK3,sK4)) ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_6717]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_7576,plain,
% 3.87/0.99      ( sK2(sK3,k1_tex_2(sK3,sK4)) = k6_domain_1(u1_struct_0(sK3),sK4)
% 3.87/0.99      | sK2(sK3,k1_tex_2(sK3,sK4)) != u1_struct_0(k1_tex_2(sK3,sK4))
% 3.87/0.99      | k6_domain_1(u1_struct_0(sK3),sK4) != u1_struct_0(k1_tex_2(sK3,sK4)) ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_7344]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_7960,plain,
% 3.87/0.99      ( v1_subset_1(k2_tarski(sK4,sK4),u1_struct_0(sK3)) != iProver_top ),
% 3.87/0.99      inference(global_propositional_subsumption,
% 3.87/0.99                [status(thm)],
% 3.87/0.99                [c_7775,c_32,c_33,c_31,c_34,c_36,c_105,c_108,c_2662,
% 3.87/0.99                 c_2709,c_5547,c_6332,c_6338,c_7303,c_7434,c_7576]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_8044,plain,
% 3.87/0.99      ( v1_zfmisc_1(u1_struct_0(sK3)) = iProver_top ),
% 3.87/0.99      inference(global_propositional_subsumption,
% 3.87/0.99                [status(thm)],
% 3.87/0.99                [c_7570,c_32,c_33,c_31,c_34,c_36,c_105,c_108,c_2662,
% 3.87/0.99                 c_2709,c_3667,c_5547,c_6332,c_6338,c_7434,c_7576]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_15,plain,
% 3.87/0.99      ( m1_subset_1(sK1(X0),X0) | ~ v1_zfmisc_1(X0) | v1_xboole_0(X0) ),
% 3.87/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_6280,plain,
% 3.87/0.99      ( m1_subset_1(sK1(X0),X0) = iProver_top
% 3.87/0.99      | v1_zfmisc_1(X0) != iProver_top
% 3.87/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_7135,plain,
% 3.87/0.99      ( k2_tarski(sK1(X0),sK1(X0)) = k6_domain_1(X0,sK1(X0))
% 3.87/0.99      | v1_zfmisc_1(X0) != iProver_top
% 3.87/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.87/0.99      inference(superposition,[status(thm)],[c_6280,c_6283]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_10138,plain,
% 3.87/0.99      ( k2_tarski(sK1(u1_struct_0(sK3)),sK1(u1_struct_0(sK3))) = k6_domain_1(u1_struct_0(sK3),sK1(u1_struct_0(sK3)))
% 3.87/0.99      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 3.87/0.99      inference(superposition,[status(thm)],[c_8044,c_7135]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_14,plain,
% 3.87/0.99      ( ~ v1_zfmisc_1(X0)
% 3.87/0.99      | v1_xboole_0(X0)
% 3.87/0.99      | k6_domain_1(X0,sK1(X0)) = X0 ),
% 3.87/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_6281,plain,
% 3.87/0.99      ( k6_domain_1(X0,sK1(X0)) = X0
% 3.87/0.99      | v1_zfmisc_1(X0) != iProver_top
% 3.87/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_8048,plain,
% 3.87/0.99      ( k6_domain_1(u1_struct_0(sK3),sK1(u1_struct_0(sK3))) = u1_struct_0(sK3)
% 3.87/0.99      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 3.87/0.99      inference(superposition,[status(thm)],[c_8044,c_6281]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_443,plain,
% 3.87/0.99      ( v2_struct_0(X0)
% 3.87/0.99      | ~ l1_pre_topc(X0)
% 3.87/0.99      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 3.87/0.99      inference(resolution,[status(thm)],[c_8,c_11]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1728,plain,
% 3.87/0.99      ( ~ v1_zfmisc_1(X0)
% 3.87/0.99      | v2_struct_0(X1)
% 3.87/0.99      | ~ l1_pre_topc(X1)
% 3.87/0.99      | k6_domain_1(X0,sK1(X0)) = X0
% 3.87/0.99      | u1_struct_0(X1) != X0 ),
% 3.87/0.99      inference(resolution_lifted,[status(thm)],[c_443,c_14]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1729,plain,
% 3.87/0.99      ( ~ v1_zfmisc_1(u1_struct_0(X0))
% 3.87/0.99      | v2_struct_0(X0)
% 3.87/0.99      | ~ l1_pre_topc(X0)
% 3.87/0.99      | k6_domain_1(u1_struct_0(X0),sK1(u1_struct_0(X0))) = u1_struct_0(X0) ),
% 3.87/0.99      inference(unflattening,[status(thm)],[c_1728]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1730,plain,
% 3.87/0.99      ( k6_domain_1(u1_struct_0(X0),sK1(u1_struct_0(X0))) = u1_struct_0(X0)
% 3.87/0.99      | v1_zfmisc_1(u1_struct_0(X0)) != iProver_top
% 3.87/0.99      | v2_struct_0(X0) = iProver_top
% 3.87/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_1729]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1732,plain,
% 3.87/0.99      ( k6_domain_1(u1_struct_0(sK3),sK1(u1_struct_0(sK3))) = u1_struct_0(sK3)
% 3.87/0.99      | v1_zfmisc_1(u1_struct_0(sK3)) != iProver_top
% 3.87/0.99      | v2_struct_0(sK3) = iProver_top
% 3.87/0.99      | l1_pre_topc(sK3) != iProver_top ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_1730]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_3058,plain,
% 3.87/0.99      ( ~ v1_tex_2(k1_tex_2(sK3,sK4),sK3)
% 3.87/0.99      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),u1_struct_0(sK3)) ),
% 3.87/0.99      inference(prop_impl,[status(thm)],[c_28]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_3059,plain,
% 3.87/0.99      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),u1_struct_0(sK3))
% 3.87/0.99      | ~ v1_tex_2(k1_tex_2(sK3,sK4),sK3) ),
% 3.87/0.99      inference(renaming,[status(thm)],[c_3058]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_3662,plain,
% 3.87/0.99      ( ~ v1_tex_2(k1_tex_2(sK3,sK4),sK3)
% 3.87/0.99      | ~ m1_subset_1(X0,X1)
% 3.87/0.99      | v1_zfmisc_1(X1)
% 3.87/0.99      | v1_xboole_0(X1)
% 3.87/0.99      | k6_domain_1(u1_struct_0(sK3),sK4) != k6_domain_1(X1,X0)
% 3.87/0.99      | u1_struct_0(sK3) != X1 ),
% 3.87/0.99      inference(resolution_lifted,[status(thm)],[c_27,c_3059]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_3663,plain,
% 3.87/0.99      ( ~ v1_tex_2(k1_tex_2(sK3,sK4),sK3)
% 3.87/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.87/0.99      | v1_zfmisc_1(u1_struct_0(sK3))
% 3.87/0.99      | v1_xboole_0(u1_struct_0(sK3))
% 3.87/0.99      | k6_domain_1(u1_struct_0(sK3),sK4) != k6_domain_1(u1_struct_0(sK3),X0) ),
% 3.87/0.99      inference(unflattening,[status(thm)],[c_3662]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_2274,plain,
% 3.87/0.99      ( v1_subset_1(k6_domain_1(X0,X1),X0)
% 3.87/0.99      | v1_zfmisc_1(X0)
% 3.87/0.99      | v1_xboole_0(X0)
% 3.87/0.99      | u1_struct_0(sK3) != X0
% 3.87/0.99      | sK4 != X1 ),
% 3.87/0.99      inference(resolution_lifted,[status(thm)],[c_27,c_30]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_2275,plain,
% 3.87/0.99      ( v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),u1_struct_0(sK3))
% 3.87/0.99      | v1_zfmisc_1(u1_struct_0(sK3))
% 3.87/0.99      | v1_xboole_0(u1_struct_0(sK3)) ),
% 3.87/0.99      inference(unflattening,[status(thm)],[c_2274]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_3665,plain,
% 3.87/0.99      ( ~ v1_tex_2(k1_tex_2(sK3,sK4),sK3)
% 3.87/0.99      | v1_zfmisc_1(u1_struct_0(sK3)) ),
% 3.87/0.99      inference(global_propositional_subsumption,
% 3.87/0.99                [status(thm)],
% 3.87/0.99                [c_3663,c_32,c_31,c_28,c_87,c_92,c_2275]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_3667,plain,
% 3.87/0.99      ( v1_tex_2(k1_tex_2(sK3,sK4),sK3) != iProver_top
% 3.87/0.99      | v1_zfmisc_1(u1_struct_0(sK3)) = iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_3665]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_8202,plain,
% 3.87/0.99      ( k6_domain_1(u1_struct_0(sK3),sK1(u1_struct_0(sK3))) = u1_struct_0(sK3) ),
% 3.87/0.99      inference(global_propositional_subsumption,
% 3.87/0.99                [status(thm)],
% 3.87/0.99                [c_8048,c_32,c_33,c_31,c_34,c_36,c_105,c_108,c_1732,
% 3.87/0.99                 c_2662,c_2709,c_3667,c_5547,c_6332,c_6338,c_7434,c_7576]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_10139,plain,
% 3.87/0.99      ( k2_tarski(sK1(u1_struct_0(sK3)),sK1(u1_struct_0(sK3))) = u1_struct_0(sK3)
% 3.87/0.99      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 3.87/0.99      inference(light_normalisation,[status(thm)],[c_10138,c_8202]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_10791,plain,
% 3.87/0.99      ( k2_tarski(sK1(u1_struct_0(sK3)),sK1(u1_struct_0(sK3))) = u1_struct_0(sK3) ),
% 3.87/0.99      inference(global_propositional_subsumption,
% 3.87/0.99                [status(thm)],
% 3.87/0.99                [c_10139,c_33,c_34,c_88,c_93]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_6288,plain,
% 3.87/0.99      ( X0 = X1 | r2_hidden(X0,k2_tarski(X1,X1)) != iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_10806,plain,
% 3.87/0.99      ( sK1(u1_struct_0(sK3)) = X0
% 3.87/0.99      | r2_hidden(X0,u1_struct_0(sK3)) != iProver_top ),
% 3.87/0.99      inference(superposition,[status(thm)],[c_10791,c_6288]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_11172,plain,
% 3.87/0.99      ( sK1(u1_struct_0(sK3)) = sK4 ),
% 3.87/0.99      inference(superposition,[status(thm)],[c_7241,c_10806]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_6263,plain,
% 3.87/0.99      ( k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1))
% 3.87/0.99      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 3.87/0.99      | v2_struct_0(X0) = iProver_top
% 3.87/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_199]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_7099,plain,
% 3.87/0.99      ( k6_domain_1(u1_struct_0(X0),sK1(u1_struct_0(X0))) = u1_struct_0(k1_tex_2(X0,sK1(u1_struct_0(X0))))
% 3.87/0.99      | v1_zfmisc_1(u1_struct_0(X0)) != iProver_top
% 3.87/0.99      | v2_struct_0(X0) = iProver_top
% 3.87/0.99      | l1_pre_topc(X0) != iProver_top
% 3.87/0.99      | v1_xboole_0(u1_struct_0(X0)) = iProver_top ),
% 3.87/0.99      inference(superposition,[status(thm)],[c_6280,c_6263]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_2386,plain,
% 3.87/0.99      ( ~ v1_zfmisc_1(X0)
% 3.87/0.99      | v2_struct_0(X1)
% 3.87/0.99      | ~ l1_pre_topc(X1)
% 3.87/0.99      | v1_xboole_0(X0)
% 3.87/0.99      | k6_domain_1(u1_struct_0(X1),X2) = u1_struct_0(k1_tex_2(X1,X2))
% 3.87/0.99      | sK1(X0) != X2
% 3.87/0.99      | u1_struct_0(X1) != X0 ),
% 3.87/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_199]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_2387,plain,
% 3.87/0.99      ( ~ v1_zfmisc_1(u1_struct_0(X0))
% 3.87/0.99      | v2_struct_0(X0)
% 3.87/0.99      | ~ l1_pre_topc(X0)
% 3.87/0.99      | v1_xboole_0(u1_struct_0(X0))
% 3.87/0.99      | k6_domain_1(u1_struct_0(X0),sK1(u1_struct_0(X0))) = u1_struct_0(k1_tex_2(X0,sK1(u1_struct_0(X0)))) ),
% 3.87/0.99      inference(unflattening,[status(thm)],[c_2386]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_10,plain,
% 3.87/0.99      ( ~ v2_struct_0(X0)
% 3.87/0.99      | ~ l1_struct_0(X0)
% 3.87/0.99      | v1_xboole_0(u1_struct_0(X0)) ),
% 3.87/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_457,plain,
% 3.87/0.99      ( ~ v2_struct_0(X0)
% 3.87/0.99      | ~ l1_pre_topc(X0)
% 3.87/0.99      | v1_xboole_0(u1_struct_0(X0)) ),
% 3.87/0.99      inference(resolution,[status(thm)],[c_8,c_10]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_2391,plain,
% 3.87/0.99      ( ~ v1_zfmisc_1(u1_struct_0(X0))
% 3.87/0.99      | ~ l1_pre_topc(X0)
% 3.87/0.99      | v1_xboole_0(u1_struct_0(X0))
% 3.87/0.99      | k6_domain_1(u1_struct_0(X0),sK1(u1_struct_0(X0))) = u1_struct_0(k1_tex_2(X0,sK1(u1_struct_0(X0)))) ),
% 3.87/0.99      inference(global_propositional_subsumption,
% 3.87/0.99                [status(thm)],
% 3.87/0.99                [c_2387,c_457]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_2393,plain,
% 3.87/0.99      ( k6_domain_1(u1_struct_0(X0),sK1(u1_struct_0(X0))) = u1_struct_0(k1_tex_2(X0,sK1(u1_struct_0(X0))))
% 3.87/0.99      | v1_zfmisc_1(u1_struct_0(X0)) != iProver_top
% 3.87/0.99      | l1_pre_topc(X0) != iProver_top
% 3.87/0.99      | v1_xboole_0(u1_struct_0(X0)) = iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_2391]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_10016,plain,
% 3.87/0.99      ( v1_zfmisc_1(u1_struct_0(X0)) != iProver_top
% 3.87/0.99      | k6_domain_1(u1_struct_0(X0),sK1(u1_struct_0(X0))) = u1_struct_0(k1_tex_2(X0,sK1(u1_struct_0(X0))))
% 3.87/0.99      | l1_pre_topc(X0) != iProver_top
% 3.87/0.99      | v1_xboole_0(u1_struct_0(X0)) = iProver_top ),
% 3.87/0.99      inference(global_propositional_subsumption,
% 3.87/0.99                [status(thm)],
% 3.87/0.99                [c_7099,c_2393]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_10017,plain,
% 3.87/0.99      ( k6_domain_1(u1_struct_0(X0),sK1(u1_struct_0(X0))) = u1_struct_0(k1_tex_2(X0,sK1(u1_struct_0(X0))))
% 3.87/0.99      | v1_zfmisc_1(u1_struct_0(X0)) != iProver_top
% 3.87/0.99      | l1_pre_topc(X0) != iProver_top
% 3.87/0.99      | v1_xboole_0(u1_struct_0(X0)) = iProver_top ),
% 3.87/0.99      inference(renaming,[status(thm)],[c_10016]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_10020,plain,
% 3.87/0.99      ( k6_domain_1(u1_struct_0(sK3),sK1(u1_struct_0(sK3))) = u1_struct_0(k1_tex_2(sK3,sK1(u1_struct_0(sK3))))
% 3.87/0.99      | l1_pre_topc(sK3) != iProver_top
% 3.87/0.99      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 3.87/0.99      inference(superposition,[status(thm)],[c_8044,c_10017]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_10023,plain,
% 3.87/0.99      ( u1_struct_0(k1_tex_2(sK3,sK1(u1_struct_0(sK3)))) = u1_struct_0(sK3)
% 3.87/0.99      | l1_pre_topc(sK3) != iProver_top
% 3.87/0.99      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 3.87/0.99      inference(light_normalisation,[status(thm)],[c_10020,c_8202]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_10903,plain,
% 3.87/0.99      ( u1_struct_0(k1_tex_2(sK3,sK1(u1_struct_0(sK3)))) = u1_struct_0(sK3) ),
% 3.87/0.99      inference(global_propositional_subsumption,
% 3.87/0.99                [status(thm)],
% 3.87/0.99                [c_10023,c_33,c_34,c_88,c_93]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_11293,plain,
% 3.87/0.99      ( u1_struct_0(k1_tex_2(sK3,sK4)) = u1_struct_0(sK3) ),
% 3.87/0.99      inference(demodulation,[status(thm)],[c_11172,c_10903]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_25,plain,
% 3.87/0.99      ( ~ v1_tex_2(X0,X1)
% 3.87/0.99      | ~ m1_pre_topc(X0,X1)
% 3.87/0.99      | ~ l1_pre_topc(X1)
% 3.87/0.99      | u1_struct_0(X0) != u1_struct_0(X1) ),
% 3.87/0.99      inference(cnf_transformation,[],[f91]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_6345,plain,
% 3.87/0.99      ( ~ v1_tex_2(X0,sK3)
% 3.87/0.99      | ~ m1_pre_topc(X0,sK3)
% 3.87/0.99      | ~ l1_pre_topc(sK3)
% 3.87/0.99      | u1_struct_0(X0) != u1_struct_0(sK3) ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_25]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_7910,plain,
% 3.87/0.99      ( ~ v1_tex_2(k1_tex_2(sK3,sK4),sK3)
% 3.87/0.99      | ~ m1_pre_topc(k1_tex_2(sK3,sK4),sK3)
% 3.87/0.99      | ~ l1_pre_topc(sK3)
% 3.87/0.99      | u1_struct_0(k1_tex_2(sK3,sK4)) != u1_struct_0(sK3) ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_6345]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_7911,plain,
% 3.87/0.99      ( u1_struct_0(k1_tex_2(sK3,sK4)) != u1_struct_0(sK3)
% 3.87/0.99      | v1_tex_2(k1_tex_2(sK3,sK4),sK3) != iProver_top
% 3.87/0.99      | m1_pre_topc(k1_tex_2(sK3,sK4),sK3) != iProver_top
% 3.87/0.99      | l1_pre_topc(sK3) != iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_7910]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_6267,plain,
% 3.87/0.99      ( v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),u1_struct_0(sK3)) = iProver_top
% 3.87/0.99      | v1_tex_2(k1_tex_2(sK3,sK4),sK3) = iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_7302,plain,
% 3.87/0.99      ( v1_subset_1(k2_tarski(sK4,sK4),u1_struct_0(sK3)) = iProver_top
% 3.87/0.99      | v1_tex_2(k1_tex_2(sK3,sK4),sK3) = iProver_top ),
% 3.87/0.99      inference(demodulation,[status(thm)],[c_7300,c_6267]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(contradiction,plain,
% 3.87/0.99      ( $false ),
% 3.87/0.99      inference(minisat,
% 3.87/0.99                [status(thm)],
% 3.87/0.99                [c_11293,c_7960,c_7911,c_7302,c_5547,c_2662,c_108,c_105,
% 3.87/0.99                 c_34,c_33]) ).
% 3.87/0.99  
% 3.87/0.99  
% 3.87/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.87/0.99  
% 3.87/0.99  ------                               Statistics
% 3.87/0.99  
% 3.87/0.99  ------ General
% 3.87/0.99  
% 3.87/0.99  abstr_ref_over_cycles:                  0
% 3.87/0.99  abstr_ref_under_cycles:                 0
% 3.87/0.99  gc_basic_clause_elim:                   0
% 3.87/0.99  forced_gc_time:                         0
% 3.87/0.99  parsing_time:                           0.009
% 3.87/0.99  unif_index_cands_time:                  0.
% 3.87/0.99  unif_index_add_time:                    0.
% 3.87/0.99  orderings_time:                         0.
% 3.87/0.99  out_proof_time:                         0.011
% 3.87/0.99  total_time:                             0.284
% 3.87/0.99  num_of_symbols:                         53
% 3.87/0.99  num_of_terms:                           6939
% 3.87/0.99  
% 3.87/0.99  ------ Preprocessing
% 3.87/0.99  
% 3.87/0.99  num_of_splits:                          0
% 3.87/0.99  num_of_split_atoms:                     0
% 3.87/0.99  num_of_reused_defs:                     0
% 3.87/0.99  num_eq_ax_congr_red:                    31
% 3.87/0.99  num_of_sem_filtered_clauses:            1
% 3.87/0.99  num_of_subtypes:                        0
% 3.87/0.99  monotx_restored_types:                  0
% 3.87/0.99  sat_num_of_epr_types:                   0
% 3.87/0.99  sat_num_of_non_cyclic_types:            0
% 3.87/0.99  sat_guarded_non_collapsed_types:        0
% 3.87/0.99  num_pure_diseq_elim:                    0
% 3.87/0.99  simp_replaced_by:                       0
% 3.87/0.99  res_preprocessed:                       160
% 3.87/0.99  prep_upred:                             0
% 3.87/0.99  prep_unflattend:                        266
% 3.87/0.99  smt_new_axioms:                         0
% 3.87/0.99  pred_elim_cands:                        10
% 3.87/0.99  pred_elim:                              1
% 3.87/0.99  pred_elim_cl:                           1
% 3.87/0.99  pred_elim_cycles:                       17
% 3.87/0.99  merged_defs:                            8
% 3.87/0.99  merged_defs_ncl:                        0
% 3.87/0.99  bin_hyper_res:                          8
% 3.87/0.99  prep_cycles:                            4
% 3.87/0.99  pred_elim_time:                         0.074
% 3.87/0.99  splitting_time:                         0.
% 3.87/0.99  sem_filter_time:                        0.
% 3.87/0.99  monotx_time:                            0.
% 3.87/0.99  subtype_inf_time:                       0.
% 3.87/0.99  
% 3.87/0.99  ------ Problem properties
% 3.87/0.99  
% 3.87/0.99  clauses:                                32
% 3.87/0.99  conjectures:                            5
% 3.87/0.99  epr:                                    4
% 3.87/0.99  horn:                                   18
% 3.87/0.99  ground:                                 5
% 3.87/0.99  unary:                                  6
% 3.87/0.99  binary:                                 3
% 3.87/0.99  lits:                                   99
% 3.87/0.99  lits_eq:                                14
% 3.87/0.99  fd_pure:                                0
% 3.87/0.99  fd_pseudo:                              0
% 3.87/0.99  fd_cond:                                0
% 3.87/0.99  fd_pseudo_cond:                         3
% 3.87/0.99  ac_symbols:                             0
% 3.87/0.99  
% 3.87/0.99  ------ Propositional Solver
% 3.87/0.99  
% 3.87/0.99  prop_solver_calls:                      31
% 3.87/0.99  prop_fast_solver_calls:                 2439
% 3.87/0.99  smt_solver_calls:                       0
% 3.87/0.99  smt_fast_solver_calls:                  0
% 3.87/0.99  prop_num_of_clauses:                    3182
% 3.87/0.99  prop_preprocess_simplified:             10578
% 3.87/0.99  prop_fo_subsumed:                       86
% 3.87/0.99  prop_solver_time:                       0.
% 3.87/0.99  smt_solver_time:                        0.
% 3.87/0.99  smt_fast_solver_time:                   0.
% 3.87/0.99  prop_fast_solver_time:                  0.
% 3.87/0.99  prop_unsat_core_time:                   0.
% 3.87/0.99  
% 3.87/0.99  ------ QBF
% 3.87/0.99  
% 3.87/0.99  qbf_q_res:                              0
% 3.87/0.99  qbf_num_tautologies:                    0
% 3.87/0.99  qbf_prep_cycles:                        0
% 3.87/0.99  
% 3.87/0.99  ------ BMC1
% 3.87/0.99  
% 3.87/0.99  bmc1_current_bound:                     -1
% 3.87/0.99  bmc1_last_solved_bound:                 -1
% 3.87/0.99  bmc1_unsat_core_size:                   -1
% 3.87/0.99  bmc1_unsat_core_parents_size:           -1
% 3.87/0.99  bmc1_merge_next_fun:                    0
% 3.87/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.87/0.99  
% 3.87/0.99  ------ Instantiation
% 3.87/0.99  
% 3.87/0.99  inst_num_of_clauses:                    862
% 3.87/0.99  inst_num_in_passive:                    235
% 3.87/0.99  inst_num_in_active:                     389
% 3.87/0.99  inst_num_in_unprocessed:                238
% 3.87/0.99  inst_num_of_loops:                      440
% 3.87/0.99  inst_num_of_learning_restarts:          0
% 3.87/0.99  inst_num_moves_active_passive:          48
% 3.87/0.99  inst_lit_activity:                      0
% 3.87/0.99  inst_lit_activity_moves:                0
% 3.87/0.99  inst_num_tautologies:                   0
% 3.87/0.99  inst_num_prop_implied:                  0
% 3.87/0.99  inst_num_existing_simplified:           0
% 3.87/0.99  inst_num_eq_res_simplified:             0
% 3.87/0.99  inst_num_child_elim:                    0
% 3.87/0.99  inst_num_of_dismatching_blockings:      332
% 3.87/0.99  inst_num_of_non_proper_insts:           871
% 3.87/0.99  inst_num_of_duplicates:                 0
% 3.87/0.99  inst_inst_num_from_inst_to_res:         0
% 3.87/0.99  inst_dismatching_checking_time:         0.
% 3.87/0.99  
% 3.87/0.99  ------ Resolution
% 3.87/0.99  
% 3.87/0.99  res_num_of_clauses:                     0
% 3.87/0.99  res_num_in_passive:                     0
% 3.87/0.99  res_num_in_active:                      0
% 3.87/0.99  res_num_of_loops:                       164
% 3.87/0.99  res_forward_subset_subsumed:            33
% 3.87/0.99  res_backward_subset_subsumed:           0
% 3.87/0.99  res_forward_subsumed:                   0
% 3.87/0.99  res_backward_subsumed:                  0
% 3.87/0.99  res_forward_subsumption_resolution:     2
% 3.87/0.99  res_backward_subsumption_resolution:    0
% 3.87/0.99  res_clause_to_clause_subsumption:       662
% 3.87/0.99  res_orphan_elimination:                 0
% 3.87/0.99  res_tautology_del:                      104
% 3.87/0.99  res_num_eq_res_simplified:              0
% 3.87/0.99  res_num_sel_changes:                    0
% 3.87/0.99  res_moves_from_active_to_pass:          0
% 3.87/0.99  
% 3.87/0.99  ------ Superposition
% 3.87/0.99  
% 3.87/0.99  sup_time_total:                         0.
% 3.87/0.99  sup_time_generating:                    0.
% 3.87/0.99  sup_time_sim_full:                      0.
% 3.87/0.99  sup_time_sim_immed:                     0.
% 3.87/0.99  
% 3.87/0.99  sup_num_of_clauses:                     173
% 3.87/0.99  sup_num_in_active:                      75
% 3.87/0.99  sup_num_in_passive:                     98
% 3.87/0.99  sup_num_of_loops:                       87
% 3.87/0.99  sup_fw_superposition:                   91
% 3.87/0.99  sup_bw_superposition:                   119
% 3.87/0.99  sup_immediate_simplified:               51
% 3.87/0.99  sup_given_eliminated:                   1
% 3.87/0.99  comparisons_done:                       0
% 3.87/0.99  comparisons_avoided:                    6
% 3.87/0.99  
% 3.87/0.99  ------ Simplifications
% 3.87/0.99  
% 3.87/0.99  
% 3.87/0.99  sim_fw_subset_subsumed:                 16
% 3.87/0.99  sim_bw_subset_subsumed:                 2
% 3.87/0.99  sim_fw_subsumed:                        10
% 3.87/0.99  sim_bw_subsumed:                        3
% 3.87/0.99  sim_fw_subsumption_res:                 0
% 3.87/0.99  sim_bw_subsumption_res:                 0
% 3.87/0.99  sim_tautology_del:                      7
% 3.87/0.99  sim_eq_tautology_del:                   9
% 3.87/0.99  sim_eq_res_simp:                        0
% 3.87/0.99  sim_fw_demodulated:                     7
% 3.87/0.99  sim_bw_demodulated:                     8
% 3.87/0.99  sim_light_normalised:                   24
% 3.87/0.99  sim_joinable_taut:                      0
% 3.87/0.99  sim_joinable_simp:                      0
% 3.87/0.99  sim_ac_normalised:                      0
% 3.87/0.99  sim_smt_subsumption:                    0
% 3.87/0.99  
%------------------------------------------------------------------------------
