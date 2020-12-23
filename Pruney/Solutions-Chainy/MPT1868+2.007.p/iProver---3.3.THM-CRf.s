%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:26:25 EST 2020

% Result     : Theorem 3.05s
% Output     : CNFRefutation 3.05s
% Verified   : 
% Statistics : Number of formulae       :  173 (3349 expanded)
%              Number of clauses        :   94 ( 932 expanded)
%              Number of leaves         :   19 ( 804 expanded)
%              Depth                    :   21
%              Number of atoms          :  649 (12017 expanded)
%              Number of equality atoms :  244 (2275 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   10 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f45,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f55,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ~ v2_tex_2(k6_domain_1(u1_struct_0(X0),sK3),X0)
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ v2_tex_2(k6_domain_1(u1_struct_0(sK2),X1),sK2)
          & m1_subset_1(X1,u1_struct_0(sK2)) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
    ( ~ v2_tex_2(k6_domain_1(u1_struct_0(sK2),sK3),sK2)
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f45,f55,f54])).

fof(f84,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f56])).

fof(f12,axiom,(
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
    inference(ennf_transformation,[],[f12])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f2,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f91,plain,(
    ! [X0,X1] :
      ( k2_tarski(X1,X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f71,f61])).

fof(f81,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f83,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f66,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f90,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f62,f61])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f51,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X1
          & m1_pre_topc(X2,X0)
          & v1_pre_topc(X2)
          & ~ v2_struct_0(X2) )
     => ( u1_struct_0(sK1(X0,X1)) = X1
        & m1_pre_topc(sK1(X0,X1),X0)
        & v1_pre_topc(sK1(X0,X1))
        & ~ v2_struct_0(sK1(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_struct_0(sK1(X0,X1)) = X1
            & m1_pre_topc(sK1(X0,X1),X0)
            & v1_pre_topc(sK1(X0,X1))
            & ~ v2_struct_0(sK1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f39,f51])).

fof(f75,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(sK1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f77,plain,(
    ! [X0,X1] :
      ( u1_struct_0(sK1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
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

fof(f47,plain,(
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
    inference(rectify,[],[f46])).

fof(f48,plain,(
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

fof(f49,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f47,f48])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f88,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f58,f61])).

fof(f92,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_tarski(X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f88])).

fof(f93,plain,(
    ! [X3] : r2_hidden(X3,k2_tarski(X3,X3)) ),
    inference(equality_resolution,[],[f92])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f13,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f13])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f50,plain,(
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
    inference(nnf_transformation,[],[f37])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k1_tex_2(X0,X1) = X2
      | u1_struct_0(X2) != k6_domain_1(u1_struct_0(X0),X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(sK1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f76,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(sK1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( v2_tex_2(X2,X0)
                <=> v1_tdlat_3(X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v2_tex_2(X2,X0)
                  | ~ v1_tdlat_3(X1) )
                & ( v1_tdlat_3(X1)
                  | ~ v2_tex_2(X2,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(X2,X0)
      | ~ v1_tdlat_3(X1)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f96,plain,(
    ! [X0,X1] :
      ( v2_tex_2(u1_struct_0(X1),X0)
      | ~ v1_tdlat_3(X1)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f80])).

fof(f85,plain,(
    ~ v2_tex_2(k6_domain_1(u1_struct_0(sK2),sK3),sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v2_pre_topc(k1_tex_2(X0,X1))
           => ( v2_tdlat_3(k1_tex_2(X0,X1))
              & v1_tdlat_3(k1_tex_2(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v2_pre_topc(k1_tex_2(X0,X1))
           => v1_tdlat_3(k1_tex_2(X0,X1)) ) ) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tdlat_3(k1_tex_2(X0,X1))
          | ~ v2_pre_topc(k1_tex_2(X0,X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tdlat_3(k1_tex_2(X0,X1))
          | ~ v2_pre_topc(k1_tex_2(X0,X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f78,plain,(
    ! [X0,X1] :
      ( v1_tdlat_3(k1_tex_2(X0,X1))
      | ~ v2_pre_topc(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f82,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2731,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_2739,plain,
    ( k6_domain_1(X0,X1) = k2_tarski(X1,X1)
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3250,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK3) = k2_tarski(sK3,sK3)
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2731,c_2739])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_25,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_11,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_67,plain,
    ( v2_struct_0(sK2)
    | ~ l1_struct_0(sK2)
    | ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_8,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_72,plain,
    ( l1_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2989,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2))
    | k6_domain_1(u1_struct_0(sK2),sK3) = k2_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_3351,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK3) = k2_tarski(sK3,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3250,c_27,c_25,c_24,c_67,c_72,c_2989])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2740,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3857,plain,
    ( m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3351,c_2740])).

cnf(c_28,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_30,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_31,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_66,plain,
    ( v2_struct_0(X0) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_68,plain,
    ( v2_struct_0(sK2) = iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_66])).

cnf(c_71,plain,
    ( l1_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_73,plain,
    ( l1_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_71])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2983,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | r2_hidden(sK3,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2984,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK3,u1_struct_0(sK2)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2983])).

cnf(c_4,plain,
    ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_3032,plain,
    ( m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK3,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_3033,plain,
    ( m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | r2_hidden(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3032])).

cnf(c_4231,plain,
    ( m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3857,c_28,c_30,c_31,c_68,c_73,c_2984,c_3033])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_pre_topc(sK1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2734,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v1_pre_topc(sK1(X1,X0)) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4239,plain,
    ( v1_pre_topc(sK1(sK2,k2_tarski(sK3,sK3))) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_xboole_0(k2_tarski(sK3,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4231,c_2734])).

cnf(c_4405,plain,
    ( v1_pre_topc(sK1(sK2,k2_tarski(sK3,sK3))) = iProver_top
    | v1_xboole_0(k2_tarski(sK3,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4239,c_28,c_30])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(sK1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2736,plain,
    ( u1_struct_0(sK1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4782,plain,
    ( u1_struct_0(sK1(sK2,k2_tarski(sK3,sK3))) = k2_tarski(sK3,sK3)
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_xboole_0(k2_tarski(sK3,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4231,c_2736])).

cnf(c_5374,plain,
    ( u1_struct_0(sK1(sK2,k2_tarski(sK3,sK3))) = k2_tarski(sK3,sK3)
    | v1_xboole_0(k2_tarski(sK3,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4782,c_28,c_30])).

cnf(c_2,plain,
    ( r2_hidden(X0,k2_tarski(X0,X0)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_2747,plain,
    ( r2_hidden(X0,k2_tarski(X0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2745,plain,
    ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1)) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2743,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3532,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,k2_tarski(X0,X0)) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2745,c_2743])).

cnf(c_81,plain,
    ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1)) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_614,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | X2 != X3
    | k2_tarski(X3,X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_6])).

cnf(c_615,plain,
    ( ~ m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1) ),
    inference(unflattening,[status(thm)],[c_614])).

cnf(c_616,plain,
    ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1)) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_615])).

cnf(c_3659,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3532,c_81,c_616])).

cnf(c_3667,plain,
    ( v1_xboole_0(k2_tarski(X0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2747,c_3659])).

cnf(c_5380,plain,
    ( u1_struct_0(sK1(sK2,k2_tarski(sK3,sK3))) = k2_tarski(sK3,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5374,c_3667])).

cnf(c_14,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v1_pre_topc(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | k1_tex_2(X1,X2) = X0
    | k6_domain_1(u1_struct_0(X1),X2) != u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2738,plain,
    ( k1_tex_2(X0,X1) = X2
    | k6_domain_1(u1_struct_0(X0),X1) != u1_struct_0(X2)
    | m1_pre_topc(X2,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v1_pre_topc(X2) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_5127,plain,
    ( k1_tex_2(sK2,sK3) = X0
    | k2_tarski(sK3,sK3) != u1_struct_0(X0)
    | m1_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | v1_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3351,c_2738])).

cnf(c_5222,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | k2_tarski(sK3,sK3) != u1_struct_0(X0)
    | k1_tex_2(sK2,sK3) = X0
    | v1_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5127,c_28,c_30,c_31])).

cnf(c_5223,plain,
    ( k1_tex_2(sK2,sK3) = X0
    | k2_tarski(sK3,sK3) != u1_struct_0(X0)
    | m1_pre_topc(X0,sK2) != iProver_top
    | v1_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_5222])).

cnf(c_5381,plain,
    ( sK1(sK2,k2_tarski(sK3,sK3)) = k1_tex_2(sK2,sK3)
    | m1_pre_topc(sK1(sK2,k2_tarski(sK3,sK3)),sK2) != iProver_top
    | v1_pre_topc(sK1(sK2,k2_tarski(sK3,sK3))) != iProver_top
    | v2_struct_0(sK1(sK2,k2_tarski(sK3,sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5380,c_5223])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_struct_0(sK1(X1,X0))
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2733,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(sK1(X1,X0)) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4497,plain,
    ( v2_struct_0(sK1(sK2,k2_tarski(sK3,sK3))) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_xboole_0(k2_tarski(sK3,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4231,c_2733])).

cnf(c_5234,plain,
    ( v2_struct_0(sK1(sK2,k2_tarski(sK3,sK3))) != iProver_top
    | v1_xboole_0(k2_tarski(sK3,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4497,c_28,c_30])).

cnf(c_5240,plain,
    ( v2_struct_0(sK1(sK2,k2_tarski(sK3,sK3))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5234,c_3667])).

cnf(c_17,plain,
    ( m1_pre_topc(sK1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2735,plain,
    ( m1_pre_topc(sK1(X0,X1),X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4828,plain,
    ( m1_pre_topc(sK1(sK2,k2_tarski(sK3,sK3)),sK2) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_xboole_0(k2_tarski(sK3,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4231,c_2735])).

cnf(c_5351,plain,
    ( m1_pre_topc(sK1(sK2,k2_tarski(sK3,sK3)),sK2) = iProver_top
    | v1_xboole_0(k2_tarski(sK3,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4828,c_28,c_30])).

cnf(c_5357,plain,
    ( m1_pre_topc(sK1(sK2,k2_tarski(sK3,sK3)),sK2) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5351,c_3667])).

cnf(c_5612,plain,
    ( v1_pre_topc(sK1(sK2,k2_tarski(sK3,sK3))) != iProver_top
    | sK1(sK2,k2_tarski(sK3,sK3)) = k1_tex_2(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5381,c_5240,c_5357])).

cnf(c_5613,plain,
    ( sK1(sK2,k2_tarski(sK3,sK3)) = k1_tex_2(sK2,sK3)
    | v1_pre_topc(sK1(sK2,k2_tarski(sK3,sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_5612])).

cnf(c_5618,plain,
    ( sK1(sK2,k2_tarski(sK3,sK3)) = k1_tex_2(sK2,sK3)
    | v1_xboole_0(k2_tarski(sK3,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4405,c_5613])).

cnf(c_5732,plain,
    ( sK1(sK2,k2_tarski(sK3,sK3)) = k1_tex_2(sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5618,c_3667])).

cnf(c_5735,plain,
    ( m1_pre_topc(k1_tex_2(sK2,sK3),sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5732,c_5357])).

cnf(c_21,plain,
    ( v2_tex_2(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_23,negated_conjecture,
    ( ~ v2_tex_2(k6_domain_1(u1_struct_0(sK2),sK3),sK2) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_346,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k6_domain_1(u1_struct_0(sK2),sK3) != u1_struct_0(X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_23])).

cnf(c_347,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | k6_domain_1(u1_struct_0(sK2),sK3) != u1_struct_0(X0) ),
    inference(unflattening,[status(thm)],[c_346])).

cnf(c_351,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | k6_domain_1(u1_struct_0(sK2),sK3) != u1_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_347,c_27,c_25])).

cnf(c_2725,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK3) != u1_struct_0(X0)
    | m1_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_tdlat_3(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_351])).

cnf(c_3354,plain,
    ( k2_tarski(sK3,sK3) != u1_struct_0(X0)
    | m1_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_tdlat_3(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3351,c_2725])).

cnf(c_5386,plain,
    ( m1_pre_topc(sK1(sK2,k2_tarski(sK3,sK3)),sK2) != iProver_top
    | m1_subset_1(u1_struct_0(sK1(sK2,k2_tarski(sK3,sK3))),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_tdlat_3(sK1(sK2,k2_tarski(sK3,sK3))) != iProver_top
    | v2_struct_0(sK1(sK2,k2_tarski(sK3,sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5380,c_3354])).

cnf(c_5442,plain,
    ( m1_pre_topc(sK1(sK2,k2_tarski(sK3,sK3)),sK2) != iProver_top
    | m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_tdlat_3(sK1(sK2,k2_tarski(sK3,sK3))) != iProver_top
    | v2_struct_0(sK1(sK2,k2_tarski(sK3,sK3))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5386,c_5380])).

cnf(c_5621,plain,
    ( v1_tdlat_3(sK1(sK2,k2_tarski(sK3,sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5442,c_28,c_30,c_31,c_68,c_73,c_2984,c_3033,c_5240,c_5357])).

cnf(c_5733,plain,
    ( v1_tdlat_3(k1_tex_2(sK2,sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5732,c_5621])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v1_tdlat_3(k1_tex_2(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(k1_tex_2(X1,X0)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2732,plain,
    ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
    | v1_tdlat_3(k1_tex_2(X1,X0)) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(k1_tex_2(X1,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3683,plain,
    ( v1_tdlat_3(k1_tex_2(sK2,sK3)) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(k1_tex_2(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2731,c_2732])).

cnf(c_4044,plain,
    ( v1_tdlat_3(k1_tex_2(sK2,sK3)) = iProver_top
    | v2_pre_topc(k1_tex_2(sK2,sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3683,c_28,c_30])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_3215,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK2,sK3),X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_pre_topc(k1_tex_2(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_3216,plain,
    ( m1_pre_topc(k1_tex_2(sK2,sK3),X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(k1_tex_2(sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3215])).

cnf(c_3218,plain,
    ( m1_pre_topc(k1_tex_2(sK2,sK3),sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(k1_tex_2(sK2,sK3)) = iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3216])).

cnf(c_26,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_29,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5735,c_5733,c_4044,c_3218,c_30,c_29])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:10:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.05/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.05/0.98  
% 3.05/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.05/0.98  
% 3.05/0.98  ------  iProver source info
% 3.05/0.98  
% 3.05/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.05/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.05/0.98  git: non_committed_changes: false
% 3.05/0.98  git: last_make_outside_of_git: false
% 3.05/0.98  
% 3.05/0.98  ------ 
% 3.05/0.98  
% 3.05/0.98  ------ Input Options
% 3.05/0.98  
% 3.05/0.98  --out_options                           all
% 3.05/0.98  --tptp_safe_out                         true
% 3.05/0.98  --problem_path                          ""
% 3.05/0.98  --include_path                          ""
% 3.05/0.98  --clausifier                            res/vclausify_rel
% 3.05/0.98  --clausifier_options                    --mode clausify
% 3.05/0.98  --stdin                                 false
% 3.05/0.98  --stats_out                             all
% 3.05/0.98  
% 3.05/0.98  ------ General Options
% 3.05/0.98  
% 3.05/0.98  --fof                                   false
% 3.05/0.98  --time_out_real                         305.
% 3.05/0.98  --time_out_virtual                      -1.
% 3.05/0.98  --symbol_type_check                     false
% 3.05/0.98  --clausify_out                          false
% 3.05/0.98  --sig_cnt_out                           false
% 3.05/0.98  --trig_cnt_out                          false
% 3.05/0.98  --trig_cnt_out_tolerance                1.
% 3.05/0.98  --trig_cnt_out_sk_spl                   false
% 3.05/0.98  --abstr_cl_out                          false
% 3.05/0.98  
% 3.05/0.98  ------ Global Options
% 3.05/0.98  
% 3.05/0.98  --schedule                              default
% 3.05/0.98  --add_important_lit                     false
% 3.05/0.98  --prop_solver_per_cl                    1000
% 3.05/0.98  --min_unsat_core                        false
% 3.05/0.98  --soft_assumptions                      false
% 3.05/0.98  --soft_lemma_size                       3
% 3.05/0.98  --prop_impl_unit_size                   0
% 3.05/0.98  --prop_impl_unit                        []
% 3.05/0.98  --share_sel_clauses                     true
% 3.05/0.98  --reset_solvers                         false
% 3.05/0.98  --bc_imp_inh                            [conj_cone]
% 3.05/0.98  --conj_cone_tolerance                   3.
% 3.05/0.98  --extra_neg_conj                        none
% 3.05/0.98  --large_theory_mode                     true
% 3.05/0.98  --prolific_symb_bound                   200
% 3.05/0.98  --lt_threshold                          2000
% 3.05/0.98  --clause_weak_htbl                      true
% 3.05/0.98  --gc_record_bc_elim                     false
% 3.05/0.98  
% 3.05/0.98  ------ Preprocessing Options
% 3.05/0.98  
% 3.05/0.98  --preprocessing_flag                    true
% 3.05/0.98  --time_out_prep_mult                    0.1
% 3.05/0.98  --splitting_mode                        input
% 3.05/0.98  --splitting_grd                         true
% 3.05/0.98  --splitting_cvd                         false
% 3.05/0.98  --splitting_cvd_svl                     false
% 3.05/0.98  --splitting_nvd                         32
% 3.05/0.98  --sub_typing                            true
% 3.05/0.98  --prep_gs_sim                           true
% 3.05/0.98  --prep_unflatten                        true
% 3.05/0.98  --prep_res_sim                          true
% 3.05/0.98  --prep_upred                            true
% 3.05/0.98  --prep_sem_filter                       exhaustive
% 3.05/0.98  --prep_sem_filter_out                   false
% 3.05/0.98  --pred_elim                             true
% 3.05/0.98  --res_sim_input                         true
% 3.05/0.98  --eq_ax_congr_red                       true
% 3.05/0.98  --pure_diseq_elim                       true
% 3.05/0.98  --brand_transform                       false
% 3.05/0.98  --non_eq_to_eq                          false
% 3.05/0.98  --prep_def_merge                        true
% 3.05/0.98  --prep_def_merge_prop_impl              false
% 3.05/0.98  --prep_def_merge_mbd                    true
% 3.05/0.98  --prep_def_merge_tr_red                 false
% 3.05/0.98  --prep_def_merge_tr_cl                  false
% 3.05/0.98  --smt_preprocessing                     true
% 3.05/0.98  --smt_ac_axioms                         fast
% 3.05/0.98  --preprocessed_out                      false
% 3.05/0.98  --preprocessed_stats                    false
% 3.05/0.98  
% 3.05/0.98  ------ Abstraction refinement Options
% 3.05/0.98  
% 3.05/0.98  --abstr_ref                             []
% 3.05/0.98  --abstr_ref_prep                        false
% 3.05/0.98  --abstr_ref_until_sat                   false
% 3.05/0.98  --abstr_ref_sig_restrict                funpre
% 3.05/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.05/0.98  --abstr_ref_under                       []
% 3.05/0.98  
% 3.05/0.98  ------ SAT Options
% 3.05/0.98  
% 3.05/0.98  --sat_mode                              false
% 3.05/0.98  --sat_fm_restart_options                ""
% 3.05/0.98  --sat_gr_def                            false
% 3.05/0.98  --sat_epr_types                         true
% 3.05/0.98  --sat_non_cyclic_types                  false
% 3.05/0.98  --sat_finite_models                     false
% 3.05/0.98  --sat_fm_lemmas                         false
% 3.05/0.98  --sat_fm_prep                           false
% 3.05/0.98  --sat_fm_uc_incr                        true
% 3.05/0.98  --sat_out_model                         small
% 3.05/0.98  --sat_out_clauses                       false
% 3.05/0.98  
% 3.05/0.98  ------ QBF Options
% 3.05/0.98  
% 3.05/0.98  --qbf_mode                              false
% 3.05/0.98  --qbf_elim_univ                         false
% 3.05/0.98  --qbf_dom_inst                          none
% 3.05/0.98  --qbf_dom_pre_inst                      false
% 3.05/0.98  --qbf_sk_in                             false
% 3.05/0.98  --qbf_pred_elim                         true
% 3.05/0.98  --qbf_split                             512
% 3.05/0.98  
% 3.05/0.98  ------ BMC1 Options
% 3.05/0.98  
% 3.05/0.98  --bmc1_incremental                      false
% 3.05/0.98  --bmc1_axioms                           reachable_all
% 3.05/0.98  --bmc1_min_bound                        0
% 3.05/0.98  --bmc1_max_bound                        -1
% 3.05/0.98  --bmc1_max_bound_default                -1
% 3.05/0.98  --bmc1_symbol_reachability              true
% 3.05/0.98  --bmc1_property_lemmas                  false
% 3.05/0.98  --bmc1_k_induction                      false
% 3.05/0.98  --bmc1_non_equiv_states                 false
% 3.05/0.98  --bmc1_deadlock                         false
% 3.05/0.98  --bmc1_ucm                              false
% 3.05/0.98  --bmc1_add_unsat_core                   none
% 3.05/0.98  --bmc1_unsat_core_children              false
% 3.05/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.05/0.98  --bmc1_out_stat                         full
% 3.05/0.98  --bmc1_ground_init                      false
% 3.05/0.98  --bmc1_pre_inst_next_state              false
% 3.05/0.98  --bmc1_pre_inst_state                   false
% 3.05/0.98  --bmc1_pre_inst_reach_state             false
% 3.05/0.98  --bmc1_out_unsat_core                   false
% 3.05/0.98  --bmc1_aig_witness_out                  false
% 3.05/0.98  --bmc1_verbose                          false
% 3.05/0.98  --bmc1_dump_clauses_tptp                false
% 3.05/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.05/0.98  --bmc1_dump_file                        -
% 3.05/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.05/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.05/0.98  --bmc1_ucm_extend_mode                  1
% 3.05/0.98  --bmc1_ucm_init_mode                    2
% 3.05/0.98  --bmc1_ucm_cone_mode                    none
% 3.05/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.05/0.98  --bmc1_ucm_relax_model                  4
% 3.05/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.05/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.05/0.98  --bmc1_ucm_layered_model                none
% 3.05/0.98  --bmc1_ucm_max_lemma_size               10
% 3.05/0.98  
% 3.05/0.98  ------ AIG Options
% 3.05/0.98  
% 3.05/0.98  --aig_mode                              false
% 3.05/0.98  
% 3.05/0.98  ------ Instantiation Options
% 3.05/0.98  
% 3.05/0.98  --instantiation_flag                    true
% 3.05/0.98  --inst_sos_flag                         false
% 3.05/0.98  --inst_sos_phase                        true
% 3.05/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.05/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.05/0.98  --inst_lit_sel_side                     num_symb
% 3.05/0.98  --inst_solver_per_active                1400
% 3.05/0.98  --inst_solver_calls_frac                1.
% 3.05/0.98  --inst_passive_queue_type               priority_queues
% 3.05/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.05/0.98  --inst_passive_queues_freq              [25;2]
% 3.05/0.98  --inst_dismatching                      true
% 3.05/0.98  --inst_eager_unprocessed_to_passive     true
% 3.05/0.98  --inst_prop_sim_given                   true
% 3.05/0.98  --inst_prop_sim_new                     false
% 3.05/0.98  --inst_subs_new                         false
% 3.05/0.98  --inst_eq_res_simp                      false
% 3.05/0.98  --inst_subs_given                       false
% 3.05/0.98  --inst_orphan_elimination               true
% 3.05/0.98  --inst_learning_loop_flag               true
% 3.05/0.98  --inst_learning_start                   3000
% 3.05/0.98  --inst_learning_factor                  2
% 3.05/0.98  --inst_start_prop_sim_after_learn       3
% 3.05/0.98  --inst_sel_renew                        solver
% 3.05/0.98  --inst_lit_activity_flag                true
% 3.05/0.98  --inst_restr_to_given                   false
% 3.05/0.98  --inst_activity_threshold               500
% 3.05/0.98  --inst_out_proof                        true
% 3.05/0.98  
% 3.05/0.98  ------ Resolution Options
% 3.05/0.98  
% 3.05/0.98  --resolution_flag                       true
% 3.05/0.98  --res_lit_sel                           adaptive
% 3.05/0.98  --res_lit_sel_side                      none
% 3.05/0.98  --res_ordering                          kbo
% 3.05/0.98  --res_to_prop_solver                    active
% 3.05/0.98  --res_prop_simpl_new                    false
% 3.05/0.98  --res_prop_simpl_given                  true
% 3.05/0.98  --res_passive_queue_type                priority_queues
% 3.05/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.05/0.98  --res_passive_queues_freq               [15;5]
% 3.05/0.98  --res_forward_subs                      full
% 3.05/0.98  --res_backward_subs                     full
% 3.05/0.98  --res_forward_subs_resolution           true
% 3.05/0.98  --res_backward_subs_resolution          true
% 3.05/0.98  --res_orphan_elimination                true
% 3.05/0.98  --res_time_limit                        2.
% 3.05/0.98  --res_out_proof                         true
% 3.05/0.98  
% 3.05/0.98  ------ Superposition Options
% 3.05/0.98  
% 3.05/0.98  --superposition_flag                    true
% 3.05/0.98  --sup_passive_queue_type                priority_queues
% 3.05/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.05/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.05/0.98  --demod_completeness_check              fast
% 3.05/0.98  --demod_use_ground                      true
% 3.05/0.98  --sup_to_prop_solver                    passive
% 3.05/0.98  --sup_prop_simpl_new                    true
% 3.05/0.98  --sup_prop_simpl_given                  true
% 3.05/0.98  --sup_fun_splitting                     false
% 3.05/0.98  --sup_smt_interval                      50000
% 3.05/0.98  
% 3.05/0.98  ------ Superposition Simplification Setup
% 3.05/0.98  
% 3.05/0.98  --sup_indices_passive                   []
% 3.05/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.05/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.05/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.05/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.05/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.05/0.98  --sup_full_bw                           [BwDemod]
% 3.05/0.98  --sup_immed_triv                        [TrivRules]
% 3.05/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.05/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.05/0.98  --sup_immed_bw_main                     []
% 3.05/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.05/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.05/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.05/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.05/0.98  
% 3.05/0.98  ------ Combination Options
% 3.05/0.98  
% 3.05/0.98  --comb_res_mult                         3
% 3.05/0.98  --comb_sup_mult                         2
% 3.05/0.98  --comb_inst_mult                        10
% 3.05/0.98  
% 3.05/0.98  ------ Debug Options
% 3.05/0.98  
% 3.05/0.98  --dbg_backtrace                         false
% 3.05/0.98  --dbg_dump_prop_clauses                 false
% 3.05/0.98  --dbg_dump_prop_clauses_file            -
% 3.05/0.98  --dbg_out_stat                          false
% 3.05/0.98  ------ Parsing...
% 3.05/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.05/0.98  
% 3.05/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.05/0.98  
% 3.05/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.05/0.98  
% 3.05/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.05/0.98  ------ Proving...
% 3.05/0.98  ------ Problem Properties 
% 3.05/0.98  
% 3.05/0.98  
% 3.05/0.98  clauses                                 25
% 3.05/0.98  conjectures                             4
% 3.05/0.98  EPR                                     6
% 3.05/0.98  Horn                                    14
% 3.05/0.98  unary                                   5
% 3.05/0.98  binary                                  2
% 3.05/0.98  lits                                    85
% 3.05/0.98  lits eq                                 11
% 3.05/0.98  fd_pure                                 0
% 3.05/0.98  fd_pseudo                               0
% 3.05/0.98  fd_cond                                 0
% 3.05/0.98  fd_pseudo_cond                          3
% 3.05/0.98  AC symbols                              0
% 3.05/0.98  
% 3.05/0.98  ------ Schedule dynamic 5 is on 
% 3.05/0.98  
% 3.05/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.05/0.98  
% 3.05/0.98  
% 3.05/0.98  ------ 
% 3.05/0.98  Current options:
% 3.05/0.98  ------ 
% 3.05/0.98  
% 3.05/0.98  ------ Input Options
% 3.05/0.98  
% 3.05/0.98  --out_options                           all
% 3.05/0.98  --tptp_safe_out                         true
% 3.05/0.98  --problem_path                          ""
% 3.05/0.98  --include_path                          ""
% 3.05/0.98  --clausifier                            res/vclausify_rel
% 3.05/0.98  --clausifier_options                    --mode clausify
% 3.05/0.98  --stdin                                 false
% 3.05/0.98  --stats_out                             all
% 3.05/0.98  
% 3.05/0.98  ------ General Options
% 3.05/0.98  
% 3.05/0.98  --fof                                   false
% 3.05/0.98  --time_out_real                         305.
% 3.05/0.98  --time_out_virtual                      -1.
% 3.05/0.98  --symbol_type_check                     false
% 3.05/0.98  --clausify_out                          false
% 3.05/0.98  --sig_cnt_out                           false
% 3.05/0.98  --trig_cnt_out                          false
% 3.05/0.98  --trig_cnt_out_tolerance                1.
% 3.05/0.98  --trig_cnt_out_sk_spl                   false
% 3.05/0.98  --abstr_cl_out                          false
% 3.05/0.98  
% 3.05/0.98  ------ Global Options
% 3.05/0.98  
% 3.05/0.98  --schedule                              default
% 3.05/0.98  --add_important_lit                     false
% 3.05/0.98  --prop_solver_per_cl                    1000
% 3.05/0.98  --min_unsat_core                        false
% 3.05/0.98  --soft_assumptions                      false
% 3.05/0.98  --soft_lemma_size                       3
% 3.05/0.98  --prop_impl_unit_size                   0
% 3.05/0.98  --prop_impl_unit                        []
% 3.05/0.98  --share_sel_clauses                     true
% 3.05/0.98  --reset_solvers                         false
% 3.05/0.98  --bc_imp_inh                            [conj_cone]
% 3.05/0.98  --conj_cone_tolerance                   3.
% 3.05/0.98  --extra_neg_conj                        none
% 3.05/0.98  --large_theory_mode                     true
% 3.05/0.98  --prolific_symb_bound                   200
% 3.05/0.98  --lt_threshold                          2000
% 3.05/0.98  --clause_weak_htbl                      true
% 3.05/0.98  --gc_record_bc_elim                     false
% 3.05/0.98  
% 3.05/0.98  ------ Preprocessing Options
% 3.05/0.98  
% 3.05/0.98  --preprocessing_flag                    true
% 3.05/0.98  --time_out_prep_mult                    0.1
% 3.05/0.98  --splitting_mode                        input
% 3.05/0.98  --splitting_grd                         true
% 3.05/0.98  --splitting_cvd                         false
% 3.05/0.98  --splitting_cvd_svl                     false
% 3.05/0.98  --splitting_nvd                         32
% 3.05/0.98  --sub_typing                            true
% 3.05/0.98  --prep_gs_sim                           true
% 3.05/0.98  --prep_unflatten                        true
% 3.05/0.98  --prep_res_sim                          true
% 3.05/0.98  --prep_upred                            true
% 3.05/0.98  --prep_sem_filter                       exhaustive
% 3.05/0.98  --prep_sem_filter_out                   false
% 3.05/0.98  --pred_elim                             true
% 3.05/0.98  --res_sim_input                         true
% 3.05/0.98  --eq_ax_congr_red                       true
% 3.05/0.98  --pure_diseq_elim                       true
% 3.05/0.98  --brand_transform                       false
% 3.05/0.98  --non_eq_to_eq                          false
% 3.05/0.98  --prep_def_merge                        true
% 3.05/0.98  --prep_def_merge_prop_impl              false
% 3.05/0.98  --prep_def_merge_mbd                    true
% 3.05/0.98  --prep_def_merge_tr_red                 false
% 3.05/0.98  --prep_def_merge_tr_cl                  false
% 3.05/0.98  --smt_preprocessing                     true
% 3.05/0.98  --smt_ac_axioms                         fast
% 3.05/0.98  --preprocessed_out                      false
% 3.05/0.98  --preprocessed_stats                    false
% 3.05/0.98  
% 3.05/0.98  ------ Abstraction refinement Options
% 3.05/0.98  
% 3.05/0.98  --abstr_ref                             []
% 3.05/0.98  --abstr_ref_prep                        false
% 3.05/0.98  --abstr_ref_until_sat                   false
% 3.05/0.98  --abstr_ref_sig_restrict                funpre
% 3.05/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.05/0.98  --abstr_ref_under                       []
% 3.05/0.98  
% 3.05/0.98  ------ SAT Options
% 3.05/0.98  
% 3.05/0.98  --sat_mode                              false
% 3.05/0.98  --sat_fm_restart_options                ""
% 3.05/0.98  --sat_gr_def                            false
% 3.05/0.98  --sat_epr_types                         true
% 3.05/0.98  --sat_non_cyclic_types                  false
% 3.05/0.98  --sat_finite_models                     false
% 3.05/0.98  --sat_fm_lemmas                         false
% 3.05/0.98  --sat_fm_prep                           false
% 3.05/0.98  --sat_fm_uc_incr                        true
% 3.05/0.98  --sat_out_model                         small
% 3.05/0.98  --sat_out_clauses                       false
% 3.05/0.98  
% 3.05/0.98  ------ QBF Options
% 3.05/0.98  
% 3.05/0.98  --qbf_mode                              false
% 3.05/0.98  --qbf_elim_univ                         false
% 3.05/0.98  --qbf_dom_inst                          none
% 3.05/0.98  --qbf_dom_pre_inst                      false
% 3.05/0.98  --qbf_sk_in                             false
% 3.05/0.98  --qbf_pred_elim                         true
% 3.05/0.98  --qbf_split                             512
% 3.05/0.98  
% 3.05/0.98  ------ BMC1 Options
% 3.05/0.98  
% 3.05/0.98  --bmc1_incremental                      false
% 3.05/0.98  --bmc1_axioms                           reachable_all
% 3.05/0.98  --bmc1_min_bound                        0
% 3.05/0.98  --bmc1_max_bound                        -1
% 3.05/0.98  --bmc1_max_bound_default                -1
% 3.05/0.98  --bmc1_symbol_reachability              true
% 3.05/0.98  --bmc1_property_lemmas                  false
% 3.05/0.98  --bmc1_k_induction                      false
% 3.05/0.98  --bmc1_non_equiv_states                 false
% 3.05/0.98  --bmc1_deadlock                         false
% 3.05/0.98  --bmc1_ucm                              false
% 3.05/0.98  --bmc1_add_unsat_core                   none
% 3.05/0.98  --bmc1_unsat_core_children              false
% 3.05/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.05/0.98  --bmc1_out_stat                         full
% 3.05/0.98  --bmc1_ground_init                      false
% 3.05/0.98  --bmc1_pre_inst_next_state              false
% 3.05/0.98  --bmc1_pre_inst_state                   false
% 3.05/0.98  --bmc1_pre_inst_reach_state             false
% 3.05/0.98  --bmc1_out_unsat_core                   false
% 3.05/0.98  --bmc1_aig_witness_out                  false
% 3.05/0.98  --bmc1_verbose                          false
% 3.05/0.98  --bmc1_dump_clauses_tptp                false
% 3.05/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.05/0.98  --bmc1_dump_file                        -
% 3.05/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.05/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.05/0.98  --bmc1_ucm_extend_mode                  1
% 3.05/0.98  --bmc1_ucm_init_mode                    2
% 3.05/0.98  --bmc1_ucm_cone_mode                    none
% 3.05/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.05/0.98  --bmc1_ucm_relax_model                  4
% 3.05/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.05/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.05/0.98  --bmc1_ucm_layered_model                none
% 3.05/0.98  --bmc1_ucm_max_lemma_size               10
% 3.05/0.98  
% 3.05/0.98  ------ AIG Options
% 3.05/0.98  
% 3.05/0.98  --aig_mode                              false
% 3.05/0.98  
% 3.05/0.98  ------ Instantiation Options
% 3.05/0.98  
% 3.05/0.98  --instantiation_flag                    true
% 3.05/0.98  --inst_sos_flag                         false
% 3.05/0.98  --inst_sos_phase                        true
% 3.05/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.05/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.05/0.98  --inst_lit_sel_side                     none
% 3.05/0.98  --inst_solver_per_active                1400
% 3.05/0.98  --inst_solver_calls_frac                1.
% 3.05/0.98  --inst_passive_queue_type               priority_queues
% 3.05/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.05/0.98  --inst_passive_queues_freq              [25;2]
% 3.05/0.98  --inst_dismatching                      true
% 3.05/0.98  --inst_eager_unprocessed_to_passive     true
% 3.05/0.98  --inst_prop_sim_given                   true
% 3.05/0.98  --inst_prop_sim_new                     false
% 3.05/0.98  --inst_subs_new                         false
% 3.05/0.98  --inst_eq_res_simp                      false
% 3.05/0.98  --inst_subs_given                       false
% 3.05/0.98  --inst_orphan_elimination               true
% 3.05/0.98  --inst_learning_loop_flag               true
% 3.05/0.98  --inst_learning_start                   3000
% 3.05/0.98  --inst_learning_factor                  2
% 3.05/0.98  --inst_start_prop_sim_after_learn       3
% 3.05/0.98  --inst_sel_renew                        solver
% 3.05/0.98  --inst_lit_activity_flag                true
% 3.05/0.98  --inst_restr_to_given                   false
% 3.05/0.98  --inst_activity_threshold               500
% 3.05/0.98  --inst_out_proof                        true
% 3.05/0.98  
% 3.05/0.98  ------ Resolution Options
% 3.05/0.98  
% 3.05/0.98  --resolution_flag                       false
% 3.05/0.98  --res_lit_sel                           adaptive
% 3.05/0.98  --res_lit_sel_side                      none
% 3.05/0.98  --res_ordering                          kbo
% 3.05/0.98  --res_to_prop_solver                    active
% 3.05/0.98  --res_prop_simpl_new                    false
% 3.05/0.98  --res_prop_simpl_given                  true
% 3.05/0.98  --res_passive_queue_type                priority_queues
% 3.05/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.05/0.98  --res_passive_queues_freq               [15;5]
% 3.05/0.98  --res_forward_subs                      full
% 3.05/0.98  --res_backward_subs                     full
% 3.05/0.98  --res_forward_subs_resolution           true
% 3.05/0.98  --res_backward_subs_resolution          true
% 3.05/0.98  --res_orphan_elimination                true
% 3.05/0.98  --res_time_limit                        2.
% 3.05/0.98  --res_out_proof                         true
% 3.05/0.98  
% 3.05/0.98  ------ Superposition Options
% 3.05/0.98  
% 3.05/0.98  --superposition_flag                    true
% 3.05/0.98  --sup_passive_queue_type                priority_queues
% 3.05/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.05/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.05/0.98  --demod_completeness_check              fast
% 3.05/0.98  --demod_use_ground                      true
% 3.05/0.98  --sup_to_prop_solver                    passive
% 3.05/0.98  --sup_prop_simpl_new                    true
% 3.05/0.98  --sup_prop_simpl_given                  true
% 3.05/0.98  --sup_fun_splitting                     false
% 3.05/0.98  --sup_smt_interval                      50000
% 3.05/0.98  
% 3.05/0.98  ------ Superposition Simplification Setup
% 3.05/0.98  
% 3.05/0.98  --sup_indices_passive                   []
% 3.05/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.05/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.05/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.05/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.05/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.05/0.98  --sup_full_bw                           [BwDemod]
% 3.05/0.98  --sup_immed_triv                        [TrivRules]
% 3.05/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.05/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.05/0.98  --sup_immed_bw_main                     []
% 3.05/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.05/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.05/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.05/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.05/0.98  
% 3.05/0.98  ------ Combination Options
% 3.05/0.98  
% 3.05/0.98  --comb_res_mult                         3
% 3.05/0.98  --comb_sup_mult                         2
% 3.05/0.98  --comb_inst_mult                        10
% 3.05/0.98  
% 3.05/0.98  ------ Debug Options
% 3.05/0.98  
% 3.05/0.98  --dbg_backtrace                         false
% 3.05/0.98  --dbg_dump_prop_clauses                 false
% 3.05/0.98  --dbg_dump_prop_clauses_file            -
% 3.05/0.98  --dbg_out_stat                          false
% 3.05/0.98  
% 3.05/0.98  
% 3.05/0.98  
% 3.05/0.98  
% 3.05/0.98  ------ Proving...
% 3.05/0.98  
% 3.05/0.98  
% 3.05/0.98  % SZS status Theorem for theBenchmark.p
% 3.05/0.98  
% 3.05/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.05/0.98  
% 3.05/0.98  fof(f17,conjecture,(
% 3.05/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 3.05/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/0.98  
% 3.05/0.98  fof(f18,negated_conjecture,(
% 3.05/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 3.05/0.98    inference(negated_conjecture,[],[f17])).
% 3.05/0.98  
% 3.05/0.98  fof(f44,plain,(
% 3.05/0.98    ? [X0] : (? [X1] : (~v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.05/0.98    inference(ennf_transformation,[],[f18])).
% 3.05/0.98  
% 3.05/0.98  fof(f45,plain,(
% 3.05/0.98    ? [X0] : (? [X1] : (~v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.05/0.98    inference(flattening,[],[f44])).
% 3.05/0.98  
% 3.05/0.98  fof(f55,plain,(
% 3.05/0.98    ( ! [X0] : (? [X1] : (~v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) & m1_subset_1(X1,u1_struct_0(X0))) => (~v2_tex_2(k6_domain_1(u1_struct_0(X0),sK3),X0) & m1_subset_1(sK3,u1_struct_0(X0)))) )),
% 3.05/0.98    introduced(choice_axiom,[])).
% 3.05/0.98  
% 3.05/0.98  fof(f54,plain,(
% 3.05/0.98    ? [X0] : (? [X1] : (~v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (~v2_tex_2(k6_domain_1(u1_struct_0(sK2),X1),sK2) & m1_subset_1(X1,u1_struct_0(sK2))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 3.05/0.98    introduced(choice_axiom,[])).
% 3.05/0.98  
% 3.05/0.98  fof(f56,plain,(
% 3.05/0.98    (~v2_tex_2(k6_domain_1(u1_struct_0(sK2),sK3),sK2) & m1_subset_1(sK3,u1_struct_0(sK2))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 3.05/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f45,f55,f54])).
% 3.05/0.98  
% 3.05/0.98  fof(f84,plain,(
% 3.05/0.98    m1_subset_1(sK3,u1_struct_0(sK2))),
% 3.05/0.98    inference(cnf_transformation,[],[f56])).
% 3.05/0.98  
% 3.05/0.98  fof(f12,axiom,(
% 3.05/0.98    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 3.05/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/0.98  
% 3.05/0.98  fof(f34,plain,(
% 3.05/0.98    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 3.05/0.98    inference(ennf_transformation,[],[f12])).
% 3.05/0.98  
% 3.05/0.98  fof(f35,plain,(
% 3.05/0.98    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 3.05/0.98    inference(flattening,[],[f34])).
% 3.05/0.98  
% 3.05/0.98  fof(f71,plain,(
% 3.05/0.98    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.05/0.98    inference(cnf_transformation,[],[f35])).
% 3.05/0.98  
% 3.05/0.98  fof(f2,axiom,(
% 3.05/0.98    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.05/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/0.98  
% 3.05/0.98  fof(f61,plain,(
% 3.05/0.98    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.05/0.98    inference(cnf_transformation,[],[f2])).
% 3.05/0.98  
% 3.05/0.98  fof(f91,plain,(
% 3.05/0.98    ( ! [X0,X1] : (k2_tarski(X1,X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.05/0.98    inference(definition_unfolding,[],[f71,f61])).
% 3.05/0.98  
% 3.05/0.98  fof(f81,plain,(
% 3.05/0.98    ~v2_struct_0(sK2)),
% 3.05/0.98    inference(cnf_transformation,[],[f56])).
% 3.05/0.98  
% 3.05/0.98  fof(f83,plain,(
% 3.05/0.98    l1_pre_topc(sK2)),
% 3.05/0.98    inference(cnf_transformation,[],[f56])).
% 3.05/0.98  
% 3.05/0.98  fof(f10,axiom,(
% 3.05/0.98    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 3.05/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/0.98  
% 3.05/0.98  fof(f30,plain,(
% 3.05/0.98    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.05/0.98    inference(ennf_transformation,[],[f10])).
% 3.05/0.98  
% 3.05/0.98  fof(f31,plain,(
% 3.05/0.98    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.05/0.98    inference(flattening,[],[f30])).
% 3.05/0.98  
% 3.05/0.98  fof(f69,plain,(
% 3.05/0.98    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.05/0.98    inference(cnf_transformation,[],[f31])).
% 3.05/0.98  
% 3.05/0.98  fof(f7,axiom,(
% 3.05/0.98    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.05/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/0.98  
% 3.05/0.98  fof(f26,plain,(
% 3.05/0.98    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.05/0.98    inference(ennf_transformation,[],[f7])).
% 3.05/0.98  
% 3.05/0.98  fof(f66,plain,(
% 3.05/0.98    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.05/0.98    inference(cnf_transformation,[],[f26])).
% 3.05/0.98  
% 3.05/0.98  fof(f11,axiom,(
% 3.05/0.98    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 3.05/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/0.98  
% 3.05/0.98  fof(f32,plain,(
% 3.05/0.98    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 3.05/0.98    inference(ennf_transformation,[],[f11])).
% 3.05/0.98  
% 3.05/0.98  fof(f33,plain,(
% 3.05/0.98    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 3.05/0.98    inference(flattening,[],[f32])).
% 3.05/0.98  
% 3.05/0.98  fof(f70,plain,(
% 3.05/0.98    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.05/0.98    inference(cnf_transformation,[],[f33])).
% 3.05/0.98  
% 3.05/0.98  fof(f4,axiom,(
% 3.05/0.98    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.05/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/0.98  
% 3.05/0.98  fof(f21,plain,(
% 3.05/0.98    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.05/0.98    inference(ennf_transformation,[],[f4])).
% 3.05/0.98  
% 3.05/0.98  fof(f22,plain,(
% 3.05/0.98    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.05/0.98    inference(flattening,[],[f21])).
% 3.05/0.98  
% 3.05/0.98  fof(f63,plain,(
% 3.05/0.98    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.05/0.98    inference(cnf_transformation,[],[f22])).
% 3.05/0.98  
% 3.05/0.98  fof(f3,axiom,(
% 3.05/0.98    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 3.05/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/0.98  
% 3.05/0.98  fof(f20,plain,(
% 3.05/0.98    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 3.05/0.98    inference(ennf_transformation,[],[f3])).
% 3.05/0.98  
% 3.05/0.98  fof(f62,plain,(
% 3.05/0.98    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 3.05/0.98    inference(cnf_transformation,[],[f20])).
% 3.05/0.98  
% 3.05/0.98  fof(f90,plain,(
% 3.05/0.98    ( ! [X0,X1] : (m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 3.05/0.98    inference(definition_unfolding,[],[f62,f61])).
% 3.05/0.98  
% 3.05/0.98  fof(f14,axiom,(
% 3.05/0.98    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2))))),
% 3.05/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/0.98  
% 3.05/0.98  fof(f38,plain,(
% 3.05/0.98    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.05/0.98    inference(ennf_transformation,[],[f14])).
% 3.05/0.98  
% 3.05/0.98  fof(f39,plain,(
% 3.05/0.98    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.05/0.98    inference(flattening,[],[f38])).
% 3.05/0.98  
% 3.05/0.98  fof(f51,plain,(
% 3.05/0.98    ! [X1,X0] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => (u1_struct_0(sK1(X0,X1)) = X1 & m1_pre_topc(sK1(X0,X1),X0) & v1_pre_topc(sK1(X0,X1)) & ~v2_struct_0(sK1(X0,X1))))),
% 3.05/0.98    introduced(choice_axiom,[])).
% 3.05/0.98  
% 3.05/0.98  fof(f52,plain,(
% 3.05/0.98    ! [X0] : (! [X1] : ((u1_struct_0(sK1(X0,X1)) = X1 & m1_pre_topc(sK1(X0,X1),X0) & v1_pre_topc(sK1(X0,X1)) & ~v2_struct_0(sK1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.05/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f39,f51])).
% 3.05/0.98  
% 3.05/0.98  fof(f75,plain,(
% 3.05/0.98    ( ! [X0,X1] : (v1_pre_topc(sK1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.05/0.98    inference(cnf_transformation,[],[f52])).
% 3.05/0.98  
% 3.05/0.98  fof(f77,plain,(
% 3.05/0.98    ( ! [X0,X1] : (u1_struct_0(sK1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.05/0.98    inference(cnf_transformation,[],[f52])).
% 3.05/0.98  
% 3.05/0.98  fof(f1,axiom,(
% 3.05/0.98    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 3.05/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/0.98  
% 3.05/0.98  fof(f46,plain,(
% 3.05/0.98    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 3.05/0.98    inference(nnf_transformation,[],[f1])).
% 3.05/0.98  
% 3.05/0.98  fof(f47,plain,(
% 3.05/0.98    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.05/0.98    inference(rectify,[],[f46])).
% 3.05/0.98  
% 3.05/0.98  fof(f48,plain,(
% 3.05/0.98    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1))))),
% 3.05/0.98    introduced(choice_axiom,[])).
% 3.05/0.98  
% 3.05/0.98  fof(f49,plain,(
% 3.05/0.98    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.05/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f47,f48])).
% 3.05/0.98  
% 3.05/0.98  fof(f58,plain,(
% 3.05/0.98    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 3.05/0.98    inference(cnf_transformation,[],[f49])).
% 3.05/0.98  
% 3.05/0.98  fof(f88,plain,(
% 3.05/0.98    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_tarski(X0,X0) != X1) )),
% 3.05/0.98    inference(definition_unfolding,[],[f58,f61])).
% 3.05/0.98  
% 3.05/0.98  fof(f92,plain,(
% 3.05/0.98    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_tarski(X3,X3) != X1) )),
% 3.05/0.98    inference(equality_resolution,[],[f88])).
% 3.05/0.98  
% 3.05/0.98  fof(f93,plain,(
% 3.05/0.98    ( ! [X3] : (r2_hidden(X3,k2_tarski(X3,X3))) )),
% 3.05/0.98    inference(equality_resolution,[],[f92])).
% 3.05/0.98  
% 3.05/0.98  fof(f5,axiom,(
% 3.05/0.98    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 3.05/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/0.98  
% 3.05/0.98  fof(f23,plain,(
% 3.05/0.98    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.05/0.98    inference(ennf_transformation,[],[f5])).
% 3.05/0.98  
% 3.05/0.98  fof(f64,plain,(
% 3.05/0.98    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.05/0.98    inference(cnf_transformation,[],[f23])).
% 3.05/0.98  
% 3.05/0.98  fof(f13,axiom,(
% 3.05/0.98    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => (k1_tex_2(X0,X1) = X2 <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)))))),
% 3.05/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/0.98  
% 3.05/0.98  fof(f36,plain,(
% 3.05/0.98    ! [X0] : (! [X1] : (! [X2] : ((k1_tex_2(X0,X1) = X2 <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)) | (~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.05/0.98    inference(ennf_transformation,[],[f13])).
% 3.05/0.98  
% 3.05/0.98  fof(f37,plain,(
% 3.05/0.98    ! [X0] : (! [X1] : (! [X2] : ((k1_tex_2(X0,X1) = X2 <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.05/0.98    inference(flattening,[],[f36])).
% 3.05/0.98  
% 3.05/0.98  fof(f50,plain,(
% 3.05/0.98    ! [X0] : (! [X1] : (! [X2] : (((k1_tex_2(X0,X1) = X2 | u1_struct_0(X2) != k6_domain_1(u1_struct_0(X0),X1)) & (u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) | k1_tex_2(X0,X1) != X2)) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.05/0.98    inference(nnf_transformation,[],[f37])).
% 3.05/0.98  
% 3.05/0.98  fof(f73,plain,(
% 3.05/0.98    ( ! [X2,X0,X1] : (k1_tex_2(X0,X1) = X2 | u1_struct_0(X2) != k6_domain_1(u1_struct_0(X0),X1) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.05/0.98    inference(cnf_transformation,[],[f50])).
% 3.05/0.98  
% 3.05/0.98  fof(f74,plain,(
% 3.05/0.98    ( ! [X0,X1] : (~v2_struct_0(sK1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.05/0.98    inference(cnf_transformation,[],[f52])).
% 3.05/0.98  
% 3.05/0.98  fof(f76,plain,(
% 3.05/0.98    ( ! [X0,X1] : (m1_pre_topc(sK1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.05/0.98    inference(cnf_transformation,[],[f52])).
% 3.05/0.98  
% 3.05/0.98  fof(f16,axiom,(
% 3.05/0.98    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => (v2_tex_2(X2,X0) <=> v1_tdlat_3(X1))))))),
% 3.05/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/0.98  
% 3.05/0.98  fof(f42,plain,(
% 3.05/0.98    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.05/0.98    inference(ennf_transformation,[],[f16])).
% 3.05/0.98  
% 3.05/0.98  fof(f43,plain,(
% 3.05/0.98    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.05/0.98    inference(flattening,[],[f42])).
% 3.05/0.98  
% 3.05/0.98  fof(f53,plain,(
% 3.05/0.98    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) | ~v1_tdlat_3(X1)) & (v1_tdlat_3(X1) | ~v2_tex_2(X2,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.05/0.98    inference(nnf_transformation,[],[f43])).
% 3.05/0.98  
% 3.05/0.98  fof(f80,plain,(
% 3.05/0.98    ( ! [X2,X0,X1] : (v2_tex_2(X2,X0) | ~v1_tdlat_3(X1) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.05/0.98    inference(cnf_transformation,[],[f53])).
% 3.05/0.98  
% 3.05/0.98  fof(f96,plain,(
% 3.05/0.98    ( ! [X0,X1] : (v2_tex_2(u1_struct_0(X1),X0) | ~v1_tdlat_3(X1) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.05/0.98    inference(equality_resolution,[],[f80])).
% 3.05/0.98  
% 3.05/0.98  fof(f85,plain,(
% 3.05/0.98    ~v2_tex_2(k6_domain_1(u1_struct_0(sK2),sK3),sK2)),
% 3.05/0.98    inference(cnf_transformation,[],[f56])).
% 3.05/0.98  
% 3.05/0.98  fof(f15,axiom,(
% 3.05/0.98    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v2_pre_topc(k1_tex_2(X0,X1)) => (v2_tdlat_3(k1_tex_2(X0,X1)) & v1_tdlat_3(k1_tex_2(X0,X1))))))),
% 3.05/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/0.98  
% 3.05/0.98  fof(f19,plain,(
% 3.05/0.98    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v2_pre_topc(k1_tex_2(X0,X1)) => v1_tdlat_3(k1_tex_2(X0,X1)))))),
% 3.05/0.98    inference(pure_predicate_removal,[],[f15])).
% 3.05/0.98  
% 3.05/0.98  fof(f40,plain,(
% 3.05/0.98    ! [X0] : (! [X1] : ((v1_tdlat_3(k1_tex_2(X0,X1)) | ~v2_pre_topc(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.05/0.98    inference(ennf_transformation,[],[f19])).
% 3.05/0.98  
% 3.05/0.98  fof(f41,plain,(
% 3.05/0.98    ! [X0] : (! [X1] : (v1_tdlat_3(k1_tex_2(X0,X1)) | ~v2_pre_topc(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.05/0.98    inference(flattening,[],[f40])).
% 3.05/0.98  
% 3.05/0.98  fof(f78,plain,(
% 3.05/0.98    ( ! [X0,X1] : (v1_tdlat_3(k1_tex_2(X0,X1)) | ~v2_pre_topc(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.05/0.98    inference(cnf_transformation,[],[f41])).
% 3.05/0.98  
% 3.05/0.98  fof(f6,axiom,(
% 3.05/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 3.05/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/0.98  
% 3.05/0.98  fof(f24,plain,(
% 3.05/0.98    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.05/0.98    inference(ennf_transformation,[],[f6])).
% 3.05/0.98  
% 3.05/0.98  fof(f25,plain,(
% 3.05/0.98    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.05/0.98    inference(flattening,[],[f24])).
% 3.05/0.98  
% 3.05/0.98  fof(f65,plain,(
% 3.05/0.98    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.05/0.98    inference(cnf_transformation,[],[f25])).
% 3.05/0.98  
% 3.05/0.98  fof(f82,plain,(
% 3.05/0.98    v2_pre_topc(sK2)),
% 3.05/0.98    inference(cnf_transformation,[],[f56])).
% 3.05/0.98  
% 3.05/0.98  cnf(c_24,negated_conjecture,
% 3.05/0.98      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 3.05/0.98      inference(cnf_transformation,[],[f84]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_2731,plain,
% 3.05/0.98      ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
% 3.05/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_13,plain,
% 3.05/0.98      ( ~ m1_subset_1(X0,X1)
% 3.05/0.98      | v1_xboole_0(X1)
% 3.05/0.98      | k6_domain_1(X1,X0) = k2_tarski(X0,X0) ),
% 3.05/0.98      inference(cnf_transformation,[],[f91]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_2739,plain,
% 3.05/0.98      ( k6_domain_1(X0,X1) = k2_tarski(X1,X1)
% 3.05/0.98      | m1_subset_1(X1,X0) != iProver_top
% 3.05/0.98      | v1_xboole_0(X0) = iProver_top ),
% 3.05/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_3250,plain,
% 3.05/0.98      ( k6_domain_1(u1_struct_0(sK2),sK3) = k2_tarski(sK3,sK3)
% 3.05/0.98      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 3.05/0.98      inference(superposition,[status(thm)],[c_2731,c_2739]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_27,negated_conjecture,
% 3.05/0.98      ( ~ v2_struct_0(sK2) ),
% 3.05/0.98      inference(cnf_transformation,[],[f81]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_25,negated_conjecture,
% 3.05/0.98      ( l1_pre_topc(sK2) ),
% 3.05/0.98      inference(cnf_transformation,[],[f83]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_11,plain,
% 3.05/0.98      ( v2_struct_0(X0)
% 3.05/0.98      | ~ l1_struct_0(X0)
% 3.05/0.98      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 3.05/0.98      inference(cnf_transformation,[],[f69]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_67,plain,
% 3.05/0.98      ( v2_struct_0(sK2)
% 3.05/0.98      | ~ l1_struct_0(sK2)
% 3.05/0.98      | ~ v1_xboole_0(u1_struct_0(sK2)) ),
% 3.05/0.98      inference(instantiation,[status(thm)],[c_11]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_8,plain,
% 3.05/0.98      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 3.05/0.98      inference(cnf_transformation,[],[f66]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_72,plain,
% 3.05/0.98      ( l1_struct_0(sK2) | ~ l1_pre_topc(sK2) ),
% 3.05/0.98      inference(instantiation,[status(thm)],[c_8]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_2989,plain,
% 3.05/0.98      ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 3.05/0.98      | v1_xboole_0(u1_struct_0(sK2))
% 3.05/0.98      | k6_domain_1(u1_struct_0(sK2),sK3) = k2_tarski(sK3,sK3) ),
% 3.05/0.98      inference(instantiation,[status(thm)],[c_13]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_3351,plain,
% 3.05/0.98      ( k6_domain_1(u1_struct_0(sK2),sK3) = k2_tarski(sK3,sK3) ),
% 3.05/0.98      inference(global_propositional_subsumption,
% 3.05/0.98                [status(thm)],
% 3.05/0.98                [c_3250,c_27,c_25,c_24,c_67,c_72,c_2989]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_12,plain,
% 3.05/0.98      ( ~ m1_subset_1(X0,X1)
% 3.05/0.98      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
% 3.05/0.98      | v1_xboole_0(X1) ),
% 3.05/0.98      inference(cnf_transformation,[],[f70]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_2740,plain,
% 3.05/0.98      ( m1_subset_1(X0,X1) != iProver_top
% 3.05/0.98      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top
% 3.05/0.98      | v1_xboole_0(X1) = iProver_top ),
% 3.05/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_3857,plain,
% 3.05/0.98      ( m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 3.05/0.98      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 3.05/0.98      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 3.05/0.98      inference(superposition,[status(thm)],[c_3351,c_2740]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_28,plain,
% 3.05/0.98      ( v2_struct_0(sK2) != iProver_top ),
% 3.05/0.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_30,plain,
% 3.05/0.98      ( l1_pre_topc(sK2) = iProver_top ),
% 3.05/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_31,plain,
% 3.05/0.98      ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
% 3.05/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_66,plain,
% 3.05/0.98      ( v2_struct_0(X0) = iProver_top
% 3.05/0.98      | l1_struct_0(X0) != iProver_top
% 3.05/0.98      | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
% 3.05/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_68,plain,
% 3.05/0.98      ( v2_struct_0(sK2) = iProver_top
% 3.05/0.98      | l1_struct_0(sK2) != iProver_top
% 3.05/0.98      | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 3.05/0.98      inference(instantiation,[status(thm)],[c_66]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_71,plain,
% 3.05/0.98      ( l1_struct_0(X0) = iProver_top | l1_pre_topc(X0) != iProver_top ),
% 3.05/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_73,plain,
% 3.05/0.98      ( l1_struct_0(sK2) = iProver_top
% 3.05/0.98      | l1_pre_topc(sK2) != iProver_top ),
% 3.05/0.98      inference(instantiation,[status(thm)],[c_71]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_5,plain,
% 3.05/0.98      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.05/0.98      inference(cnf_transformation,[],[f63]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_2983,plain,
% 3.05/0.98      ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 3.05/0.98      | r2_hidden(sK3,u1_struct_0(sK2))
% 3.05/0.98      | v1_xboole_0(u1_struct_0(sK2)) ),
% 3.05/0.98      inference(instantiation,[status(thm)],[c_5]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_2984,plain,
% 3.05/0.98      ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 3.05/0.98      | r2_hidden(sK3,u1_struct_0(sK2)) = iProver_top
% 3.05/0.98      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 3.05/0.98      inference(predicate_to_equality,[status(thm)],[c_2983]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_4,plain,
% 3.05/0.98      ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1))
% 3.05/0.98      | ~ r2_hidden(X0,X1) ),
% 3.05/0.98      inference(cnf_transformation,[],[f90]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_3032,plain,
% 3.05/0.98      ( m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.05/0.98      | ~ r2_hidden(sK3,u1_struct_0(sK2)) ),
% 3.05/0.98      inference(instantiation,[status(thm)],[c_4]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_3033,plain,
% 3.05/0.98      ( m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 3.05/0.98      | r2_hidden(sK3,u1_struct_0(sK2)) != iProver_top ),
% 3.05/0.98      inference(predicate_to_equality,[status(thm)],[c_3032]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_4231,plain,
% 3.05/0.98      ( m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.05/0.98      inference(global_propositional_subsumption,
% 3.05/0.98                [status(thm)],
% 3.05/0.98                [c_3857,c_28,c_30,c_31,c_68,c_73,c_2984,c_3033]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_18,plain,
% 3.05/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.05/0.98      | v1_pre_topc(sK1(X1,X0))
% 3.05/0.98      | v2_struct_0(X1)
% 3.05/0.98      | ~ l1_pre_topc(X1)
% 3.05/0.98      | v1_xboole_0(X0) ),
% 3.05/0.98      inference(cnf_transformation,[],[f75]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_2734,plain,
% 3.05/0.98      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.05/0.98      | v1_pre_topc(sK1(X1,X0)) = iProver_top
% 3.05/0.98      | v2_struct_0(X1) = iProver_top
% 3.05/0.98      | l1_pre_topc(X1) != iProver_top
% 3.05/0.98      | v1_xboole_0(X0) = iProver_top ),
% 3.05/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_4239,plain,
% 3.05/0.98      ( v1_pre_topc(sK1(sK2,k2_tarski(sK3,sK3))) = iProver_top
% 3.05/0.98      | v2_struct_0(sK2) = iProver_top
% 3.05/0.98      | l1_pre_topc(sK2) != iProver_top
% 3.05/0.98      | v1_xboole_0(k2_tarski(sK3,sK3)) = iProver_top ),
% 3.05/0.98      inference(superposition,[status(thm)],[c_4231,c_2734]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_4405,plain,
% 3.05/0.98      ( v1_pre_topc(sK1(sK2,k2_tarski(sK3,sK3))) = iProver_top
% 3.05/0.98      | v1_xboole_0(k2_tarski(sK3,sK3)) = iProver_top ),
% 3.05/0.98      inference(global_propositional_subsumption,
% 3.05/0.98                [status(thm)],
% 3.05/0.98                [c_4239,c_28,c_30]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_16,plain,
% 3.05/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.05/0.98      | v2_struct_0(X1)
% 3.05/0.98      | ~ l1_pre_topc(X1)
% 3.05/0.98      | v1_xboole_0(X0)
% 3.05/0.98      | u1_struct_0(sK1(X1,X0)) = X0 ),
% 3.05/0.98      inference(cnf_transformation,[],[f77]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_2736,plain,
% 3.05/0.98      ( u1_struct_0(sK1(X0,X1)) = X1
% 3.05/0.98      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.05/0.98      | v2_struct_0(X0) = iProver_top
% 3.05/0.98      | l1_pre_topc(X0) != iProver_top
% 3.05/0.98      | v1_xboole_0(X1) = iProver_top ),
% 3.05/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_4782,plain,
% 3.05/0.98      ( u1_struct_0(sK1(sK2,k2_tarski(sK3,sK3))) = k2_tarski(sK3,sK3)
% 3.05/0.98      | v2_struct_0(sK2) = iProver_top
% 3.05/0.98      | l1_pre_topc(sK2) != iProver_top
% 3.05/0.98      | v1_xboole_0(k2_tarski(sK3,sK3)) = iProver_top ),
% 3.05/0.98      inference(superposition,[status(thm)],[c_4231,c_2736]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_5374,plain,
% 3.05/0.98      ( u1_struct_0(sK1(sK2,k2_tarski(sK3,sK3))) = k2_tarski(sK3,sK3)
% 3.05/0.98      | v1_xboole_0(k2_tarski(sK3,sK3)) = iProver_top ),
% 3.05/0.98      inference(global_propositional_subsumption,
% 3.05/0.98                [status(thm)],
% 3.05/0.98                [c_4782,c_28,c_30]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_2,plain,
% 3.05/0.98      ( r2_hidden(X0,k2_tarski(X0,X0)) ),
% 3.05/0.98      inference(cnf_transformation,[],[f93]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_2747,plain,
% 3.05/0.98      ( r2_hidden(X0,k2_tarski(X0,X0)) = iProver_top ),
% 3.05/0.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_2745,plain,
% 3.05/0.98      ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1)) = iProver_top
% 3.05/0.98      | r2_hidden(X0,X1) != iProver_top ),
% 3.05/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_6,plain,
% 3.05/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.05/0.98      | ~ r2_hidden(X2,X0)
% 3.05/0.98      | ~ v1_xboole_0(X1) ),
% 3.05/0.98      inference(cnf_transformation,[],[f64]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_2743,plain,
% 3.05/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.05/0.98      | r2_hidden(X2,X0) != iProver_top
% 3.05/0.98      | v1_xboole_0(X1) != iProver_top ),
% 3.05/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_3532,plain,
% 3.05/0.98      ( r2_hidden(X0,X1) != iProver_top
% 3.05/0.98      | r2_hidden(X2,k2_tarski(X0,X0)) != iProver_top
% 3.05/0.98      | v1_xboole_0(X1) != iProver_top ),
% 3.05/0.98      inference(superposition,[status(thm)],[c_2745,c_2743]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_81,plain,
% 3.05/0.98      ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1)) = iProver_top
% 3.05/0.98      | r2_hidden(X0,X1) != iProver_top ),
% 3.05/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_614,plain,
% 3.05/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.05/0.98      | ~ v1_xboole_0(X1)
% 3.05/0.98      | X2 != X3
% 3.05/0.98      | k2_tarski(X3,X3) != X0 ),
% 3.05/0.98      inference(resolution_lifted,[status(thm)],[c_2,c_6]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_615,plain,
% 3.05/0.98      ( ~ m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1))
% 3.05/0.98      | ~ v1_xboole_0(X1) ),
% 3.05/0.98      inference(unflattening,[status(thm)],[c_614]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_616,plain,
% 3.05/0.98      ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1)) != iProver_top
% 3.05/0.98      | v1_xboole_0(X1) != iProver_top ),
% 3.05/0.98      inference(predicate_to_equality,[status(thm)],[c_615]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_3659,plain,
% 3.05/0.98      ( r2_hidden(X0,X1) != iProver_top
% 3.05/0.98      | v1_xboole_0(X1) != iProver_top ),
% 3.05/0.98      inference(global_propositional_subsumption,
% 3.05/0.98                [status(thm)],
% 3.05/0.98                [c_3532,c_81,c_616]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_3667,plain,
% 3.05/0.98      ( v1_xboole_0(k2_tarski(X0,X0)) != iProver_top ),
% 3.05/0.98      inference(superposition,[status(thm)],[c_2747,c_3659]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_5380,plain,
% 3.05/0.98      ( u1_struct_0(sK1(sK2,k2_tarski(sK3,sK3))) = k2_tarski(sK3,sK3) ),
% 3.05/0.98      inference(forward_subsumption_resolution,
% 3.05/0.98                [status(thm)],
% 3.05/0.98                [c_5374,c_3667]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_14,plain,
% 3.05/0.98      ( ~ m1_pre_topc(X0,X1)
% 3.05/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.05/0.98      | ~ v1_pre_topc(X0)
% 3.05/0.98      | v2_struct_0(X1)
% 3.05/0.98      | v2_struct_0(X0)
% 3.05/0.98      | ~ l1_pre_topc(X1)
% 3.05/0.98      | k1_tex_2(X1,X2) = X0
% 3.05/0.98      | k6_domain_1(u1_struct_0(X1),X2) != u1_struct_0(X0) ),
% 3.05/0.98      inference(cnf_transformation,[],[f73]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_2738,plain,
% 3.05/0.98      ( k1_tex_2(X0,X1) = X2
% 3.05/0.98      | k6_domain_1(u1_struct_0(X0),X1) != u1_struct_0(X2)
% 3.05/0.98      | m1_pre_topc(X2,X0) != iProver_top
% 3.05/0.98      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 3.05/0.98      | v1_pre_topc(X2) != iProver_top
% 3.05/0.98      | v2_struct_0(X0) = iProver_top
% 3.05/0.98      | v2_struct_0(X2) = iProver_top
% 3.05/0.98      | l1_pre_topc(X0) != iProver_top ),
% 3.05/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_5127,plain,
% 3.05/0.98      ( k1_tex_2(sK2,sK3) = X0
% 3.05/0.98      | k2_tarski(sK3,sK3) != u1_struct_0(X0)
% 3.05/0.98      | m1_pre_topc(X0,sK2) != iProver_top
% 3.05/0.98      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 3.05/0.98      | v1_pre_topc(X0) != iProver_top
% 3.05/0.98      | v2_struct_0(X0) = iProver_top
% 3.05/0.98      | v2_struct_0(sK2) = iProver_top
% 3.05/0.98      | l1_pre_topc(sK2) != iProver_top ),
% 3.05/0.98      inference(superposition,[status(thm)],[c_3351,c_2738]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_5222,plain,
% 3.05/0.98      ( m1_pre_topc(X0,sK2) != iProver_top
% 3.05/0.98      | k2_tarski(sK3,sK3) != u1_struct_0(X0)
% 3.05/0.98      | k1_tex_2(sK2,sK3) = X0
% 3.05/0.98      | v1_pre_topc(X0) != iProver_top
% 3.05/0.98      | v2_struct_0(X0) = iProver_top ),
% 3.05/0.98      inference(global_propositional_subsumption,
% 3.05/0.98                [status(thm)],
% 3.05/0.98                [c_5127,c_28,c_30,c_31]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_5223,plain,
% 3.05/0.98      ( k1_tex_2(sK2,sK3) = X0
% 3.05/0.98      | k2_tarski(sK3,sK3) != u1_struct_0(X0)
% 3.05/0.98      | m1_pre_topc(X0,sK2) != iProver_top
% 3.05/0.98      | v1_pre_topc(X0) != iProver_top
% 3.05/0.98      | v2_struct_0(X0) = iProver_top ),
% 3.05/0.98      inference(renaming,[status(thm)],[c_5222]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_5381,plain,
% 3.05/0.98      ( sK1(sK2,k2_tarski(sK3,sK3)) = k1_tex_2(sK2,sK3)
% 3.05/0.98      | m1_pre_topc(sK1(sK2,k2_tarski(sK3,sK3)),sK2) != iProver_top
% 3.05/0.98      | v1_pre_topc(sK1(sK2,k2_tarski(sK3,sK3))) != iProver_top
% 3.05/0.98      | v2_struct_0(sK1(sK2,k2_tarski(sK3,sK3))) = iProver_top ),
% 3.05/0.98      inference(superposition,[status(thm)],[c_5380,c_5223]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_19,plain,
% 3.05/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.05/0.98      | v2_struct_0(X1)
% 3.05/0.98      | ~ v2_struct_0(sK1(X1,X0))
% 3.05/0.98      | ~ l1_pre_topc(X1)
% 3.05/0.98      | v1_xboole_0(X0) ),
% 3.05/0.98      inference(cnf_transformation,[],[f74]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_2733,plain,
% 3.05/0.98      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.05/0.98      | v2_struct_0(X1) = iProver_top
% 3.05/0.98      | v2_struct_0(sK1(X1,X0)) != iProver_top
% 3.05/0.98      | l1_pre_topc(X1) != iProver_top
% 3.05/0.98      | v1_xboole_0(X0) = iProver_top ),
% 3.05/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_4497,plain,
% 3.05/0.98      ( v2_struct_0(sK1(sK2,k2_tarski(sK3,sK3))) != iProver_top
% 3.05/0.98      | v2_struct_0(sK2) = iProver_top
% 3.05/0.98      | l1_pre_topc(sK2) != iProver_top
% 3.05/0.98      | v1_xboole_0(k2_tarski(sK3,sK3)) = iProver_top ),
% 3.05/0.98      inference(superposition,[status(thm)],[c_4231,c_2733]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_5234,plain,
% 3.05/0.98      ( v2_struct_0(sK1(sK2,k2_tarski(sK3,sK3))) != iProver_top
% 3.05/0.98      | v1_xboole_0(k2_tarski(sK3,sK3)) = iProver_top ),
% 3.05/0.98      inference(global_propositional_subsumption,
% 3.05/0.98                [status(thm)],
% 3.05/0.98                [c_4497,c_28,c_30]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_5240,plain,
% 3.05/0.98      ( v2_struct_0(sK1(sK2,k2_tarski(sK3,sK3))) != iProver_top ),
% 3.05/0.98      inference(forward_subsumption_resolution,
% 3.05/0.98                [status(thm)],
% 3.05/0.98                [c_5234,c_3667]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_17,plain,
% 3.05/0.98      ( m1_pre_topc(sK1(X0,X1),X0)
% 3.05/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.05/0.98      | v2_struct_0(X0)
% 3.05/0.98      | ~ l1_pre_topc(X0)
% 3.05/0.98      | v1_xboole_0(X1) ),
% 3.05/0.98      inference(cnf_transformation,[],[f76]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_2735,plain,
% 3.05/0.98      ( m1_pre_topc(sK1(X0,X1),X0) = iProver_top
% 3.05/0.98      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.05/0.98      | v2_struct_0(X0) = iProver_top
% 3.05/0.98      | l1_pre_topc(X0) != iProver_top
% 3.05/0.98      | v1_xboole_0(X1) = iProver_top ),
% 3.05/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_4828,plain,
% 3.05/0.98      ( m1_pre_topc(sK1(sK2,k2_tarski(sK3,sK3)),sK2) = iProver_top
% 3.05/0.98      | v2_struct_0(sK2) = iProver_top
% 3.05/0.98      | l1_pre_topc(sK2) != iProver_top
% 3.05/0.98      | v1_xboole_0(k2_tarski(sK3,sK3)) = iProver_top ),
% 3.05/0.98      inference(superposition,[status(thm)],[c_4231,c_2735]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_5351,plain,
% 3.05/0.98      ( m1_pre_topc(sK1(sK2,k2_tarski(sK3,sK3)),sK2) = iProver_top
% 3.05/0.98      | v1_xboole_0(k2_tarski(sK3,sK3)) = iProver_top ),
% 3.05/0.98      inference(global_propositional_subsumption,
% 3.05/0.98                [status(thm)],
% 3.05/0.98                [c_4828,c_28,c_30]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_5357,plain,
% 3.05/0.98      ( m1_pre_topc(sK1(sK2,k2_tarski(sK3,sK3)),sK2) = iProver_top ),
% 3.05/0.98      inference(forward_subsumption_resolution,
% 3.05/0.98                [status(thm)],
% 3.05/0.98                [c_5351,c_3667]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_5612,plain,
% 3.05/0.98      ( v1_pre_topc(sK1(sK2,k2_tarski(sK3,sK3))) != iProver_top
% 3.05/0.98      | sK1(sK2,k2_tarski(sK3,sK3)) = k1_tex_2(sK2,sK3) ),
% 3.05/0.98      inference(global_propositional_subsumption,
% 3.05/0.98                [status(thm)],
% 3.05/0.98                [c_5381,c_5240,c_5357]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_5613,plain,
% 3.05/0.98      ( sK1(sK2,k2_tarski(sK3,sK3)) = k1_tex_2(sK2,sK3)
% 3.05/0.98      | v1_pre_topc(sK1(sK2,k2_tarski(sK3,sK3))) != iProver_top ),
% 3.05/0.98      inference(renaming,[status(thm)],[c_5612]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_5618,plain,
% 3.05/0.98      ( sK1(sK2,k2_tarski(sK3,sK3)) = k1_tex_2(sK2,sK3)
% 3.05/0.98      | v1_xboole_0(k2_tarski(sK3,sK3)) = iProver_top ),
% 3.05/0.98      inference(superposition,[status(thm)],[c_4405,c_5613]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_5732,plain,
% 3.05/0.98      ( sK1(sK2,k2_tarski(sK3,sK3)) = k1_tex_2(sK2,sK3) ),
% 3.05/0.98      inference(forward_subsumption_resolution,
% 3.05/0.98                [status(thm)],
% 3.05/0.98                [c_5618,c_3667]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_5735,plain,
% 3.05/0.98      ( m1_pre_topc(k1_tex_2(sK2,sK3),sK2) = iProver_top ),
% 3.05/0.98      inference(demodulation,[status(thm)],[c_5732,c_5357]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_21,plain,
% 3.05/0.98      ( v2_tex_2(u1_struct_0(X0),X1)
% 3.05/0.98      | ~ m1_pre_topc(X0,X1)
% 3.05/0.98      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.05/0.98      | ~ v1_tdlat_3(X0)
% 3.05/0.98      | v2_struct_0(X1)
% 3.05/0.98      | v2_struct_0(X0)
% 3.05/0.98      | ~ l1_pre_topc(X1) ),
% 3.05/0.98      inference(cnf_transformation,[],[f96]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_23,negated_conjecture,
% 3.05/0.98      ( ~ v2_tex_2(k6_domain_1(u1_struct_0(sK2),sK3),sK2) ),
% 3.05/0.98      inference(cnf_transformation,[],[f85]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_346,plain,
% 3.05/0.98      ( ~ m1_pre_topc(X0,X1)
% 3.05/0.98      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.05/0.98      | ~ v1_tdlat_3(X0)
% 3.05/0.98      | v2_struct_0(X0)
% 3.05/0.98      | v2_struct_0(X1)
% 3.05/0.98      | ~ l1_pre_topc(X1)
% 3.05/0.98      | k6_domain_1(u1_struct_0(sK2),sK3) != u1_struct_0(X0)
% 3.05/0.98      | sK2 != X1 ),
% 3.05/0.98      inference(resolution_lifted,[status(thm)],[c_21,c_23]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_347,plain,
% 3.05/0.98      ( ~ m1_pre_topc(X0,sK2)
% 3.05/0.98      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.05/0.98      | ~ v1_tdlat_3(X0)
% 3.05/0.98      | v2_struct_0(X0)
% 3.05/0.98      | v2_struct_0(sK2)
% 3.05/0.98      | ~ l1_pre_topc(sK2)
% 3.05/0.98      | k6_domain_1(u1_struct_0(sK2),sK3) != u1_struct_0(X0) ),
% 3.05/0.98      inference(unflattening,[status(thm)],[c_346]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_351,plain,
% 3.05/0.98      ( ~ m1_pre_topc(X0,sK2)
% 3.05/0.98      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.05/0.98      | ~ v1_tdlat_3(X0)
% 3.05/0.98      | v2_struct_0(X0)
% 3.05/0.98      | k6_domain_1(u1_struct_0(sK2),sK3) != u1_struct_0(X0) ),
% 3.05/0.98      inference(global_propositional_subsumption,
% 3.05/0.98                [status(thm)],
% 3.05/0.98                [c_347,c_27,c_25]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_2725,plain,
% 3.05/0.98      ( k6_domain_1(u1_struct_0(sK2),sK3) != u1_struct_0(X0)
% 3.05/0.98      | m1_pre_topc(X0,sK2) != iProver_top
% 3.05/0.98      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.05/0.98      | v1_tdlat_3(X0) != iProver_top
% 3.05/0.98      | v2_struct_0(X0) = iProver_top ),
% 3.05/0.98      inference(predicate_to_equality,[status(thm)],[c_351]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_3354,plain,
% 3.05/0.98      ( k2_tarski(sK3,sK3) != u1_struct_0(X0)
% 3.05/0.98      | m1_pre_topc(X0,sK2) != iProver_top
% 3.05/0.98      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.05/0.98      | v1_tdlat_3(X0) != iProver_top
% 3.05/0.98      | v2_struct_0(X0) = iProver_top ),
% 3.05/0.98      inference(demodulation,[status(thm)],[c_3351,c_2725]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_5386,plain,
% 3.05/0.98      ( m1_pre_topc(sK1(sK2,k2_tarski(sK3,sK3)),sK2) != iProver_top
% 3.05/0.98      | m1_subset_1(u1_struct_0(sK1(sK2,k2_tarski(sK3,sK3))),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.05/0.98      | v1_tdlat_3(sK1(sK2,k2_tarski(sK3,sK3))) != iProver_top
% 3.05/0.98      | v2_struct_0(sK1(sK2,k2_tarski(sK3,sK3))) = iProver_top ),
% 3.05/0.98      inference(superposition,[status(thm)],[c_5380,c_3354]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_5442,plain,
% 3.05/0.98      ( m1_pre_topc(sK1(sK2,k2_tarski(sK3,sK3)),sK2) != iProver_top
% 3.05/0.98      | m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.05/0.98      | v1_tdlat_3(sK1(sK2,k2_tarski(sK3,sK3))) != iProver_top
% 3.05/0.98      | v2_struct_0(sK1(sK2,k2_tarski(sK3,sK3))) = iProver_top ),
% 3.05/0.98      inference(light_normalisation,[status(thm)],[c_5386,c_5380]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_5621,plain,
% 3.05/0.98      ( v1_tdlat_3(sK1(sK2,k2_tarski(sK3,sK3))) != iProver_top ),
% 3.05/0.98      inference(global_propositional_subsumption,
% 3.05/0.98                [status(thm)],
% 3.05/0.98                [c_5442,c_28,c_30,c_31,c_68,c_73,c_2984,c_3033,c_5240,
% 3.05/0.98                 c_5357]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_5733,plain,
% 3.05/0.98      ( v1_tdlat_3(k1_tex_2(sK2,sK3)) != iProver_top ),
% 3.05/0.98      inference(demodulation,[status(thm)],[c_5732,c_5621]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_20,plain,
% 3.05/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.05/0.98      | v1_tdlat_3(k1_tex_2(X1,X0))
% 3.05/0.98      | v2_struct_0(X1)
% 3.05/0.98      | ~ l1_pre_topc(X1)
% 3.05/0.98      | ~ v2_pre_topc(k1_tex_2(X1,X0)) ),
% 3.05/0.98      inference(cnf_transformation,[],[f78]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_2732,plain,
% 3.05/0.98      ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
% 3.05/0.98      | v1_tdlat_3(k1_tex_2(X1,X0)) = iProver_top
% 3.05/0.98      | v2_struct_0(X1) = iProver_top
% 3.05/0.98      | l1_pre_topc(X1) != iProver_top
% 3.05/0.98      | v2_pre_topc(k1_tex_2(X1,X0)) != iProver_top ),
% 3.05/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_3683,plain,
% 3.05/0.98      ( v1_tdlat_3(k1_tex_2(sK2,sK3)) = iProver_top
% 3.05/0.98      | v2_struct_0(sK2) = iProver_top
% 3.05/0.98      | l1_pre_topc(sK2) != iProver_top
% 3.05/0.98      | v2_pre_topc(k1_tex_2(sK2,sK3)) != iProver_top ),
% 3.05/0.98      inference(superposition,[status(thm)],[c_2731,c_2732]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_4044,plain,
% 3.05/0.98      ( v1_tdlat_3(k1_tex_2(sK2,sK3)) = iProver_top
% 3.05/0.98      | v2_pre_topc(k1_tex_2(sK2,sK3)) != iProver_top ),
% 3.05/0.98      inference(global_propositional_subsumption,
% 3.05/0.98                [status(thm)],
% 3.05/0.98                [c_3683,c_28,c_30]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_7,plain,
% 3.05/0.98      ( ~ m1_pre_topc(X0,X1)
% 3.05/0.98      | ~ l1_pre_topc(X1)
% 3.05/0.98      | ~ v2_pre_topc(X1)
% 3.05/0.98      | v2_pre_topc(X0) ),
% 3.05/0.98      inference(cnf_transformation,[],[f65]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_3215,plain,
% 3.05/0.98      ( ~ m1_pre_topc(k1_tex_2(sK2,sK3),X0)
% 3.05/0.98      | ~ l1_pre_topc(X0)
% 3.05/0.98      | ~ v2_pre_topc(X0)
% 3.05/0.98      | v2_pre_topc(k1_tex_2(sK2,sK3)) ),
% 3.05/0.98      inference(instantiation,[status(thm)],[c_7]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_3216,plain,
% 3.05/0.98      ( m1_pre_topc(k1_tex_2(sK2,sK3),X0) != iProver_top
% 3.05/0.98      | l1_pre_topc(X0) != iProver_top
% 3.05/0.98      | v2_pre_topc(X0) != iProver_top
% 3.05/0.98      | v2_pre_topc(k1_tex_2(sK2,sK3)) = iProver_top ),
% 3.05/0.98      inference(predicate_to_equality,[status(thm)],[c_3215]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_3218,plain,
% 3.05/0.98      ( m1_pre_topc(k1_tex_2(sK2,sK3),sK2) != iProver_top
% 3.05/0.98      | l1_pre_topc(sK2) != iProver_top
% 3.05/0.98      | v2_pre_topc(k1_tex_2(sK2,sK3)) = iProver_top
% 3.05/0.98      | v2_pre_topc(sK2) != iProver_top ),
% 3.05/0.98      inference(instantiation,[status(thm)],[c_3216]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_26,negated_conjecture,
% 3.05/0.98      ( v2_pre_topc(sK2) ),
% 3.05/0.98      inference(cnf_transformation,[],[f82]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(c_29,plain,
% 3.05/0.98      ( v2_pre_topc(sK2) = iProver_top ),
% 3.05/0.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.05/0.98  
% 3.05/0.98  cnf(contradiction,plain,
% 3.05/0.98      ( $false ),
% 3.05/0.98      inference(minisat,
% 3.05/0.98                [status(thm)],
% 3.05/0.98                [c_5735,c_5733,c_4044,c_3218,c_30,c_29]) ).
% 3.05/0.98  
% 3.05/0.98  
% 3.05/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.05/0.98  
% 3.05/0.98  ------                               Statistics
% 3.05/0.98  
% 3.05/0.98  ------ General
% 3.05/0.98  
% 3.05/0.98  abstr_ref_over_cycles:                  0
% 3.05/0.98  abstr_ref_under_cycles:                 0
% 3.05/0.98  gc_basic_clause_elim:                   0
% 3.05/0.98  forced_gc_time:                         0
% 3.05/0.98  parsing_time:                           0.011
% 3.05/0.98  unif_index_cands_time:                  0.
% 3.05/0.98  unif_index_add_time:                    0.
% 3.05/0.98  orderings_time:                         0.
% 3.05/0.98  out_proof_time:                         0.011
% 3.05/0.98  total_time:                             0.173
% 3.05/0.98  num_of_symbols:                         51
% 3.05/0.98  num_of_terms:                           4192
% 3.05/0.98  
% 3.05/0.98  ------ Preprocessing
% 3.05/0.98  
% 3.05/0.98  num_of_splits:                          0
% 3.05/0.98  num_of_split_atoms:                     0
% 3.05/0.98  num_of_reused_defs:                     0
% 3.05/0.98  num_eq_ax_congr_red:                    26
% 3.05/0.98  num_of_sem_filtered_clauses:            1
% 3.05/0.98  num_of_subtypes:                        0
% 3.05/0.98  monotx_restored_types:                  0
% 3.05/0.98  sat_num_of_epr_types:                   0
% 3.05/0.98  sat_num_of_non_cyclic_types:            0
% 3.05/0.98  sat_guarded_non_collapsed_types:        0
% 3.05/0.98  num_pure_diseq_elim:                    0
% 3.05/0.98  simp_replaced_by:                       0
% 3.05/0.98  res_preprocessed:                       132
% 3.05/0.98  prep_upred:                             0
% 3.05/0.98  prep_unflattend:                        81
% 3.05/0.98  smt_new_axioms:                         0
% 3.05/0.98  pred_elim_cands:                        9
% 3.05/0.98  pred_elim:                              2
% 3.05/0.98  pred_elim_cl:                           3
% 3.05/0.98  pred_elim_cycles:                       12
% 3.05/0.98  merged_defs:                            0
% 3.05/0.98  merged_defs_ncl:                        0
% 3.05/0.98  bin_hyper_res:                          0
% 3.05/0.98  prep_cycles:                            4
% 3.05/0.98  pred_elim_time:                         0.031
% 3.05/0.98  splitting_time:                         0.
% 3.05/0.98  sem_filter_time:                        0.
% 3.05/0.98  monotx_time:                            0.001
% 3.05/0.98  subtype_inf_time:                       0.
% 3.05/0.98  
% 3.05/0.98  ------ Problem properties
% 3.05/0.98  
% 3.05/0.98  clauses:                                25
% 3.05/0.98  conjectures:                            4
% 3.05/0.98  epr:                                    6
% 3.05/0.98  horn:                                   14
% 3.05/0.98  ground:                                 4
% 3.05/0.98  unary:                                  5
% 3.05/0.98  binary:                                 2
% 3.05/0.98  lits:                                   85
% 3.05/0.98  lits_eq:                                11
% 3.05/0.98  fd_pure:                                0
% 3.05/0.98  fd_pseudo:                              0
% 3.05/0.98  fd_cond:                                0
% 3.05/0.98  fd_pseudo_cond:                         3
% 3.05/0.98  ac_symbols:                             0
% 3.05/0.98  
% 3.05/0.98  ------ Propositional Solver
% 3.05/0.98  
% 3.05/0.98  prop_solver_calls:                      27
% 3.05/0.98  prop_fast_solver_calls:                 1438
% 3.05/0.98  smt_solver_calls:                       0
% 3.05/0.98  smt_fast_solver_calls:                  0
% 3.05/0.98  prop_num_of_clauses:                    1587
% 3.05/0.98  prop_preprocess_simplified:             6120
% 3.05/0.98  prop_fo_subsumed:                       32
% 3.05/0.98  prop_solver_time:                       0.
% 3.05/0.98  smt_solver_time:                        0.
% 3.05/0.98  smt_fast_solver_time:                   0.
% 3.05/0.98  prop_fast_solver_time:                  0.
% 3.05/0.98  prop_unsat_core_time:                   0.
% 3.05/0.98  
% 3.05/0.98  ------ QBF
% 3.05/0.98  
% 3.05/0.98  qbf_q_res:                              0
% 3.05/0.98  qbf_num_tautologies:                    0
% 3.05/0.98  qbf_prep_cycles:                        0
% 3.05/0.98  
% 3.05/0.98  ------ BMC1
% 3.05/0.98  
% 3.05/0.98  bmc1_current_bound:                     -1
% 3.05/0.98  bmc1_last_solved_bound:                 -1
% 3.05/0.98  bmc1_unsat_core_size:                   -1
% 3.05/0.98  bmc1_unsat_core_parents_size:           -1
% 3.05/0.98  bmc1_merge_next_fun:                    0
% 3.05/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.05/0.98  
% 3.05/0.98  ------ Instantiation
% 3.05/0.98  
% 3.05/0.98  inst_num_of_clauses:                    426
% 3.05/0.98  inst_num_in_passive:                    151
% 3.05/0.98  inst_num_in_active:                     191
% 3.05/0.98  inst_num_in_unprocessed:                84
% 3.05/0.98  inst_num_of_loops:                      220
% 3.05/0.98  inst_num_of_learning_restarts:          0
% 3.05/0.98  inst_num_moves_active_passive:          26
% 3.05/0.98  inst_lit_activity:                      0
% 3.05/0.98  inst_lit_activity_moves:                0
% 3.05/0.98  inst_num_tautologies:                   0
% 3.05/0.98  inst_num_prop_implied:                  0
% 3.05/0.98  inst_num_existing_simplified:           0
% 3.05/0.98  inst_num_eq_res_simplified:             0
% 3.05/0.98  inst_num_child_elim:                    0
% 3.05/0.98  inst_num_of_dismatching_blockings:      115
% 3.05/0.98  inst_num_of_non_proper_insts:           385
% 3.05/0.98  inst_num_of_duplicates:                 0
% 3.05/0.98  inst_inst_num_from_inst_to_res:         0
% 3.05/0.98  inst_dismatching_checking_time:         0.
% 3.05/0.98  
% 3.05/0.98  ------ Resolution
% 3.05/0.98  
% 3.05/0.98  res_num_of_clauses:                     0
% 3.05/0.98  res_num_in_passive:                     0
% 3.05/0.98  res_num_in_active:                      0
% 3.05/0.98  res_num_of_loops:                       136
% 3.05/0.98  res_forward_subset_subsumed:            30
% 3.05/0.98  res_backward_subset_subsumed:           0
% 3.05/0.98  res_forward_subsumed:                   0
% 3.05/0.98  res_backward_subsumed:                  0
% 3.05/0.98  res_forward_subsumption_resolution:     3
% 3.05/0.98  res_backward_subsumption_resolution:    0
% 3.05/0.98  res_clause_to_clause_subsumption:       168
% 3.05/0.98  res_orphan_elimination:                 0
% 3.05/0.98  res_tautology_del:                      34
% 3.05/0.98  res_num_eq_res_simplified:              0
% 3.05/0.98  res_num_sel_changes:                    0
% 3.05/0.98  res_moves_from_active_to_pass:          0
% 3.05/0.98  
% 3.05/0.98  ------ Superposition
% 3.05/0.98  
% 3.05/0.98  sup_time_total:                         0.
% 3.05/0.98  sup_time_generating:                    0.
% 3.05/0.98  sup_time_sim_full:                      0.
% 3.05/0.98  sup_time_sim_immed:                     0.
% 3.05/0.98  
% 3.05/0.98  sup_num_of_clauses:                     65
% 3.05/0.98  sup_num_in_active:                      35
% 3.05/0.98  sup_num_in_passive:                     30
% 3.05/0.98  sup_num_of_loops:                       42
% 3.05/0.98  sup_fw_superposition:                   25
% 3.05/0.98  sup_bw_superposition:                   23
% 3.05/0.98  sup_immediate_simplified:               6
% 3.05/0.98  sup_given_eliminated:                   0
% 3.05/0.98  comparisons_done:                       0
% 3.05/0.98  comparisons_avoided:                    2
% 3.05/0.98  
% 3.05/0.98  ------ Simplifications
% 3.05/0.98  
% 3.05/0.98  
% 3.05/0.98  sim_fw_subset_subsumed:                 3
% 3.05/0.98  sim_bw_subset_subsumed:                 1
% 3.05/0.98  sim_fw_subsumed:                        1
% 3.05/0.98  sim_bw_subsumed:                        0
% 3.05/0.98  sim_fw_subsumption_res:                 4
% 3.05/0.98  sim_bw_subsumption_res:                 0
% 3.05/0.98  sim_tautology_del:                      3
% 3.05/0.98  sim_eq_tautology_del:                   1
% 3.05/0.98  sim_eq_res_simp:                        0
% 3.05/0.98  sim_fw_demodulated:                     0
% 3.05/0.98  sim_bw_demodulated:                     6
% 3.05/0.98  sim_light_normalised:                   2
% 3.05/0.98  sim_joinable_taut:                      0
% 3.05/0.98  sim_joinable_simp:                      0
% 3.05/0.98  sim_ac_normalised:                      0
% 3.05/0.98  sim_smt_subsumption:                    0
% 3.05/0.98  
%------------------------------------------------------------------------------
