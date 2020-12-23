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

% Result     : Theorem 3.33s
% Output     : CNFRefutation 3.33s
% Verified   : 
% Statistics : Number of formulae       :  197 (4925 expanded)
%              Number of clauses        :  110 (1418 expanded)
%              Number of leaves         :   22 (1009 expanded)
%              Depth                    :   32
%              Number of atoms          :  692 (24044 expanded)
%              Number of equality atoms :  205 (2006 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f54])).

fof(f56,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f55,f56])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f51,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f50])).

fof(f52,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f51,f52])).

fof(f71,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f93,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f79,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f15,axiom,(
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
    inference(pure_predicate_removal,[],[f15])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f95,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
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
    inference(flattening,[],[f36])).

fof(f59,plain,(
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
    inference(nnf_transformation,[],[f37])).

fof(f60,plain,(
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
    inference(rectify,[],[f59])).

fof(f61,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v1_subset_1(X2,u1_struct_0(X0))
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_subset_1(sK2(X0,X1),u1_struct_0(X0))
        & u1_struct_0(X1) = sK2(X0,X1)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f60,f61])).

fof(f90,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | u1_struct_0(X1) = sK2(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f62])).

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

fof(f48,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f49,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f66,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f49])).

fof(f67,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f66])).

fof(f69,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),sK5),u1_struct_0(X0))
          | ~ v1_tex_2(k1_tex_2(X0,sK5),X0) )
        & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),sK5),u1_struct_0(X0))
          | v1_tex_2(k1_tex_2(X0,sK5),X0) )
        & m1_subset_1(sK5,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,
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
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK4),X1),u1_struct_0(sK4))
            | ~ v1_tex_2(k1_tex_2(sK4,X1),sK4) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(sK4),X1),u1_struct_0(sK4))
            | v1_tex_2(k1_tex_2(sK4,X1),sK4) )
          & m1_subset_1(X1,u1_struct_0(sK4)) )
      & l1_pre_topc(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,
    ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),u1_struct_0(sK4))
      | ~ v1_tex_2(k1_tex_2(sK4,sK5),sK4) )
    & ( v1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),u1_struct_0(sK4))
      | v1_tex_2(k1_tex_2(sK4,sK5),sK4) )
    & m1_subset_1(sK5,u1_struct_0(sK4))
    & l1_pre_topc(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f67,f69,f68])).

fof(f107,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),u1_struct_0(sK4))
    | ~ v1_tex_2(k1_tex_2(sK4,sK5),sK4) ),
    inference(cnf_transformation,[],[f70])).

fof(f104,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f70])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v7_struct_0(X0) )
     => ~ v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f84,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f82,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f106,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),u1_struct_0(sK4))
    | v1_tex_2(k1_tex_2(sK4,sK5),sK4) ),
    inference(cnf_transformation,[],[f70])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ~ ( v7_struct_0(X0)
              & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v7_struct_0(X0)
          | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v7_struct_0(X0)
          | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ v7_struct_0(X0)
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f103,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f70])).

fof(f105,plain,(
    m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f70])).

fof(f12,axiom,(
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
    inference(ennf_transformation,[],[f12])).

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

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ v1_tex_2(X1,X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f16,axiom,(
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
    inference(pure_predicate_removal,[],[f16])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k1_tex_2(X0,X1))
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

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f101,plain,(
    ! [X0,X1] :
      ( v1_subset_1(k6_domain_1(X0,X1),X0)
      | ~ m1_subset_1(X1,X0)
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f97,plain,(
    ! [X0,X1] :
      ( v7_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f85,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_zfmisc_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_zfmisc_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f81,plain,(
    ! [X0,X1] :
      ( v1_zfmisc_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_zfmisc_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f9,axiom,(
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
    inference(ennf_transformation,[],[f9])).

fof(f83,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f91,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | ~ v1_subset_1(sK2(X0,X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f89,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_3973,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_3975,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4772,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3973,c_3975])).

cnf(c_21,plain,
    ( v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_288,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_7])).

cnf(c_289,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_288])).

cnf(c_360,plain,
    ( v1_subset_1(X0,X1)
    | ~ r1_tarski(X0,X1)
    | X0 = X1 ),
    inference(bin_hyper_res,[status(thm)],[c_21,c_289])).

cnf(c_3946,plain,
    ( X0 = X1
    | v1_subset_1(X0,X1) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_360])).

cnf(c_6052,plain,
    ( X0 = X1
    | v1_subset_1(X1,X0) = iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4772,c_3946])).

cnf(c_23,plain,
    ( m1_pre_topc(k1_tex_2(X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_3959,plain,
    ( m1_pre_topc(k1_tex_2(X0,X1),X0) = iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_18,plain,
    ( v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK2(X1,X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_3963,plain,
    ( sK2(X0,X1) = u1_struct_0(X1)
    | v1_tex_2(X1,X0) = iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_6205,plain,
    ( sK2(X0,k1_tex_2(X0,X1)) = u1_struct_0(k1_tex_2(X0,X1))
    | v1_tex_2(k1_tex_2(X0,X1),X0) = iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3959,c_3963])).

cnf(c_32,negated_conjecture,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),u1_struct_0(sK4))
    | ~ v1_tex_2(k1_tex_2(sK4,sK5),sK4) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_3952,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),u1_struct_0(sK4)) != iProver_top
    | v1_tex_2(k1_tex_2(sK4,sK5),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_7442,plain,
    ( k6_domain_1(u1_struct_0(sK4),sK5) = u1_struct_0(sK4)
    | v1_tex_2(k1_tex_2(sK4,sK5),sK4) != iProver_top
    | v1_xboole_0(k6_domain_1(u1_struct_0(sK4),sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6052,c_3952])).

cnf(c_9106,plain,
    ( k6_domain_1(u1_struct_0(sK4),sK5) = u1_struct_0(sK4)
    | sK2(sK4,k1_tex_2(sK4,sK5)) = u1_struct_0(k1_tex_2(sK4,sK5))
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v1_xboole_0(k6_domain_1(u1_struct_0(sK4),sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6205,c_7442])).

cnf(c_35,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_38,plain,
    ( l1_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_13,plain,
    ( v7_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_zfmisc_1(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_92,plain,
    ( v7_struct_0(X0) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | v1_zfmisc_1(u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_94,plain,
    ( v7_struct_0(sK4) = iProver_top
    | l1_struct_0(sK4) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_92])).

cnf(c_11,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_96,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_98,plain,
    ( l1_pre_topc(sK4) != iProver_top
    | l1_struct_0(sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_96])).

cnf(c_33,negated_conjecture,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),u1_struct_0(sK4))
    | v1_tex_2(k1_tex_2(sK4,sK5),sK4) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_3951,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),u1_struct_0(sK4)) = iProver_top
    | v1_tex_2(k1_tex_2(sK4,sK5),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_31,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v7_struct_0(X0)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_487,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v7_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_11,c_31])).

cnf(c_3945,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v7_struct_0(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_487])).

cnf(c_5156,plain,
    ( v1_tex_2(k1_tex_2(sK4,sK5),sK4) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v7_struct_0(sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3951,c_3945])).

cnf(c_36,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_37,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_39,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_41,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),u1_struct_0(sK4)) != iProver_top
    | v1_tex_2(k1_tex_2(sK4,sK5),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_15,plain,
    ( ~ v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v7_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_292,plain,
    ( v1_tex_2(k1_tex_2(sK4,sK5),sK4)
    | v1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),u1_struct_0(sK4)) ),
    inference(prop_impl,[status(thm)],[c_33])).

cnf(c_293,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),u1_struct_0(sK4))
    | v1_tex_2(k1_tex_2(sK4,sK5),sK4) ),
    inference(renaming,[status(thm)],[c_292])).

cnf(c_1218,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),u1_struct_0(sK4))
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v7_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k1_tex_2(sK4,sK5) != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_293])).

cnf(c_1219,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),u1_struct_0(sK4))
    | ~ m1_pre_topc(k1_tex_2(sK4,sK5),sK4)
    | v2_struct_0(k1_tex_2(sK4,sK5))
    | v2_struct_0(sK4)
    | ~ v7_struct_0(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_1218])).

cnf(c_1221,plain,
    ( ~ v7_struct_0(sK4)
    | v1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),u1_struct_0(sK4))
    | ~ m1_pre_topc(k1_tex_2(sK4,sK5),sK4)
    | v2_struct_0(k1_tex_2(sK4,sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1219,c_36,c_35])).

cnf(c_1222,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),u1_struct_0(sK4))
    | ~ m1_pre_topc(k1_tex_2(sK4,sK5),sK4)
    | v2_struct_0(k1_tex_2(sK4,sK5))
    | ~ v7_struct_0(sK4) ),
    inference(renaming,[status(thm)],[c_1221])).

cnf(c_1223,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),u1_struct_0(sK4)) = iProver_top
    | m1_pre_topc(k1_tex_2(sK4,sK5),sK4) != iProver_top
    | v2_struct_0(k1_tex_2(sK4,sK5)) = iProver_top
    | v7_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1222])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k1_tex_2(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_4250,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ v2_struct_0(k1_tex_2(sK4,sK5))
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_4251,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
    | v2_struct_0(k1_tex_2(sK4,sK5)) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4250])).

cnf(c_4258,plain,
    ( m1_pre_topc(k1_tex_2(sK4,sK5),sK4)
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_4259,plain,
    ( m1_pre_topc(k1_tex_2(sK4,sK5),sK4) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4258])).

cnf(c_5636,plain,
    ( v7_struct_0(sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5156,c_37,c_38,c_39,c_41,c_1223,c_4251,c_4259])).

cnf(c_30,plain,
    ( v1_subset_1(k6_domain_1(X0,X1),X0)
    | ~ m1_subset_1(X1,X0)
    | v1_zfmisc_1(X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_3953,plain,
    ( v1_subset_1(k6_domain_1(X0,X1),X0) = iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | v1_zfmisc_1(X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_5308,plain,
    ( v1_tex_2(k1_tex_2(sK4,sK5),sK4) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK4)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3953,c_3952])).

cnf(c_5571,plain,
    ( v1_tex_2(k1_tex_2(sK4,sK5),sK4) != iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5308,c_37,c_38,c_39,c_41,c_94,c_98,c_1223,c_4251,c_4259,c_5156])).

cnf(c_9107,plain,
    ( sK2(sK4,k1_tex_2(sK4,sK5)) = u1_struct_0(k1_tex_2(sK4,sK5))
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6205,c_5571])).

cnf(c_9779,plain,
    ( sK2(sK4,k1_tex_2(sK4,sK5)) = u1_struct_0(k1_tex_2(sK4,sK5))
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9107,c_37,c_38,c_39])).

cnf(c_3950,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v7_struct_0(k1_tex_2(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_3957,plain,
    ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v7_struct_0(k1_tex_2(X1,X0)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_5451,plain,
    ( v2_struct_0(sK4) = iProver_top
    | v7_struct_0(k1_tex_2(sK4,sK5)) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3950,c_3957])).

cnf(c_4247,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | v2_struct_0(sK4)
    | v7_struct_0(k1_tex_2(sK4,sK5))
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_4248,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v7_struct_0(k1_tex_2(sK4,sK5)) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4247])).

cnf(c_5565,plain,
    ( v7_struct_0(k1_tex_2(sK4,sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5451,c_37,c_38,c_39,c_4248])).

cnf(c_14,plain,
    ( ~ v7_struct_0(X0)
    | ~ l1_struct_0(X0)
    | v1_zfmisc_1(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_507,plain,
    ( ~ v7_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | v1_zfmisc_1(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_11,c_14])).

cnf(c_3944,plain,
    ( v7_struct_0(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_zfmisc_1(u1_struct_0(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_507])).

cnf(c_6,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_3970,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_3968,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4522,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3970,c_3968])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_zfmisc_1(X1)
    | v1_zfmisc_1(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_359,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_zfmisc_1(X1)
    | v1_zfmisc_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_10,c_289])).

cnf(c_3947,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_zfmisc_1(X1) != iProver_top
    | v1_zfmisc_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_359])).

cnf(c_5031,plain,
    ( v1_zfmisc_1(X0) != iProver_top
    | v1_zfmisc_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4522,c_3947])).

cnf(c_5132,plain,
    ( v7_struct_0(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_zfmisc_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3944,c_5031])).

cnf(c_5717,plain,
    ( l1_pre_topc(k1_tex_2(sK4,sK5)) != iProver_top
    | v1_zfmisc_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5565,c_5132])).

cnf(c_12,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_4509,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK4,sK5),X0)
    | ~ l1_pre_topc(X0)
    | l1_pre_topc(k1_tex_2(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_4510,plain,
    ( m1_pre_topc(k1_tex_2(sK4,sK5),X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(k1_tex_2(sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4509])).

cnf(c_4512,plain,
    ( m1_pre_topc(k1_tex_2(sK4,sK5),sK4) != iProver_top
    | l1_pre_topc(k1_tex_2(sK4,sK5)) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4510])).

cnf(c_5840,plain,
    ( v1_zfmisc_1(k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5717,c_37,c_38,c_39,c_4259,c_4512])).

cnf(c_5030,plain,
    ( v1_zfmisc_1(X0) != iProver_top
    | v1_zfmisc_1(X1) = iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4772,c_3947])).

cnf(c_5845,plain,
    ( v1_zfmisc_1(X0) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5840,c_5030])).

cnf(c_9786,plain,
    ( sK2(sK4,k1_tex_2(sK4,sK5)) = u1_struct_0(k1_tex_2(sK4,sK5))
    | v1_zfmisc_1(u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_9779,c_5845])).

cnf(c_9798,plain,
    ( sK2(sK4,k1_tex_2(sK4,sK5)) = u1_struct_0(k1_tex_2(sK4,sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9106,c_37,c_38,c_39,c_41,c_94,c_98,c_1223,c_4251,c_4259,c_5156,c_9786])).

cnf(c_17,plain,
    ( ~ v1_subset_1(sK2(X0,X1),u1_struct_0(X0))
    | v1_tex_2(X1,X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_3964,plain,
    ( v1_subset_1(sK2(X0,X1),u1_struct_0(X0)) != iProver_top
    | v1_tex_2(X1,X0) = iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_9801,plain,
    ( v1_subset_1(u1_struct_0(k1_tex_2(sK4,sK5)),u1_struct_0(sK4)) != iProver_top
    | v1_tex_2(k1_tex_2(sK4,sK5),sK4) = iProver_top
    | m1_pre_topc(k1_tex_2(sK4,sK5),sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_9798,c_3964])).

cnf(c_10000,plain,
    ( v1_subset_1(u1_struct_0(k1_tex_2(sK4,sK5)),u1_struct_0(sK4)) != iProver_top
    | v1_tex_2(k1_tex_2(sK4,sK5),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9801,c_37,c_38,c_39,c_4259])).

cnf(c_10007,plain,
    ( u1_struct_0(k1_tex_2(sK4,sK5)) = u1_struct_0(sK4)
    | v1_tex_2(k1_tex_2(sK4,sK5),sK4) = iProver_top
    | v1_xboole_0(u1_struct_0(k1_tex_2(sK4,sK5))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6052,c_10000])).

cnf(c_19,plain,
    ( v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | m1_subset_1(sK2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_3962,plain,
    ( v1_tex_2(X0,X1) = iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(sK2(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_9802,plain,
    ( v1_tex_2(k1_tex_2(sK4,sK5),sK4) = iProver_top
    | m1_pre_topc(k1_tex_2(sK4,sK5),sK4) != iProver_top
    | m1_subset_1(u1_struct_0(k1_tex_2(sK4,sK5)),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_9798,c_3962])).

cnf(c_10016,plain,
    ( m1_subset_1(u1_struct_0(k1_tex_2(sK4,sK5)),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | v1_tex_2(k1_tex_2(sK4,sK5),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9802,c_37,c_38,c_39,c_4259])).

cnf(c_10017,plain,
    ( v1_tex_2(k1_tex_2(sK4,sK5),sK4) = iProver_top
    | m1_subset_1(u1_struct_0(k1_tex_2(sK4,sK5)),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(renaming,[status(thm)],[c_10016])).

cnf(c_10022,plain,
    ( v1_tex_2(k1_tex_2(sK4,sK5),sK4) = iProver_top
    | r1_tarski(u1_struct_0(k1_tex_2(sK4,sK5)),u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_10017,c_3968])).

cnf(c_10220,plain,
    ( u1_struct_0(k1_tex_2(sK4,sK5)) = u1_struct_0(sK4)
    | v1_subset_1(u1_struct_0(k1_tex_2(sK4,sK5)),u1_struct_0(sK4)) = iProver_top
    | v1_tex_2(k1_tex_2(sK4,sK5),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_10022,c_3946])).

cnf(c_10248,plain,
    ( v1_tex_2(k1_tex_2(sK4,sK5),sK4) = iProver_top
    | u1_struct_0(k1_tex_2(sK4,sK5)) = u1_struct_0(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10007,c_37,c_38,c_39,c_4259,c_9801,c_10220])).

cnf(c_10249,plain,
    ( u1_struct_0(k1_tex_2(sK4,sK5)) = u1_struct_0(sK4)
    | v1_tex_2(k1_tex_2(sK4,sK5),sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_10248])).

cnf(c_10255,plain,
    ( k6_domain_1(u1_struct_0(sK4),sK5) = u1_struct_0(sK4)
    | u1_struct_0(k1_tex_2(sK4,sK5)) = u1_struct_0(sK4)
    | v1_xboole_0(k6_domain_1(u1_struct_0(sK4),sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10249,c_7442])).

cnf(c_10256,plain,
    ( u1_struct_0(k1_tex_2(sK4,sK5)) = u1_struct_0(sK4)
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_10249,c_5571])).

cnf(c_11291,plain,
    ( u1_struct_0(k1_tex_2(sK4,sK5)) = u1_struct_0(sK4)
    | v1_zfmisc_1(u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_10256,c_5845])).

cnf(c_11325,plain,
    ( u1_struct_0(k1_tex_2(sK4,sK5)) = u1_struct_0(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10255,c_37,c_38,c_39,c_41,c_94,c_98,c_1223,c_4251,c_4259,c_5156,c_11291])).

cnf(c_11349,plain,
    ( v7_struct_0(k1_tex_2(sK4,sK5)) != iProver_top
    | l1_pre_topc(k1_tex_2(sK4,sK5)) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_11325,c_3944])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11349,c_5636,c_4512,c_4259,c_4248,c_98,c_94,c_39,c_38,c_37])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:31:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.33/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.33/1.01  
% 3.33/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.33/1.01  
% 3.33/1.01  ------  iProver source info
% 3.33/1.01  
% 3.33/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.33/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.33/1.01  git: non_committed_changes: false
% 3.33/1.01  git: last_make_outside_of_git: false
% 3.33/1.01  
% 3.33/1.01  ------ 
% 3.33/1.01  
% 3.33/1.01  ------ Input Options
% 3.33/1.01  
% 3.33/1.01  --out_options                           all
% 3.33/1.01  --tptp_safe_out                         true
% 3.33/1.01  --problem_path                          ""
% 3.33/1.01  --include_path                          ""
% 3.33/1.01  --clausifier                            res/vclausify_rel
% 3.33/1.01  --clausifier_options                    --mode clausify
% 3.33/1.01  --stdin                                 false
% 3.33/1.01  --stats_out                             all
% 3.33/1.01  
% 3.33/1.01  ------ General Options
% 3.33/1.01  
% 3.33/1.01  --fof                                   false
% 3.33/1.01  --time_out_real                         305.
% 3.33/1.01  --time_out_virtual                      -1.
% 3.33/1.01  --symbol_type_check                     false
% 3.33/1.01  --clausify_out                          false
% 3.33/1.01  --sig_cnt_out                           false
% 3.33/1.01  --trig_cnt_out                          false
% 3.33/1.01  --trig_cnt_out_tolerance                1.
% 3.33/1.01  --trig_cnt_out_sk_spl                   false
% 3.33/1.01  --abstr_cl_out                          false
% 3.33/1.01  
% 3.33/1.01  ------ Global Options
% 3.33/1.01  
% 3.33/1.01  --schedule                              default
% 3.33/1.01  --add_important_lit                     false
% 3.33/1.01  --prop_solver_per_cl                    1000
% 3.33/1.01  --min_unsat_core                        false
% 3.33/1.01  --soft_assumptions                      false
% 3.33/1.01  --soft_lemma_size                       3
% 3.33/1.01  --prop_impl_unit_size                   0
% 3.33/1.01  --prop_impl_unit                        []
% 3.33/1.01  --share_sel_clauses                     true
% 3.33/1.01  --reset_solvers                         false
% 3.33/1.01  --bc_imp_inh                            [conj_cone]
% 3.33/1.01  --conj_cone_tolerance                   3.
% 3.33/1.01  --extra_neg_conj                        none
% 3.33/1.01  --large_theory_mode                     true
% 3.33/1.01  --prolific_symb_bound                   200
% 3.33/1.01  --lt_threshold                          2000
% 3.33/1.01  --clause_weak_htbl                      true
% 3.33/1.01  --gc_record_bc_elim                     false
% 3.33/1.01  
% 3.33/1.01  ------ Preprocessing Options
% 3.33/1.01  
% 3.33/1.01  --preprocessing_flag                    true
% 3.33/1.01  --time_out_prep_mult                    0.1
% 3.33/1.01  --splitting_mode                        input
% 3.33/1.01  --splitting_grd                         true
% 3.33/1.01  --splitting_cvd                         false
% 3.33/1.01  --splitting_cvd_svl                     false
% 3.33/1.01  --splitting_nvd                         32
% 3.33/1.01  --sub_typing                            true
% 3.33/1.01  --prep_gs_sim                           true
% 3.33/1.01  --prep_unflatten                        true
% 3.33/1.01  --prep_res_sim                          true
% 3.33/1.01  --prep_upred                            true
% 3.33/1.01  --prep_sem_filter                       exhaustive
% 3.33/1.01  --prep_sem_filter_out                   false
% 3.33/1.01  --pred_elim                             true
% 3.33/1.01  --res_sim_input                         true
% 3.33/1.01  --eq_ax_congr_red                       true
% 3.33/1.01  --pure_diseq_elim                       true
% 3.33/1.01  --brand_transform                       false
% 3.33/1.01  --non_eq_to_eq                          false
% 3.33/1.01  --prep_def_merge                        true
% 3.33/1.01  --prep_def_merge_prop_impl              false
% 3.33/1.01  --prep_def_merge_mbd                    true
% 3.33/1.01  --prep_def_merge_tr_red                 false
% 3.33/1.01  --prep_def_merge_tr_cl                  false
% 3.33/1.01  --smt_preprocessing                     true
% 3.33/1.01  --smt_ac_axioms                         fast
% 3.33/1.01  --preprocessed_out                      false
% 3.33/1.01  --preprocessed_stats                    false
% 3.33/1.01  
% 3.33/1.01  ------ Abstraction refinement Options
% 3.33/1.01  
% 3.33/1.01  --abstr_ref                             []
% 3.33/1.01  --abstr_ref_prep                        false
% 3.33/1.01  --abstr_ref_until_sat                   false
% 3.33/1.01  --abstr_ref_sig_restrict                funpre
% 3.33/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.33/1.01  --abstr_ref_under                       []
% 3.33/1.01  
% 3.33/1.01  ------ SAT Options
% 3.33/1.01  
% 3.33/1.01  --sat_mode                              false
% 3.33/1.01  --sat_fm_restart_options                ""
% 3.33/1.01  --sat_gr_def                            false
% 3.33/1.01  --sat_epr_types                         true
% 3.33/1.01  --sat_non_cyclic_types                  false
% 3.33/1.01  --sat_finite_models                     false
% 3.33/1.01  --sat_fm_lemmas                         false
% 3.33/1.01  --sat_fm_prep                           false
% 3.33/1.01  --sat_fm_uc_incr                        true
% 3.33/1.01  --sat_out_model                         small
% 3.33/1.01  --sat_out_clauses                       false
% 3.33/1.01  
% 3.33/1.01  ------ QBF Options
% 3.33/1.01  
% 3.33/1.01  --qbf_mode                              false
% 3.33/1.01  --qbf_elim_univ                         false
% 3.33/1.01  --qbf_dom_inst                          none
% 3.33/1.01  --qbf_dom_pre_inst                      false
% 3.33/1.01  --qbf_sk_in                             false
% 3.33/1.01  --qbf_pred_elim                         true
% 3.33/1.01  --qbf_split                             512
% 3.33/1.01  
% 3.33/1.01  ------ BMC1 Options
% 3.33/1.01  
% 3.33/1.01  --bmc1_incremental                      false
% 3.33/1.01  --bmc1_axioms                           reachable_all
% 3.33/1.01  --bmc1_min_bound                        0
% 3.33/1.01  --bmc1_max_bound                        -1
% 3.33/1.01  --bmc1_max_bound_default                -1
% 3.33/1.01  --bmc1_symbol_reachability              true
% 3.33/1.01  --bmc1_property_lemmas                  false
% 3.33/1.01  --bmc1_k_induction                      false
% 3.33/1.01  --bmc1_non_equiv_states                 false
% 3.33/1.01  --bmc1_deadlock                         false
% 3.33/1.01  --bmc1_ucm                              false
% 3.33/1.01  --bmc1_add_unsat_core                   none
% 3.33/1.01  --bmc1_unsat_core_children              false
% 3.33/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.33/1.01  --bmc1_out_stat                         full
% 3.33/1.01  --bmc1_ground_init                      false
% 3.33/1.01  --bmc1_pre_inst_next_state              false
% 3.33/1.01  --bmc1_pre_inst_state                   false
% 3.33/1.01  --bmc1_pre_inst_reach_state             false
% 3.33/1.01  --bmc1_out_unsat_core                   false
% 3.33/1.01  --bmc1_aig_witness_out                  false
% 3.33/1.01  --bmc1_verbose                          false
% 3.33/1.01  --bmc1_dump_clauses_tptp                false
% 3.33/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.33/1.01  --bmc1_dump_file                        -
% 3.33/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.33/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.33/1.01  --bmc1_ucm_extend_mode                  1
% 3.33/1.01  --bmc1_ucm_init_mode                    2
% 3.33/1.01  --bmc1_ucm_cone_mode                    none
% 3.33/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.33/1.01  --bmc1_ucm_relax_model                  4
% 3.33/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.33/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.33/1.01  --bmc1_ucm_layered_model                none
% 3.33/1.01  --bmc1_ucm_max_lemma_size               10
% 3.33/1.01  
% 3.33/1.01  ------ AIG Options
% 3.33/1.01  
% 3.33/1.01  --aig_mode                              false
% 3.33/1.01  
% 3.33/1.01  ------ Instantiation Options
% 3.33/1.01  
% 3.33/1.01  --instantiation_flag                    true
% 3.33/1.01  --inst_sos_flag                         false
% 3.33/1.01  --inst_sos_phase                        true
% 3.33/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.33/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.33/1.01  --inst_lit_sel_side                     num_symb
% 3.33/1.01  --inst_solver_per_active                1400
% 3.33/1.01  --inst_solver_calls_frac                1.
% 3.33/1.01  --inst_passive_queue_type               priority_queues
% 3.33/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.33/1.01  --inst_passive_queues_freq              [25;2]
% 3.33/1.01  --inst_dismatching                      true
% 3.33/1.01  --inst_eager_unprocessed_to_passive     true
% 3.33/1.01  --inst_prop_sim_given                   true
% 3.33/1.01  --inst_prop_sim_new                     false
% 3.33/1.01  --inst_subs_new                         false
% 3.33/1.01  --inst_eq_res_simp                      false
% 3.33/1.01  --inst_subs_given                       false
% 3.33/1.01  --inst_orphan_elimination               true
% 3.33/1.01  --inst_learning_loop_flag               true
% 3.33/1.01  --inst_learning_start                   3000
% 3.33/1.01  --inst_learning_factor                  2
% 3.33/1.01  --inst_start_prop_sim_after_learn       3
% 3.33/1.01  --inst_sel_renew                        solver
% 3.33/1.01  --inst_lit_activity_flag                true
% 3.33/1.01  --inst_restr_to_given                   false
% 3.33/1.01  --inst_activity_threshold               500
% 3.33/1.01  --inst_out_proof                        true
% 3.33/1.01  
% 3.33/1.01  ------ Resolution Options
% 3.33/1.01  
% 3.33/1.01  --resolution_flag                       true
% 3.33/1.01  --res_lit_sel                           adaptive
% 3.33/1.01  --res_lit_sel_side                      none
% 3.33/1.01  --res_ordering                          kbo
% 3.33/1.01  --res_to_prop_solver                    active
% 3.33/1.01  --res_prop_simpl_new                    false
% 3.33/1.01  --res_prop_simpl_given                  true
% 3.33/1.01  --res_passive_queue_type                priority_queues
% 3.33/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.33/1.01  --res_passive_queues_freq               [15;5]
% 3.33/1.01  --res_forward_subs                      full
% 3.33/1.01  --res_backward_subs                     full
% 3.33/1.01  --res_forward_subs_resolution           true
% 3.33/1.01  --res_backward_subs_resolution          true
% 3.33/1.01  --res_orphan_elimination                true
% 3.33/1.01  --res_time_limit                        2.
% 3.33/1.01  --res_out_proof                         true
% 3.33/1.01  
% 3.33/1.01  ------ Superposition Options
% 3.33/1.01  
% 3.33/1.01  --superposition_flag                    true
% 3.33/1.01  --sup_passive_queue_type                priority_queues
% 3.33/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.33/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.33/1.01  --demod_completeness_check              fast
% 3.33/1.01  --demod_use_ground                      true
% 3.33/1.01  --sup_to_prop_solver                    passive
% 3.33/1.01  --sup_prop_simpl_new                    true
% 3.33/1.01  --sup_prop_simpl_given                  true
% 3.33/1.01  --sup_fun_splitting                     false
% 3.33/1.01  --sup_smt_interval                      50000
% 3.33/1.01  
% 3.33/1.01  ------ Superposition Simplification Setup
% 3.33/1.01  
% 3.33/1.01  --sup_indices_passive                   []
% 3.33/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.33/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.33/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.33/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.33/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.33/1.01  --sup_full_bw                           [BwDemod]
% 3.33/1.01  --sup_immed_triv                        [TrivRules]
% 3.33/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.33/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.33/1.01  --sup_immed_bw_main                     []
% 3.33/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.33/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.33/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.33/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.33/1.01  
% 3.33/1.01  ------ Combination Options
% 3.33/1.01  
% 3.33/1.01  --comb_res_mult                         3
% 3.33/1.01  --comb_sup_mult                         2
% 3.33/1.01  --comb_inst_mult                        10
% 3.33/1.01  
% 3.33/1.01  ------ Debug Options
% 3.33/1.01  
% 3.33/1.01  --dbg_backtrace                         false
% 3.33/1.01  --dbg_dump_prop_clauses                 false
% 3.33/1.01  --dbg_dump_prop_clauses_file            -
% 3.33/1.01  --dbg_out_stat                          false
% 3.33/1.01  ------ Parsing...
% 3.33/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.33/1.01  
% 3.33/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.33/1.01  
% 3.33/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.33/1.01  
% 3.33/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.33/1.01  ------ Proving...
% 3.33/1.01  ------ Problem Properties 
% 3.33/1.01  
% 3.33/1.01  
% 3.33/1.01  clauses                                 34
% 3.33/1.01  conjectures                             5
% 3.33/1.01  EPR                                     8
% 3.33/1.01  Horn                                    22
% 3.33/1.01  unary                                   5
% 3.33/1.01  binary                                  12
% 3.33/1.01  lits                                    94
% 3.33/1.01  lits eq                                 2
% 3.33/1.01  fd_pure                                 0
% 3.33/1.01  fd_pseudo                               0
% 3.33/1.01  fd_cond                                 0
% 3.33/1.01  fd_pseudo_cond                          1
% 3.33/1.01  AC symbols                              0
% 3.33/1.01  
% 3.33/1.01  ------ Schedule dynamic 5 is on 
% 3.33/1.01  
% 3.33/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.33/1.01  
% 3.33/1.01  
% 3.33/1.01  ------ 
% 3.33/1.01  Current options:
% 3.33/1.01  ------ 
% 3.33/1.01  
% 3.33/1.01  ------ Input Options
% 3.33/1.01  
% 3.33/1.01  --out_options                           all
% 3.33/1.01  --tptp_safe_out                         true
% 3.33/1.01  --problem_path                          ""
% 3.33/1.01  --include_path                          ""
% 3.33/1.01  --clausifier                            res/vclausify_rel
% 3.33/1.01  --clausifier_options                    --mode clausify
% 3.33/1.01  --stdin                                 false
% 3.33/1.01  --stats_out                             all
% 3.33/1.01  
% 3.33/1.01  ------ General Options
% 3.33/1.01  
% 3.33/1.01  --fof                                   false
% 3.33/1.01  --time_out_real                         305.
% 3.33/1.01  --time_out_virtual                      -1.
% 3.33/1.01  --symbol_type_check                     false
% 3.33/1.01  --clausify_out                          false
% 3.33/1.01  --sig_cnt_out                           false
% 3.33/1.01  --trig_cnt_out                          false
% 3.33/1.01  --trig_cnt_out_tolerance                1.
% 3.33/1.01  --trig_cnt_out_sk_spl                   false
% 3.33/1.01  --abstr_cl_out                          false
% 3.33/1.01  
% 3.33/1.01  ------ Global Options
% 3.33/1.01  
% 3.33/1.01  --schedule                              default
% 3.33/1.01  --add_important_lit                     false
% 3.33/1.01  --prop_solver_per_cl                    1000
% 3.33/1.01  --min_unsat_core                        false
% 3.33/1.01  --soft_assumptions                      false
% 3.33/1.01  --soft_lemma_size                       3
% 3.33/1.01  --prop_impl_unit_size                   0
% 3.33/1.01  --prop_impl_unit                        []
% 3.33/1.01  --share_sel_clauses                     true
% 3.33/1.01  --reset_solvers                         false
% 3.33/1.01  --bc_imp_inh                            [conj_cone]
% 3.33/1.01  --conj_cone_tolerance                   3.
% 3.33/1.01  --extra_neg_conj                        none
% 3.33/1.01  --large_theory_mode                     true
% 3.33/1.01  --prolific_symb_bound                   200
% 3.33/1.01  --lt_threshold                          2000
% 3.33/1.01  --clause_weak_htbl                      true
% 3.33/1.01  --gc_record_bc_elim                     false
% 3.33/1.01  
% 3.33/1.01  ------ Preprocessing Options
% 3.33/1.01  
% 3.33/1.01  --preprocessing_flag                    true
% 3.33/1.01  --time_out_prep_mult                    0.1
% 3.33/1.01  --splitting_mode                        input
% 3.33/1.01  --splitting_grd                         true
% 3.33/1.01  --splitting_cvd                         false
% 3.33/1.01  --splitting_cvd_svl                     false
% 3.33/1.01  --splitting_nvd                         32
% 3.33/1.01  --sub_typing                            true
% 3.33/1.01  --prep_gs_sim                           true
% 3.33/1.01  --prep_unflatten                        true
% 3.33/1.01  --prep_res_sim                          true
% 3.33/1.01  --prep_upred                            true
% 3.33/1.01  --prep_sem_filter                       exhaustive
% 3.33/1.01  --prep_sem_filter_out                   false
% 3.33/1.01  --pred_elim                             true
% 3.33/1.01  --res_sim_input                         true
% 3.33/1.01  --eq_ax_congr_red                       true
% 3.33/1.01  --pure_diseq_elim                       true
% 3.33/1.01  --brand_transform                       false
% 3.33/1.01  --non_eq_to_eq                          false
% 3.33/1.01  --prep_def_merge                        true
% 3.33/1.01  --prep_def_merge_prop_impl              false
% 3.33/1.01  --prep_def_merge_mbd                    true
% 3.33/1.01  --prep_def_merge_tr_red                 false
% 3.33/1.01  --prep_def_merge_tr_cl                  false
% 3.33/1.01  --smt_preprocessing                     true
% 3.33/1.01  --smt_ac_axioms                         fast
% 3.33/1.01  --preprocessed_out                      false
% 3.33/1.01  --preprocessed_stats                    false
% 3.33/1.01  
% 3.33/1.01  ------ Abstraction refinement Options
% 3.33/1.01  
% 3.33/1.01  --abstr_ref                             []
% 3.33/1.01  --abstr_ref_prep                        false
% 3.33/1.01  --abstr_ref_until_sat                   false
% 3.33/1.01  --abstr_ref_sig_restrict                funpre
% 3.33/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.33/1.01  --abstr_ref_under                       []
% 3.33/1.01  
% 3.33/1.01  ------ SAT Options
% 3.33/1.01  
% 3.33/1.01  --sat_mode                              false
% 3.33/1.01  --sat_fm_restart_options                ""
% 3.33/1.01  --sat_gr_def                            false
% 3.33/1.01  --sat_epr_types                         true
% 3.33/1.01  --sat_non_cyclic_types                  false
% 3.33/1.01  --sat_finite_models                     false
% 3.33/1.01  --sat_fm_lemmas                         false
% 3.33/1.01  --sat_fm_prep                           false
% 3.33/1.01  --sat_fm_uc_incr                        true
% 3.33/1.01  --sat_out_model                         small
% 3.33/1.01  --sat_out_clauses                       false
% 3.33/1.01  
% 3.33/1.01  ------ QBF Options
% 3.33/1.01  
% 3.33/1.01  --qbf_mode                              false
% 3.33/1.01  --qbf_elim_univ                         false
% 3.33/1.01  --qbf_dom_inst                          none
% 3.33/1.01  --qbf_dom_pre_inst                      false
% 3.33/1.01  --qbf_sk_in                             false
% 3.33/1.01  --qbf_pred_elim                         true
% 3.33/1.01  --qbf_split                             512
% 3.33/1.01  
% 3.33/1.01  ------ BMC1 Options
% 3.33/1.01  
% 3.33/1.01  --bmc1_incremental                      false
% 3.33/1.01  --bmc1_axioms                           reachable_all
% 3.33/1.01  --bmc1_min_bound                        0
% 3.33/1.01  --bmc1_max_bound                        -1
% 3.33/1.01  --bmc1_max_bound_default                -1
% 3.33/1.01  --bmc1_symbol_reachability              true
% 3.33/1.01  --bmc1_property_lemmas                  false
% 3.33/1.01  --bmc1_k_induction                      false
% 3.33/1.01  --bmc1_non_equiv_states                 false
% 3.33/1.01  --bmc1_deadlock                         false
% 3.33/1.01  --bmc1_ucm                              false
% 3.33/1.01  --bmc1_add_unsat_core                   none
% 3.33/1.01  --bmc1_unsat_core_children              false
% 3.33/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.33/1.01  --bmc1_out_stat                         full
% 3.33/1.01  --bmc1_ground_init                      false
% 3.33/1.01  --bmc1_pre_inst_next_state              false
% 3.33/1.01  --bmc1_pre_inst_state                   false
% 3.33/1.01  --bmc1_pre_inst_reach_state             false
% 3.33/1.01  --bmc1_out_unsat_core                   false
% 3.33/1.01  --bmc1_aig_witness_out                  false
% 3.33/1.01  --bmc1_verbose                          false
% 3.33/1.01  --bmc1_dump_clauses_tptp                false
% 3.33/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.33/1.01  --bmc1_dump_file                        -
% 3.33/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.33/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.33/1.01  --bmc1_ucm_extend_mode                  1
% 3.33/1.01  --bmc1_ucm_init_mode                    2
% 3.33/1.01  --bmc1_ucm_cone_mode                    none
% 3.33/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.33/1.01  --bmc1_ucm_relax_model                  4
% 3.33/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.33/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.33/1.01  --bmc1_ucm_layered_model                none
% 3.33/1.01  --bmc1_ucm_max_lemma_size               10
% 3.33/1.01  
% 3.33/1.01  ------ AIG Options
% 3.33/1.01  
% 3.33/1.01  --aig_mode                              false
% 3.33/1.01  
% 3.33/1.01  ------ Instantiation Options
% 3.33/1.01  
% 3.33/1.01  --instantiation_flag                    true
% 3.33/1.01  --inst_sos_flag                         false
% 3.33/1.01  --inst_sos_phase                        true
% 3.33/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.33/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.33/1.01  --inst_lit_sel_side                     none
% 3.33/1.01  --inst_solver_per_active                1400
% 3.33/1.01  --inst_solver_calls_frac                1.
% 3.33/1.01  --inst_passive_queue_type               priority_queues
% 3.33/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.33/1.01  --inst_passive_queues_freq              [25;2]
% 3.33/1.01  --inst_dismatching                      true
% 3.33/1.01  --inst_eager_unprocessed_to_passive     true
% 3.33/1.01  --inst_prop_sim_given                   true
% 3.33/1.01  --inst_prop_sim_new                     false
% 3.33/1.01  --inst_subs_new                         false
% 3.33/1.01  --inst_eq_res_simp                      false
% 3.33/1.01  --inst_subs_given                       false
% 3.33/1.01  --inst_orphan_elimination               true
% 3.33/1.01  --inst_learning_loop_flag               true
% 3.33/1.01  --inst_learning_start                   3000
% 3.33/1.01  --inst_learning_factor                  2
% 3.33/1.01  --inst_start_prop_sim_after_learn       3
% 3.33/1.01  --inst_sel_renew                        solver
% 3.33/1.01  --inst_lit_activity_flag                true
% 3.33/1.01  --inst_restr_to_given                   false
% 3.33/1.01  --inst_activity_threshold               500
% 3.33/1.01  --inst_out_proof                        true
% 3.33/1.01  
% 3.33/1.01  ------ Resolution Options
% 3.33/1.01  
% 3.33/1.01  --resolution_flag                       false
% 3.33/1.01  --res_lit_sel                           adaptive
% 3.33/1.01  --res_lit_sel_side                      none
% 3.33/1.01  --res_ordering                          kbo
% 3.33/1.01  --res_to_prop_solver                    active
% 3.33/1.01  --res_prop_simpl_new                    false
% 3.33/1.01  --res_prop_simpl_given                  true
% 3.33/1.01  --res_passive_queue_type                priority_queues
% 3.33/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.33/1.01  --res_passive_queues_freq               [15;5]
% 3.33/1.01  --res_forward_subs                      full
% 3.33/1.01  --res_backward_subs                     full
% 3.33/1.01  --res_forward_subs_resolution           true
% 3.33/1.01  --res_backward_subs_resolution          true
% 3.33/1.01  --res_orphan_elimination                true
% 3.33/1.01  --res_time_limit                        2.
% 3.33/1.01  --res_out_proof                         true
% 3.33/1.01  
% 3.33/1.01  ------ Superposition Options
% 3.33/1.01  
% 3.33/1.01  --superposition_flag                    true
% 3.33/1.01  --sup_passive_queue_type                priority_queues
% 3.33/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.33/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.33/1.01  --demod_completeness_check              fast
% 3.33/1.01  --demod_use_ground                      true
% 3.33/1.01  --sup_to_prop_solver                    passive
% 3.33/1.01  --sup_prop_simpl_new                    true
% 3.33/1.01  --sup_prop_simpl_given                  true
% 3.33/1.01  --sup_fun_splitting                     false
% 3.33/1.01  --sup_smt_interval                      50000
% 3.33/1.01  
% 3.33/1.01  ------ Superposition Simplification Setup
% 3.33/1.01  
% 3.33/1.01  --sup_indices_passive                   []
% 3.33/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.33/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.33/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.33/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.33/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.33/1.01  --sup_full_bw                           [BwDemod]
% 3.33/1.01  --sup_immed_triv                        [TrivRules]
% 3.33/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.33/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.33/1.01  --sup_immed_bw_main                     []
% 3.33/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.33/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.33/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.33/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.33/1.01  
% 3.33/1.01  ------ Combination Options
% 3.33/1.01  
% 3.33/1.01  --comb_res_mult                         3
% 3.33/1.01  --comb_sup_mult                         2
% 3.33/1.01  --comb_inst_mult                        10
% 3.33/1.01  
% 3.33/1.01  ------ Debug Options
% 3.33/1.01  
% 3.33/1.01  --dbg_backtrace                         false
% 3.33/1.01  --dbg_dump_prop_clauses                 false
% 3.33/1.01  --dbg_dump_prop_clauses_file            -
% 3.33/1.01  --dbg_out_stat                          false
% 3.33/1.01  
% 3.33/1.01  
% 3.33/1.01  
% 3.33/1.01  
% 3.33/1.01  ------ Proving...
% 3.33/1.01  
% 3.33/1.01  
% 3.33/1.01  % SZS status Theorem for theBenchmark.p
% 3.33/1.01  
% 3.33/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.33/1.01  
% 3.33/1.01  fof(f2,axiom,(
% 3.33/1.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.33/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.01  
% 3.33/1.01  fof(f24,plain,(
% 3.33/1.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.33/1.01    inference(ennf_transformation,[],[f2])).
% 3.33/1.01  
% 3.33/1.01  fof(f54,plain,(
% 3.33/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.33/1.01    inference(nnf_transformation,[],[f24])).
% 3.33/1.01  
% 3.33/1.01  fof(f55,plain,(
% 3.33/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.33/1.01    inference(rectify,[],[f54])).
% 3.33/1.01  
% 3.33/1.01  fof(f56,plain,(
% 3.33/1.01    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 3.33/1.01    introduced(choice_axiom,[])).
% 3.33/1.01  
% 3.33/1.01  fof(f57,plain,(
% 3.33/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.33/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f55,f56])).
% 3.33/1.01  
% 3.33/1.01  fof(f74,plain,(
% 3.33/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 3.33/1.01    inference(cnf_transformation,[],[f57])).
% 3.33/1.01  
% 3.33/1.01  fof(f1,axiom,(
% 3.33/1.01    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.33/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.01  
% 3.33/1.01  fof(f50,plain,(
% 3.33/1.01    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.33/1.01    inference(nnf_transformation,[],[f1])).
% 3.33/1.01  
% 3.33/1.01  fof(f51,plain,(
% 3.33/1.01    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.33/1.01    inference(rectify,[],[f50])).
% 3.33/1.01  
% 3.33/1.01  fof(f52,plain,(
% 3.33/1.01    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.33/1.01    introduced(choice_axiom,[])).
% 3.33/1.01  
% 3.33/1.01  fof(f53,plain,(
% 3.33/1.01    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.33/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f51,f52])).
% 3.33/1.01  
% 3.33/1.01  fof(f71,plain,(
% 3.33/1.01    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.33/1.01    inference(cnf_transformation,[],[f53])).
% 3.33/1.01  
% 3.33/1.01  fof(f14,axiom,(
% 3.33/1.01    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 3.33/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.01  
% 3.33/1.01  fof(f38,plain,(
% 3.33/1.01    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.33/1.01    inference(ennf_transformation,[],[f14])).
% 3.33/1.01  
% 3.33/1.01  fof(f63,plain,(
% 3.33/1.01    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.33/1.01    inference(nnf_transformation,[],[f38])).
% 3.33/1.01  
% 3.33/1.01  fof(f93,plain,(
% 3.33/1.01    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.33/1.01    inference(cnf_transformation,[],[f63])).
% 3.33/1.01  
% 3.33/1.01  fof(f5,axiom,(
% 3.33/1.01    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.33/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.01  
% 3.33/1.01  fof(f58,plain,(
% 3.33/1.01    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.33/1.01    inference(nnf_transformation,[],[f5])).
% 3.33/1.01  
% 3.33/1.01  fof(f79,plain,(
% 3.33/1.01    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.33/1.01    inference(cnf_transformation,[],[f58])).
% 3.33/1.01  
% 3.33/1.01  fof(f15,axiom,(
% 3.33/1.01    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 3.33/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.01  
% 3.33/1.01  fof(f22,plain,(
% 3.33/1.01    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 3.33/1.01    inference(pure_predicate_removal,[],[f15])).
% 3.33/1.01  
% 3.33/1.01  fof(f39,plain,(
% 3.33/1.01    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.33/1.01    inference(ennf_transformation,[],[f22])).
% 3.33/1.01  
% 3.33/1.01  fof(f40,plain,(
% 3.33/1.01    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.33/1.01    inference(flattening,[],[f39])).
% 3.33/1.01  
% 3.33/1.01  fof(f95,plain,(
% 3.33/1.01    ( ! [X0,X1] : (m1_pre_topc(k1_tex_2(X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.33/1.01    inference(cnf_transformation,[],[f40])).
% 3.33/1.01  
% 3.33/1.01  fof(f13,axiom,(
% 3.33/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v1_subset_1(X2,u1_struct_0(X0)))))))),
% 3.33/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.01  
% 3.33/1.01  fof(f36,plain,(
% 3.33/1.01    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : ((v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.33/1.01    inference(ennf_transformation,[],[f13])).
% 3.33/1.01  
% 3.33/1.01  fof(f37,plain,(
% 3.33/1.01    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.33/1.01    inference(flattening,[],[f36])).
% 3.33/1.01  
% 3.33/1.01  fof(f59,plain,(
% 3.33/1.01    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.33/1.01    inference(nnf_transformation,[],[f37])).
% 3.33/1.01  
% 3.33/1.01  fof(f60,plain,(
% 3.33/1.01    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.33/1.01    inference(rectify,[],[f59])).
% 3.33/1.01  
% 3.33/1.01  fof(f61,plain,(
% 3.33/1.01    ! [X1,X0] : (? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_subset_1(sK2(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK2(X0,X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.33/1.01    introduced(choice_axiom,[])).
% 3.33/1.01  
% 3.33/1.01  fof(f62,plain,(
% 3.33/1.01    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | (~v1_subset_1(sK2(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK2(X0,X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.33/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f60,f61])).
% 3.33/1.01  
% 3.33/1.01  fof(f90,plain,(
% 3.33/1.01    ( ! [X0,X1] : (v1_tex_2(X1,X0) | u1_struct_0(X1) = sK2(X0,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.33/1.01    inference(cnf_transformation,[],[f62])).
% 3.33/1.01  
% 3.33/1.01  fof(f20,conjecture,(
% 3.33/1.01    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 3.33/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.01  
% 3.33/1.01  fof(f21,negated_conjecture,(
% 3.33/1.01    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 3.33/1.01    inference(negated_conjecture,[],[f20])).
% 3.33/1.01  
% 3.33/1.01  fof(f48,plain,(
% 3.33/1.01    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.33/1.01    inference(ennf_transformation,[],[f21])).
% 3.33/1.01  
% 3.33/1.01  fof(f49,plain,(
% 3.33/1.01    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.33/1.01    inference(flattening,[],[f48])).
% 3.33/1.01  
% 3.33/1.01  fof(f66,plain,(
% 3.33/1.01    ? [X0] : (? [X1] : (((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.33/1.01    inference(nnf_transformation,[],[f49])).
% 3.33/1.01  
% 3.33/1.01  fof(f67,plain,(
% 3.33/1.01    ? [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.33/1.01    inference(flattening,[],[f66])).
% 3.33/1.01  
% 3.33/1.01  fof(f69,plain,(
% 3.33/1.01    ( ! [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) => ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),sK5),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,sK5),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),sK5),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,sK5),X0)) & m1_subset_1(sK5,u1_struct_0(X0)))) )),
% 3.33/1.01    introduced(choice_axiom,[])).
% 3.33/1.01  
% 3.33/1.01  fof(f68,plain,(
% 3.33/1.01    ? [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(sK4),X1),u1_struct_0(sK4)) | ~v1_tex_2(k1_tex_2(sK4,X1),sK4)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK4),X1),u1_struct_0(sK4)) | v1_tex_2(k1_tex_2(sK4,X1),sK4)) & m1_subset_1(X1,u1_struct_0(sK4))) & l1_pre_topc(sK4) & ~v2_struct_0(sK4))),
% 3.33/1.01    introduced(choice_axiom,[])).
% 3.33/1.01  
% 3.33/1.01  fof(f70,plain,(
% 3.33/1.01    ((~v1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),u1_struct_0(sK4)) | ~v1_tex_2(k1_tex_2(sK4,sK5),sK4)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),u1_struct_0(sK4)) | v1_tex_2(k1_tex_2(sK4,sK5),sK4)) & m1_subset_1(sK5,u1_struct_0(sK4))) & l1_pre_topc(sK4) & ~v2_struct_0(sK4)),
% 3.33/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f67,f69,f68])).
% 3.33/1.01  
% 3.33/1.01  fof(f107,plain,(
% 3.33/1.01    ~v1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),u1_struct_0(sK4)) | ~v1_tex_2(k1_tex_2(sK4,sK5),sK4)),
% 3.33/1.01    inference(cnf_transformation,[],[f70])).
% 3.33/1.01  
% 3.33/1.01  fof(f104,plain,(
% 3.33/1.01    l1_pre_topc(sK4)),
% 3.33/1.01    inference(cnf_transformation,[],[f70])).
% 3.33/1.01  
% 3.33/1.01  fof(f10,axiom,(
% 3.33/1.01    ! [X0] : ((l1_struct_0(X0) & ~v7_struct_0(X0)) => ~v1_zfmisc_1(u1_struct_0(X0)))),
% 3.33/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.01  
% 3.33/1.01  fof(f30,plain,(
% 3.33/1.01    ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | v7_struct_0(X0)))),
% 3.33/1.01    inference(ennf_transformation,[],[f10])).
% 3.33/1.01  
% 3.33/1.01  fof(f31,plain,(
% 3.33/1.01    ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | v7_struct_0(X0))),
% 3.33/1.01    inference(flattening,[],[f30])).
% 3.33/1.01  
% 3.33/1.01  fof(f84,plain,(
% 3.33/1.01    ( ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | v7_struct_0(X0)) )),
% 3.33/1.01    inference(cnf_transformation,[],[f31])).
% 3.33/1.01  
% 3.33/1.01  fof(f8,axiom,(
% 3.33/1.01    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.33/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.01  
% 3.33/1.01  fof(f28,plain,(
% 3.33/1.01    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.33/1.01    inference(ennf_transformation,[],[f8])).
% 3.33/1.01  
% 3.33/1.01  fof(f82,plain,(
% 3.33/1.01    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.33/1.01    inference(cnf_transformation,[],[f28])).
% 3.33/1.01  
% 3.33/1.01  fof(f106,plain,(
% 3.33/1.01    v1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),u1_struct_0(sK4)) | v1_tex_2(k1_tex_2(sK4,sK5),sK4)),
% 3.33/1.01    inference(cnf_transformation,[],[f70])).
% 3.33/1.01  
% 3.33/1.01  fof(f19,axiom,(
% 3.33/1.01    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~(v7_struct_0(X0) & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 3.33/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.01  
% 3.33/1.01  fof(f46,plain,(
% 3.33/1.01    ! [X0] : (! [X1] : ((~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.33/1.01    inference(ennf_transformation,[],[f19])).
% 3.33/1.01  
% 3.33/1.01  fof(f47,plain,(
% 3.33/1.01    ! [X0] : (! [X1] : (~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.33/1.01    inference(flattening,[],[f46])).
% 3.33/1.01  
% 3.33/1.01  fof(f102,plain,(
% 3.33/1.01    ( ! [X0,X1] : (~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.33/1.01    inference(cnf_transformation,[],[f47])).
% 3.33/1.01  
% 3.33/1.01  fof(f103,plain,(
% 3.33/1.01    ~v2_struct_0(sK4)),
% 3.33/1.01    inference(cnf_transformation,[],[f70])).
% 3.33/1.01  
% 3.33/1.01  fof(f105,plain,(
% 3.33/1.01    m1_subset_1(sK5,u1_struct_0(sK4))),
% 3.33/1.01    inference(cnf_transformation,[],[f70])).
% 3.33/1.01  
% 3.33/1.01  fof(f12,axiom,(
% 3.33/1.01    ! [X0] : ((l1_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (~v2_struct_0(X1) => (~v1_tex_2(X1,X0) & ~v2_struct_0(X1)))))),
% 3.33/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.01  
% 3.33/1.01  fof(f34,plain,(
% 3.33/1.01    ! [X0] : (! [X1] : (((~v1_tex_2(X1,X0) & ~v2_struct_0(X1)) | v2_struct_0(X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0)))),
% 3.33/1.01    inference(ennf_transformation,[],[f12])).
% 3.33/1.01  
% 3.33/1.01  fof(f35,plain,(
% 3.33/1.01    ! [X0] : (! [X1] : ((~v1_tex_2(X1,X0) & ~v2_struct_0(X1)) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0))),
% 3.33/1.01    inference(flattening,[],[f34])).
% 3.33/1.01  
% 3.33/1.01  fof(f87,plain,(
% 3.33/1.01    ( ! [X0,X1] : (~v1_tex_2(X1,X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0)) )),
% 3.33/1.01    inference(cnf_transformation,[],[f35])).
% 3.33/1.01  
% 3.33/1.01  fof(f16,axiom,(
% 3.33/1.01    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 3.33/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.01  
% 3.33/1.01  fof(f23,plain,(
% 3.33/1.01    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 3.33/1.01    inference(pure_predicate_removal,[],[f16])).
% 3.33/1.01  
% 3.33/1.01  fof(f41,plain,(
% 3.33/1.01    ! [X0,X1] : ((v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.33/1.01    inference(ennf_transformation,[],[f23])).
% 3.33/1.01  
% 3.33/1.01  fof(f42,plain,(
% 3.33/1.01    ! [X0,X1] : ((v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.33/1.01    inference(flattening,[],[f41])).
% 3.33/1.01  
% 3.33/1.01  fof(f96,plain,(
% 3.33/1.01    ( ! [X0,X1] : (~v2_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.33/1.01    inference(cnf_transformation,[],[f42])).
% 3.33/1.01  
% 3.33/1.01  fof(f18,axiom,(
% 3.33/1.01    ! [X0] : ((~v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,X0) => v1_subset_1(k6_domain_1(X0,X1),X0)))),
% 3.33/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.01  
% 3.33/1.01  fof(f44,plain,(
% 3.33/1.01    ! [X0] : (! [X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | (v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 3.33/1.01    inference(ennf_transformation,[],[f18])).
% 3.33/1.01  
% 3.33/1.01  fof(f45,plain,(
% 3.33/1.01    ! [X0] : (! [X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 3.33/1.01    inference(flattening,[],[f44])).
% 3.33/1.01  
% 3.33/1.01  fof(f101,plain,(
% 3.33/1.01    ( ! [X0,X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0) | v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 3.33/1.01    inference(cnf_transformation,[],[f45])).
% 3.33/1.01  
% 3.33/1.01  fof(f97,plain,(
% 3.33/1.01    ( ! [X0,X1] : (v7_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.33/1.01    inference(cnf_transformation,[],[f42])).
% 3.33/1.01  
% 3.33/1.01  fof(f11,axiom,(
% 3.33/1.01    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 3.33/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.01  
% 3.33/1.01  fof(f32,plain,(
% 3.33/1.01    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 3.33/1.01    inference(ennf_transformation,[],[f11])).
% 3.33/1.01  
% 3.33/1.01  fof(f33,plain,(
% 3.33/1.01    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 3.33/1.01    inference(flattening,[],[f32])).
% 3.33/1.01  
% 3.33/1.01  fof(f85,plain,(
% 3.33/1.01    ( ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0)) )),
% 3.33/1.01    inference(cnf_transformation,[],[f33])).
% 3.33/1.01  
% 3.33/1.01  fof(f4,axiom,(
% 3.33/1.01    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.33/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.01  
% 3.33/1.01  fof(f77,plain,(
% 3.33/1.01    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.33/1.01    inference(cnf_transformation,[],[f4])).
% 3.33/1.01  
% 3.33/1.01  fof(f78,plain,(
% 3.33/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.33/1.01    inference(cnf_transformation,[],[f58])).
% 3.33/1.01  
% 3.33/1.01  fof(f7,axiom,(
% 3.33/1.01    ! [X0] : (v1_zfmisc_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_zfmisc_1(X1)))),
% 3.33/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.01  
% 3.33/1.01  fof(f27,plain,(
% 3.33/1.01    ! [X0] : (! [X1] : (v1_zfmisc_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_zfmisc_1(X0))),
% 3.33/1.01    inference(ennf_transformation,[],[f7])).
% 3.33/1.01  
% 3.33/1.01  fof(f81,plain,(
% 3.33/1.01    ( ! [X0,X1] : (v1_zfmisc_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_zfmisc_1(X0)) )),
% 3.33/1.01    inference(cnf_transformation,[],[f27])).
% 3.33/1.01  
% 3.33/1.01  fof(f9,axiom,(
% 3.33/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.33/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.01  
% 3.33/1.01  fof(f29,plain,(
% 3.33/1.01    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.33/1.01    inference(ennf_transformation,[],[f9])).
% 3.33/1.01  
% 3.33/1.01  fof(f83,plain,(
% 3.33/1.01    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.33/1.01    inference(cnf_transformation,[],[f29])).
% 3.33/1.01  
% 3.33/1.01  fof(f91,plain,(
% 3.33/1.01    ( ! [X0,X1] : (v1_tex_2(X1,X0) | ~v1_subset_1(sK2(X0,X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.33/1.01    inference(cnf_transformation,[],[f62])).
% 3.33/1.01  
% 3.33/1.01  fof(f89,plain,(
% 3.33/1.01    ( ! [X0,X1] : (v1_tex_2(X1,X0) | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.33/1.01    inference(cnf_transformation,[],[f62])).
% 3.33/1.01  
% 3.33/1.01  cnf(c_3,plain,
% 3.33/1.01      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 3.33/1.01      inference(cnf_transformation,[],[f74]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_3973,plain,
% 3.33/1.01      ( r1_tarski(X0,X1) = iProver_top
% 3.33/1.01      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 3.33/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_1,plain,
% 3.33/1.01      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.33/1.01      inference(cnf_transformation,[],[f71]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_3975,plain,
% 3.33/1.01      ( r2_hidden(X0,X1) != iProver_top
% 3.33/1.01      | v1_xboole_0(X1) != iProver_top ),
% 3.33/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_4772,plain,
% 3.33/1.01      ( r1_tarski(X0,X1) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 3.33/1.01      inference(superposition,[status(thm)],[c_3973,c_3975]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_21,plain,
% 3.33/1.01      ( v1_subset_1(X0,X1)
% 3.33/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.33/1.01      | X0 = X1 ),
% 3.33/1.01      inference(cnf_transformation,[],[f93]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_7,plain,
% 3.33/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.33/1.01      inference(cnf_transformation,[],[f79]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_288,plain,
% 3.33/1.01      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.33/1.01      inference(prop_impl,[status(thm)],[c_7]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_289,plain,
% 3.33/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.33/1.01      inference(renaming,[status(thm)],[c_288]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_360,plain,
% 3.33/1.01      ( v1_subset_1(X0,X1) | ~ r1_tarski(X0,X1) | X0 = X1 ),
% 3.33/1.01      inference(bin_hyper_res,[status(thm)],[c_21,c_289]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_3946,plain,
% 3.33/1.01      ( X0 = X1
% 3.33/1.01      | v1_subset_1(X0,X1) = iProver_top
% 3.33/1.01      | r1_tarski(X0,X1) != iProver_top ),
% 3.33/1.01      inference(predicate_to_equality,[status(thm)],[c_360]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_6052,plain,
% 3.33/1.01      ( X0 = X1
% 3.33/1.01      | v1_subset_1(X1,X0) = iProver_top
% 3.33/1.01      | v1_xboole_0(X1) != iProver_top ),
% 3.33/1.01      inference(superposition,[status(thm)],[c_4772,c_3946]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_23,plain,
% 3.33/1.01      ( m1_pre_topc(k1_tex_2(X0,X1),X0)
% 3.33/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.33/1.01      | v2_struct_0(X0)
% 3.33/1.01      | ~ l1_pre_topc(X0) ),
% 3.33/1.01      inference(cnf_transformation,[],[f95]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_3959,plain,
% 3.33/1.01      ( m1_pre_topc(k1_tex_2(X0,X1),X0) = iProver_top
% 3.33/1.01      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 3.33/1.01      | v2_struct_0(X0) = iProver_top
% 3.33/1.01      | l1_pre_topc(X0) != iProver_top ),
% 3.33/1.01      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_18,plain,
% 3.33/1.01      ( v1_tex_2(X0,X1)
% 3.33/1.01      | ~ m1_pre_topc(X0,X1)
% 3.33/1.01      | ~ l1_pre_topc(X1)
% 3.33/1.01      | sK2(X1,X0) = u1_struct_0(X0) ),
% 3.33/1.01      inference(cnf_transformation,[],[f90]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_3963,plain,
% 3.33/1.01      ( sK2(X0,X1) = u1_struct_0(X1)
% 3.33/1.01      | v1_tex_2(X1,X0) = iProver_top
% 3.33/1.01      | m1_pre_topc(X1,X0) != iProver_top
% 3.33/1.01      | l1_pre_topc(X0) != iProver_top ),
% 3.33/1.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_6205,plain,
% 3.33/1.01      ( sK2(X0,k1_tex_2(X0,X1)) = u1_struct_0(k1_tex_2(X0,X1))
% 3.33/1.01      | v1_tex_2(k1_tex_2(X0,X1),X0) = iProver_top
% 3.33/1.01      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 3.33/1.01      | v2_struct_0(X0) = iProver_top
% 3.33/1.01      | l1_pre_topc(X0) != iProver_top ),
% 3.33/1.01      inference(superposition,[status(thm)],[c_3959,c_3963]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_32,negated_conjecture,
% 3.33/1.01      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),u1_struct_0(sK4))
% 3.33/1.01      | ~ v1_tex_2(k1_tex_2(sK4,sK5),sK4) ),
% 3.33/1.01      inference(cnf_transformation,[],[f107]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_3952,plain,
% 3.33/1.01      ( v1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),u1_struct_0(sK4)) != iProver_top
% 3.33/1.01      | v1_tex_2(k1_tex_2(sK4,sK5),sK4) != iProver_top ),
% 3.33/1.01      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_7442,plain,
% 3.33/1.01      ( k6_domain_1(u1_struct_0(sK4),sK5) = u1_struct_0(sK4)
% 3.33/1.01      | v1_tex_2(k1_tex_2(sK4,sK5),sK4) != iProver_top
% 3.33/1.01      | v1_xboole_0(k6_domain_1(u1_struct_0(sK4),sK5)) != iProver_top ),
% 3.33/1.01      inference(superposition,[status(thm)],[c_6052,c_3952]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_9106,plain,
% 3.33/1.01      ( k6_domain_1(u1_struct_0(sK4),sK5) = u1_struct_0(sK4)
% 3.33/1.01      | sK2(sK4,k1_tex_2(sK4,sK5)) = u1_struct_0(k1_tex_2(sK4,sK5))
% 3.33/1.01      | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
% 3.33/1.01      | v2_struct_0(sK4) = iProver_top
% 3.33/1.01      | l1_pre_topc(sK4) != iProver_top
% 3.33/1.01      | v1_xboole_0(k6_domain_1(u1_struct_0(sK4),sK5)) != iProver_top ),
% 3.33/1.01      inference(superposition,[status(thm)],[c_6205,c_7442]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_35,negated_conjecture,
% 3.33/1.01      ( l1_pre_topc(sK4) ),
% 3.33/1.01      inference(cnf_transformation,[],[f104]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_38,plain,
% 3.33/1.01      ( l1_pre_topc(sK4) = iProver_top ),
% 3.33/1.01      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_13,plain,
% 3.33/1.01      ( v7_struct_0(X0)
% 3.33/1.01      | ~ l1_struct_0(X0)
% 3.33/1.01      | ~ v1_zfmisc_1(u1_struct_0(X0)) ),
% 3.33/1.01      inference(cnf_transformation,[],[f84]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_92,plain,
% 3.33/1.01      ( v7_struct_0(X0) = iProver_top
% 3.33/1.01      | l1_struct_0(X0) != iProver_top
% 3.33/1.01      | v1_zfmisc_1(u1_struct_0(X0)) != iProver_top ),
% 3.33/1.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_94,plain,
% 3.33/1.01      ( v7_struct_0(sK4) = iProver_top
% 3.33/1.01      | l1_struct_0(sK4) != iProver_top
% 3.33/1.01      | v1_zfmisc_1(u1_struct_0(sK4)) != iProver_top ),
% 3.33/1.01      inference(instantiation,[status(thm)],[c_92]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_11,plain,
% 3.33/1.01      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 3.33/1.01      inference(cnf_transformation,[],[f82]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_96,plain,
% 3.33/1.01      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 3.33/1.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_98,plain,
% 3.33/1.01      ( l1_pre_topc(sK4) != iProver_top
% 3.33/1.01      | l1_struct_0(sK4) = iProver_top ),
% 3.33/1.01      inference(instantiation,[status(thm)],[c_96]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_33,negated_conjecture,
% 3.33/1.01      ( v1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),u1_struct_0(sK4))
% 3.33/1.01      | v1_tex_2(k1_tex_2(sK4,sK5),sK4) ),
% 3.33/1.01      inference(cnf_transformation,[],[f106]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_3951,plain,
% 3.33/1.01      ( v1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),u1_struct_0(sK4)) = iProver_top
% 3.33/1.01      | v1_tex_2(k1_tex_2(sK4,sK5),sK4) = iProver_top ),
% 3.33/1.01      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_31,plain,
% 3.33/1.01      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
% 3.33/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.33/1.01      | v2_struct_0(X0)
% 3.33/1.01      | ~ v7_struct_0(X0)
% 3.33/1.01      | ~ l1_struct_0(X0) ),
% 3.33/1.01      inference(cnf_transformation,[],[f102]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_487,plain,
% 3.33/1.01      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
% 3.33/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.33/1.01      | v2_struct_0(X0)
% 3.33/1.01      | ~ v7_struct_0(X0)
% 3.33/1.01      | ~ l1_pre_topc(X0) ),
% 3.33/1.01      inference(resolution,[status(thm)],[c_11,c_31]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_3945,plain,
% 3.33/1.01      ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) != iProver_top
% 3.33/1.01      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 3.33/1.01      | v2_struct_0(X0) = iProver_top
% 3.33/1.01      | v7_struct_0(X0) != iProver_top
% 3.33/1.01      | l1_pre_topc(X0) != iProver_top ),
% 3.33/1.01      inference(predicate_to_equality,[status(thm)],[c_487]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_5156,plain,
% 3.33/1.01      ( v1_tex_2(k1_tex_2(sK4,sK5),sK4) = iProver_top
% 3.33/1.01      | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
% 3.33/1.01      | v2_struct_0(sK4) = iProver_top
% 3.33/1.01      | v7_struct_0(sK4) != iProver_top
% 3.33/1.01      | l1_pre_topc(sK4) != iProver_top ),
% 3.33/1.01      inference(superposition,[status(thm)],[c_3951,c_3945]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_36,negated_conjecture,
% 3.33/1.01      ( ~ v2_struct_0(sK4) ),
% 3.33/1.01      inference(cnf_transformation,[],[f103]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_37,plain,
% 3.33/1.01      ( v2_struct_0(sK4) != iProver_top ),
% 3.33/1.01      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_34,negated_conjecture,
% 3.33/1.01      ( m1_subset_1(sK5,u1_struct_0(sK4)) ),
% 3.33/1.01      inference(cnf_transformation,[],[f105]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_39,plain,
% 3.33/1.01      ( m1_subset_1(sK5,u1_struct_0(sK4)) = iProver_top ),
% 3.33/1.01      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_41,plain,
% 3.33/1.01      ( v1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),u1_struct_0(sK4)) != iProver_top
% 3.33/1.01      | v1_tex_2(k1_tex_2(sK4,sK5),sK4) != iProver_top ),
% 3.33/1.01      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_15,plain,
% 3.33/1.01      ( ~ v1_tex_2(X0,X1)
% 3.33/1.01      | ~ m1_pre_topc(X0,X1)
% 3.33/1.01      | v2_struct_0(X1)
% 3.33/1.01      | v2_struct_0(X0)
% 3.33/1.01      | ~ v7_struct_0(X1)
% 3.33/1.01      | ~ l1_pre_topc(X1) ),
% 3.33/1.01      inference(cnf_transformation,[],[f87]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_292,plain,
% 3.33/1.01      ( v1_tex_2(k1_tex_2(sK4,sK5),sK4)
% 3.33/1.01      | v1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),u1_struct_0(sK4)) ),
% 3.33/1.01      inference(prop_impl,[status(thm)],[c_33]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_293,plain,
% 3.33/1.01      ( v1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),u1_struct_0(sK4))
% 3.33/1.01      | v1_tex_2(k1_tex_2(sK4,sK5),sK4) ),
% 3.33/1.01      inference(renaming,[status(thm)],[c_292]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_1218,plain,
% 3.33/1.01      ( v1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),u1_struct_0(sK4))
% 3.33/1.01      | ~ m1_pre_topc(X0,X1)
% 3.33/1.01      | v2_struct_0(X0)
% 3.33/1.01      | v2_struct_0(X1)
% 3.33/1.01      | ~ v7_struct_0(X1)
% 3.33/1.01      | ~ l1_pre_topc(X1)
% 3.33/1.01      | k1_tex_2(sK4,sK5) != X0
% 3.33/1.01      | sK4 != X1 ),
% 3.33/1.01      inference(resolution_lifted,[status(thm)],[c_15,c_293]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_1219,plain,
% 3.33/1.01      ( v1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),u1_struct_0(sK4))
% 3.33/1.01      | ~ m1_pre_topc(k1_tex_2(sK4,sK5),sK4)
% 3.33/1.01      | v2_struct_0(k1_tex_2(sK4,sK5))
% 3.33/1.01      | v2_struct_0(sK4)
% 3.33/1.01      | ~ v7_struct_0(sK4)
% 3.33/1.01      | ~ l1_pre_topc(sK4) ),
% 3.33/1.01      inference(unflattening,[status(thm)],[c_1218]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_1221,plain,
% 3.33/1.01      ( ~ v7_struct_0(sK4)
% 3.33/1.01      | v1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),u1_struct_0(sK4))
% 3.33/1.01      | ~ m1_pre_topc(k1_tex_2(sK4,sK5),sK4)
% 3.33/1.01      | v2_struct_0(k1_tex_2(sK4,sK5)) ),
% 3.33/1.01      inference(global_propositional_subsumption,
% 3.33/1.01                [status(thm)],
% 3.33/1.01                [c_1219,c_36,c_35]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_1222,plain,
% 3.33/1.01      ( v1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),u1_struct_0(sK4))
% 3.33/1.01      | ~ m1_pre_topc(k1_tex_2(sK4,sK5),sK4)
% 3.33/1.01      | v2_struct_0(k1_tex_2(sK4,sK5))
% 3.33/1.01      | ~ v7_struct_0(sK4) ),
% 3.33/1.01      inference(renaming,[status(thm)],[c_1221]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_1223,plain,
% 3.33/1.01      ( v1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),u1_struct_0(sK4)) = iProver_top
% 3.33/1.01      | m1_pre_topc(k1_tex_2(sK4,sK5),sK4) != iProver_top
% 3.33/1.01      | v2_struct_0(k1_tex_2(sK4,sK5)) = iProver_top
% 3.33/1.01      | v7_struct_0(sK4) != iProver_top ),
% 3.33/1.01      inference(predicate_to_equality,[status(thm)],[c_1222]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_26,plain,
% 3.33/1.01      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.33/1.01      | v2_struct_0(X1)
% 3.33/1.01      | ~ v2_struct_0(k1_tex_2(X1,X0))
% 3.33/1.01      | ~ l1_pre_topc(X1) ),
% 3.33/1.01      inference(cnf_transformation,[],[f96]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_4250,plain,
% 3.33/1.01      ( ~ m1_subset_1(sK5,u1_struct_0(sK4))
% 3.33/1.01      | ~ v2_struct_0(k1_tex_2(sK4,sK5))
% 3.33/1.01      | v2_struct_0(sK4)
% 3.33/1.01      | ~ l1_pre_topc(sK4) ),
% 3.33/1.01      inference(instantiation,[status(thm)],[c_26]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_4251,plain,
% 3.33/1.01      ( m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
% 3.33/1.01      | v2_struct_0(k1_tex_2(sK4,sK5)) != iProver_top
% 3.33/1.01      | v2_struct_0(sK4) = iProver_top
% 3.33/1.01      | l1_pre_topc(sK4) != iProver_top ),
% 3.33/1.01      inference(predicate_to_equality,[status(thm)],[c_4250]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_4258,plain,
% 3.33/1.01      ( m1_pre_topc(k1_tex_2(sK4,sK5),sK4)
% 3.33/1.01      | ~ m1_subset_1(sK5,u1_struct_0(sK4))
% 3.33/1.01      | v2_struct_0(sK4)
% 3.33/1.01      | ~ l1_pre_topc(sK4) ),
% 3.33/1.01      inference(instantiation,[status(thm)],[c_23]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_4259,plain,
% 3.33/1.01      ( m1_pre_topc(k1_tex_2(sK4,sK5),sK4) = iProver_top
% 3.33/1.01      | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
% 3.33/1.01      | v2_struct_0(sK4) = iProver_top
% 3.33/1.01      | l1_pre_topc(sK4) != iProver_top ),
% 3.33/1.01      inference(predicate_to_equality,[status(thm)],[c_4258]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_5636,plain,
% 3.33/1.01      ( v7_struct_0(sK4) != iProver_top ),
% 3.33/1.01      inference(global_propositional_subsumption,
% 3.33/1.01                [status(thm)],
% 3.33/1.01                [c_5156,c_37,c_38,c_39,c_41,c_1223,c_4251,c_4259]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_30,plain,
% 3.33/1.01      ( v1_subset_1(k6_domain_1(X0,X1),X0)
% 3.33/1.01      | ~ m1_subset_1(X1,X0)
% 3.33/1.01      | v1_zfmisc_1(X0)
% 3.33/1.01      | v1_xboole_0(X0) ),
% 3.33/1.01      inference(cnf_transformation,[],[f101]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_3953,plain,
% 3.33/1.01      ( v1_subset_1(k6_domain_1(X0,X1),X0) = iProver_top
% 3.33/1.01      | m1_subset_1(X1,X0) != iProver_top
% 3.33/1.01      | v1_zfmisc_1(X0) = iProver_top
% 3.33/1.01      | v1_xboole_0(X0) = iProver_top ),
% 3.33/1.01      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_5308,plain,
% 3.33/1.01      ( v1_tex_2(k1_tex_2(sK4,sK5),sK4) != iProver_top
% 3.33/1.01      | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
% 3.33/1.01      | v1_zfmisc_1(u1_struct_0(sK4)) = iProver_top
% 3.33/1.01      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
% 3.33/1.01      inference(superposition,[status(thm)],[c_3953,c_3952]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_5571,plain,
% 3.33/1.01      ( v1_tex_2(k1_tex_2(sK4,sK5),sK4) != iProver_top
% 3.33/1.01      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
% 3.33/1.01      inference(global_propositional_subsumption,
% 3.33/1.01                [status(thm)],
% 3.33/1.01                [c_5308,c_37,c_38,c_39,c_41,c_94,c_98,c_1223,c_4251,
% 3.33/1.01                 c_4259,c_5156]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_9107,plain,
% 3.33/1.01      ( sK2(sK4,k1_tex_2(sK4,sK5)) = u1_struct_0(k1_tex_2(sK4,sK5))
% 3.33/1.01      | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
% 3.33/1.01      | v2_struct_0(sK4) = iProver_top
% 3.33/1.01      | l1_pre_topc(sK4) != iProver_top
% 3.33/1.01      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
% 3.33/1.01      inference(superposition,[status(thm)],[c_6205,c_5571]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_9779,plain,
% 3.33/1.01      ( sK2(sK4,k1_tex_2(sK4,sK5)) = u1_struct_0(k1_tex_2(sK4,sK5))
% 3.33/1.01      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
% 3.33/1.01      inference(global_propositional_subsumption,
% 3.33/1.01                [status(thm)],
% 3.33/1.01                [c_9107,c_37,c_38,c_39]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_3950,plain,
% 3.33/1.01      ( m1_subset_1(sK5,u1_struct_0(sK4)) = iProver_top ),
% 3.33/1.01      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_25,plain,
% 3.33/1.01      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.33/1.01      | v2_struct_0(X1)
% 3.33/1.01      | v7_struct_0(k1_tex_2(X1,X0))
% 3.33/1.01      | ~ l1_pre_topc(X1) ),
% 3.33/1.01      inference(cnf_transformation,[],[f97]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_3957,plain,
% 3.33/1.01      ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
% 3.33/1.01      | v2_struct_0(X1) = iProver_top
% 3.33/1.01      | v7_struct_0(k1_tex_2(X1,X0)) = iProver_top
% 3.33/1.01      | l1_pre_topc(X1) != iProver_top ),
% 3.33/1.01      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_5451,plain,
% 3.33/1.01      ( v2_struct_0(sK4) = iProver_top
% 3.33/1.01      | v7_struct_0(k1_tex_2(sK4,sK5)) = iProver_top
% 3.33/1.01      | l1_pre_topc(sK4) != iProver_top ),
% 3.33/1.01      inference(superposition,[status(thm)],[c_3950,c_3957]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_4247,plain,
% 3.33/1.01      ( ~ m1_subset_1(sK5,u1_struct_0(sK4))
% 3.33/1.01      | v2_struct_0(sK4)
% 3.33/1.01      | v7_struct_0(k1_tex_2(sK4,sK5))
% 3.33/1.01      | ~ l1_pre_topc(sK4) ),
% 3.33/1.01      inference(instantiation,[status(thm)],[c_25]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_4248,plain,
% 3.33/1.01      ( m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
% 3.33/1.01      | v2_struct_0(sK4) = iProver_top
% 3.33/1.01      | v7_struct_0(k1_tex_2(sK4,sK5)) = iProver_top
% 3.33/1.01      | l1_pre_topc(sK4) != iProver_top ),
% 3.33/1.01      inference(predicate_to_equality,[status(thm)],[c_4247]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_5565,plain,
% 3.33/1.01      ( v7_struct_0(k1_tex_2(sK4,sK5)) = iProver_top ),
% 3.33/1.01      inference(global_propositional_subsumption,
% 3.33/1.01                [status(thm)],
% 3.33/1.01                [c_5451,c_37,c_38,c_39,c_4248]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_14,plain,
% 3.33/1.01      ( ~ v7_struct_0(X0)
% 3.33/1.01      | ~ l1_struct_0(X0)
% 3.33/1.01      | v1_zfmisc_1(u1_struct_0(X0)) ),
% 3.33/1.01      inference(cnf_transformation,[],[f85]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_507,plain,
% 3.33/1.01      ( ~ v7_struct_0(X0)
% 3.33/1.01      | ~ l1_pre_topc(X0)
% 3.33/1.01      | v1_zfmisc_1(u1_struct_0(X0)) ),
% 3.33/1.01      inference(resolution,[status(thm)],[c_11,c_14]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_3944,plain,
% 3.33/1.01      ( v7_struct_0(X0) != iProver_top
% 3.33/1.01      | l1_pre_topc(X0) != iProver_top
% 3.33/1.01      | v1_zfmisc_1(u1_struct_0(X0)) = iProver_top ),
% 3.33/1.01      inference(predicate_to_equality,[status(thm)],[c_507]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_6,plain,
% 3.33/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.33/1.01      inference(cnf_transformation,[],[f77]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_3970,plain,
% 3.33/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.33/1.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_8,plain,
% 3.33/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.33/1.01      inference(cnf_transformation,[],[f78]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_3968,plain,
% 3.33/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.33/1.01      | r1_tarski(X0,X1) = iProver_top ),
% 3.33/1.01      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_4522,plain,
% 3.33/1.01      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.33/1.01      inference(superposition,[status(thm)],[c_3970,c_3968]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_10,plain,
% 3.33/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.33/1.01      | ~ v1_zfmisc_1(X1)
% 3.33/1.01      | v1_zfmisc_1(X0) ),
% 3.33/1.01      inference(cnf_transformation,[],[f81]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_359,plain,
% 3.33/1.01      ( ~ r1_tarski(X0,X1) | ~ v1_zfmisc_1(X1) | v1_zfmisc_1(X0) ),
% 3.33/1.01      inference(bin_hyper_res,[status(thm)],[c_10,c_289]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_3947,plain,
% 3.33/1.01      ( r1_tarski(X0,X1) != iProver_top
% 3.33/1.01      | v1_zfmisc_1(X1) != iProver_top
% 3.33/1.01      | v1_zfmisc_1(X0) = iProver_top ),
% 3.33/1.01      inference(predicate_to_equality,[status(thm)],[c_359]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_5031,plain,
% 3.33/1.01      ( v1_zfmisc_1(X0) != iProver_top
% 3.33/1.01      | v1_zfmisc_1(k1_xboole_0) = iProver_top ),
% 3.33/1.01      inference(superposition,[status(thm)],[c_4522,c_3947]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_5132,plain,
% 3.33/1.01      ( v7_struct_0(X0) != iProver_top
% 3.33/1.01      | l1_pre_topc(X0) != iProver_top
% 3.33/1.01      | v1_zfmisc_1(k1_xboole_0) = iProver_top ),
% 3.33/1.01      inference(superposition,[status(thm)],[c_3944,c_5031]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_5717,plain,
% 3.33/1.01      ( l1_pre_topc(k1_tex_2(sK4,sK5)) != iProver_top
% 3.33/1.01      | v1_zfmisc_1(k1_xboole_0) = iProver_top ),
% 3.33/1.01      inference(superposition,[status(thm)],[c_5565,c_5132]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_12,plain,
% 3.33/1.01      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.33/1.01      inference(cnf_transformation,[],[f83]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_4509,plain,
% 3.33/1.01      ( ~ m1_pre_topc(k1_tex_2(sK4,sK5),X0)
% 3.33/1.01      | ~ l1_pre_topc(X0)
% 3.33/1.01      | l1_pre_topc(k1_tex_2(sK4,sK5)) ),
% 3.33/1.01      inference(instantiation,[status(thm)],[c_12]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_4510,plain,
% 3.33/1.01      ( m1_pre_topc(k1_tex_2(sK4,sK5),X0) != iProver_top
% 3.33/1.01      | l1_pre_topc(X0) != iProver_top
% 3.33/1.01      | l1_pre_topc(k1_tex_2(sK4,sK5)) = iProver_top ),
% 3.33/1.01      inference(predicate_to_equality,[status(thm)],[c_4509]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_4512,plain,
% 3.33/1.01      ( m1_pre_topc(k1_tex_2(sK4,sK5),sK4) != iProver_top
% 3.33/1.01      | l1_pre_topc(k1_tex_2(sK4,sK5)) = iProver_top
% 3.33/1.01      | l1_pre_topc(sK4) != iProver_top ),
% 3.33/1.01      inference(instantiation,[status(thm)],[c_4510]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_5840,plain,
% 3.33/1.01      ( v1_zfmisc_1(k1_xboole_0) = iProver_top ),
% 3.33/1.01      inference(global_propositional_subsumption,
% 3.33/1.01                [status(thm)],
% 3.33/1.01                [c_5717,c_37,c_38,c_39,c_4259,c_4512]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_5030,plain,
% 3.33/1.01      ( v1_zfmisc_1(X0) != iProver_top
% 3.33/1.01      | v1_zfmisc_1(X1) = iProver_top
% 3.33/1.01      | v1_xboole_0(X1) != iProver_top ),
% 3.33/1.01      inference(superposition,[status(thm)],[c_4772,c_3947]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_5845,plain,
% 3.33/1.01      ( v1_zfmisc_1(X0) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 3.33/1.01      inference(superposition,[status(thm)],[c_5840,c_5030]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_9786,plain,
% 3.33/1.01      ( sK2(sK4,k1_tex_2(sK4,sK5)) = u1_struct_0(k1_tex_2(sK4,sK5))
% 3.33/1.01      | v1_zfmisc_1(u1_struct_0(sK4)) = iProver_top ),
% 3.33/1.01      inference(superposition,[status(thm)],[c_9779,c_5845]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_9798,plain,
% 3.33/1.01      ( sK2(sK4,k1_tex_2(sK4,sK5)) = u1_struct_0(k1_tex_2(sK4,sK5)) ),
% 3.33/1.01      inference(global_propositional_subsumption,
% 3.33/1.01                [status(thm)],
% 3.33/1.01                [c_9106,c_37,c_38,c_39,c_41,c_94,c_98,c_1223,c_4251,
% 3.33/1.01                 c_4259,c_5156,c_9786]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_17,plain,
% 3.33/1.01      ( ~ v1_subset_1(sK2(X0,X1),u1_struct_0(X0))
% 3.33/1.01      | v1_tex_2(X1,X0)
% 3.33/1.01      | ~ m1_pre_topc(X1,X0)
% 3.33/1.01      | ~ l1_pre_topc(X0) ),
% 3.33/1.01      inference(cnf_transformation,[],[f91]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_3964,plain,
% 3.33/1.01      ( v1_subset_1(sK2(X0,X1),u1_struct_0(X0)) != iProver_top
% 3.33/1.01      | v1_tex_2(X1,X0) = iProver_top
% 3.33/1.01      | m1_pre_topc(X1,X0) != iProver_top
% 3.33/1.01      | l1_pre_topc(X0) != iProver_top ),
% 3.33/1.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_9801,plain,
% 3.33/1.01      ( v1_subset_1(u1_struct_0(k1_tex_2(sK4,sK5)),u1_struct_0(sK4)) != iProver_top
% 3.33/1.01      | v1_tex_2(k1_tex_2(sK4,sK5),sK4) = iProver_top
% 3.33/1.01      | m1_pre_topc(k1_tex_2(sK4,sK5),sK4) != iProver_top
% 3.33/1.01      | l1_pre_topc(sK4) != iProver_top ),
% 3.33/1.01      inference(superposition,[status(thm)],[c_9798,c_3964]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_10000,plain,
% 3.33/1.01      ( v1_subset_1(u1_struct_0(k1_tex_2(sK4,sK5)),u1_struct_0(sK4)) != iProver_top
% 3.33/1.01      | v1_tex_2(k1_tex_2(sK4,sK5),sK4) = iProver_top ),
% 3.33/1.01      inference(global_propositional_subsumption,
% 3.33/1.01                [status(thm)],
% 3.33/1.01                [c_9801,c_37,c_38,c_39,c_4259]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_10007,plain,
% 3.33/1.01      ( u1_struct_0(k1_tex_2(sK4,sK5)) = u1_struct_0(sK4)
% 3.33/1.01      | v1_tex_2(k1_tex_2(sK4,sK5),sK4) = iProver_top
% 3.33/1.01      | v1_xboole_0(u1_struct_0(k1_tex_2(sK4,sK5))) != iProver_top ),
% 3.33/1.01      inference(superposition,[status(thm)],[c_6052,c_10000]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_19,plain,
% 3.33/1.01      ( v1_tex_2(X0,X1)
% 3.33/1.01      | ~ m1_pre_topc(X0,X1)
% 3.33/1.01      | m1_subset_1(sK2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.33/1.01      | ~ l1_pre_topc(X1) ),
% 3.33/1.01      inference(cnf_transformation,[],[f89]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_3962,plain,
% 3.33/1.01      ( v1_tex_2(X0,X1) = iProver_top
% 3.33/1.01      | m1_pre_topc(X0,X1) != iProver_top
% 3.33/1.01      | m1_subset_1(sK2(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 3.33/1.01      | l1_pre_topc(X1) != iProver_top ),
% 3.33/1.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_9802,plain,
% 3.33/1.01      ( v1_tex_2(k1_tex_2(sK4,sK5),sK4) = iProver_top
% 3.33/1.01      | m1_pre_topc(k1_tex_2(sK4,sK5),sK4) != iProver_top
% 3.33/1.01      | m1_subset_1(u1_struct_0(k1_tex_2(sK4,sK5)),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 3.33/1.01      | l1_pre_topc(sK4) != iProver_top ),
% 3.33/1.01      inference(superposition,[status(thm)],[c_9798,c_3962]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_10016,plain,
% 3.33/1.01      ( m1_subset_1(u1_struct_0(k1_tex_2(sK4,sK5)),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 3.33/1.01      | v1_tex_2(k1_tex_2(sK4,sK5),sK4) = iProver_top ),
% 3.33/1.01      inference(global_propositional_subsumption,
% 3.33/1.01                [status(thm)],
% 3.33/1.01                [c_9802,c_37,c_38,c_39,c_4259]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_10017,plain,
% 3.33/1.01      ( v1_tex_2(k1_tex_2(sK4,sK5),sK4) = iProver_top
% 3.33/1.01      | m1_subset_1(u1_struct_0(k1_tex_2(sK4,sK5)),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 3.33/1.01      inference(renaming,[status(thm)],[c_10016]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_10022,plain,
% 3.33/1.01      ( v1_tex_2(k1_tex_2(sK4,sK5),sK4) = iProver_top
% 3.33/1.01      | r1_tarski(u1_struct_0(k1_tex_2(sK4,sK5)),u1_struct_0(sK4)) = iProver_top ),
% 3.33/1.01      inference(superposition,[status(thm)],[c_10017,c_3968]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_10220,plain,
% 3.33/1.01      ( u1_struct_0(k1_tex_2(sK4,sK5)) = u1_struct_0(sK4)
% 3.33/1.01      | v1_subset_1(u1_struct_0(k1_tex_2(sK4,sK5)),u1_struct_0(sK4)) = iProver_top
% 3.33/1.01      | v1_tex_2(k1_tex_2(sK4,sK5),sK4) = iProver_top ),
% 3.33/1.01      inference(superposition,[status(thm)],[c_10022,c_3946]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_10248,plain,
% 3.33/1.01      ( v1_tex_2(k1_tex_2(sK4,sK5),sK4) = iProver_top
% 3.33/1.01      | u1_struct_0(k1_tex_2(sK4,sK5)) = u1_struct_0(sK4) ),
% 3.33/1.01      inference(global_propositional_subsumption,
% 3.33/1.01                [status(thm)],
% 3.33/1.01                [c_10007,c_37,c_38,c_39,c_4259,c_9801,c_10220]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_10249,plain,
% 3.33/1.01      ( u1_struct_0(k1_tex_2(sK4,sK5)) = u1_struct_0(sK4)
% 3.33/1.01      | v1_tex_2(k1_tex_2(sK4,sK5),sK4) = iProver_top ),
% 3.33/1.01      inference(renaming,[status(thm)],[c_10248]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_10255,plain,
% 3.33/1.01      ( k6_domain_1(u1_struct_0(sK4),sK5) = u1_struct_0(sK4)
% 3.33/1.01      | u1_struct_0(k1_tex_2(sK4,sK5)) = u1_struct_0(sK4)
% 3.33/1.01      | v1_xboole_0(k6_domain_1(u1_struct_0(sK4),sK5)) != iProver_top ),
% 3.33/1.01      inference(superposition,[status(thm)],[c_10249,c_7442]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_10256,plain,
% 3.33/1.01      ( u1_struct_0(k1_tex_2(sK4,sK5)) = u1_struct_0(sK4)
% 3.33/1.01      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
% 3.33/1.01      inference(superposition,[status(thm)],[c_10249,c_5571]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_11291,plain,
% 3.33/1.01      ( u1_struct_0(k1_tex_2(sK4,sK5)) = u1_struct_0(sK4)
% 3.33/1.01      | v1_zfmisc_1(u1_struct_0(sK4)) = iProver_top ),
% 3.33/1.01      inference(superposition,[status(thm)],[c_10256,c_5845]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_11325,plain,
% 3.33/1.01      ( u1_struct_0(k1_tex_2(sK4,sK5)) = u1_struct_0(sK4) ),
% 3.33/1.01      inference(global_propositional_subsumption,
% 3.33/1.01                [status(thm)],
% 3.33/1.01                [c_10255,c_37,c_38,c_39,c_41,c_94,c_98,c_1223,c_4251,
% 3.33/1.01                 c_4259,c_5156,c_11291]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_11349,plain,
% 3.33/1.01      ( v7_struct_0(k1_tex_2(sK4,sK5)) != iProver_top
% 3.33/1.01      | l1_pre_topc(k1_tex_2(sK4,sK5)) != iProver_top
% 3.33/1.01      | v1_zfmisc_1(u1_struct_0(sK4)) = iProver_top ),
% 3.33/1.01      inference(superposition,[status(thm)],[c_11325,c_3944]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(contradiction,plain,
% 3.33/1.01      ( $false ),
% 3.33/1.01      inference(minisat,
% 3.33/1.01                [status(thm)],
% 3.33/1.01                [c_11349,c_5636,c_4512,c_4259,c_4248,c_98,c_94,c_39,c_38,
% 3.33/1.01                 c_37]) ).
% 3.33/1.01  
% 3.33/1.01  
% 3.33/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.33/1.01  
% 3.33/1.01  ------                               Statistics
% 3.33/1.01  
% 3.33/1.01  ------ General
% 3.33/1.01  
% 3.33/1.01  abstr_ref_over_cycles:                  0
% 3.33/1.01  abstr_ref_under_cycles:                 0
% 3.33/1.01  gc_basic_clause_elim:                   0
% 3.33/1.01  forced_gc_time:                         0
% 3.33/1.01  parsing_time:                           0.012
% 3.33/1.01  unif_index_cands_time:                  0.
% 3.33/1.01  unif_index_add_time:                    0.
% 3.33/1.01  orderings_time:                         0.
% 3.33/1.01  out_proof_time:                         0.016
% 3.33/1.01  total_time:                             0.329
% 3.33/1.01  num_of_symbols:                         55
% 3.33/1.01  num_of_terms:                           8203
% 3.33/1.01  
% 3.33/1.01  ------ Preprocessing
% 3.33/1.01  
% 3.33/1.01  num_of_splits:                          0
% 3.33/1.01  num_of_split_atoms:                     0
% 3.33/1.01  num_of_reused_defs:                     0
% 3.33/1.01  num_eq_ax_congr_red:                    55
% 3.33/1.01  num_of_sem_filtered_clauses:            1
% 3.33/1.01  num_of_subtypes:                        0
% 3.33/1.01  monotx_restored_types:                  0
% 3.33/1.01  sat_num_of_epr_types:                   0
% 3.33/1.01  sat_num_of_non_cyclic_types:            0
% 3.33/1.01  sat_guarded_non_collapsed_types:        0
% 3.33/1.01  num_pure_diseq_elim:                    0
% 3.33/1.01  simp_replaced_by:                       0
% 3.33/1.01  res_preprocessed:                       170
% 3.33/1.01  prep_upred:                             0
% 3.33/1.01  prep_unflattend:                        88
% 3.33/1.01  smt_new_axioms:                         0
% 3.33/1.01  pred_elim_cands:                        11
% 3.33/1.01  pred_elim:                              1
% 3.33/1.01  pred_elim_cl:                           1
% 3.33/1.01  pred_elim_cycles:                       11
% 3.33/1.01  merged_defs:                            16
% 3.33/1.01  merged_defs_ncl:                        0
% 3.33/1.01  bin_hyper_res:                          18
% 3.33/1.01  prep_cycles:                            4
% 3.33/1.01  pred_elim_time:                         0.066
% 3.33/1.01  splitting_time:                         0.
% 3.33/1.01  sem_filter_time:                        0.
% 3.33/1.01  monotx_time:                            0.001
% 3.33/1.01  subtype_inf_time:                       0.
% 3.33/1.01  
% 3.33/1.01  ------ Problem properties
% 3.33/1.01  
% 3.33/1.01  clauses:                                34
% 3.33/1.01  conjectures:                            5
% 3.33/1.01  epr:                                    8
% 3.33/1.01  horn:                                   22
% 3.33/1.01  ground:                                 5
% 3.33/1.01  unary:                                  5
% 3.33/1.01  binary:                                 12
% 3.33/1.01  lits:                                   94
% 3.33/1.01  lits_eq:                                2
% 3.33/1.01  fd_pure:                                0
% 3.33/1.01  fd_pseudo:                              0
% 3.33/1.01  fd_cond:                                0
% 3.33/1.01  fd_pseudo_cond:                         1
% 3.33/1.01  ac_symbols:                             0
% 3.33/1.01  
% 3.33/1.01  ------ Propositional Solver
% 3.33/1.01  
% 3.33/1.01  prop_solver_calls:                      28
% 3.33/1.01  prop_fast_solver_calls:                 1824
% 3.33/1.01  smt_solver_calls:                       0
% 3.33/1.01  smt_fast_solver_calls:                  0
% 3.33/1.01  prop_num_of_clauses:                    3493
% 3.33/1.01  prop_preprocess_simplified:             11071
% 3.33/1.01  prop_fo_subsumed:                       48
% 3.33/1.01  prop_solver_time:                       0.
% 3.33/1.01  smt_solver_time:                        0.
% 3.33/1.01  smt_fast_solver_time:                   0.
% 3.33/1.01  prop_fast_solver_time:                  0.
% 3.33/1.01  prop_unsat_core_time:                   0.
% 3.33/1.01  
% 3.33/1.01  ------ QBF
% 3.33/1.01  
% 3.33/1.01  qbf_q_res:                              0
% 3.33/1.01  qbf_num_tautologies:                    0
% 3.33/1.01  qbf_prep_cycles:                        0
% 3.33/1.01  
% 3.33/1.01  ------ BMC1
% 3.33/1.01  
% 3.33/1.01  bmc1_current_bound:                     -1
% 3.33/1.01  bmc1_last_solved_bound:                 -1
% 3.33/1.01  bmc1_unsat_core_size:                   -1
% 3.33/1.01  bmc1_unsat_core_parents_size:           -1
% 3.33/1.01  bmc1_merge_next_fun:                    0
% 3.33/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.33/1.01  
% 3.33/1.01  ------ Instantiation
% 3.33/1.01  
% 3.33/1.01  inst_num_of_clauses:                    911
% 3.33/1.01  inst_num_in_passive:                    459
% 3.33/1.01  inst_num_in_active:                     410
% 3.33/1.01  inst_num_in_unprocessed:                42
% 3.33/1.01  inst_num_of_loops:                      530
% 3.33/1.01  inst_num_of_learning_restarts:          0
% 3.33/1.01  inst_num_moves_active_passive:          117
% 3.33/1.01  inst_lit_activity:                      0
% 3.33/1.01  inst_lit_activity_moves:                0
% 3.33/1.01  inst_num_tautologies:                   0
% 3.33/1.01  inst_num_prop_implied:                  0
% 3.33/1.01  inst_num_existing_simplified:           0
% 3.33/1.01  inst_num_eq_res_simplified:             0
% 3.33/1.01  inst_num_child_elim:                    0
% 3.33/1.01  inst_num_of_dismatching_blockings:      257
% 3.33/1.01  inst_num_of_non_proper_insts:           782
% 3.33/1.01  inst_num_of_duplicates:                 0
% 3.33/1.01  inst_inst_num_from_inst_to_res:         0
% 3.33/1.01  inst_dismatching_checking_time:         0.
% 3.33/1.01  
% 3.33/1.01  ------ Resolution
% 3.33/1.01  
% 3.33/1.01  res_num_of_clauses:                     0
% 3.33/1.01  res_num_in_passive:                     0
% 3.33/1.01  res_num_in_active:                      0
% 3.33/1.01  res_num_of_loops:                       174
% 3.33/1.01  res_forward_subset_subsumed:            47
% 3.33/1.01  res_backward_subset_subsumed:           0
% 3.33/1.01  res_forward_subsumed:                   2
% 3.33/1.01  res_backward_subsumed:                  0
% 3.33/1.01  res_forward_subsumption_resolution:     3
% 3.33/1.01  res_backward_subsumption_resolution:    0
% 3.33/1.01  res_clause_to_clause_subsumption:       754
% 3.33/1.01  res_orphan_elimination:                 0
% 3.33/1.01  res_tautology_del:                      101
% 3.33/1.01  res_num_eq_res_simplified:              0
% 3.33/1.01  res_num_sel_changes:                    0
% 3.33/1.01  res_moves_from_active_to_pass:          0
% 3.33/1.01  
% 3.33/1.01  ------ Superposition
% 3.33/1.01  
% 3.33/1.01  sup_time_total:                         0.
% 3.33/1.01  sup_time_generating:                    0.
% 3.33/1.01  sup_time_sim_full:                      0.
% 3.33/1.01  sup_time_sim_immed:                     0.
% 3.33/1.01  
% 3.33/1.01  sup_num_of_clauses:                     176
% 3.33/1.01  sup_num_in_active:                      94
% 3.33/1.01  sup_num_in_passive:                     82
% 3.33/1.01  sup_num_of_loops:                       104
% 3.33/1.01  sup_fw_superposition:                   97
% 3.33/1.01  sup_bw_superposition:                   155
% 3.33/1.01  sup_immediate_simplified:               38
% 3.33/1.01  sup_given_eliminated:                   3
% 3.33/1.01  comparisons_done:                       0
% 3.33/1.01  comparisons_avoided:                    0
% 3.33/1.01  
% 3.33/1.01  ------ Simplifications
% 3.33/1.01  
% 3.33/1.01  
% 3.33/1.01  sim_fw_subset_subsumed:                 14
% 3.33/1.01  sim_bw_subset_subsumed:                 11
% 3.33/1.01  sim_fw_subsumed:                        22
% 3.33/1.01  sim_bw_subsumed:                        3
% 3.33/1.01  sim_fw_subsumption_res:                 3
% 3.33/1.01  sim_bw_subsumption_res:                 0
% 3.33/1.01  sim_tautology_del:                      11
% 3.33/1.01  sim_eq_tautology_del:                   6
% 3.33/1.01  sim_eq_res_simp:                        0
% 3.33/1.01  sim_fw_demodulated:                     0
% 3.33/1.01  sim_bw_demodulated:                     4
% 3.33/1.01  sim_light_normalised:                   6
% 3.33/1.01  sim_joinable_taut:                      0
% 3.33/1.01  sim_joinable_simp:                      0
% 3.33/1.01  sim_ac_normalised:                      0
% 3.33/1.01  sim_smt_subsumption:                    0
% 3.33/1.01  
%------------------------------------------------------------------------------
