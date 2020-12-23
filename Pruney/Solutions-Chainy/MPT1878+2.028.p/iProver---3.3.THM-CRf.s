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
% DateTime   : Thu Dec  3 12:27:03 EST 2020

% Result     : Theorem 2.92s
% Output     : CNFRefutation 2.92s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 472 expanded)
%              Number of clauses        :   76 ( 145 expanded)
%              Number of leaves         :   22 ( 118 expanded)
%              Depth                    :   21
%              Number of atoms          :  479 (2032 expanded)
%              Number of equality atoms :  122 ( 170 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] : m1_subset_1(sK1(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f6,f38])).

fof(f56,plain,(
    ! [X0] : m1_subset_1(sK1(X0),X0) ),
    inference(cnf_transformation,[],[f39])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v4_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_xboole_0(sK2(X0))
        & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ( ~ v1_xboole_0(sK2(X0))
        & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f23,f40])).

fof(f60,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => ~ v3_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => ~ v3_tex_2(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
     => ( v3_tex_2(sK5,X0)
        & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
        & v1_xboole_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( v3_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( v3_tex_2(X1,sK4)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(sK4)
      & v2_pre_topc(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( v3_tex_2(sK5,sK4)
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    & v1_xboole_0(sK5)
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f33,f48,f47])).

fof(f72,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f49])).

fof(f71,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f49])).

fof(f73,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f49])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f34])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f35,f36])).

fof(f51,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK2(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f74,plain,(
    v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f49])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f52,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f76,plain,(
    v3_tex_2(sK5,sK4) ),
    inference(cnf_transformation,[],[f49])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r1_tarski(X1,X2)
                      & v2_tex_2(X2,X0) )
                   => X1 = X2 ) )
              & v2_tex_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X2] :
                    ( X1 = X2
                    | ~ r1_tarski(X1,X2)
                    | ~ v2_tex_2(X2,X0)
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X2] :
                    ( X1 = X2
                    | ~ r1_tarski(X1,X2)
                    | ~ v2_tex_2(X2,X0)
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f42])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X3] :
                    ( X1 = X3
                    | ~ r1_tarski(X1,X3)
                    | ~ v2_tex_2(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f43])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r1_tarski(X1,X2)
          & v2_tex_2(X2,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK3(X0,X1) != X1
        & r1_tarski(X1,sK3(X0,X1))
        & v2_tex_2(sK3(X0,X1),X0)
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ( sK3(X0,X1) != X1
                & r1_tarski(X1,sK3(X0,X1))
                & v2_tex_2(sK3(X0,X1),X0)
                & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X3] :
                    ( X1 = X3
                    | ~ r1_tarski(X1,X3)
                    | ~ v2_tex_2(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f44,f45])).

fof(f65,plain,(
    ! [X0,X3,X1] :
      ( X1 = X3
      | ~ r1_tarski(X1,X3)
      | ~ v2_tex_2(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f5,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f5])).

cnf(c_6,plain,
    ( m1_subset_1(sK1(X0),X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1211,plain,
    ( m1_subset_1(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1208,plain,
    ( k6_domain_1(X0,X1) = k1_tarski(X1)
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2280,plain,
    ( k6_domain_1(X0,sK1(X0)) = k1_tarski(sK1(X0))
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1211,c_1208])).

cnf(c_11,plain,
    ( m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_25,negated_conjecture,
    ( v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_342,plain,
    ( m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_25])).

cnf(c_343,plain,
    ( m1_subset_1(sK2(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_342])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_345,plain,
    ( m1_subset_1(sK2(sK4),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_343,c_26,c_24])).

cnf(c_1202,plain,
    ( m1_subset_1(sK2(sK4),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_345])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_303,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | X0 != X2
    | sK0(X2) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_9])).

cnf(c_304,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_303])).

cnf(c_1204,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_304])).

cnf(c_2220,plain,
    ( v1_xboole_0(u1_struct_0(sK4)) != iProver_top
    | v1_xboole_0(sK2(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1202,c_1204])).

cnf(c_27,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_29,plain,
    ( l1_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_344,plain,
    ( m1_subset_1(sK2(sK4),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_343])).

cnf(c_10,plain,
    ( v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(sK2(X0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_353,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(sK2(X0))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_25])).

cnf(c_354,plain,
    ( v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v1_xboole_0(sK2(sK4)) ),
    inference(unflattening,[status(thm)],[c_353])).

cnf(c_355,plain,
    ( v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v1_xboole_0(sK2(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_354])).

cnf(c_1346,plain,
    ( ~ m1_subset_1(sK2(sK4),k1_zfmisc_1(X0))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(sK2(sK4)) ),
    inference(instantiation,[status(thm)],[c_304])).

cnf(c_1436,plain,
    ( ~ m1_subset_1(sK2(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v1_xboole_0(u1_struct_0(sK4))
    | v1_xboole_0(sK2(sK4)) ),
    inference(instantiation,[status(thm)],[c_1346])).

cnf(c_1437,plain,
    ( m1_subset_1(sK2(sK4),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) != iProver_top
    | v1_xboole_0(sK2(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1436])).

cnf(c_2485,plain,
    ( v1_xboole_0(u1_struct_0(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2220,c_27,c_29,c_344,c_355,c_1437])).

cnf(c_3183,plain,
    ( k6_domain_1(u1_struct_0(sK4),sK1(u1_struct_0(sK4))) = k1_tarski(sK1(u1_struct_0(sK4))) ),
    inference(superposition,[status(thm)],[c_2280,c_2485])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1209,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3420,plain,
    ( m1_subset_1(sK1(u1_struct_0(sK4)),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(k1_tarski(sK1(u1_struct_0(sK4))),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3183,c_1209])).

cnf(c_1340,plain,
    ( m1_subset_1(sK1(u1_struct_0(sK4)),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1342,plain,
    ( m1_subset_1(sK1(u1_struct_0(sK4)),u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1340])).

cnf(c_4373,plain,
    ( m1_subset_1(k1_tarski(sK1(u1_struct_0(sK4))),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3420,c_27,c_29,c_344,c_355,c_1342,c_1437])).

cnf(c_23,negated_conjecture,
    ( v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1206,plain,
    ( v1_xboole_0(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1212,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2093,plain,
    ( sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1206,c_1212])).

cnf(c_21,negated_conjecture,
    ( v3_tex_2(sK5,sK4) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_4,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_18,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ v3_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | ~ l1_pre_topc(X1)
    | X0 = X2 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_459,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ v3_tex_2(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | X2 = X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_24])).

cnf(c_460,plain,
    ( ~ v2_tex_2(X0,sK4)
    | ~ v3_tex_2(X1,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(unflattening,[status(thm)],[c_459])).

cnf(c_586,plain,
    ( ~ v2_tex_2(X0,sK4)
    | ~ v3_tex_2(X1,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | X0 != X2
    | X0 = X1
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_460])).

cnf(c_587,plain,
    ( ~ v2_tex_2(X0,sK4)
    | ~ v3_tex_2(k1_xboole_0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4)))
    | X0 = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_586])).

cnf(c_7,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_601,plain,
    ( ~ v2_tex_2(X0,sK4)
    | ~ v3_tex_2(k1_xboole_0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | X0 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_587,c_7])).

cnf(c_628,plain,
    ( ~ v2_tex_2(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | sK4 != sK4
    | sK5 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_601])).

cnf(c_766,plain,
    ( ~ v2_tex_2(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | sK5 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_628])).

cnf(c_1193,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 = X0
    | v2_tex_2(X0,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_766])).

cnf(c_2195,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 != k1_xboole_0
    | v2_tex_2(X0,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2093,c_1193])).

cnf(c_2204,plain,
    ( k1_xboole_0 = X0
    | v2_tex_2(X0,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2195])).

cnf(c_4381,plain,
    ( k1_tarski(sK1(u1_struct_0(sK4))) = k1_xboole_0
    | v2_tex_2(k1_tarski(sK1(u1_struct_0(sK4))),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4373,c_2204])).

cnf(c_872,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1552,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(u1_struct_0(sK4))
    | u1_struct_0(sK4) != X0 ),
    inference(instantiation,[status(thm)],[c_872])).

cnf(c_2179,plain,
    ( v1_xboole_0(u1_struct_0(sK4))
    | ~ v1_xboole_0(sK5)
    | u1_struct_0(sK4) != sK5 ),
    inference(instantiation,[status(thm)],[c_1552])).

cnf(c_871,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1427,plain,
    ( X0 != X1
    | X0 = sK5
    | sK5 != X1 ),
    inference(instantiation,[status(thm)],[c_871])).

cnf(c_2180,plain,
    ( u1_struct_0(sK4) != X0
    | u1_struct_0(sK4) = sK5
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_1427])).

cnf(c_2183,plain,
    ( u1_struct_0(sK4) = sK5
    | u1_struct_0(sK4) != k1_xboole_0
    | sK5 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2180])).

cnf(c_3181,plain,
    ( k6_domain_1(X0,sK1(X0)) = k1_tarski(sK1(X0))
    | k1_xboole_0 = X0 ),
    inference(superposition,[status(thm)],[c_2280,c_1212])).

cnf(c_20,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_324,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_25])).

cnf(c_325,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK4),X0),sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_324])).

cnf(c_329,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK4),X0),sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_325,c_26,c_24])).

cnf(c_1203,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK4),X0),sK4) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_329])).

cnf(c_3199,plain,
    ( u1_struct_0(sK4) = k1_xboole_0
    | v2_tex_2(k1_tarski(sK1(u1_struct_0(sK4))),sK4) = iProver_top
    | m1_subset_1(sK1(u1_struct_0(sK4)),u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3181,c_1203])).

cnf(c_4823,plain,
    ( k1_tarski(sK1(u1_struct_0(sK4))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4381,c_26,c_24,c_23,c_343,c_354,c_1342,c_1436,c_2093,c_2179,c_2183,c_3199])).

cnf(c_3,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_5,plain,
    ( k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1705,plain,
    ( k1_tarski(X0) != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3,c_5])).

cnf(c_4826,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4823,c_1705])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:32:34 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.92/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.92/1.00  
% 2.92/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.92/1.00  
% 2.92/1.00  ------  iProver source info
% 2.92/1.00  
% 2.92/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.92/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.92/1.00  git: non_committed_changes: false
% 2.92/1.00  git: last_make_outside_of_git: false
% 2.92/1.00  
% 2.92/1.00  ------ 
% 2.92/1.00  
% 2.92/1.00  ------ Input Options
% 2.92/1.00  
% 2.92/1.00  --out_options                           all
% 2.92/1.00  --tptp_safe_out                         true
% 2.92/1.00  --problem_path                          ""
% 2.92/1.00  --include_path                          ""
% 2.92/1.00  --clausifier                            res/vclausify_rel
% 2.92/1.00  --clausifier_options                    --mode clausify
% 2.92/1.00  --stdin                                 false
% 2.92/1.00  --stats_out                             all
% 2.92/1.00  
% 2.92/1.00  ------ General Options
% 2.92/1.00  
% 2.92/1.00  --fof                                   false
% 2.92/1.00  --time_out_real                         305.
% 2.92/1.00  --time_out_virtual                      -1.
% 2.92/1.00  --symbol_type_check                     false
% 2.92/1.00  --clausify_out                          false
% 2.92/1.00  --sig_cnt_out                           false
% 2.92/1.00  --trig_cnt_out                          false
% 2.92/1.00  --trig_cnt_out_tolerance                1.
% 2.92/1.00  --trig_cnt_out_sk_spl                   false
% 2.92/1.00  --abstr_cl_out                          false
% 2.92/1.00  
% 2.92/1.00  ------ Global Options
% 2.92/1.00  
% 2.92/1.00  --schedule                              default
% 2.92/1.00  --add_important_lit                     false
% 2.92/1.00  --prop_solver_per_cl                    1000
% 2.92/1.00  --min_unsat_core                        false
% 2.92/1.00  --soft_assumptions                      false
% 2.92/1.00  --soft_lemma_size                       3
% 2.92/1.00  --prop_impl_unit_size                   0
% 2.92/1.00  --prop_impl_unit                        []
% 2.92/1.00  --share_sel_clauses                     true
% 2.92/1.00  --reset_solvers                         false
% 2.92/1.00  --bc_imp_inh                            [conj_cone]
% 2.92/1.00  --conj_cone_tolerance                   3.
% 2.92/1.00  --extra_neg_conj                        none
% 2.92/1.00  --large_theory_mode                     true
% 2.92/1.00  --prolific_symb_bound                   200
% 2.92/1.00  --lt_threshold                          2000
% 2.92/1.00  --clause_weak_htbl                      true
% 2.92/1.00  --gc_record_bc_elim                     false
% 2.92/1.00  
% 2.92/1.00  ------ Preprocessing Options
% 2.92/1.00  
% 2.92/1.00  --preprocessing_flag                    true
% 2.92/1.00  --time_out_prep_mult                    0.1
% 2.92/1.00  --splitting_mode                        input
% 2.92/1.00  --splitting_grd                         true
% 2.92/1.00  --splitting_cvd                         false
% 2.92/1.00  --splitting_cvd_svl                     false
% 2.92/1.00  --splitting_nvd                         32
% 2.92/1.00  --sub_typing                            true
% 2.92/1.00  --prep_gs_sim                           true
% 2.92/1.00  --prep_unflatten                        true
% 2.92/1.00  --prep_res_sim                          true
% 2.92/1.00  --prep_upred                            true
% 2.92/1.00  --prep_sem_filter                       exhaustive
% 2.92/1.00  --prep_sem_filter_out                   false
% 2.92/1.00  --pred_elim                             true
% 2.92/1.00  --res_sim_input                         true
% 2.92/1.00  --eq_ax_congr_red                       true
% 2.92/1.00  --pure_diseq_elim                       true
% 2.92/1.00  --brand_transform                       false
% 2.92/1.00  --non_eq_to_eq                          false
% 2.92/1.00  --prep_def_merge                        true
% 2.92/1.00  --prep_def_merge_prop_impl              false
% 2.92/1.00  --prep_def_merge_mbd                    true
% 2.92/1.00  --prep_def_merge_tr_red                 false
% 2.92/1.00  --prep_def_merge_tr_cl                  false
% 2.92/1.00  --smt_preprocessing                     true
% 2.92/1.00  --smt_ac_axioms                         fast
% 2.92/1.00  --preprocessed_out                      false
% 2.92/1.00  --preprocessed_stats                    false
% 2.92/1.00  
% 2.92/1.00  ------ Abstraction refinement Options
% 2.92/1.00  
% 2.92/1.00  --abstr_ref                             []
% 2.92/1.00  --abstr_ref_prep                        false
% 2.92/1.00  --abstr_ref_until_sat                   false
% 2.92/1.00  --abstr_ref_sig_restrict                funpre
% 2.92/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.92/1.00  --abstr_ref_under                       []
% 2.92/1.00  
% 2.92/1.00  ------ SAT Options
% 2.92/1.00  
% 2.92/1.00  --sat_mode                              false
% 2.92/1.00  --sat_fm_restart_options                ""
% 2.92/1.00  --sat_gr_def                            false
% 2.92/1.00  --sat_epr_types                         true
% 2.92/1.00  --sat_non_cyclic_types                  false
% 2.92/1.00  --sat_finite_models                     false
% 2.92/1.00  --sat_fm_lemmas                         false
% 2.92/1.00  --sat_fm_prep                           false
% 2.92/1.00  --sat_fm_uc_incr                        true
% 2.92/1.00  --sat_out_model                         small
% 2.92/1.00  --sat_out_clauses                       false
% 2.92/1.00  
% 2.92/1.00  ------ QBF Options
% 2.92/1.00  
% 2.92/1.00  --qbf_mode                              false
% 2.92/1.00  --qbf_elim_univ                         false
% 2.92/1.00  --qbf_dom_inst                          none
% 2.92/1.00  --qbf_dom_pre_inst                      false
% 2.92/1.00  --qbf_sk_in                             false
% 2.92/1.00  --qbf_pred_elim                         true
% 2.92/1.00  --qbf_split                             512
% 2.92/1.00  
% 2.92/1.00  ------ BMC1 Options
% 2.92/1.00  
% 2.92/1.00  --bmc1_incremental                      false
% 2.92/1.00  --bmc1_axioms                           reachable_all
% 2.92/1.00  --bmc1_min_bound                        0
% 2.92/1.00  --bmc1_max_bound                        -1
% 2.92/1.00  --bmc1_max_bound_default                -1
% 2.92/1.00  --bmc1_symbol_reachability              true
% 2.92/1.00  --bmc1_property_lemmas                  false
% 2.92/1.00  --bmc1_k_induction                      false
% 2.92/1.00  --bmc1_non_equiv_states                 false
% 2.92/1.00  --bmc1_deadlock                         false
% 2.92/1.00  --bmc1_ucm                              false
% 2.92/1.00  --bmc1_add_unsat_core                   none
% 2.92/1.00  --bmc1_unsat_core_children              false
% 2.92/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.92/1.00  --bmc1_out_stat                         full
% 2.92/1.00  --bmc1_ground_init                      false
% 2.92/1.00  --bmc1_pre_inst_next_state              false
% 2.92/1.00  --bmc1_pre_inst_state                   false
% 2.92/1.00  --bmc1_pre_inst_reach_state             false
% 2.92/1.00  --bmc1_out_unsat_core                   false
% 2.92/1.00  --bmc1_aig_witness_out                  false
% 2.92/1.00  --bmc1_verbose                          false
% 2.92/1.00  --bmc1_dump_clauses_tptp                false
% 2.92/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.92/1.00  --bmc1_dump_file                        -
% 2.92/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.92/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.92/1.00  --bmc1_ucm_extend_mode                  1
% 2.92/1.00  --bmc1_ucm_init_mode                    2
% 2.92/1.00  --bmc1_ucm_cone_mode                    none
% 2.92/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.92/1.00  --bmc1_ucm_relax_model                  4
% 2.92/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.92/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.92/1.00  --bmc1_ucm_layered_model                none
% 2.92/1.00  --bmc1_ucm_max_lemma_size               10
% 2.92/1.00  
% 2.92/1.00  ------ AIG Options
% 2.92/1.00  
% 2.92/1.00  --aig_mode                              false
% 2.92/1.00  
% 2.92/1.00  ------ Instantiation Options
% 2.92/1.00  
% 2.92/1.00  --instantiation_flag                    true
% 2.92/1.00  --inst_sos_flag                         false
% 2.92/1.00  --inst_sos_phase                        true
% 2.92/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.92/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.92/1.00  --inst_lit_sel_side                     num_symb
% 2.92/1.00  --inst_solver_per_active                1400
% 2.92/1.00  --inst_solver_calls_frac                1.
% 2.92/1.00  --inst_passive_queue_type               priority_queues
% 2.92/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.92/1.00  --inst_passive_queues_freq              [25;2]
% 2.92/1.00  --inst_dismatching                      true
% 2.92/1.00  --inst_eager_unprocessed_to_passive     true
% 2.92/1.00  --inst_prop_sim_given                   true
% 2.92/1.00  --inst_prop_sim_new                     false
% 2.92/1.00  --inst_subs_new                         false
% 2.92/1.00  --inst_eq_res_simp                      false
% 2.92/1.00  --inst_subs_given                       false
% 2.92/1.00  --inst_orphan_elimination               true
% 2.92/1.00  --inst_learning_loop_flag               true
% 2.92/1.00  --inst_learning_start                   3000
% 2.92/1.00  --inst_learning_factor                  2
% 2.92/1.00  --inst_start_prop_sim_after_learn       3
% 2.92/1.00  --inst_sel_renew                        solver
% 2.92/1.00  --inst_lit_activity_flag                true
% 2.92/1.00  --inst_restr_to_given                   false
% 2.92/1.00  --inst_activity_threshold               500
% 2.92/1.00  --inst_out_proof                        true
% 2.92/1.00  
% 2.92/1.00  ------ Resolution Options
% 2.92/1.00  
% 2.92/1.00  --resolution_flag                       true
% 2.92/1.00  --res_lit_sel                           adaptive
% 2.92/1.00  --res_lit_sel_side                      none
% 2.92/1.00  --res_ordering                          kbo
% 2.92/1.00  --res_to_prop_solver                    active
% 2.92/1.00  --res_prop_simpl_new                    false
% 2.92/1.00  --res_prop_simpl_given                  true
% 2.92/1.00  --res_passive_queue_type                priority_queues
% 2.92/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.92/1.00  --res_passive_queues_freq               [15;5]
% 2.92/1.00  --res_forward_subs                      full
% 2.92/1.00  --res_backward_subs                     full
% 2.92/1.00  --res_forward_subs_resolution           true
% 2.92/1.00  --res_backward_subs_resolution          true
% 2.92/1.00  --res_orphan_elimination                true
% 2.92/1.00  --res_time_limit                        2.
% 2.92/1.00  --res_out_proof                         true
% 2.92/1.00  
% 2.92/1.00  ------ Superposition Options
% 2.92/1.00  
% 2.92/1.00  --superposition_flag                    true
% 2.92/1.00  --sup_passive_queue_type                priority_queues
% 2.92/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.92/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.92/1.00  --demod_completeness_check              fast
% 2.92/1.00  --demod_use_ground                      true
% 2.92/1.00  --sup_to_prop_solver                    passive
% 2.92/1.00  --sup_prop_simpl_new                    true
% 2.92/1.00  --sup_prop_simpl_given                  true
% 2.92/1.00  --sup_fun_splitting                     false
% 2.92/1.00  --sup_smt_interval                      50000
% 2.92/1.00  
% 2.92/1.00  ------ Superposition Simplification Setup
% 2.92/1.00  
% 2.92/1.00  --sup_indices_passive                   []
% 2.92/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.92/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.92/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.92/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.92/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.92/1.00  --sup_full_bw                           [BwDemod]
% 2.92/1.00  --sup_immed_triv                        [TrivRules]
% 2.92/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.92/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.92/1.00  --sup_immed_bw_main                     []
% 2.92/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.92/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.92/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.92/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.92/1.00  
% 2.92/1.00  ------ Combination Options
% 2.92/1.00  
% 2.92/1.00  --comb_res_mult                         3
% 2.92/1.00  --comb_sup_mult                         2
% 2.92/1.00  --comb_inst_mult                        10
% 2.92/1.00  
% 2.92/1.00  ------ Debug Options
% 2.92/1.00  
% 2.92/1.00  --dbg_backtrace                         false
% 2.92/1.00  --dbg_dump_prop_clauses                 false
% 2.92/1.00  --dbg_dump_prop_clauses_file            -
% 2.92/1.00  --dbg_out_stat                          false
% 2.92/1.00  ------ Parsing...
% 2.92/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.92/1.00  
% 2.92/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 2.92/1.00  
% 2.92/1.00  ------ Preprocessing... gs_s  sp: 3 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.92/1.00  
% 2.92/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.92/1.00  ------ Proving...
% 2.92/1.00  ------ Problem Properties 
% 2.92/1.00  
% 2.92/1.00  
% 2.92/1.00  clauses                                 22
% 2.92/1.00  conjectures                             2
% 2.92/1.00  EPR                                     3
% 2.92/1.00  Horn                                    17
% 2.92/1.00  unary                                   9
% 2.92/1.00  binary                                  2
% 2.92/1.00  lits                                    50
% 2.92/1.00  lits eq                                 10
% 2.92/1.00  fd_pure                                 0
% 2.92/1.00  fd_pseudo                               0
% 2.92/1.00  fd_cond                                 5
% 2.92/1.00  fd_pseudo_cond                          0
% 2.92/1.00  AC symbols                              0
% 2.92/1.00  
% 2.92/1.00  ------ Schedule dynamic 5 is on 
% 2.92/1.00  
% 2.92/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.92/1.00  
% 2.92/1.00  
% 2.92/1.00  ------ 
% 2.92/1.00  Current options:
% 2.92/1.00  ------ 
% 2.92/1.00  
% 2.92/1.00  ------ Input Options
% 2.92/1.00  
% 2.92/1.00  --out_options                           all
% 2.92/1.00  --tptp_safe_out                         true
% 2.92/1.00  --problem_path                          ""
% 2.92/1.00  --include_path                          ""
% 2.92/1.00  --clausifier                            res/vclausify_rel
% 2.92/1.00  --clausifier_options                    --mode clausify
% 2.92/1.00  --stdin                                 false
% 2.92/1.00  --stats_out                             all
% 2.92/1.00  
% 2.92/1.00  ------ General Options
% 2.92/1.00  
% 2.92/1.00  --fof                                   false
% 2.92/1.00  --time_out_real                         305.
% 2.92/1.00  --time_out_virtual                      -1.
% 2.92/1.00  --symbol_type_check                     false
% 2.92/1.00  --clausify_out                          false
% 2.92/1.00  --sig_cnt_out                           false
% 2.92/1.00  --trig_cnt_out                          false
% 2.92/1.00  --trig_cnt_out_tolerance                1.
% 2.92/1.00  --trig_cnt_out_sk_spl                   false
% 2.92/1.00  --abstr_cl_out                          false
% 2.92/1.00  
% 2.92/1.00  ------ Global Options
% 2.92/1.00  
% 2.92/1.00  --schedule                              default
% 2.92/1.00  --add_important_lit                     false
% 2.92/1.00  --prop_solver_per_cl                    1000
% 2.92/1.00  --min_unsat_core                        false
% 2.92/1.00  --soft_assumptions                      false
% 2.92/1.00  --soft_lemma_size                       3
% 2.92/1.00  --prop_impl_unit_size                   0
% 2.92/1.00  --prop_impl_unit                        []
% 2.92/1.00  --share_sel_clauses                     true
% 2.92/1.00  --reset_solvers                         false
% 2.92/1.00  --bc_imp_inh                            [conj_cone]
% 2.92/1.00  --conj_cone_tolerance                   3.
% 2.92/1.00  --extra_neg_conj                        none
% 2.92/1.00  --large_theory_mode                     true
% 2.92/1.00  --prolific_symb_bound                   200
% 2.92/1.00  --lt_threshold                          2000
% 2.92/1.00  --clause_weak_htbl                      true
% 2.92/1.00  --gc_record_bc_elim                     false
% 2.92/1.00  
% 2.92/1.00  ------ Preprocessing Options
% 2.92/1.00  
% 2.92/1.00  --preprocessing_flag                    true
% 2.92/1.00  --time_out_prep_mult                    0.1
% 2.92/1.00  --splitting_mode                        input
% 2.92/1.00  --splitting_grd                         true
% 2.92/1.00  --splitting_cvd                         false
% 2.92/1.00  --splitting_cvd_svl                     false
% 2.92/1.00  --splitting_nvd                         32
% 2.92/1.00  --sub_typing                            true
% 2.92/1.00  --prep_gs_sim                           true
% 2.92/1.00  --prep_unflatten                        true
% 2.92/1.00  --prep_res_sim                          true
% 2.92/1.00  --prep_upred                            true
% 2.92/1.00  --prep_sem_filter                       exhaustive
% 2.92/1.00  --prep_sem_filter_out                   false
% 2.92/1.00  --pred_elim                             true
% 2.92/1.00  --res_sim_input                         true
% 2.92/1.00  --eq_ax_congr_red                       true
% 2.92/1.00  --pure_diseq_elim                       true
% 2.92/1.00  --brand_transform                       false
% 2.92/1.00  --non_eq_to_eq                          false
% 2.92/1.00  --prep_def_merge                        true
% 2.92/1.00  --prep_def_merge_prop_impl              false
% 2.92/1.00  --prep_def_merge_mbd                    true
% 2.92/1.00  --prep_def_merge_tr_red                 false
% 2.92/1.00  --prep_def_merge_tr_cl                  false
% 2.92/1.00  --smt_preprocessing                     true
% 2.92/1.00  --smt_ac_axioms                         fast
% 2.92/1.00  --preprocessed_out                      false
% 2.92/1.00  --preprocessed_stats                    false
% 2.92/1.00  
% 2.92/1.00  ------ Abstraction refinement Options
% 2.92/1.00  
% 2.92/1.00  --abstr_ref                             []
% 2.92/1.00  --abstr_ref_prep                        false
% 2.92/1.00  --abstr_ref_until_sat                   false
% 2.92/1.00  --abstr_ref_sig_restrict                funpre
% 2.92/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.92/1.00  --abstr_ref_under                       []
% 2.92/1.00  
% 2.92/1.00  ------ SAT Options
% 2.92/1.00  
% 2.92/1.00  --sat_mode                              false
% 2.92/1.00  --sat_fm_restart_options                ""
% 2.92/1.00  --sat_gr_def                            false
% 2.92/1.00  --sat_epr_types                         true
% 2.92/1.00  --sat_non_cyclic_types                  false
% 2.92/1.00  --sat_finite_models                     false
% 2.92/1.00  --sat_fm_lemmas                         false
% 2.92/1.00  --sat_fm_prep                           false
% 2.92/1.00  --sat_fm_uc_incr                        true
% 2.92/1.00  --sat_out_model                         small
% 2.92/1.00  --sat_out_clauses                       false
% 2.92/1.00  
% 2.92/1.00  ------ QBF Options
% 2.92/1.00  
% 2.92/1.00  --qbf_mode                              false
% 2.92/1.00  --qbf_elim_univ                         false
% 2.92/1.00  --qbf_dom_inst                          none
% 2.92/1.00  --qbf_dom_pre_inst                      false
% 2.92/1.00  --qbf_sk_in                             false
% 2.92/1.00  --qbf_pred_elim                         true
% 2.92/1.00  --qbf_split                             512
% 2.92/1.00  
% 2.92/1.00  ------ BMC1 Options
% 2.92/1.00  
% 2.92/1.00  --bmc1_incremental                      false
% 2.92/1.00  --bmc1_axioms                           reachable_all
% 2.92/1.00  --bmc1_min_bound                        0
% 2.92/1.00  --bmc1_max_bound                        -1
% 2.92/1.00  --bmc1_max_bound_default                -1
% 2.92/1.00  --bmc1_symbol_reachability              true
% 2.92/1.00  --bmc1_property_lemmas                  false
% 2.92/1.00  --bmc1_k_induction                      false
% 2.92/1.00  --bmc1_non_equiv_states                 false
% 2.92/1.00  --bmc1_deadlock                         false
% 2.92/1.00  --bmc1_ucm                              false
% 2.92/1.00  --bmc1_add_unsat_core                   none
% 2.92/1.00  --bmc1_unsat_core_children              false
% 2.92/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.92/1.00  --bmc1_out_stat                         full
% 2.92/1.00  --bmc1_ground_init                      false
% 2.92/1.00  --bmc1_pre_inst_next_state              false
% 2.92/1.00  --bmc1_pre_inst_state                   false
% 2.92/1.00  --bmc1_pre_inst_reach_state             false
% 2.92/1.00  --bmc1_out_unsat_core                   false
% 2.92/1.00  --bmc1_aig_witness_out                  false
% 2.92/1.00  --bmc1_verbose                          false
% 2.92/1.00  --bmc1_dump_clauses_tptp                false
% 2.92/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.92/1.00  --bmc1_dump_file                        -
% 2.92/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.92/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.92/1.00  --bmc1_ucm_extend_mode                  1
% 2.92/1.00  --bmc1_ucm_init_mode                    2
% 2.92/1.00  --bmc1_ucm_cone_mode                    none
% 2.92/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.92/1.00  --bmc1_ucm_relax_model                  4
% 2.92/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.92/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.92/1.00  --bmc1_ucm_layered_model                none
% 2.92/1.00  --bmc1_ucm_max_lemma_size               10
% 2.92/1.00  
% 2.92/1.00  ------ AIG Options
% 2.92/1.00  
% 2.92/1.00  --aig_mode                              false
% 2.92/1.00  
% 2.92/1.00  ------ Instantiation Options
% 2.92/1.00  
% 2.92/1.00  --instantiation_flag                    true
% 2.92/1.00  --inst_sos_flag                         false
% 2.92/1.00  --inst_sos_phase                        true
% 2.92/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.92/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.92/1.00  --inst_lit_sel_side                     none
% 2.92/1.00  --inst_solver_per_active                1400
% 2.92/1.00  --inst_solver_calls_frac                1.
% 2.92/1.00  --inst_passive_queue_type               priority_queues
% 2.92/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.92/1.00  --inst_passive_queues_freq              [25;2]
% 2.92/1.00  --inst_dismatching                      true
% 2.92/1.00  --inst_eager_unprocessed_to_passive     true
% 2.92/1.00  --inst_prop_sim_given                   true
% 2.92/1.00  --inst_prop_sim_new                     false
% 2.92/1.00  --inst_subs_new                         false
% 2.92/1.00  --inst_eq_res_simp                      false
% 2.92/1.00  --inst_subs_given                       false
% 2.92/1.00  --inst_orphan_elimination               true
% 2.92/1.00  --inst_learning_loop_flag               true
% 2.92/1.00  --inst_learning_start                   3000
% 2.92/1.00  --inst_learning_factor                  2
% 2.92/1.00  --inst_start_prop_sim_after_learn       3
% 2.92/1.00  --inst_sel_renew                        solver
% 2.92/1.00  --inst_lit_activity_flag                true
% 2.92/1.00  --inst_restr_to_given                   false
% 2.92/1.00  --inst_activity_threshold               500
% 2.92/1.00  --inst_out_proof                        true
% 2.92/1.00  
% 2.92/1.00  ------ Resolution Options
% 2.92/1.00  
% 2.92/1.00  --resolution_flag                       false
% 2.92/1.00  --res_lit_sel                           adaptive
% 2.92/1.00  --res_lit_sel_side                      none
% 2.92/1.00  --res_ordering                          kbo
% 2.92/1.00  --res_to_prop_solver                    active
% 2.92/1.00  --res_prop_simpl_new                    false
% 2.92/1.00  --res_prop_simpl_given                  true
% 2.92/1.00  --res_passive_queue_type                priority_queues
% 2.92/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.92/1.00  --res_passive_queues_freq               [15;5]
% 2.92/1.00  --res_forward_subs                      full
% 2.92/1.00  --res_backward_subs                     full
% 2.92/1.00  --res_forward_subs_resolution           true
% 2.92/1.00  --res_backward_subs_resolution          true
% 2.92/1.00  --res_orphan_elimination                true
% 2.92/1.00  --res_time_limit                        2.
% 2.92/1.00  --res_out_proof                         true
% 2.92/1.00  
% 2.92/1.00  ------ Superposition Options
% 2.92/1.00  
% 2.92/1.00  --superposition_flag                    true
% 2.92/1.00  --sup_passive_queue_type                priority_queues
% 2.92/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.92/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.92/1.00  --demod_completeness_check              fast
% 2.92/1.00  --demod_use_ground                      true
% 2.92/1.00  --sup_to_prop_solver                    passive
% 2.92/1.00  --sup_prop_simpl_new                    true
% 2.92/1.00  --sup_prop_simpl_given                  true
% 2.92/1.00  --sup_fun_splitting                     false
% 2.92/1.00  --sup_smt_interval                      50000
% 2.92/1.00  
% 2.92/1.00  ------ Superposition Simplification Setup
% 2.92/1.00  
% 2.92/1.00  --sup_indices_passive                   []
% 2.92/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.92/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.92/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.92/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.92/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.92/1.00  --sup_full_bw                           [BwDemod]
% 2.92/1.00  --sup_immed_triv                        [TrivRules]
% 2.92/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.92/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.92/1.00  --sup_immed_bw_main                     []
% 2.92/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.92/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.92/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.92/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.92/1.00  
% 2.92/1.00  ------ Combination Options
% 2.92/1.00  
% 2.92/1.00  --comb_res_mult                         3
% 2.92/1.00  --comb_sup_mult                         2
% 2.92/1.00  --comb_inst_mult                        10
% 2.92/1.00  
% 2.92/1.00  ------ Debug Options
% 2.92/1.00  
% 2.92/1.00  --dbg_backtrace                         false
% 2.92/1.00  --dbg_dump_prop_clauses                 false
% 2.92/1.00  --dbg_dump_prop_clauses_file            -
% 2.92/1.00  --dbg_out_stat                          false
% 2.92/1.00  
% 2.92/1.00  
% 2.92/1.00  
% 2.92/1.00  
% 2.92/1.00  ------ Proving...
% 2.92/1.00  
% 2.92/1.00  
% 2.92/1.00  % SZS status Theorem for theBenchmark.p
% 2.92/1.00  
% 2.92/1.00   Resolution empty clause
% 2.92/1.00  
% 2.92/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.92/1.00  
% 2.92/1.00  fof(f6,axiom,(
% 2.92/1.00    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 2.92/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/1.00  
% 2.92/1.00  fof(f38,plain,(
% 2.92/1.00    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK1(X0),X0))),
% 2.92/1.00    introduced(choice_axiom,[])).
% 2.92/1.00  
% 2.92/1.00  fof(f39,plain,(
% 2.92/1.00    ! [X0] : m1_subset_1(sK1(X0),X0)),
% 2.92/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f6,f38])).
% 2.92/1.00  
% 2.92/1.00  fof(f56,plain,(
% 2.92/1.00    ( ! [X0] : (m1_subset_1(sK1(X0),X0)) )),
% 2.92/1.00    inference(cnf_transformation,[],[f39])).
% 2.92/1.00  
% 2.92/1.00  fof(f12,axiom,(
% 2.92/1.00    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 2.92/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/1.00  
% 2.92/1.00  fof(f26,plain,(
% 2.92/1.00    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.92/1.00    inference(ennf_transformation,[],[f12])).
% 2.92/1.00  
% 2.92/1.00  fof(f27,plain,(
% 2.92/1.00    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.92/1.00    inference(flattening,[],[f26])).
% 2.92/1.00  
% 2.92/1.00  fof(f63,plain,(
% 2.92/1.00    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.92/1.00    inference(cnf_transformation,[],[f27])).
% 2.92/1.00  
% 2.92/1.00  fof(f10,axiom,(
% 2.92/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v4_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.92/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/1.00  
% 2.92/1.00  fof(f17,plain,(
% 2.92/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.92/1.00    inference(pure_predicate_removal,[],[f10])).
% 2.92/1.00  
% 2.92/1.00  fof(f22,plain,(
% 2.92/1.00    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.92/1.00    inference(ennf_transformation,[],[f17])).
% 2.92/1.00  
% 2.92/1.00  fof(f23,plain,(
% 2.92/1.00    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.92/1.00    inference(flattening,[],[f22])).
% 2.92/1.00  
% 2.92/1.00  fof(f40,plain,(
% 2.92/1.00    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_xboole_0(sK2(X0)) & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.92/1.00    introduced(choice_axiom,[])).
% 2.92/1.00  
% 2.92/1.00  fof(f41,plain,(
% 2.92/1.00    ! [X0] : ((~v1_xboole_0(sK2(X0)) & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.92/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f23,f40])).
% 2.92/1.00  
% 2.92/1.00  fof(f60,plain,(
% 2.92/1.00    ( ! [X0] : (m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.92/1.00    inference(cnf_transformation,[],[f41])).
% 2.92/1.00  
% 2.92/1.00  fof(f15,conjecture,(
% 2.92/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => ~v3_tex_2(X1,X0)))),
% 2.92/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/1.00  
% 2.92/1.00  fof(f16,negated_conjecture,(
% 2.92/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => ~v3_tex_2(X1,X0)))),
% 2.92/1.00    inference(negated_conjecture,[],[f15])).
% 2.92/1.00  
% 2.92/1.00  fof(f32,plain,(
% 2.92/1.00    ? [X0] : (? [X1] : (v3_tex_2(X1,X0) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.92/1.00    inference(ennf_transformation,[],[f16])).
% 2.92/1.00  
% 2.92/1.00  fof(f33,plain,(
% 2.92/1.00    ? [X0] : (? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.92/1.00    inference(flattening,[],[f32])).
% 2.92/1.00  
% 2.92/1.00  fof(f48,plain,(
% 2.92/1.00    ( ! [X0] : (? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => (v3_tex_2(sK5,X0) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(sK5))) )),
% 2.92/1.00    introduced(choice_axiom,[])).
% 2.92/1.00  
% 2.92/1.00  fof(f47,plain,(
% 2.92/1.00    ? [X0] : (? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (v3_tex_2(X1,sK4) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) & v1_xboole_0(X1)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4))),
% 2.92/1.00    introduced(choice_axiom,[])).
% 2.92/1.00  
% 2.92/1.00  fof(f49,plain,(
% 2.92/1.00    (v3_tex_2(sK5,sK4) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) & v1_xboole_0(sK5)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4)),
% 2.92/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f33,f48,f47])).
% 2.92/1.00  
% 2.92/1.00  fof(f72,plain,(
% 2.92/1.00    v2_pre_topc(sK4)),
% 2.92/1.00    inference(cnf_transformation,[],[f49])).
% 2.92/1.00  
% 2.92/1.00  fof(f71,plain,(
% 2.92/1.00    ~v2_struct_0(sK4)),
% 2.92/1.00    inference(cnf_transformation,[],[f49])).
% 2.92/1.00  
% 2.92/1.00  fof(f73,plain,(
% 2.92/1.00    l1_pre_topc(sK4)),
% 2.92/1.00    inference(cnf_transformation,[],[f49])).
% 2.92/1.00  
% 2.92/1.00  fof(f1,axiom,(
% 2.92/1.00    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.92/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/1.00  
% 2.92/1.00  fof(f34,plain,(
% 2.92/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.92/1.00    inference(nnf_transformation,[],[f1])).
% 2.92/1.00  
% 2.92/1.00  fof(f35,plain,(
% 2.92/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.92/1.00    inference(rectify,[],[f34])).
% 2.92/1.00  
% 2.92/1.00  fof(f36,plain,(
% 2.92/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.92/1.00    introduced(choice_axiom,[])).
% 2.92/1.00  
% 2.92/1.00  fof(f37,plain,(
% 2.92/1.00    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.92/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f35,f36])).
% 2.92/1.00  
% 2.92/1.00  fof(f51,plain,(
% 2.92/1.00    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 2.92/1.00    inference(cnf_transformation,[],[f37])).
% 2.92/1.00  
% 2.92/1.00  fof(f9,axiom,(
% 2.92/1.00    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.92/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/1.00  
% 2.92/1.00  fof(f21,plain,(
% 2.92/1.00    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.92/1.00    inference(ennf_transformation,[],[f9])).
% 2.92/1.00  
% 2.92/1.00  fof(f59,plain,(
% 2.92/1.00    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.92/1.00    inference(cnf_transformation,[],[f21])).
% 2.92/1.00  
% 2.92/1.00  fof(f61,plain,(
% 2.92/1.00    ( ! [X0] : (~v1_xboole_0(sK2(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.92/1.00    inference(cnf_transformation,[],[f41])).
% 2.92/1.00  
% 2.92/1.00  fof(f11,axiom,(
% 2.92/1.00    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.92/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/1.00  
% 2.92/1.00  fof(f24,plain,(
% 2.92/1.00    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.92/1.00    inference(ennf_transformation,[],[f11])).
% 2.92/1.00  
% 2.92/1.00  fof(f25,plain,(
% 2.92/1.00    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.92/1.00    inference(flattening,[],[f24])).
% 2.92/1.00  
% 2.92/1.00  fof(f62,plain,(
% 2.92/1.00    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.92/1.00    inference(cnf_transformation,[],[f25])).
% 2.92/1.00  
% 2.92/1.00  fof(f74,plain,(
% 2.92/1.00    v1_xboole_0(sK5)),
% 2.92/1.00    inference(cnf_transformation,[],[f49])).
% 2.92/1.00  
% 2.92/1.00  fof(f2,axiom,(
% 2.92/1.00    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.92/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/1.00  
% 2.92/1.00  fof(f18,plain,(
% 2.92/1.00    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.92/1.00    inference(ennf_transformation,[],[f2])).
% 2.92/1.00  
% 2.92/1.00  fof(f52,plain,(
% 2.92/1.00    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.92/1.00    inference(cnf_transformation,[],[f18])).
% 2.92/1.00  
% 2.92/1.00  fof(f76,plain,(
% 2.92/1.00    v3_tex_2(sK5,sK4)),
% 2.92/1.00    inference(cnf_transformation,[],[f49])).
% 2.92/1.00  
% 2.92/1.00  fof(f4,axiom,(
% 2.92/1.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.92/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/1.00  
% 2.92/1.00  fof(f54,plain,(
% 2.92/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.92/1.00    inference(cnf_transformation,[],[f4])).
% 2.92/1.00  
% 2.92/1.00  fof(f13,axiom,(
% 2.92/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 2.92/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/1.00  
% 2.92/1.00  fof(f28,plain,(
% 2.92/1.00    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.92/1.00    inference(ennf_transformation,[],[f13])).
% 2.92/1.00  
% 2.92/1.00  fof(f29,plain,(
% 2.92/1.00    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.92/1.00    inference(flattening,[],[f28])).
% 2.92/1.00  
% 2.92/1.00  fof(f42,plain,(
% 2.92/1.00    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.92/1.00    inference(nnf_transformation,[],[f29])).
% 2.92/1.00  
% 2.92/1.00  fof(f43,plain,(
% 2.92/1.00    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.92/1.00    inference(flattening,[],[f42])).
% 2.92/1.00  
% 2.92/1.00  fof(f44,plain,(
% 2.92/1.00    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.92/1.00    inference(rectify,[],[f43])).
% 2.92/1.00  
% 2.92/1.00  fof(f45,plain,(
% 2.92/1.00    ! [X1,X0] : (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK3(X0,X1) != X1 & r1_tarski(X1,sK3(X0,X1)) & v2_tex_2(sK3(X0,X1),X0) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.92/1.00    introduced(choice_axiom,[])).
% 2.92/1.00  
% 2.92/1.00  fof(f46,plain,(
% 2.92/1.00    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (sK3(X0,X1) != X1 & r1_tarski(X1,sK3(X0,X1)) & v2_tex_2(sK3(X0,X1),X0) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.92/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f44,f45])).
% 2.92/1.00  
% 2.92/1.00  fof(f65,plain,(
% 2.92/1.00    ( ! [X0,X3,X1] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.92/1.00    inference(cnf_transformation,[],[f46])).
% 2.92/1.00  
% 2.92/1.00  fof(f7,axiom,(
% 2.92/1.00    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.92/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/1.00  
% 2.92/1.00  fof(f57,plain,(
% 2.92/1.00    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.92/1.00    inference(cnf_transformation,[],[f7])).
% 2.92/1.00  
% 2.92/1.00  fof(f14,axiom,(
% 2.92/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 2.92/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/1.00  
% 2.92/1.00  fof(f30,plain,(
% 2.92/1.00    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.92/1.00    inference(ennf_transformation,[],[f14])).
% 2.92/1.00  
% 2.92/1.00  fof(f31,plain,(
% 2.92/1.00    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.92/1.00    inference(flattening,[],[f30])).
% 2.92/1.00  
% 2.92/1.00  fof(f70,plain,(
% 2.92/1.00    ( ! [X0,X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.92/1.00    inference(cnf_transformation,[],[f31])).
% 2.92/1.00  
% 2.92/1.00  fof(f3,axiom,(
% 2.92/1.00    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 2.92/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/1.00  
% 2.92/1.00  fof(f53,plain,(
% 2.92/1.00    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.92/1.00    inference(cnf_transformation,[],[f3])).
% 2.92/1.00  
% 2.92/1.00  fof(f5,axiom,(
% 2.92/1.00    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 2.92/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/1.00  
% 2.92/1.00  fof(f55,plain,(
% 2.92/1.00    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 2.92/1.00    inference(cnf_transformation,[],[f5])).
% 2.92/1.00  
% 2.92/1.00  cnf(c_6,plain,
% 2.92/1.00      ( m1_subset_1(sK1(X0),X0) ),
% 2.92/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_1211,plain,
% 2.92/1.00      ( m1_subset_1(sK1(X0),X0) = iProver_top ),
% 2.92/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_13,plain,
% 2.92/1.00      ( ~ m1_subset_1(X0,X1)
% 2.92/1.00      | v1_xboole_0(X1)
% 2.92/1.00      | k6_domain_1(X1,X0) = k1_tarski(X0) ),
% 2.92/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_1208,plain,
% 2.92/1.00      ( k6_domain_1(X0,X1) = k1_tarski(X1)
% 2.92/1.00      | m1_subset_1(X1,X0) != iProver_top
% 2.92/1.00      | v1_xboole_0(X0) = iProver_top ),
% 2.92/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_2280,plain,
% 2.92/1.00      ( k6_domain_1(X0,sK1(X0)) = k1_tarski(sK1(X0))
% 2.92/1.00      | v1_xboole_0(X0) = iProver_top ),
% 2.92/1.00      inference(superposition,[status(thm)],[c_1211,c_1208]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_11,plain,
% 2.92/1.00      ( m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 2.92/1.00      | v2_struct_0(X0)
% 2.92/1.00      | ~ v2_pre_topc(X0)
% 2.92/1.00      | ~ l1_pre_topc(X0) ),
% 2.92/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_25,negated_conjecture,
% 2.92/1.00      ( v2_pre_topc(sK4) ),
% 2.92/1.00      inference(cnf_transformation,[],[f72]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_342,plain,
% 2.92/1.00      ( m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 2.92/1.00      | v2_struct_0(X0)
% 2.92/1.00      | ~ l1_pre_topc(X0)
% 2.92/1.00      | sK4 != X0 ),
% 2.92/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_25]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_343,plain,
% 2.92/1.00      ( m1_subset_1(sK2(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 2.92/1.00      | v2_struct_0(sK4)
% 2.92/1.00      | ~ l1_pre_topc(sK4) ),
% 2.92/1.00      inference(unflattening,[status(thm)],[c_342]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_26,negated_conjecture,
% 2.92/1.00      ( ~ v2_struct_0(sK4) ),
% 2.92/1.00      inference(cnf_transformation,[],[f71]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_24,negated_conjecture,
% 2.92/1.00      ( l1_pre_topc(sK4) ),
% 2.92/1.00      inference(cnf_transformation,[],[f73]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_345,plain,
% 2.92/1.00      ( m1_subset_1(sK2(sK4),k1_zfmisc_1(u1_struct_0(sK4))) ),
% 2.92/1.00      inference(global_propositional_subsumption,
% 2.92/1.00                [status(thm)],
% 2.92/1.00                [c_343,c_26,c_24]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_1202,plain,
% 2.92/1.00      ( m1_subset_1(sK2(sK4),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 2.92/1.00      inference(predicate_to_equality,[status(thm)],[c_345]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_0,plain,
% 2.92/1.00      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 2.92/1.00      inference(cnf_transformation,[],[f51]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_9,plain,
% 2.92/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.92/1.00      | ~ r2_hidden(X2,X0)
% 2.92/1.00      | ~ v1_xboole_0(X1) ),
% 2.92/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_303,plain,
% 2.92/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.92/1.00      | ~ v1_xboole_0(X1)
% 2.92/1.00      | v1_xboole_0(X2)
% 2.92/1.00      | X0 != X2
% 2.92/1.00      | sK0(X2) != X3 ),
% 2.92/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_9]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_304,plain,
% 2.92/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.92/1.00      | ~ v1_xboole_0(X1)
% 2.92/1.00      | v1_xboole_0(X0) ),
% 2.92/1.00      inference(unflattening,[status(thm)],[c_303]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_1204,plain,
% 2.92/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.92/1.00      | v1_xboole_0(X1) != iProver_top
% 2.92/1.00      | v1_xboole_0(X0) = iProver_top ),
% 2.92/1.00      inference(predicate_to_equality,[status(thm)],[c_304]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_2220,plain,
% 2.92/1.00      ( v1_xboole_0(u1_struct_0(sK4)) != iProver_top
% 2.92/1.00      | v1_xboole_0(sK2(sK4)) = iProver_top ),
% 2.92/1.00      inference(superposition,[status(thm)],[c_1202,c_1204]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_27,plain,
% 2.92/1.00      ( v2_struct_0(sK4) != iProver_top ),
% 2.92/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_29,plain,
% 2.92/1.00      ( l1_pre_topc(sK4) = iProver_top ),
% 2.92/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_344,plain,
% 2.92/1.00      ( m1_subset_1(sK2(sK4),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 2.92/1.00      | v2_struct_0(sK4) = iProver_top
% 2.92/1.00      | l1_pre_topc(sK4) != iProver_top ),
% 2.92/1.00      inference(predicate_to_equality,[status(thm)],[c_343]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_10,plain,
% 2.92/1.00      ( v2_struct_0(X0)
% 2.92/1.00      | ~ v2_pre_topc(X0)
% 2.92/1.00      | ~ l1_pre_topc(X0)
% 2.92/1.00      | ~ v1_xboole_0(sK2(X0)) ),
% 2.92/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_353,plain,
% 2.92/1.00      ( v2_struct_0(X0)
% 2.92/1.00      | ~ l1_pre_topc(X0)
% 2.92/1.00      | ~ v1_xboole_0(sK2(X0))
% 2.92/1.00      | sK4 != X0 ),
% 2.92/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_25]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_354,plain,
% 2.92/1.00      ( v2_struct_0(sK4) | ~ l1_pre_topc(sK4) | ~ v1_xboole_0(sK2(sK4)) ),
% 2.92/1.00      inference(unflattening,[status(thm)],[c_353]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_355,plain,
% 2.92/1.00      ( v2_struct_0(sK4) = iProver_top
% 2.92/1.00      | l1_pre_topc(sK4) != iProver_top
% 2.92/1.00      | v1_xboole_0(sK2(sK4)) != iProver_top ),
% 2.92/1.00      inference(predicate_to_equality,[status(thm)],[c_354]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_1346,plain,
% 2.92/1.00      ( ~ m1_subset_1(sK2(sK4),k1_zfmisc_1(X0))
% 2.92/1.00      | ~ v1_xboole_0(X0)
% 2.92/1.00      | v1_xboole_0(sK2(sK4)) ),
% 2.92/1.00      inference(instantiation,[status(thm)],[c_304]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_1436,plain,
% 2.92/1.00      ( ~ m1_subset_1(sK2(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 2.92/1.00      | ~ v1_xboole_0(u1_struct_0(sK4))
% 2.92/1.00      | v1_xboole_0(sK2(sK4)) ),
% 2.92/1.00      inference(instantiation,[status(thm)],[c_1346]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_1437,plain,
% 2.92/1.00      ( m1_subset_1(sK2(sK4),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.92/1.00      | v1_xboole_0(u1_struct_0(sK4)) != iProver_top
% 2.92/1.00      | v1_xboole_0(sK2(sK4)) = iProver_top ),
% 2.92/1.00      inference(predicate_to_equality,[status(thm)],[c_1436]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_2485,plain,
% 2.92/1.00      ( v1_xboole_0(u1_struct_0(sK4)) != iProver_top ),
% 2.92/1.00      inference(global_propositional_subsumption,
% 2.92/1.00                [status(thm)],
% 2.92/1.00                [c_2220,c_27,c_29,c_344,c_355,c_1437]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_3183,plain,
% 2.92/1.00      ( k6_domain_1(u1_struct_0(sK4),sK1(u1_struct_0(sK4))) = k1_tarski(sK1(u1_struct_0(sK4))) ),
% 2.92/1.00      inference(superposition,[status(thm)],[c_2280,c_2485]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_12,plain,
% 2.92/1.00      ( ~ m1_subset_1(X0,X1)
% 2.92/1.00      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
% 2.92/1.00      | v1_xboole_0(X1) ),
% 2.92/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_1209,plain,
% 2.92/1.00      ( m1_subset_1(X0,X1) != iProver_top
% 2.92/1.00      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top
% 2.92/1.00      | v1_xboole_0(X1) = iProver_top ),
% 2.92/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_3420,plain,
% 2.92/1.00      ( m1_subset_1(sK1(u1_struct_0(sK4)),u1_struct_0(sK4)) != iProver_top
% 2.92/1.00      | m1_subset_1(k1_tarski(sK1(u1_struct_0(sK4))),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 2.92/1.00      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
% 2.92/1.00      inference(superposition,[status(thm)],[c_3183,c_1209]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_1340,plain,
% 2.92/1.00      ( m1_subset_1(sK1(u1_struct_0(sK4)),u1_struct_0(sK4)) ),
% 2.92/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_1342,plain,
% 2.92/1.00      ( m1_subset_1(sK1(u1_struct_0(sK4)),u1_struct_0(sK4)) = iProver_top ),
% 2.92/1.00      inference(predicate_to_equality,[status(thm)],[c_1340]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_4373,plain,
% 2.92/1.00      ( m1_subset_1(k1_tarski(sK1(u1_struct_0(sK4))),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 2.92/1.00      inference(global_propositional_subsumption,
% 2.92/1.00                [status(thm)],
% 2.92/1.00                [c_3420,c_27,c_29,c_344,c_355,c_1342,c_1437]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_23,negated_conjecture,
% 2.92/1.00      ( v1_xboole_0(sK5) ),
% 2.92/1.00      inference(cnf_transformation,[],[f74]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_1206,plain,
% 2.92/1.00      ( v1_xboole_0(sK5) = iProver_top ),
% 2.92/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_2,plain,
% 2.92/1.00      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 2.92/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_1212,plain,
% 2.92/1.00      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 2.92/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_2093,plain,
% 2.92/1.00      ( sK5 = k1_xboole_0 ),
% 2.92/1.00      inference(superposition,[status(thm)],[c_1206,c_1212]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_21,negated_conjecture,
% 2.92/1.00      ( v3_tex_2(sK5,sK4) ),
% 2.92/1.00      inference(cnf_transformation,[],[f76]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_4,plain,
% 2.92/1.00      ( r1_tarski(k1_xboole_0,X0) ),
% 2.92/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_18,plain,
% 2.92/1.00      ( ~ v2_tex_2(X0,X1)
% 2.92/1.00      | ~ v3_tex_2(X2,X1)
% 2.92/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.92/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.92/1.00      | ~ r1_tarski(X2,X0)
% 2.92/1.00      | ~ l1_pre_topc(X1)
% 2.92/1.00      | X0 = X2 ),
% 2.92/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_459,plain,
% 2.92/1.00      ( ~ v2_tex_2(X0,X1)
% 2.92/1.00      | ~ v3_tex_2(X2,X1)
% 2.92/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.92/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.92/1.00      | ~ r1_tarski(X2,X0)
% 2.92/1.00      | X2 = X0
% 2.92/1.00      | sK4 != X1 ),
% 2.92/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_24]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_460,plain,
% 2.92/1.00      ( ~ v2_tex_2(X0,sK4)
% 2.92/1.00      | ~ v3_tex_2(X1,sK4)
% 2.92/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.92/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.92/1.00      | ~ r1_tarski(X1,X0)
% 2.92/1.00      | X1 = X0 ),
% 2.92/1.00      inference(unflattening,[status(thm)],[c_459]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_586,plain,
% 2.92/1.00      ( ~ v2_tex_2(X0,sK4)
% 2.92/1.00      | ~ v3_tex_2(X1,sK4)
% 2.92/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.92/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.92/1.00      | X0 != X2
% 2.92/1.00      | X0 = X1
% 2.92/1.00      | k1_xboole_0 != X1 ),
% 2.92/1.00      inference(resolution_lifted,[status(thm)],[c_4,c_460]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_587,plain,
% 2.92/1.00      ( ~ v2_tex_2(X0,sK4)
% 2.92/1.00      | ~ v3_tex_2(k1_xboole_0,sK4)
% 2.92/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.92/1.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.92/1.00      | X0 = k1_xboole_0 ),
% 2.92/1.00      inference(unflattening,[status(thm)],[c_586]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_7,plain,
% 2.92/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.92/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_601,plain,
% 2.92/1.00      ( ~ v2_tex_2(X0,sK4)
% 2.92/1.00      | ~ v3_tex_2(k1_xboole_0,sK4)
% 2.92/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.92/1.00      | X0 = k1_xboole_0 ),
% 2.92/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_587,c_7]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_628,plain,
% 2.92/1.00      ( ~ v2_tex_2(X0,sK4)
% 2.92/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.92/1.00      | sK4 != sK4
% 2.92/1.00      | sK5 != k1_xboole_0
% 2.92/1.00      | k1_xboole_0 = X0 ),
% 2.92/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_601]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_766,plain,
% 2.92/1.00      ( ~ v2_tex_2(X0,sK4)
% 2.92/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.92/1.00      | sK5 != k1_xboole_0
% 2.92/1.00      | k1_xboole_0 = X0 ),
% 2.92/1.00      inference(equality_resolution_simp,[status(thm)],[c_628]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_1193,plain,
% 2.92/1.00      ( sK5 != k1_xboole_0
% 2.92/1.00      | k1_xboole_0 = X0
% 2.92/1.00      | v2_tex_2(X0,sK4) != iProver_top
% 2.92/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 2.92/1.00      inference(predicate_to_equality,[status(thm)],[c_766]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_2195,plain,
% 2.92/1.00      ( k1_xboole_0 = X0
% 2.92/1.00      | k1_xboole_0 != k1_xboole_0
% 2.92/1.00      | v2_tex_2(X0,sK4) != iProver_top
% 2.92/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 2.92/1.00      inference(demodulation,[status(thm)],[c_2093,c_1193]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_2204,plain,
% 2.92/1.00      ( k1_xboole_0 = X0
% 2.92/1.00      | v2_tex_2(X0,sK4) != iProver_top
% 2.92/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 2.92/1.00      inference(equality_resolution_simp,[status(thm)],[c_2195]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_4381,plain,
% 2.92/1.00      ( k1_tarski(sK1(u1_struct_0(sK4))) = k1_xboole_0
% 2.92/1.00      | v2_tex_2(k1_tarski(sK1(u1_struct_0(sK4))),sK4) != iProver_top ),
% 2.92/1.00      inference(superposition,[status(thm)],[c_4373,c_2204]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_872,plain,
% 2.92/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 2.92/1.00      theory(equality) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_1552,plain,
% 2.92/1.00      ( ~ v1_xboole_0(X0)
% 2.92/1.00      | v1_xboole_0(u1_struct_0(sK4))
% 2.92/1.00      | u1_struct_0(sK4) != X0 ),
% 2.92/1.00      inference(instantiation,[status(thm)],[c_872]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_2179,plain,
% 2.92/1.00      ( v1_xboole_0(u1_struct_0(sK4))
% 2.92/1.00      | ~ v1_xboole_0(sK5)
% 2.92/1.00      | u1_struct_0(sK4) != sK5 ),
% 2.92/1.00      inference(instantiation,[status(thm)],[c_1552]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_871,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_1427,plain,
% 2.92/1.00      ( X0 != X1 | X0 = sK5 | sK5 != X1 ),
% 2.92/1.00      inference(instantiation,[status(thm)],[c_871]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_2180,plain,
% 2.92/1.00      ( u1_struct_0(sK4) != X0 | u1_struct_0(sK4) = sK5 | sK5 != X0 ),
% 2.92/1.00      inference(instantiation,[status(thm)],[c_1427]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_2183,plain,
% 2.92/1.00      ( u1_struct_0(sK4) = sK5
% 2.92/1.00      | u1_struct_0(sK4) != k1_xboole_0
% 2.92/1.00      | sK5 != k1_xboole_0 ),
% 2.92/1.00      inference(instantiation,[status(thm)],[c_2180]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_3181,plain,
% 2.92/1.00      ( k6_domain_1(X0,sK1(X0)) = k1_tarski(sK1(X0)) | k1_xboole_0 = X0 ),
% 2.92/1.00      inference(superposition,[status(thm)],[c_2280,c_1212]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_20,plain,
% 2.92/1.00      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
% 2.92/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.92/1.00      | v2_struct_0(X0)
% 2.92/1.00      | ~ v2_pre_topc(X0)
% 2.92/1.00      | ~ l1_pre_topc(X0) ),
% 2.92/1.00      inference(cnf_transformation,[],[f70]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_324,plain,
% 2.92/1.00      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
% 2.92/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.92/1.00      | v2_struct_0(X0)
% 2.92/1.00      | ~ l1_pre_topc(X0)
% 2.92/1.00      | sK4 != X0 ),
% 2.92/1.00      inference(resolution_lifted,[status(thm)],[c_20,c_25]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_325,plain,
% 2.92/1.00      ( v2_tex_2(k6_domain_1(u1_struct_0(sK4),X0),sK4)
% 2.92/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.92/1.00      | v2_struct_0(sK4)
% 2.92/1.00      | ~ l1_pre_topc(sK4) ),
% 2.92/1.00      inference(unflattening,[status(thm)],[c_324]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_329,plain,
% 2.92/1.00      ( v2_tex_2(k6_domain_1(u1_struct_0(sK4),X0),sK4)
% 2.92/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 2.92/1.00      inference(global_propositional_subsumption,
% 2.92/1.00                [status(thm)],
% 2.92/1.00                [c_325,c_26,c_24]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_1203,plain,
% 2.92/1.00      ( v2_tex_2(k6_domain_1(u1_struct_0(sK4),X0),sK4) = iProver_top
% 2.92/1.00      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top ),
% 2.92/1.00      inference(predicate_to_equality,[status(thm)],[c_329]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_3199,plain,
% 2.92/1.00      ( u1_struct_0(sK4) = k1_xboole_0
% 2.92/1.00      | v2_tex_2(k1_tarski(sK1(u1_struct_0(sK4))),sK4) = iProver_top
% 2.92/1.00      | m1_subset_1(sK1(u1_struct_0(sK4)),u1_struct_0(sK4)) != iProver_top ),
% 2.92/1.00      inference(superposition,[status(thm)],[c_3181,c_1203]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_4823,plain,
% 2.92/1.00      ( k1_tarski(sK1(u1_struct_0(sK4))) = k1_xboole_0 ),
% 2.92/1.00      inference(global_propositional_subsumption,
% 2.92/1.00                [status(thm)],
% 2.92/1.00                [c_4381,c_26,c_24,c_23,c_343,c_354,c_1342,c_1436,c_2093,
% 2.92/1.00                 c_2179,c_2183,c_3199]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_3,plain,
% 2.92/1.00      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 2.92/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_5,plain,
% 2.92/1.00      ( k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
% 2.92/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_1705,plain,
% 2.92/1.00      ( k1_tarski(X0) != k1_xboole_0 ),
% 2.92/1.00      inference(superposition,[status(thm)],[c_3,c_5]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_4826,plain,
% 2.92/1.00      ( $false ),
% 2.92/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_4823,c_1705]) ).
% 2.92/1.00  
% 2.92/1.00  
% 2.92/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.92/1.00  
% 2.92/1.00  ------                               Statistics
% 2.92/1.00  
% 2.92/1.00  ------ General
% 2.92/1.00  
% 2.92/1.00  abstr_ref_over_cycles:                  0
% 2.92/1.00  abstr_ref_under_cycles:                 0
% 2.92/1.00  gc_basic_clause_elim:                   0
% 2.92/1.00  forced_gc_time:                         0
% 2.92/1.00  parsing_time:                           0.019
% 2.92/1.00  unif_index_cands_time:                  0.
% 2.92/1.00  unif_index_add_time:                    0.
% 2.92/1.00  orderings_time:                         0.
% 2.92/1.00  out_proof_time:                         0.009
% 2.92/1.00  total_time:                             0.179
% 2.92/1.00  num_of_symbols:                         53
% 2.92/1.00  num_of_terms:                           3535
% 2.92/1.00  
% 2.92/1.00  ------ Preprocessing
% 2.92/1.00  
% 2.92/1.00  num_of_splits:                          3
% 2.92/1.00  num_of_split_atoms:                     1
% 2.92/1.00  num_of_reused_defs:                     2
% 2.92/1.00  num_eq_ax_congr_red:                    17
% 2.92/1.00  num_of_sem_filtered_clauses:            1
% 2.92/1.00  num_of_subtypes:                        0
% 2.92/1.00  monotx_restored_types:                  0
% 2.92/1.00  sat_num_of_epr_types:                   0
% 2.92/1.00  sat_num_of_non_cyclic_types:            0
% 2.92/1.00  sat_guarded_non_collapsed_types:        0
% 2.92/1.00  num_pure_diseq_elim:                    0
% 2.92/1.00  simp_replaced_by:                       0
% 2.92/1.00  res_preprocessed:                       109
% 2.92/1.00  prep_upred:                             0
% 2.92/1.00  prep_unflattend:                        27
% 2.92/1.00  smt_new_axioms:                         0
% 2.92/1.00  pred_elim_cands:                        3
% 2.92/1.00  pred_elim:                              6
% 2.92/1.00  pred_elim_cl:                           8
% 2.92/1.00  pred_elim_cycles:                       9
% 2.92/1.00  merged_defs:                            0
% 2.92/1.00  merged_defs_ncl:                        0
% 2.92/1.00  bin_hyper_res:                          0
% 2.92/1.00  prep_cycles:                            4
% 2.92/1.00  pred_elim_time:                         0.01
% 2.92/1.00  splitting_time:                         0.
% 2.92/1.00  sem_filter_time:                        0.
% 2.92/1.00  monotx_time:                            0.
% 2.92/1.00  subtype_inf_time:                       0.
% 2.92/1.00  
% 2.92/1.00  ------ Problem properties
% 2.92/1.00  
% 2.92/1.00  clauses:                                22
% 2.92/1.00  conjectures:                            2
% 2.92/1.00  epr:                                    3
% 2.92/1.00  horn:                                   17
% 2.92/1.00  ground:                                 8
% 2.92/1.00  unary:                                  9
% 2.92/1.00  binary:                                 2
% 2.92/1.00  lits:                                   50
% 2.92/1.00  lits_eq:                                10
% 2.92/1.00  fd_pure:                                0
% 2.92/1.00  fd_pseudo:                              0
% 2.92/1.00  fd_cond:                                5
% 2.92/1.00  fd_pseudo_cond:                         0
% 2.92/1.00  ac_symbols:                             0
% 2.92/1.00  
% 2.92/1.00  ------ Propositional Solver
% 2.92/1.00  
% 2.92/1.00  prop_solver_calls:                      27
% 2.92/1.00  prop_fast_solver_calls:                 796
% 2.92/1.00  smt_solver_calls:                       0
% 2.92/1.00  smt_fast_solver_calls:                  0
% 2.92/1.00  prop_num_of_clauses:                    1720
% 2.92/1.00  prop_preprocess_simplified:             4938
% 2.92/1.00  prop_fo_subsumed:                       35
% 2.92/1.00  prop_solver_time:                       0.
% 2.92/1.00  smt_solver_time:                        0.
% 2.92/1.00  smt_fast_solver_time:                   0.
% 2.92/1.00  prop_fast_solver_time:                  0.
% 2.92/1.00  prop_unsat_core_time:                   0.
% 2.92/1.00  
% 2.92/1.00  ------ QBF
% 2.92/1.00  
% 2.92/1.00  qbf_q_res:                              0
% 2.92/1.00  qbf_num_tautologies:                    0
% 2.92/1.00  qbf_prep_cycles:                        0
% 2.92/1.00  
% 2.92/1.00  ------ BMC1
% 2.92/1.00  
% 2.92/1.00  bmc1_current_bound:                     -1
% 2.92/1.00  bmc1_last_solved_bound:                 -1
% 2.92/1.00  bmc1_unsat_core_size:                   -1
% 2.92/1.00  bmc1_unsat_core_parents_size:           -1
% 2.92/1.00  bmc1_merge_next_fun:                    0
% 2.92/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.92/1.00  
% 2.92/1.00  ------ Instantiation
% 2.92/1.00  
% 2.92/1.00  inst_num_of_clauses:                    521
% 2.92/1.00  inst_num_in_passive:                    3
% 2.92/1.00  inst_num_in_active:                     296
% 2.92/1.00  inst_num_in_unprocessed:                222
% 2.92/1.00  inst_num_of_loops:                      320
% 2.92/1.00  inst_num_of_learning_restarts:          0
% 2.92/1.00  inst_num_moves_active_passive:          22
% 2.92/1.00  inst_lit_activity:                      0
% 2.92/1.00  inst_lit_activity_moves:                0
% 2.92/1.00  inst_num_tautologies:                   0
% 2.92/1.00  inst_num_prop_implied:                  0
% 2.92/1.00  inst_num_existing_simplified:           0
% 2.92/1.00  inst_num_eq_res_simplified:             0
% 2.92/1.00  inst_num_child_elim:                    0
% 2.92/1.00  inst_num_of_dismatching_blockings:      192
% 2.92/1.00  inst_num_of_non_proper_insts:           456
% 2.92/1.00  inst_num_of_duplicates:                 0
% 2.92/1.00  inst_inst_num_from_inst_to_res:         0
% 2.92/1.00  inst_dismatching_checking_time:         0.
% 2.92/1.00  
% 2.92/1.00  ------ Resolution
% 2.92/1.00  
% 2.92/1.00  res_num_of_clauses:                     0
% 2.92/1.00  res_num_in_passive:                     0
% 2.92/1.00  res_num_in_active:                      0
% 2.92/1.00  res_num_of_loops:                       113
% 2.92/1.00  res_forward_subset_subsumed:            33
% 2.92/1.00  res_backward_subset_subsumed:           0
% 2.92/1.00  res_forward_subsumed:                   0
% 2.92/1.00  res_backward_subsumed:                  0
% 2.92/1.00  res_forward_subsumption_resolution:     5
% 2.92/1.00  res_backward_subsumption_resolution:    0
% 2.92/1.00  res_clause_to_clause_subsumption:       131
% 2.92/1.00  res_orphan_elimination:                 0
% 2.92/1.00  res_tautology_del:                      39
% 2.92/1.00  res_num_eq_res_simplified:              1
% 2.92/1.00  res_num_sel_changes:                    0
% 2.92/1.00  res_moves_from_active_to_pass:          0
% 2.92/1.00  
% 2.92/1.00  ------ Superposition
% 2.92/1.00  
% 2.92/1.00  sup_time_total:                         0.
% 2.92/1.00  sup_time_generating:                    0.
% 2.92/1.00  sup_time_sim_full:                      0.
% 2.92/1.00  sup_time_sim_immed:                     0.
% 2.92/1.00  
% 2.92/1.00  sup_num_of_clauses:                     82
% 2.92/1.00  sup_num_in_active:                      55
% 2.92/1.00  sup_num_in_passive:                     27
% 2.92/1.00  sup_num_of_loops:                       63
% 2.92/1.00  sup_fw_superposition:                   32
% 2.92/1.00  sup_bw_superposition:                   56
% 2.92/1.00  sup_immediate_simplified:               14
% 2.92/1.00  sup_given_eliminated:                   0
% 2.92/1.00  comparisons_done:                       0
% 2.92/1.00  comparisons_avoided:                    23
% 2.92/1.00  
% 2.92/1.00  ------ Simplifications
% 2.92/1.00  
% 2.92/1.00  
% 2.92/1.00  sim_fw_subset_subsumed:                 10
% 2.92/1.00  sim_bw_subset_subsumed:                 5
% 2.92/1.00  sim_fw_subsumed:                        3
% 2.92/1.00  sim_bw_subsumed:                        0
% 2.92/1.00  sim_fw_subsumption_res:                 1
% 2.92/1.00  sim_bw_subsumption_res:                 0
% 2.92/1.00  sim_tautology_del:                      3
% 2.92/1.00  sim_eq_tautology_del:                   3
% 2.92/1.00  sim_eq_res_simp:                        1
% 2.92/1.00  sim_fw_demodulated:                     0
% 2.92/1.00  sim_bw_demodulated:                     4
% 2.92/1.00  sim_light_normalised:                   2
% 2.92/1.00  sim_joinable_taut:                      0
% 2.92/1.00  sim_joinable_simp:                      0
% 2.92/1.00  sim_ac_normalised:                      0
% 2.92/1.00  sim_smt_subsumption:                    0
% 2.92/1.00  
%------------------------------------------------------------------------------
