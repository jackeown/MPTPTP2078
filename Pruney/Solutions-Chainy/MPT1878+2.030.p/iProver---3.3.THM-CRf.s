%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:27:03 EST 2020

% Result     : Theorem 2.70s
% Output     : CNFRefutation 2.70s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 867 expanded)
%              Number of clauses        :   76 ( 234 expanded)
%              Number of leaves         :   19 ( 218 expanded)
%              Depth                    :   21
%              Number of atoms          :  482 (3881 expanded)
%              Number of equality atoms :  110 ( 188 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f33])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).

fof(f48,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v4_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_xboole_0(sK1(X0))
        & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ( ~ v1_xboole_0(sK1(X0))
        & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f37])).

fof(f56,plain,(
    ! [X0] :
      ( m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => ~ v3_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => ~ v3_tex_2(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
     => ( v3_tex_2(sK4,X0)
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0)))
        & v1_xboole_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( v3_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( v3_tex_2(X1,sK3)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( v3_tex_2(sK4,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    & v1_xboole_0(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f32,f45,f44])).

fof(f68,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f67,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f69,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK1(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f47,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f70,plain,(
    v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f46])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f49,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f72,plain,(
    v3_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f12,axiom,(
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

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f12])).

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
    inference(flattening,[],[f27])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f41,plain,(
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
    inference(rectify,[],[f40])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r1_tarski(X1,X2)
          & v2_tex_2(X2,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK2(X0,X1) != X1
        & r1_tarski(X1,sK2(X0,X1))
        & v2_tex_2(sK2(X0,X1),X0)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ( sK2(X0,X1) != X1
                & r1_tarski(X1,sK2(X0,X1))
                & v2_tex_2(sK2(X0,X1),X0)
                & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f41,f42])).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( X1 = X3
      | ~ r1_tarski(X1,X3)
      | ~ v2_tex_2(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f5,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f5])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1494,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_10,plain,
    ( m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_24,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_291,plain,
    ( m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_24])).

cnf(c_292,plain,
    ( m1_subset_1(sK1(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_291])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_23,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_294,plain,
    ( m1_subset_1(sK1(sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_292,c_25,c_23])).

cnf(c_1483,plain,
    ( m1_subset_1(sK1(sK3),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_294])).

cnf(c_8,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1489,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2609,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3)) = iProver_top
    | r2_hidden(X0,sK1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1483,c_1489])).

cnf(c_2747,plain,
    ( m1_subset_1(sK0(sK1(sK3)),u1_struct_0(sK3)) = iProver_top
    | v1_xboole_0(sK1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1494,c_2609])).

cnf(c_26,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_28,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_293,plain,
    ( m1_subset_1(sK1(sK3),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_292])).

cnf(c_9,plain,
    ( v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(sK1(X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_302,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(sK1(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_24])).

cnf(c_303,plain,
    ( v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v1_xboole_0(sK1(sK3)) ),
    inference(unflattening,[status(thm)],[c_302])).

cnf(c_305,plain,
    ( ~ v1_xboole_0(sK1(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_303,c_25,c_23])).

cnf(c_479,plain,
    ( r2_hidden(sK0(X0),X0)
    | sK1(sK3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_305])).

cnf(c_480,plain,
    ( r2_hidden(sK0(sK1(sK3)),sK1(sK3)) ),
    inference(unflattening,[status(thm)],[c_479])).

cnf(c_481,plain,
    ( r2_hidden(sK0(sK1(sK3)),sK1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_480])).

cnf(c_1714,plain,
    ( ~ m1_subset_1(sK1(sK3),k1_zfmisc_1(X0))
    | m1_subset_1(sK0(sK1(sK3)),X0)
    | ~ r2_hidden(sK0(sK1(sK3)),sK1(sK3)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1972,plain,
    ( ~ m1_subset_1(sK1(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(sK0(sK1(sK3)),u1_struct_0(sK3))
    | ~ r2_hidden(sK0(sK1(sK3)),sK1(sK3)) ),
    inference(instantiation,[status(thm)],[c_1714])).

cnf(c_1973,plain,
    ( m1_subset_1(sK1(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK0(sK1(sK3)),u1_struct_0(sK3)) = iProver_top
    | r2_hidden(sK0(sK1(sK3)),sK1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1972])).

cnf(c_2925,plain,
    ( m1_subset_1(sK0(sK1(sK3)),u1_struct_0(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2747,c_26,c_28,c_293,c_481,c_1973])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1487,plain,
    ( k6_domain_1(X0,X1) = k1_tarski(X1)
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2930,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK0(sK1(sK3))) = k1_tarski(sK0(sK1(sK3)))
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2925,c_1487])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1709,plain,
    ( ~ m1_subset_1(sK1(sK3),k1_zfmisc_1(X0))
    | r2_hidden(sK0(sK1(sK3)),X0)
    | ~ r2_hidden(sK0(sK1(sK3)),sK1(sK3)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1967,plain,
    ( ~ m1_subset_1(sK1(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | r2_hidden(sK0(sK1(sK3)),u1_struct_0(sK3))
    | ~ r2_hidden(sK0(sK1(sK3)),sK1(sK3)) ),
    inference(instantiation,[status(thm)],[c_1709])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2134,plain,
    ( ~ r2_hidden(sK0(sK1(sK3)),u1_struct_0(sK3))
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2190,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3))
    | k6_domain_1(u1_struct_0(sK3),X0) = k1_tarski(X0) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2861,plain,
    ( ~ m1_subset_1(sK0(sK1(sK3)),u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3))
    | k6_domain_1(u1_struct_0(sK3),sK0(sK1(sK3))) = k1_tarski(sK0(sK1(sK3))) ),
    inference(instantiation,[status(thm)],[c_2190])).

cnf(c_3016,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK0(sK1(sK3))) = k1_tarski(sK0(sK1(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2930,c_25,c_23,c_292,c_480,c_1967,c_1972,c_2134,c_2861])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1488,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3019,plain,
    ( m1_subset_1(k1_tarski(sK0(sK1(sK3))),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | m1_subset_1(sK0(sK1(sK3)),u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3016,c_1488])).

cnf(c_1968,plain,
    ( m1_subset_1(sK1(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(sK0(sK1(sK3)),u1_struct_0(sK3)) = iProver_top
    | r2_hidden(sK0(sK1(sK3)),sK1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1967])).

cnf(c_2135,plain,
    ( r2_hidden(sK0(sK1(sK3)),u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2134])).

cnf(c_3556,plain,
    ( m1_subset_1(k1_tarski(sK0(sK1(sK3))),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3019,c_26,c_28,c_293,c_481,c_1968,c_1973,c_2135])).

cnf(c_22,negated_conjecture,
    ( v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1485,plain,
    ( v1_xboole_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1492,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2234,plain,
    ( sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1485,c_1492])).

cnf(c_20,negated_conjecture,
    ( v3_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_4,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_17,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ v3_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | ~ l1_pre_topc(X1)
    | X0 = X2 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_562,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ v3_tex_2(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | X2 = X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_23])).

cnf(c_563,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ v3_tex_2(X1,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(unflattening,[status(thm)],[c_562])).

cnf(c_689,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ v3_tex_2(X1,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | X0 != X2
    | X0 = X1
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_563])).

cnf(c_690,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ v3_tex_2(k1_xboole_0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3)))
    | X0 = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_689])).

cnf(c_7,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_704,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ v3_tex_2(k1_xboole_0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | X0 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_690,c_7])).

cnf(c_731,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | sK3 != sK3
    | sK4 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_704])).

cnf(c_870,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | sK4 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_731])).

cnf(c_1474,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = X0
    | v2_tex_2(X0,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_870])).

cnf(c_2291,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 != k1_xboole_0
    | v2_tex_2(X0,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2234,c_1474])).

cnf(c_2300,plain,
    ( k1_xboole_0 = X0
    | v2_tex_2(X0,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2291])).

cnf(c_3565,plain,
    ( k1_tarski(sK0(sK1(sK3))) = k1_xboole_0
    | v2_tex_2(k1_tarski(sK0(sK1(sK3))),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3556,c_2300])).

cnf(c_19,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_273,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_24])).

cnf(c_274,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_273])).

cnf(c_278,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_274,c_25,c_23])).

cnf(c_1484,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_278])).

cnf(c_3020,plain,
    ( v2_tex_2(k1_tarski(sK0(sK1(sK3))),sK3) = iProver_top
    | m1_subset_1(sK0(sK1(sK3)),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3016,c_1484])).

cnf(c_3741,plain,
    ( k1_tarski(sK0(sK1(sK3))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3565,c_26,c_28,c_293,c_481,c_1973,c_3020])).

cnf(c_3,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_5,plain,
    ( k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1945,plain,
    ( k1_tarski(X0) != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3,c_5])).

cnf(c_3744,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3741,c_1945])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:27:24 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.70/1.03  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.70/1.03  
% 2.70/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.70/1.03  
% 2.70/1.03  ------  iProver source info
% 2.70/1.03  
% 2.70/1.03  git: date: 2020-06-30 10:37:57 +0100
% 2.70/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.70/1.03  git: non_committed_changes: false
% 2.70/1.03  git: last_make_outside_of_git: false
% 2.70/1.03  
% 2.70/1.03  ------ 
% 2.70/1.03  
% 2.70/1.03  ------ Input Options
% 2.70/1.03  
% 2.70/1.03  --out_options                           all
% 2.70/1.03  --tptp_safe_out                         true
% 2.70/1.03  --problem_path                          ""
% 2.70/1.03  --include_path                          ""
% 2.70/1.03  --clausifier                            res/vclausify_rel
% 2.70/1.03  --clausifier_options                    --mode clausify
% 2.70/1.03  --stdin                                 false
% 2.70/1.03  --stats_out                             all
% 2.70/1.03  
% 2.70/1.03  ------ General Options
% 2.70/1.03  
% 2.70/1.03  --fof                                   false
% 2.70/1.03  --time_out_real                         305.
% 2.70/1.03  --time_out_virtual                      -1.
% 2.70/1.03  --symbol_type_check                     false
% 2.70/1.03  --clausify_out                          false
% 2.70/1.03  --sig_cnt_out                           false
% 2.70/1.03  --trig_cnt_out                          false
% 2.70/1.03  --trig_cnt_out_tolerance                1.
% 2.70/1.03  --trig_cnt_out_sk_spl                   false
% 2.70/1.03  --abstr_cl_out                          false
% 2.70/1.03  
% 2.70/1.03  ------ Global Options
% 2.70/1.03  
% 2.70/1.03  --schedule                              default
% 2.70/1.03  --add_important_lit                     false
% 2.70/1.03  --prop_solver_per_cl                    1000
% 2.70/1.03  --min_unsat_core                        false
% 2.70/1.03  --soft_assumptions                      false
% 2.70/1.03  --soft_lemma_size                       3
% 2.70/1.03  --prop_impl_unit_size                   0
% 2.70/1.03  --prop_impl_unit                        []
% 2.70/1.03  --share_sel_clauses                     true
% 2.70/1.03  --reset_solvers                         false
% 2.70/1.03  --bc_imp_inh                            [conj_cone]
% 2.70/1.03  --conj_cone_tolerance                   3.
% 2.70/1.03  --extra_neg_conj                        none
% 2.70/1.03  --large_theory_mode                     true
% 2.70/1.03  --prolific_symb_bound                   200
% 2.70/1.03  --lt_threshold                          2000
% 2.70/1.03  --clause_weak_htbl                      true
% 2.70/1.03  --gc_record_bc_elim                     false
% 2.70/1.03  
% 2.70/1.03  ------ Preprocessing Options
% 2.70/1.03  
% 2.70/1.03  --preprocessing_flag                    true
% 2.70/1.03  --time_out_prep_mult                    0.1
% 2.70/1.03  --splitting_mode                        input
% 2.70/1.03  --splitting_grd                         true
% 2.70/1.03  --splitting_cvd                         false
% 2.70/1.03  --splitting_cvd_svl                     false
% 2.70/1.03  --splitting_nvd                         32
% 2.70/1.03  --sub_typing                            true
% 2.70/1.03  --prep_gs_sim                           true
% 2.70/1.03  --prep_unflatten                        true
% 2.70/1.03  --prep_res_sim                          true
% 2.70/1.03  --prep_upred                            true
% 2.70/1.03  --prep_sem_filter                       exhaustive
% 2.70/1.03  --prep_sem_filter_out                   false
% 2.70/1.03  --pred_elim                             true
% 2.70/1.03  --res_sim_input                         true
% 2.70/1.03  --eq_ax_congr_red                       true
% 2.70/1.03  --pure_diseq_elim                       true
% 2.70/1.03  --brand_transform                       false
% 2.70/1.03  --non_eq_to_eq                          false
% 2.70/1.03  --prep_def_merge                        true
% 2.70/1.03  --prep_def_merge_prop_impl              false
% 2.70/1.03  --prep_def_merge_mbd                    true
% 2.70/1.03  --prep_def_merge_tr_red                 false
% 2.70/1.03  --prep_def_merge_tr_cl                  false
% 2.70/1.03  --smt_preprocessing                     true
% 2.70/1.03  --smt_ac_axioms                         fast
% 2.70/1.03  --preprocessed_out                      false
% 2.70/1.03  --preprocessed_stats                    false
% 2.70/1.03  
% 2.70/1.03  ------ Abstraction refinement Options
% 2.70/1.03  
% 2.70/1.03  --abstr_ref                             []
% 2.70/1.03  --abstr_ref_prep                        false
% 2.70/1.03  --abstr_ref_until_sat                   false
% 2.70/1.03  --abstr_ref_sig_restrict                funpre
% 2.70/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.70/1.03  --abstr_ref_under                       []
% 2.70/1.03  
% 2.70/1.03  ------ SAT Options
% 2.70/1.03  
% 2.70/1.03  --sat_mode                              false
% 2.70/1.03  --sat_fm_restart_options                ""
% 2.70/1.03  --sat_gr_def                            false
% 2.70/1.03  --sat_epr_types                         true
% 2.70/1.03  --sat_non_cyclic_types                  false
% 2.70/1.03  --sat_finite_models                     false
% 2.70/1.03  --sat_fm_lemmas                         false
% 2.70/1.03  --sat_fm_prep                           false
% 2.70/1.03  --sat_fm_uc_incr                        true
% 2.70/1.03  --sat_out_model                         small
% 2.70/1.03  --sat_out_clauses                       false
% 2.70/1.03  
% 2.70/1.03  ------ QBF Options
% 2.70/1.03  
% 2.70/1.03  --qbf_mode                              false
% 2.70/1.03  --qbf_elim_univ                         false
% 2.70/1.03  --qbf_dom_inst                          none
% 2.70/1.03  --qbf_dom_pre_inst                      false
% 2.70/1.03  --qbf_sk_in                             false
% 2.70/1.03  --qbf_pred_elim                         true
% 2.70/1.03  --qbf_split                             512
% 2.70/1.03  
% 2.70/1.03  ------ BMC1 Options
% 2.70/1.03  
% 2.70/1.03  --bmc1_incremental                      false
% 2.70/1.03  --bmc1_axioms                           reachable_all
% 2.70/1.03  --bmc1_min_bound                        0
% 2.70/1.03  --bmc1_max_bound                        -1
% 2.70/1.03  --bmc1_max_bound_default                -1
% 2.70/1.03  --bmc1_symbol_reachability              true
% 2.70/1.03  --bmc1_property_lemmas                  false
% 2.70/1.03  --bmc1_k_induction                      false
% 2.70/1.03  --bmc1_non_equiv_states                 false
% 2.70/1.03  --bmc1_deadlock                         false
% 2.70/1.03  --bmc1_ucm                              false
% 2.70/1.03  --bmc1_add_unsat_core                   none
% 2.70/1.03  --bmc1_unsat_core_children              false
% 2.70/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.70/1.03  --bmc1_out_stat                         full
% 2.70/1.03  --bmc1_ground_init                      false
% 2.70/1.03  --bmc1_pre_inst_next_state              false
% 2.70/1.03  --bmc1_pre_inst_state                   false
% 2.70/1.03  --bmc1_pre_inst_reach_state             false
% 2.70/1.03  --bmc1_out_unsat_core                   false
% 2.70/1.03  --bmc1_aig_witness_out                  false
% 2.70/1.03  --bmc1_verbose                          false
% 2.70/1.03  --bmc1_dump_clauses_tptp                false
% 2.70/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.70/1.03  --bmc1_dump_file                        -
% 2.70/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.70/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.70/1.03  --bmc1_ucm_extend_mode                  1
% 2.70/1.03  --bmc1_ucm_init_mode                    2
% 2.70/1.03  --bmc1_ucm_cone_mode                    none
% 2.70/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.70/1.03  --bmc1_ucm_relax_model                  4
% 2.70/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.70/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.70/1.03  --bmc1_ucm_layered_model                none
% 2.70/1.03  --bmc1_ucm_max_lemma_size               10
% 2.70/1.03  
% 2.70/1.03  ------ AIG Options
% 2.70/1.03  
% 2.70/1.03  --aig_mode                              false
% 2.70/1.03  
% 2.70/1.03  ------ Instantiation Options
% 2.70/1.03  
% 2.70/1.03  --instantiation_flag                    true
% 2.70/1.03  --inst_sos_flag                         false
% 2.70/1.03  --inst_sos_phase                        true
% 2.70/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.70/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.70/1.03  --inst_lit_sel_side                     num_symb
% 2.70/1.03  --inst_solver_per_active                1400
% 2.70/1.03  --inst_solver_calls_frac                1.
% 2.70/1.03  --inst_passive_queue_type               priority_queues
% 2.70/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.70/1.03  --inst_passive_queues_freq              [25;2]
% 2.70/1.03  --inst_dismatching                      true
% 2.70/1.03  --inst_eager_unprocessed_to_passive     true
% 2.70/1.03  --inst_prop_sim_given                   true
% 2.70/1.03  --inst_prop_sim_new                     false
% 2.70/1.03  --inst_subs_new                         false
% 2.70/1.03  --inst_eq_res_simp                      false
% 2.70/1.03  --inst_subs_given                       false
% 2.70/1.03  --inst_orphan_elimination               true
% 2.70/1.03  --inst_learning_loop_flag               true
% 2.70/1.03  --inst_learning_start                   3000
% 2.70/1.03  --inst_learning_factor                  2
% 2.70/1.03  --inst_start_prop_sim_after_learn       3
% 2.70/1.03  --inst_sel_renew                        solver
% 2.70/1.03  --inst_lit_activity_flag                true
% 2.70/1.03  --inst_restr_to_given                   false
% 2.70/1.03  --inst_activity_threshold               500
% 2.70/1.03  --inst_out_proof                        true
% 2.70/1.03  
% 2.70/1.03  ------ Resolution Options
% 2.70/1.03  
% 2.70/1.03  --resolution_flag                       true
% 2.70/1.03  --res_lit_sel                           adaptive
% 2.70/1.03  --res_lit_sel_side                      none
% 2.70/1.03  --res_ordering                          kbo
% 2.70/1.03  --res_to_prop_solver                    active
% 2.70/1.03  --res_prop_simpl_new                    false
% 2.70/1.03  --res_prop_simpl_given                  true
% 2.70/1.03  --res_passive_queue_type                priority_queues
% 2.70/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.70/1.03  --res_passive_queues_freq               [15;5]
% 2.70/1.03  --res_forward_subs                      full
% 2.70/1.03  --res_backward_subs                     full
% 2.70/1.03  --res_forward_subs_resolution           true
% 2.70/1.03  --res_backward_subs_resolution          true
% 2.70/1.03  --res_orphan_elimination                true
% 2.70/1.03  --res_time_limit                        2.
% 2.70/1.03  --res_out_proof                         true
% 2.70/1.03  
% 2.70/1.03  ------ Superposition Options
% 2.70/1.03  
% 2.70/1.03  --superposition_flag                    true
% 2.70/1.03  --sup_passive_queue_type                priority_queues
% 2.70/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.70/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.70/1.03  --demod_completeness_check              fast
% 2.70/1.03  --demod_use_ground                      true
% 2.70/1.03  --sup_to_prop_solver                    passive
% 2.70/1.03  --sup_prop_simpl_new                    true
% 2.70/1.03  --sup_prop_simpl_given                  true
% 2.70/1.03  --sup_fun_splitting                     false
% 2.70/1.03  --sup_smt_interval                      50000
% 2.70/1.03  
% 2.70/1.03  ------ Superposition Simplification Setup
% 2.70/1.03  
% 2.70/1.03  --sup_indices_passive                   []
% 2.70/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.70/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.70/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.70/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.70/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.70/1.03  --sup_full_bw                           [BwDemod]
% 2.70/1.03  --sup_immed_triv                        [TrivRules]
% 2.70/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.70/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.70/1.03  --sup_immed_bw_main                     []
% 2.70/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.70/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.70/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.70/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.70/1.03  
% 2.70/1.03  ------ Combination Options
% 2.70/1.03  
% 2.70/1.03  --comb_res_mult                         3
% 2.70/1.03  --comb_sup_mult                         2
% 2.70/1.03  --comb_inst_mult                        10
% 2.70/1.03  
% 2.70/1.03  ------ Debug Options
% 2.70/1.03  
% 2.70/1.03  --dbg_backtrace                         false
% 2.70/1.03  --dbg_dump_prop_clauses                 false
% 2.70/1.03  --dbg_dump_prop_clauses_file            -
% 2.70/1.03  --dbg_out_stat                          false
% 2.70/1.03  ------ Parsing...
% 2.70/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.70/1.03  
% 2.70/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 2.70/1.03  
% 2.70/1.03  ------ Preprocessing... gs_s  sp: 3 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.70/1.03  
% 2.70/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.70/1.03  ------ Proving...
% 2.70/1.03  ------ Problem Properties 
% 2.70/1.03  
% 2.70/1.03  
% 2.70/1.03  clauses                                 23
% 2.70/1.03  conjectures                             2
% 2.70/1.03  EPR                                     4
% 2.70/1.03  Horn                                    18
% 2.70/1.03  unary                                   8
% 2.70/1.03  binary                                  4
% 2.70/1.03  lits                                    53
% 2.70/1.03  lits eq                                 10
% 2.70/1.03  fd_pure                                 0
% 2.70/1.03  fd_pseudo                               0
% 2.70/1.03  fd_cond                                 5
% 2.70/1.03  fd_pseudo_cond                          0
% 2.70/1.03  AC symbols                              0
% 2.70/1.03  
% 2.70/1.03  ------ Schedule dynamic 5 is on 
% 2.70/1.03  
% 2.70/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.70/1.03  
% 2.70/1.03  
% 2.70/1.03  ------ 
% 2.70/1.03  Current options:
% 2.70/1.03  ------ 
% 2.70/1.03  
% 2.70/1.03  ------ Input Options
% 2.70/1.03  
% 2.70/1.03  --out_options                           all
% 2.70/1.03  --tptp_safe_out                         true
% 2.70/1.03  --problem_path                          ""
% 2.70/1.03  --include_path                          ""
% 2.70/1.03  --clausifier                            res/vclausify_rel
% 2.70/1.03  --clausifier_options                    --mode clausify
% 2.70/1.03  --stdin                                 false
% 2.70/1.03  --stats_out                             all
% 2.70/1.03  
% 2.70/1.03  ------ General Options
% 2.70/1.03  
% 2.70/1.03  --fof                                   false
% 2.70/1.03  --time_out_real                         305.
% 2.70/1.03  --time_out_virtual                      -1.
% 2.70/1.03  --symbol_type_check                     false
% 2.70/1.03  --clausify_out                          false
% 2.70/1.03  --sig_cnt_out                           false
% 2.70/1.03  --trig_cnt_out                          false
% 2.70/1.03  --trig_cnt_out_tolerance                1.
% 2.70/1.03  --trig_cnt_out_sk_spl                   false
% 2.70/1.03  --abstr_cl_out                          false
% 2.70/1.03  
% 2.70/1.03  ------ Global Options
% 2.70/1.03  
% 2.70/1.03  --schedule                              default
% 2.70/1.03  --add_important_lit                     false
% 2.70/1.03  --prop_solver_per_cl                    1000
% 2.70/1.03  --min_unsat_core                        false
% 2.70/1.03  --soft_assumptions                      false
% 2.70/1.03  --soft_lemma_size                       3
% 2.70/1.03  --prop_impl_unit_size                   0
% 2.70/1.03  --prop_impl_unit                        []
% 2.70/1.03  --share_sel_clauses                     true
% 2.70/1.03  --reset_solvers                         false
% 2.70/1.03  --bc_imp_inh                            [conj_cone]
% 2.70/1.03  --conj_cone_tolerance                   3.
% 2.70/1.03  --extra_neg_conj                        none
% 2.70/1.03  --large_theory_mode                     true
% 2.70/1.03  --prolific_symb_bound                   200
% 2.70/1.03  --lt_threshold                          2000
% 2.70/1.03  --clause_weak_htbl                      true
% 2.70/1.03  --gc_record_bc_elim                     false
% 2.70/1.03  
% 2.70/1.03  ------ Preprocessing Options
% 2.70/1.03  
% 2.70/1.03  --preprocessing_flag                    true
% 2.70/1.03  --time_out_prep_mult                    0.1
% 2.70/1.03  --splitting_mode                        input
% 2.70/1.03  --splitting_grd                         true
% 2.70/1.03  --splitting_cvd                         false
% 2.70/1.03  --splitting_cvd_svl                     false
% 2.70/1.03  --splitting_nvd                         32
% 2.70/1.03  --sub_typing                            true
% 2.70/1.03  --prep_gs_sim                           true
% 2.70/1.03  --prep_unflatten                        true
% 2.70/1.03  --prep_res_sim                          true
% 2.70/1.03  --prep_upred                            true
% 2.70/1.03  --prep_sem_filter                       exhaustive
% 2.70/1.03  --prep_sem_filter_out                   false
% 2.70/1.03  --pred_elim                             true
% 2.70/1.03  --res_sim_input                         true
% 2.70/1.03  --eq_ax_congr_red                       true
% 2.70/1.03  --pure_diseq_elim                       true
% 2.70/1.03  --brand_transform                       false
% 2.70/1.03  --non_eq_to_eq                          false
% 2.70/1.03  --prep_def_merge                        true
% 2.70/1.03  --prep_def_merge_prop_impl              false
% 2.70/1.03  --prep_def_merge_mbd                    true
% 2.70/1.03  --prep_def_merge_tr_red                 false
% 2.70/1.03  --prep_def_merge_tr_cl                  false
% 2.70/1.03  --smt_preprocessing                     true
% 2.70/1.03  --smt_ac_axioms                         fast
% 2.70/1.03  --preprocessed_out                      false
% 2.70/1.03  --preprocessed_stats                    false
% 2.70/1.03  
% 2.70/1.03  ------ Abstraction refinement Options
% 2.70/1.03  
% 2.70/1.03  --abstr_ref                             []
% 2.70/1.03  --abstr_ref_prep                        false
% 2.70/1.03  --abstr_ref_until_sat                   false
% 2.70/1.03  --abstr_ref_sig_restrict                funpre
% 2.70/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.70/1.03  --abstr_ref_under                       []
% 2.70/1.03  
% 2.70/1.03  ------ SAT Options
% 2.70/1.03  
% 2.70/1.03  --sat_mode                              false
% 2.70/1.03  --sat_fm_restart_options                ""
% 2.70/1.03  --sat_gr_def                            false
% 2.70/1.03  --sat_epr_types                         true
% 2.70/1.03  --sat_non_cyclic_types                  false
% 2.70/1.03  --sat_finite_models                     false
% 2.70/1.03  --sat_fm_lemmas                         false
% 2.70/1.03  --sat_fm_prep                           false
% 2.70/1.03  --sat_fm_uc_incr                        true
% 2.70/1.03  --sat_out_model                         small
% 2.70/1.03  --sat_out_clauses                       false
% 2.70/1.03  
% 2.70/1.03  ------ QBF Options
% 2.70/1.03  
% 2.70/1.03  --qbf_mode                              false
% 2.70/1.03  --qbf_elim_univ                         false
% 2.70/1.03  --qbf_dom_inst                          none
% 2.70/1.03  --qbf_dom_pre_inst                      false
% 2.70/1.03  --qbf_sk_in                             false
% 2.70/1.03  --qbf_pred_elim                         true
% 2.70/1.03  --qbf_split                             512
% 2.70/1.03  
% 2.70/1.03  ------ BMC1 Options
% 2.70/1.03  
% 2.70/1.03  --bmc1_incremental                      false
% 2.70/1.03  --bmc1_axioms                           reachable_all
% 2.70/1.03  --bmc1_min_bound                        0
% 2.70/1.03  --bmc1_max_bound                        -1
% 2.70/1.03  --bmc1_max_bound_default                -1
% 2.70/1.03  --bmc1_symbol_reachability              true
% 2.70/1.03  --bmc1_property_lemmas                  false
% 2.70/1.03  --bmc1_k_induction                      false
% 2.70/1.03  --bmc1_non_equiv_states                 false
% 2.70/1.03  --bmc1_deadlock                         false
% 2.70/1.03  --bmc1_ucm                              false
% 2.70/1.03  --bmc1_add_unsat_core                   none
% 2.70/1.03  --bmc1_unsat_core_children              false
% 2.70/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.70/1.03  --bmc1_out_stat                         full
% 2.70/1.03  --bmc1_ground_init                      false
% 2.70/1.03  --bmc1_pre_inst_next_state              false
% 2.70/1.03  --bmc1_pre_inst_state                   false
% 2.70/1.03  --bmc1_pre_inst_reach_state             false
% 2.70/1.03  --bmc1_out_unsat_core                   false
% 2.70/1.03  --bmc1_aig_witness_out                  false
% 2.70/1.03  --bmc1_verbose                          false
% 2.70/1.03  --bmc1_dump_clauses_tptp                false
% 2.70/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.70/1.03  --bmc1_dump_file                        -
% 2.70/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.70/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.70/1.03  --bmc1_ucm_extend_mode                  1
% 2.70/1.03  --bmc1_ucm_init_mode                    2
% 2.70/1.03  --bmc1_ucm_cone_mode                    none
% 2.70/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.70/1.03  --bmc1_ucm_relax_model                  4
% 2.70/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.70/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.70/1.03  --bmc1_ucm_layered_model                none
% 2.70/1.03  --bmc1_ucm_max_lemma_size               10
% 2.70/1.03  
% 2.70/1.03  ------ AIG Options
% 2.70/1.03  
% 2.70/1.03  --aig_mode                              false
% 2.70/1.03  
% 2.70/1.03  ------ Instantiation Options
% 2.70/1.03  
% 2.70/1.03  --instantiation_flag                    true
% 2.70/1.03  --inst_sos_flag                         false
% 2.70/1.03  --inst_sos_phase                        true
% 2.70/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.70/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.70/1.03  --inst_lit_sel_side                     none
% 2.70/1.03  --inst_solver_per_active                1400
% 2.70/1.03  --inst_solver_calls_frac                1.
% 2.70/1.03  --inst_passive_queue_type               priority_queues
% 2.70/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.70/1.03  --inst_passive_queues_freq              [25;2]
% 2.70/1.03  --inst_dismatching                      true
% 2.70/1.03  --inst_eager_unprocessed_to_passive     true
% 2.70/1.03  --inst_prop_sim_given                   true
% 2.70/1.03  --inst_prop_sim_new                     false
% 2.70/1.03  --inst_subs_new                         false
% 2.70/1.03  --inst_eq_res_simp                      false
% 2.70/1.03  --inst_subs_given                       false
% 2.70/1.03  --inst_orphan_elimination               true
% 2.70/1.03  --inst_learning_loop_flag               true
% 2.70/1.03  --inst_learning_start                   3000
% 2.70/1.03  --inst_learning_factor                  2
% 2.70/1.03  --inst_start_prop_sim_after_learn       3
% 2.70/1.03  --inst_sel_renew                        solver
% 2.70/1.03  --inst_lit_activity_flag                true
% 2.70/1.03  --inst_restr_to_given                   false
% 2.70/1.03  --inst_activity_threshold               500
% 2.70/1.03  --inst_out_proof                        true
% 2.70/1.03  
% 2.70/1.03  ------ Resolution Options
% 2.70/1.03  
% 2.70/1.03  --resolution_flag                       false
% 2.70/1.03  --res_lit_sel                           adaptive
% 2.70/1.03  --res_lit_sel_side                      none
% 2.70/1.03  --res_ordering                          kbo
% 2.70/1.03  --res_to_prop_solver                    active
% 2.70/1.03  --res_prop_simpl_new                    false
% 2.70/1.03  --res_prop_simpl_given                  true
% 2.70/1.03  --res_passive_queue_type                priority_queues
% 2.70/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.70/1.03  --res_passive_queues_freq               [15;5]
% 2.70/1.03  --res_forward_subs                      full
% 2.70/1.03  --res_backward_subs                     full
% 2.70/1.03  --res_forward_subs_resolution           true
% 2.70/1.03  --res_backward_subs_resolution          true
% 2.70/1.03  --res_orphan_elimination                true
% 2.70/1.03  --res_time_limit                        2.
% 2.70/1.03  --res_out_proof                         true
% 2.70/1.03  
% 2.70/1.03  ------ Superposition Options
% 2.70/1.03  
% 2.70/1.03  --superposition_flag                    true
% 2.70/1.03  --sup_passive_queue_type                priority_queues
% 2.70/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.70/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.70/1.03  --demod_completeness_check              fast
% 2.70/1.03  --demod_use_ground                      true
% 2.70/1.03  --sup_to_prop_solver                    passive
% 2.70/1.03  --sup_prop_simpl_new                    true
% 2.70/1.03  --sup_prop_simpl_given                  true
% 2.70/1.03  --sup_fun_splitting                     false
% 2.70/1.03  --sup_smt_interval                      50000
% 2.70/1.03  
% 2.70/1.03  ------ Superposition Simplification Setup
% 2.70/1.03  
% 2.70/1.03  --sup_indices_passive                   []
% 2.70/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.70/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.70/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.70/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.70/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.70/1.03  --sup_full_bw                           [BwDemod]
% 2.70/1.03  --sup_immed_triv                        [TrivRules]
% 2.70/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.70/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.70/1.03  --sup_immed_bw_main                     []
% 2.70/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.70/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.70/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.70/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.70/1.03  
% 2.70/1.03  ------ Combination Options
% 2.70/1.03  
% 2.70/1.03  --comb_res_mult                         3
% 2.70/1.03  --comb_sup_mult                         2
% 2.70/1.03  --comb_inst_mult                        10
% 2.70/1.03  
% 2.70/1.03  ------ Debug Options
% 2.70/1.03  
% 2.70/1.03  --dbg_backtrace                         false
% 2.70/1.03  --dbg_dump_prop_clauses                 false
% 2.70/1.03  --dbg_dump_prop_clauses_file            -
% 2.70/1.03  --dbg_out_stat                          false
% 2.70/1.03  
% 2.70/1.03  
% 2.70/1.03  
% 2.70/1.03  
% 2.70/1.03  ------ Proving...
% 2.70/1.03  
% 2.70/1.03  
% 2.70/1.03  % SZS status Theorem for theBenchmark.p
% 2.70/1.03  
% 2.70/1.03   Resolution empty clause
% 2.70/1.03  
% 2.70/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 2.70/1.03  
% 2.70/1.03  fof(f1,axiom,(
% 2.70/1.03    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.70/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/1.03  
% 2.70/1.03  fof(f33,plain,(
% 2.70/1.03    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.70/1.03    inference(nnf_transformation,[],[f1])).
% 2.70/1.03  
% 2.70/1.03  fof(f34,plain,(
% 2.70/1.03    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.70/1.03    inference(rectify,[],[f33])).
% 2.70/1.03  
% 2.70/1.03  fof(f35,plain,(
% 2.70/1.03    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.70/1.03    introduced(choice_axiom,[])).
% 2.70/1.03  
% 2.70/1.03  fof(f36,plain,(
% 2.70/1.03    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.70/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).
% 2.70/1.03  
% 2.70/1.03  fof(f48,plain,(
% 2.70/1.03    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 2.70/1.03    inference(cnf_transformation,[],[f36])).
% 2.70/1.03  
% 2.70/1.03  fof(f9,axiom,(
% 2.70/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v4_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.70/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/1.03  
% 2.70/1.03  fof(f16,plain,(
% 2.70/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.70/1.03    inference(pure_predicate_removal,[],[f9])).
% 2.70/1.03  
% 2.70/1.03  fof(f21,plain,(
% 2.70/1.03    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.70/1.03    inference(ennf_transformation,[],[f16])).
% 2.70/1.03  
% 2.70/1.03  fof(f22,plain,(
% 2.70/1.03    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.70/1.03    inference(flattening,[],[f21])).
% 2.70/1.03  
% 2.70/1.03  fof(f37,plain,(
% 2.70/1.03    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_xboole_0(sK1(X0)) & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.70/1.03    introduced(choice_axiom,[])).
% 2.70/1.03  
% 2.70/1.03  fof(f38,plain,(
% 2.70/1.03    ! [X0] : ((~v1_xboole_0(sK1(X0)) & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.70/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f37])).
% 2.70/1.03  
% 2.70/1.03  fof(f56,plain,(
% 2.70/1.03    ( ! [X0] : (m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.70/1.03    inference(cnf_transformation,[],[f38])).
% 2.70/1.03  
% 2.70/1.03  fof(f14,conjecture,(
% 2.70/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => ~v3_tex_2(X1,X0)))),
% 2.70/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/1.03  
% 2.70/1.03  fof(f15,negated_conjecture,(
% 2.70/1.03    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => ~v3_tex_2(X1,X0)))),
% 2.70/1.03    inference(negated_conjecture,[],[f14])).
% 2.70/1.03  
% 2.70/1.03  fof(f31,plain,(
% 2.70/1.03    ? [X0] : (? [X1] : (v3_tex_2(X1,X0) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.70/1.03    inference(ennf_transformation,[],[f15])).
% 2.70/1.03  
% 2.70/1.03  fof(f32,plain,(
% 2.70/1.03    ? [X0] : (? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.70/1.03    inference(flattening,[],[f31])).
% 2.70/1.03  
% 2.70/1.03  fof(f45,plain,(
% 2.70/1.03    ( ! [X0] : (? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => (v3_tex_2(sK4,X0) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(sK4))) )),
% 2.70/1.03    introduced(choice_axiom,[])).
% 2.70/1.03  
% 2.70/1.03  fof(f44,plain,(
% 2.70/1.03    ? [X0] : (? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (v3_tex_2(X1,sK3) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) & v1_xboole_0(X1)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 2.70/1.03    introduced(choice_axiom,[])).
% 2.70/1.03  
% 2.70/1.03  fof(f46,plain,(
% 2.70/1.03    (v3_tex_2(sK4,sK3) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) & v1_xboole_0(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 2.70/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f32,f45,f44])).
% 2.70/1.03  
% 2.70/1.03  fof(f68,plain,(
% 2.70/1.03    v2_pre_topc(sK3)),
% 2.70/1.03    inference(cnf_transformation,[],[f46])).
% 2.70/1.03  
% 2.70/1.03  fof(f67,plain,(
% 2.70/1.03    ~v2_struct_0(sK3)),
% 2.70/1.03    inference(cnf_transformation,[],[f46])).
% 2.70/1.03  
% 2.70/1.03  fof(f69,plain,(
% 2.70/1.03    l1_pre_topc(sK3)),
% 2.70/1.03    inference(cnf_transformation,[],[f46])).
% 2.70/1.03  
% 2.70/1.03  fof(f8,axiom,(
% 2.70/1.03    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.70/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/1.03  
% 2.70/1.03  fof(f19,plain,(
% 2.70/1.03    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.70/1.03    inference(ennf_transformation,[],[f8])).
% 2.70/1.03  
% 2.70/1.03  fof(f20,plain,(
% 2.70/1.03    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.70/1.03    inference(flattening,[],[f19])).
% 2.70/1.03  
% 2.70/1.03  fof(f55,plain,(
% 2.70/1.03    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.70/1.03    inference(cnf_transformation,[],[f20])).
% 2.70/1.03  
% 2.70/1.03  fof(f57,plain,(
% 2.70/1.03    ( ! [X0] : (~v1_xboole_0(sK1(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.70/1.03    inference(cnf_transformation,[],[f38])).
% 2.70/1.03  
% 2.70/1.03  fof(f11,axiom,(
% 2.70/1.03    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 2.70/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/1.03  
% 2.70/1.03  fof(f25,plain,(
% 2.70/1.03    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.70/1.03    inference(ennf_transformation,[],[f11])).
% 2.70/1.03  
% 2.70/1.03  fof(f26,plain,(
% 2.70/1.03    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.70/1.03    inference(flattening,[],[f25])).
% 2.70/1.03  
% 2.70/1.03  fof(f59,plain,(
% 2.70/1.03    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.70/1.03    inference(cnf_transformation,[],[f26])).
% 2.70/1.03  
% 2.70/1.03  fof(f6,axiom,(
% 2.70/1.03    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 2.70/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/1.03  
% 2.70/1.03  fof(f18,plain,(
% 2.70/1.03    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.70/1.03    inference(ennf_transformation,[],[f6])).
% 2.70/1.03  
% 2.70/1.03  fof(f53,plain,(
% 2.70/1.03    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.70/1.03    inference(cnf_transformation,[],[f18])).
% 2.70/1.03  
% 2.70/1.03  fof(f47,plain,(
% 2.70/1.03    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.70/1.03    inference(cnf_transformation,[],[f36])).
% 2.70/1.03  
% 2.70/1.03  fof(f10,axiom,(
% 2.70/1.03    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.70/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/1.03  
% 2.70/1.03  fof(f23,plain,(
% 2.70/1.03    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.70/1.03    inference(ennf_transformation,[],[f10])).
% 2.70/1.03  
% 2.70/1.03  fof(f24,plain,(
% 2.70/1.03    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.70/1.03    inference(flattening,[],[f23])).
% 2.70/1.03  
% 2.70/1.03  fof(f58,plain,(
% 2.70/1.03    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.70/1.03    inference(cnf_transformation,[],[f24])).
% 2.70/1.03  
% 2.70/1.03  fof(f70,plain,(
% 2.70/1.03    v1_xboole_0(sK4)),
% 2.70/1.03    inference(cnf_transformation,[],[f46])).
% 2.70/1.03  
% 2.70/1.03  fof(f2,axiom,(
% 2.70/1.03    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.70/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/1.03  
% 2.70/1.03  fof(f17,plain,(
% 2.70/1.03    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.70/1.03    inference(ennf_transformation,[],[f2])).
% 2.70/1.03  
% 2.70/1.03  fof(f49,plain,(
% 2.70/1.03    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.70/1.03    inference(cnf_transformation,[],[f17])).
% 2.70/1.03  
% 2.70/1.03  fof(f72,plain,(
% 2.70/1.03    v3_tex_2(sK4,sK3)),
% 2.70/1.03    inference(cnf_transformation,[],[f46])).
% 2.70/1.03  
% 2.70/1.03  fof(f4,axiom,(
% 2.70/1.03    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.70/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/1.03  
% 2.70/1.03  fof(f51,plain,(
% 2.70/1.03    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.70/1.03    inference(cnf_transformation,[],[f4])).
% 2.70/1.03  
% 2.70/1.03  fof(f12,axiom,(
% 2.70/1.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 2.70/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/1.03  
% 2.70/1.03  fof(f27,plain,(
% 2.70/1.03    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.70/1.03    inference(ennf_transformation,[],[f12])).
% 2.70/1.03  
% 2.70/1.03  fof(f28,plain,(
% 2.70/1.03    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.70/1.03    inference(flattening,[],[f27])).
% 2.70/1.03  
% 2.70/1.03  fof(f39,plain,(
% 2.70/1.03    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.70/1.03    inference(nnf_transformation,[],[f28])).
% 2.70/1.03  
% 2.70/1.03  fof(f40,plain,(
% 2.70/1.03    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.70/1.03    inference(flattening,[],[f39])).
% 2.70/1.03  
% 2.70/1.03  fof(f41,plain,(
% 2.70/1.03    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.70/1.03    inference(rectify,[],[f40])).
% 2.70/1.03  
% 2.70/1.03  fof(f42,plain,(
% 2.70/1.03    ! [X1,X0] : (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK2(X0,X1) != X1 & r1_tarski(X1,sK2(X0,X1)) & v2_tex_2(sK2(X0,X1),X0) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.70/1.03    introduced(choice_axiom,[])).
% 2.70/1.03  
% 2.70/1.03  fof(f43,plain,(
% 2.70/1.03    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (sK2(X0,X1) != X1 & r1_tarski(X1,sK2(X0,X1)) & v2_tex_2(sK2(X0,X1),X0) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.70/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f41,f42])).
% 2.70/1.03  
% 2.70/1.03  fof(f61,plain,(
% 2.70/1.03    ( ! [X0,X3,X1] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.70/1.03    inference(cnf_transformation,[],[f43])).
% 2.70/1.03  
% 2.70/1.03  fof(f7,axiom,(
% 2.70/1.03    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.70/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/1.03  
% 2.70/1.03  fof(f54,plain,(
% 2.70/1.03    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.70/1.03    inference(cnf_transformation,[],[f7])).
% 2.70/1.03  
% 2.70/1.03  fof(f13,axiom,(
% 2.70/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 2.70/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/1.03  
% 2.70/1.03  fof(f29,plain,(
% 2.70/1.03    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.70/1.03    inference(ennf_transformation,[],[f13])).
% 2.70/1.03  
% 2.70/1.03  fof(f30,plain,(
% 2.70/1.03    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.70/1.03    inference(flattening,[],[f29])).
% 2.70/1.03  
% 2.70/1.03  fof(f66,plain,(
% 2.70/1.03    ( ! [X0,X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.70/1.03    inference(cnf_transformation,[],[f30])).
% 2.70/1.03  
% 2.70/1.03  fof(f3,axiom,(
% 2.70/1.03    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 2.70/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/1.03  
% 2.70/1.03  fof(f50,plain,(
% 2.70/1.03    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.70/1.03    inference(cnf_transformation,[],[f3])).
% 2.70/1.03  
% 2.70/1.03  fof(f5,axiom,(
% 2.70/1.03    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 2.70/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/1.03  
% 2.70/1.03  fof(f52,plain,(
% 2.70/1.03    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 2.70/1.03    inference(cnf_transformation,[],[f5])).
% 2.70/1.03  
% 2.70/1.03  cnf(c_0,plain,
% 2.70/1.03      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 2.70/1.03      inference(cnf_transformation,[],[f48]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_1494,plain,
% 2.70/1.03      ( r2_hidden(sK0(X0),X0) = iProver_top | v1_xboole_0(X0) = iProver_top ),
% 2.70/1.03      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_10,plain,
% 2.70/1.03      ( m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 2.70/1.03      | v2_struct_0(X0)
% 2.70/1.03      | ~ v2_pre_topc(X0)
% 2.70/1.03      | ~ l1_pre_topc(X0) ),
% 2.70/1.03      inference(cnf_transformation,[],[f56]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_24,negated_conjecture,
% 2.70/1.03      ( v2_pre_topc(sK3) ),
% 2.70/1.03      inference(cnf_transformation,[],[f68]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_291,plain,
% 2.70/1.03      ( m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 2.70/1.03      | v2_struct_0(X0)
% 2.70/1.03      | ~ l1_pre_topc(X0)
% 2.70/1.03      | sK3 != X0 ),
% 2.70/1.03      inference(resolution_lifted,[status(thm)],[c_10,c_24]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_292,plain,
% 2.70/1.03      ( m1_subset_1(sK1(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.70/1.03      | v2_struct_0(sK3)
% 2.70/1.03      | ~ l1_pre_topc(sK3) ),
% 2.70/1.03      inference(unflattening,[status(thm)],[c_291]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_25,negated_conjecture,
% 2.70/1.03      ( ~ v2_struct_0(sK3) ),
% 2.70/1.03      inference(cnf_transformation,[],[f67]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_23,negated_conjecture,
% 2.70/1.03      ( l1_pre_topc(sK3) ),
% 2.70/1.03      inference(cnf_transformation,[],[f69]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_294,plain,
% 2.70/1.03      ( m1_subset_1(sK1(sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.70/1.03      inference(global_propositional_subsumption,
% 2.70/1.03                [status(thm)],
% 2.70/1.03                [c_292,c_25,c_23]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_1483,plain,
% 2.70/1.03      ( m1_subset_1(sK1(sK3),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 2.70/1.03      inference(predicate_to_equality,[status(thm)],[c_294]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_8,plain,
% 2.70/1.03      ( m1_subset_1(X0,X1)
% 2.70/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.70/1.03      | ~ r2_hidden(X0,X2) ),
% 2.70/1.03      inference(cnf_transformation,[],[f55]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_1489,plain,
% 2.70/1.03      ( m1_subset_1(X0,X1) = iProver_top
% 2.70/1.03      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 2.70/1.03      | r2_hidden(X0,X2) != iProver_top ),
% 2.70/1.03      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_2609,plain,
% 2.70/1.03      ( m1_subset_1(X0,u1_struct_0(sK3)) = iProver_top
% 2.70/1.03      | r2_hidden(X0,sK1(sK3)) != iProver_top ),
% 2.70/1.03      inference(superposition,[status(thm)],[c_1483,c_1489]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_2747,plain,
% 2.70/1.03      ( m1_subset_1(sK0(sK1(sK3)),u1_struct_0(sK3)) = iProver_top
% 2.70/1.03      | v1_xboole_0(sK1(sK3)) = iProver_top ),
% 2.70/1.03      inference(superposition,[status(thm)],[c_1494,c_2609]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_26,plain,
% 2.70/1.03      ( v2_struct_0(sK3) != iProver_top ),
% 2.70/1.03      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_28,plain,
% 2.70/1.03      ( l1_pre_topc(sK3) = iProver_top ),
% 2.70/1.03      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_293,plain,
% 2.70/1.03      ( m1_subset_1(sK1(sK3),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 2.70/1.03      | v2_struct_0(sK3) = iProver_top
% 2.70/1.03      | l1_pre_topc(sK3) != iProver_top ),
% 2.70/1.03      inference(predicate_to_equality,[status(thm)],[c_292]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_9,plain,
% 2.70/1.03      ( v2_struct_0(X0)
% 2.70/1.03      | ~ v2_pre_topc(X0)
% 2.70/1.03      | ~ l1_pre_topc(X0)
% 2.70/1.03      | ~ v1_xboole_0(sK1(X0)) ),
% 2.70/1.03      inference(cnf_transformation,[],[f57]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_302,plain,
% 2.70/1.03      ( v2_struct_0(X0)
% 2.70/1.03      | ~ l1_pre_topc(X0)
% 2.70/1.03      | ~ v1_xboole_0(sK1(X0))
% 2.70/1.03      | sK3 != X0 ),
% 2.70/1.03      inference(resolution_lifted,[status(thm)],[c_9,c_24]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_303,plain,
% 2.70/1.03      ( v2_struct_0(sK3) | ~ l1_pre_topc(sK3) | ~ v1_xboole_0(sK1(sK3)) ),
% 2.70/1.03      inference(unflattening,[status(thm)],[c_302]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_305,plain,
% 2.70/1.03      ( ~ v1_xboole_0(sK1(sK3)) ),
% 2.70/1.03      inference(global_propositional_subsumption,
% 2.70/1.03                [status(thm)],
% 2.70/1.03                [c_303,c_25,c_23]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_479,plain,
% 2.70/1.03      ( r2_hidden(sK0(X0),X0) | sK1(sK3) != X0 ),
% 2.70/1.03      inference(resolution_lifted,[status(thm)],[c_0,c_305]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_480,plain,
% 2.70/1.03      ( r2_hidden(sK0(sK1(sK3)),sK1(sK3)) ),
% 2.70/1.03      inference(unflattening,[status(thm)],[c_479]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_481,plain,
% 2.70/1.03      ( r2_hidden(sK0(sK1(sK3)),sK1(sK3)) = iProver_top ),
% 2.70/1.03      inference(predicate_to_equality,[status(thm)],[c_480]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_1714,plain,
% 2.70/1.03      ( ~ m1_subset_1(sK1(sK3),k1_zfmisc_1(X0))
% 2.70/1.03      | m1_subset_1(sK0(sK1(sK3)),X0)
% 2.70/1.03      | ~ r2_hidden(sK0(sK1(sK3)),sK1(sK3)) ),
% 2.70/1.03      inference(instantiation,[status(thm)],[c_8]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_1972,plain,
% 2.70/1.03      ( ~ m1_subset_1(sK1(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.70/1.03      | m1_subset_1(sK0(sK1(sK3)),u1_struct_0(sK3))
% 2.70/1.03      | ~ r2_hidden(sK0(sK1(sK3)),sK1(sK3)) ),
% 2.70/1.03      inference(instantiation,[status(thm)],[c_1714]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_1973,plain,
% 2.70/1.03      ( m1_subset_1(sK1(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.70/1.03      | m1_subset_1(sK0(sK1(sK3)),u1_struct_0(sK3)) = iProver_top
% 2.70/1.03      | r2_hidden(sK0(sK1(sK3)),sK1(sK3)) != iProver_top ),
% 2.70/1.03      inference(predicate_to_equality,[status(thm)],[c_1972]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_2925,plain,
% 2.70/1.03      ( m1_subset_1(sK0(sK1(sK3)),u1_struct_0(sK3)) = iProver_top ),
% 2.70/1.03      inference(global_propositional_subsumption,
% 2.70/1.03                [status(thm)],
% 2.70/1.03                [c_2747,c_26,c_28,c_293,c_481,c_1973]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_12,plain,
% 2.70/1.03      ( ~ m1_subset_1(X0,X1)
% 2.70/1.03      | v1_xboole_0(X1)
% 2.70/1.03      | k6_domain_1(X1,X0) = k1_tarski(X0) ),
% 2.70/1.03      inference(cnf_transformation,[],[f59]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_1487,plain,
% 2.70/1.03      ( k6_domain_1(X0,X1) = k1_tarski(X1)
% 2.70/1.03      | m1_subset_1(X1,X0) != iProver_top
% 2.70/1.03      | v1_xboole_0(X0) = iProver_top ),
% 2.70/1.03      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_2930,plain,
% 2.70/1.03      ( k6_domain_1(u1_struct_0(sK3),sK0(sK1(sK3))) = k1_tarski(sK0(sK1(sK3)))
% 2.70/1.03      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 2.70/1.03      inference(superposition,[status(thm)],[c_2925,c_1487]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_6,plain,
% 2.70/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.70/1.03      | ~ r2_hidden(X2,X0)
% 2.70/1.03      | r2_hidden(X2,X1) ),
% 2.70/1.03      inference(cnf_transformation,[],[f53]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_1709,plain,
% 2.70/1.03      ( ~ m1_subset_1(sK1(sK3),k1_zfmisc_1(X0))
% 2.70/1.03      | r2_hidden(sK0(sK1(sK3)),X0)
% 2.70/1.03      | ~ r2_hidden(sK0(sK1(sK3)),sK1(sK3)) ),
% 2.70/1.03      inference(instantiation,[status(thm)],[c_6]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_1967,plain,
% 2.70/1.03      ( ~ m1_subset_1(sK1(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.70/1.03      | r2_hidden(sK0(sK1(sK3)),u1_struct_0(sK3))
% 2.70/1.03      | ~ r2_hidden(sK0(sK1(sK3)),sK1(sK3)) ),
% 2.70/1.03      inference(instantiation,[status(thm)],[c_1709]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_1,plain,
% 2.70/1.03      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.70/1.03      inference(cnf_transformation,[],[f47]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_2134,plain,
% 2.70/1.03      ( ~ r2_hidden(sK0(sK1(sK3)),u1_struct_0(sK3))
% 2.70/1.03      | ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 2.70/1.03      inference(instantiation,[status(thm)],[c_1]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_2190,plain,
% 2.70/1.03      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.70/1.03      | v1_xboole_0(u1_struct_0(sK3))
% 2.70/1.03      | k6_domain_1(u1_struct_0(sK3),X0) = k1_tarski(X0) ),
% 2.70/1.03      inference(instantiation,[status(thm)],[c_12]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_2861,plain,
% 2.70/1.03      ( ~ m1_subset_1(sK0(sK1(sK3)),u1_struct_0(sK3))
% 2.70/1.03      | v1_xboole_0(u1_struct_0(sK3))
% 2.70/1.03      | k6_domain_1(u1_struct_0(sK3),sK0(sK1(sK3))) = k1_tarski(sK0(sK1(sK3))) ),
% 2.70/1.03      inference(instantiation,[status(thm)],[c_2190]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_3016,plain,
% 2.70/1.03      ( k6_domain_1(u1_struct_0(sK3),sK0(sK1(sK3))) = k1_tarski(sK0(sK1(sK3))) ),
% 2.70/1.03      inference(global_propositional_subsumption,
% 2.70/1.03                [status(thm)],
% 2.70/1.03                [c_2930,c_25,c_23,c_292,c_480,c_1967,c_1972,c_2134,c_2861]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_11,plain,
% 2.70/1.03      ( ~ m1_subset_1(X0,X1)
% 2.70/1.03      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
% 2.70/1.03      | v1_xboole_0(X1) ),
% 2.70/1.03      inference(cnf_transformation,[],[f58]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_1488,plain,
% 2.70/1.03      ( m1_subset_1(X0,X1) != iProver_top
% 2.70/1.03      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top
% 2.70/1.03      | v1_xboole_0(X1) = iProver_top ),
% 2.70/1.03      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_3019,plain,
% 2.70/1.03      ( m1_subset_1(k1_tarski(sK0(sK1(sK3))),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 2.70/1.03      | m1_subset_1(sK0(sK1(sK3)),u1_struct_0(sK3)) != iProver_top
% 2.70/1.03      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 2.70/1.03      inference(superposition,[status(thm)],[c_3016,c_1488]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_1968,plain,
% 2.70/1.03      ( m1_subset_1(sK1(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.70/1.03      | r2_hidden(sK0(sK1(sK3)),u1_struct_0(sK3)) = iProver_top
% 2.70/1.03      | r2_hidden(sK0(sK1(sK3)),sK1(sK3)) != iProver_top ),
% 2.70/1.03      inference(predicate_to_equality,[status(thm)],[c_1967]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_2135,plain,
% 2.70/1.03      ( r2_hidden(sK0(sK1(sK3)),u1_struct_0(sK3)) != iProver_top
% 2.70/1.03      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
% 2.70/1.03      inference(predicate_to_equality,[status(thm)],[c_2134]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_3556,plain,
% 2.70/1.03      ( m1_subset_1(k1_tarski(sK0(sK1(sK3))),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 2.70/1.03      inference(global_propositional_subsumption,
% 2.70/1.03                [status(thm)],
% 2.70/1.03                [c_3019,c_26,c_28,c_293,c_481,c_1968,c_1973,c_2135]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_22,negated_conjecture,
% 2.70/1.03      ( v1_xboole_0(sK4) ),
% 2.70/1.03      inference(cnf_transformation,[],[f70]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_1485,plain,
% 2.70/1.03      ( v1_xboole_0(sK4) = iProver_top ),
% 2.70/1.03      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_2,plain,
% 2.70/1.03      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 2.70/1.03      inference(cnf_transformation,[],[f49]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_1492,plain,
% 2.70/1.03      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 2.70/1.03      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_2234,plain,
% 2.70/1.03      ( sK4 = k1_xboole_0 ),
% 2.70/1.03      inference(superposition,[status(thm)],[c_1485,c_1492]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_20,negated_conjecture,
% 2.70/1.03      ( v3_tex_2(sK4,sK3) ),
% 2.70/1.03      inference(cnf_transformation,[],[f72]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_4,plain,
% 2.70/1.03      ( r1_tarski(k1_xboole_0,X0) ),
% 2.70/1.03      inference(cnf_transformation,[],[f51]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_17,plain,
% 2.70/1.03      ( ~ v2_tex_2(X0,X1)
% 2.70/1.03      | ~ v3_tex_2(X2,X1)
% 2.70/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.70/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.70/1.03      | ~ r1_tarski(X2,X0)
% 2.70/1.03      | ~ l1_pre_topc(X1)
% 2.70/1.03      | X0 = X2 ),
% 2.70/1.03      inference(cnf_transformation,[],[f61]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_562,plain,
% 2.70/1.03      ( ~ v2_tex_2(X0,X1)
% 2.70/1.03      | ~ v3_tex_2(X2,X1)
% 2.70/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.70/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.70/1.03      | ~ r1_tarski(X2,X0)
% 2.70/1.03      | X2 = X0
% 2.70/1.03      | sK3 != X1 ),
% 2.70/1.03      inference(resolution_lifted,[status(thm)],[c_17,c_23]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_563,plain,
% 2.70/1.03      ( ~ v2_tex_2(X0,sK3)
% 2.70/1.03      | ~ v3_tex_2(X1,sK3)
% 2.70/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.70/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.70/1.03      | ~ r1_tarski(X1,X0)
% 2.70/1.03      | X1 = X0 ),
% 2.70/1.03      inference(unflattening,[status(thm)],[c_562]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_689,plain,
% 2.70/1.03      ( ~ v2_tex_2(X0,sK3)
% 2.70/1.03      | ~ v3_tex_2(X1,sK3)
% 2.70/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.70/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.70/1.03      | X0 != X2
% 2.70/1.03      | X0 = X1
% 2.70/1.03      | k1_xboole_0 != X1 ),
% 2.70/1.03      inference(resolution_lifted,[status(thm)],[c_4,c_563]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_690,plain,
% 2.70/1.03      ( ~ v2_tex_2(X0,sK3)
% 2.70/1.03      | ~ v3_tex_2(k1_xboole_0,sK3)
% 2.70/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.70/1.03      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.70/1.03      | X0 = k1_xboole_0 ),
% 2.70/1.03      inference(unflattening,[status(thm)],[c_689]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_7,plain,
% 2.70/1.03      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.70/1.03      inference(cnf_transformation,[],[f54]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_704,plain,
% 2.70/1.03      ( ~ v2_tex_2(X0,sK3)
% 2.70/1.03      | ~ v3_tex_2(k1_xboole_0,sK3)
% 2.70/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.70/1.03      | X0 = k1_xboole_0 ),
% 2.70/1.03      inference(forward_subsumption_resolution,[status(thm)],[c_690,c_7]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_731,plain,
% 2.70/1.03      ( ~ v2_tex_2(X0,sK3)
% 2.70/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.70/1.03      | sK3 != sK3
% 2.70/1.03      | sK4 != k1_xboole_0
% 2.70/1.03      | k1_xboole_0 = X0 ),
% 2.70/1.03      inference(resolution_lifted,[status(thm)],[c_20,c_704]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_870,plain,
% 2.70/1.03      ( ~ v2_tex_2(X0,sK3)
% 2.70/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.70/1.03      | sK4 != k1_xboole_0
% 2.70/1.03      | k1_xboole_0 = X0 ),
% 2.70/1.03      inference(equality_resolution_simp,[status(thm)],[c_731]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_1474,plain,
% 2.70/1.03      ( sK4 != k1_xboole_0
% 2.70/1.03      | k1_xboole_0 = X0
% 2.70/1.03      | v2_tex_2(X0,sK3) != iProver_top
% 2.70/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.70/1.03      inference(predicate_to_equality,[status(thm)],[c_870]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_2291,plain,
% 2.70/1.03      ( k1_xboole_0 = X0
% 2.70/1.03      | k1_xboole_0 != k1_xboole_0
% 2.70/1.03      | v2_tex_2(X0,sK3) != iProver_top
% 2.70/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.70/1.03      inference(demodulation,[status(thm)],[c_2234,c_1474]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_2300,plain,
% 2.70/1.03      ( k1_xboole_0 = X0
% 2.70/1.03      | v2_tex_2(X0,sK3) != iProver_top
% 2.70/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.70/1.03      inference(equality_resolution_simp,[status(thm)],[c_2291]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_3565,plain,
% 2.70/1.03      ( k1_tarski(sK0(sK1(sK3))) = k1_xboole_0
% 2.70/1.03      | v2_tex_2(k1_tarski(sK0(sK1(sK3))),sK3) != iProver_top ),
% 2.70/1.03      inference(superposition,[status(thm)],[c_3556,c_2300]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_19,plain,
% 2.70/1.03      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
% 2.70/1.03      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.70/1.03      | v2_struct_0(X0)
% 2.70/1.03      | ~ v2_pre_topc(X0)
% 2.70/1.03      | ~ l1_pre_topc(X0) ),
% 2.70/1.03      inference(cnf_transformation,[],[f66]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_273,plain,
% 2.70/1.03      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
% 2.70/1.03      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.70/1.03      | v2_struct_0(X0)
% 2.70/1.03      | ~ l1_pre_topc(X0)
% 2.70/1.03      | sK3 != X0 ),
% 2.70/1.03      inference(resolution_lifted,[status(thm)],[c_19,c_24]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_274,plain,
% 2.70/1.03      ( v2_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3)
% 2.70/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.70/1.03      | v2_struct_0(sK3)
% 2.70/1.03      | ~ l1_pre_topc(sK3) ),
% 2.70/1.03      inference(unflattening,[status(thm)],[c_273]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_278,plain,
% 2.70/1.03      ( v2_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3)
% 2.70/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 2.70/1.03      inference(global_propositional_subsumption,
% 2.70/1.03                [status(thm)],
% 2.70/1.03                [c_274,c_25,c_23]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_1484,plain,
% 2.70/1.03      ( v2_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3) = iProver_top
% 2.70/1.03      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
% 2.70/1.03      inference(predicate_to_equality,[status(thm)],[c_278]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_3020,plain,
% 2.70/1.03      ( v2_tex_2(k1_tarski(sK0(sK1(sK3))),sK3) = iProver_top
% 2.70/1.03      | m1_subset_1(sK0(sK1(sK3)),u1_struct_0(sK3)) != iProver_top ),
% 2.70/1.03      inference(superposition,[status(thm)],[c_3016,c_1484]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_3741,plain,
% 2.70/1.03      ( k1_tarski(sK0(sK1(sK3))) = k1_xboole_0 ),
% 2.70/1.03      inference(global_propositional_subsumption,
% 2.70/1.03                [status(thm)],
% 2.70/1.03                [c_3565,c_26,c_28,c_293,c_481,c_1973,c_3020]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_3,plain,
% 2.70/1.03      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 2.70/1.03      inference(cnf_transformation,[],[f50]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_5,plain,
% 2.70/1.03      ( k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
% 2.70/1.03      inference(cnf_transformation,[],[f52]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_1945,plain,
% 2.70/1.03      ( k1_tarski(X0) != k1_xboole_0 ),
% 2.70/1.03      inference(superposition,[status(thm)],[c_3,c_5]) ).
% 2.70/1.03  
% 2.70/1.03  cnf(c_3744,plain,
% 2.70/1.03      ( $false ),
% 2.70/1.03      inference(forward_subsumption_resolution,[status(thm)],[c_3741,c_1945]) ).
% 2.70/1.03  
% 2.70/1.03  
% 2.70/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 2.70/1.03  
% 2.70/1.03  ------                               Statistics
% 2.70/1.03  
% 2.70/1.03  ------ General
% 2.70/1.03  
% 2.70/1.03  abstr_ref_over_cycles:                  0
% 2.70/1.03  abstr_ref_under_cycles:                 0
% 2.70/1.03  gc_basic_clause_elim:                   0
% 2.70/1.03  forced_gc_time:                         0
% 2.70/1.03  parsing_time:                           0.012
% 2.70/1.03  unif_index_cands_time:                  0.
% 2.70/1.03  unif_index_add_time:                    0.
% 2.70/1.03  orderings_time:                         0.
% 2.70/1.03  out_proof_time:                         0.007
% 2.70/1.03  total_time:                             0.155
% 2.70/1.03  num_of_symbols:                         52
% 2.70/1.03  num_of_terms:                           2413
% 2.70/1.03  
% 2.70/1.03  ------ Preprocessing
% 2.70/1.03  
% 2.70/1.03  num_of_splits:                          3
% 2.70/1.03  num_of_split_atoms:                     1
% 2.70/1.03  num_of_reused_defs:                     2
% 2.70/1.03  num_eq_ax_congr_red:                    16
% 2.70/1.03  num_of_sem_filtered_clauses:            1
% 2.70/1.03  num_of_subtypes:                        0
% 2.70/1.03  monotx_restored_types:                  0
% 2.70/1.03  sat_num_of_epr_types:                   0
% 2.70/1.03  sat_num_of_non_cyclic_types:            0
% 2.70/1.03  sat_guarded_non_collapsed_types:        0
% 2.70/1.03  num_pure_diseq_elim:                    0
% 2.70/1.03  simp_replaced_by:                       0
% 2.70/1.03  res_preprocessed:                       113
% 2.70/1.03  prep_upred:                             0
% 2.70/1.03  prep_unflattend:                        37
% 2.70/1.03  smt_new_axioms:                         0
% 2.70/1.03  pred_elim_cands:                        4
% 2.70/1.03  pred_elim:                              5
% 2.70/1.03  pred_elim_cl:                           6
% 2.70/1.03  pred_elim_cycles:                       9
% 2.70/1.03  merged_defs:                            0
% 2.70/1.03  merged_defs_ncl:                        0
% 2.70/1.03  bin_hyper_res:                          0
% 2.70/1.03  prep_cycles:                            4
% 2.70/1.03  pred_elim_time:                         0.013
% 2.70/1.03  splitting_time:                         0.
% 2.70/1.03  sem_filter_time:                        0.
% 2.70/1.03  monotx_time:                            0.
% 2.70/1.03  subtype_inf_time:                       0.
% 2.70/1.03  
% 2.70/1.03  ------ Problem properties
% 2.70/1.03  
% 2.70/1.03  clauses:                                23
% 2.70/1.03  conjectures:                            2
% 2.70/1.03  epr:                                    4
% 2.70/1.03  horn:                                   18
% 2.70/1.03  ground:                                 8
% 2.70/1.03  unary:                                  8
% 2.70/1.03  binary:                                 4
% 2.70/1.03  lits:                                   53
% 2.70/1.03  lits_eq:                                10
% 2.70/1.03  fd_pure:                                0
% 2.70/1.03  fd_pseudo:                              0
% 2.70/1.03  fd_cond:                                5
% 2.70/1.03  fd_pseudo_cond:                         0
% 2.70/1.03  ac_symbols:                             0
% 2.70/1.03  
% 2.70/1.03  ------ Propositional Solver
% 2.70/1.03  
% 2.70/1.03  prop_solver_calls:                      28
% 2.70/1.03  prop_fast_solver_calls:                 834
% 2.70/1.03  smt_solver_calls:                       0
% 2.70/1.03  smt_fast_solver_calls:                  0
% 2.70/1.03  prop_num_of_clauses:                    1208
% 2.70/1.03  prop_preprocess_simplified:             4220
% 2.70/1.03  prop_fo_subsumed:                       27
% 2.70/1.03  prop_solver_time:                       0.
% 2.70/1.03  smt_solver_time:                        0.
% 2.70/1.03  smt_fast_solver_time:                   0.
% 2.70/1.03  prop_fast_solver_time:                  0.
% 2.70/1.03  prop_unsat_core_time:                   0.
% 2.70/1.03  
% 2.70/1.03  ------ QBF
% 2.70/1.03  
% 2.70/1.03  qbf_q_res:                              0
% 2.70/1.03  qbf_num_tautologies:                    0
% 2.70/1.03  qbf_prep_cycles:                        0
% 2.70/1.03  
% 2.70/1.03  ------ BMC1
% 2.70/1.03  
% 2.70/1.03  bmc1_current_bound:                     -1
% 2.70/1.03  bmc1_last_solved_bound:                 -1
% 2.70/1.03  bmc1_unsat_core_size:                   -1
% 2.70/1.03  bmc1_unsat_core_parents_size:           -1
% 2.70/1.03  bmc1_merge_next_fun:                    0
% 2.70/1.03  bmc1_unsat_core_clauses_time:           0.
% 2.70/1.03  
% 2.70/1.03  ------ Instantiation
% 2.70/1.03  
% 2.70/1.03  inst_num_of_clauses:                    368
% 2.70/1.03  inst_num_in_passive:                    91
% 2.70/1.03  inst_num_in_active:                     223
% 2.70/1.03  inst_num_in_unprocessed:                54
% 2.70/1.03  inst_num_of_loops:                      250
% 2.70/1.03  inst_num_of_learning_restarts:          0
% 2.70/1.03  inst_num_moves_active_passive:          24
% 2.70/1.03  inst_lit_activity:                      0
% 2.70/1.03  inst_lit_activity_moves:                0
% 2.70/1.03  inst_num_tautologies:                   0
% 2.70/1.03  inst_num_prop_implied:                  0
% 2.70/1.03  inst_num_existing_simplified:           0
% 2.70/1.03  inst_num_eq_res_simplified:             0
% 2.70/1.03  inst_num_child_elim:                    0
% 2.70/1.03  inst_num_of_dismatching_blockings:      115
% 2.70/1.03  inst_num_of_non_proper_insts:           333
% 2.70/1.03  inst_num_of_duplicates:                 0
% 2.70/1.03  inst_inst_num_from_inst_to_res:         0
% 2.70/1.03  inst_dismatching_checking_time:         0.
% 2.70/1.03  
% 2.70/1.03  ------ Resolution
% 2.70/1.03  
% 2.70/1.03  res_num_of_clauses:                     0
% 2.70/1.03  res_num_in_passive:                     0
% 2.70/1.03  res_num_in_active:                      0
% 2.70/1.03  res_num_of_loops:                       117
% 2.70/1.03  res_forward_subset_subsumed:            26
% 2.70/1.03  res_backward_subset_subsumed:           2
% 2.70/1.03  res_forward_subsumed:                   0
% 2.70/1.03  res_backward_subsumed:                  0
% 2.70/1.03  res_forward_subsumption_resolution:     5
% 2.70/1.03  res_backward_subsumption_resolution:    0
% 2.70/1.03  res_clause_to_clause_subsumption:       105
% 2.70/1.03  res_orphan_elimination:                 0
% 2.70/1.03  res_tautology_del:                      25
% 2.70/1.03  res_num_eq_res_simplified:              1
% 2.70/1.03  res_num_sel_changes:                    0
% 2.70/1.03  res_moves_from_active_to_pass:          0
% 2.70/1.03  
% 2.70/1.03  ------ Superposition
% 2.70/1.03  
% 2.70/1.03  sup_time_total:                         0.
% 2.70/1.03  sup_time_generating:                    0.
% 2.70/1.03  sup_time_sim_full:                      0.
% 2.70/1.03  sup_time_sim_immed:                     0.
% 2.70/1.03  
% 2.70/1.03  sup_num_of_clauses:                     60
% 2.70/1.03  sup_num_in_active:                      42
% 2.70/1.03  sup_num_in_passive:                     18
% 2.70/1.03  sup_num_of_loops:                       49
% 2.70/1.03  sup_fw_superposition:                   36
% 2.70/1.03  sup_bw_superposition:                   17
% 2.70/1.03  sup_immediate_simplified:               5
% 2.70/1.03  sup_given_eliminated:                   0
% 2.70/1.03  comparisons_done:                       0
% 2.70/1.03  comparisons_avoided:                    9
% 2.70/1.03  
% 2.70/1.03  ------ Simplifications
% 2.70/1.03  
% 2.70/1.03  
% 2.70/1.03  sim_fw_subset_subsumed:                 3
% 2.70/1.03  sim_bw_subset_subsumed:                 3
% 2.70/1.03  sim_fw_subsumed:                        1
% 2.70/1.03  sim_bw_subsumed:                        0
% 2.70/1.03  sim_fw_subsumption_res:                 1
% 2.70/1.03  sim_bw_subsumption_res:                 0
% 2.70/1.03  sim_tautology_del:                      2
% 2.70/1.03  sim_eq_tautology_del:                   3
% 2.70/1.03  sim_eq_res_simp:                        1
% 2.70/1.03  sim_fw_demodulated:                     0
% 2.70/1.03  sim_bw_demodulated:                     4
% 2.70/1.03  sim_light_normalised:                   1
% 2.70/1.03  sim_joinable_taut:                      0
% 2.70/1.03  sim_joinable_simp:                      0
% 2.70/1.03  sim_ac_normalised:                      0
% 2.70/1.03  sim_smt_subsumption:                    0
% 2.70/1.03  
%------------------------------------------------------------------------------
