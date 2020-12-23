%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:26:59 EST 2020

% Result     : Theorem 3.01s
% Output     : CNFRefutation 3.01s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 722 expanded)
%              Number of clauses        :   69 ( 199 expanded)
%              Number of leaves         :   21 ( 188 expanded)
%              Depth                    :   21
%              Number of atoms          :  480 (3379 expanded)
%              Number of equality atoms :  117 ( 232 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v4_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_xboole_0(sK1(X0))
        & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ( ~ v1_xboole_0(sK1(X0))
        & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f39])).

fof(f61,plain,(
    ! [X0] :
      ( m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => ~ v3_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => ~ v3_tex_2(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f47,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
     => ( v3_tex_2(sK4,X0)
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0)))
        & v1_xboole_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
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

fof(f48,plain,
    ( v3_tex_2(sK4,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    & v1_xboole_0(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f36,f47,f46])).

fof(f73,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f72,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f74,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f10,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ~ ( k4_tarski(X2,X3) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] :
            ( k4_tarski(X2,X3) != sK0(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK0(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ( ! [X2,X3] :
            ( k4_tarski(X2,X3) != sK0(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK0(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f37])).

fof(f58,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK1(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f75,plain,(
    v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f50,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f77,plain,(
    v3_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f14,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

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
            & ( ( ! [X2] :
                    ( X1 = X2
                    | ~ r1_tarski(X1,X2)
                    | ~ v2_tex_2(X2,X0)
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f32])).

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
    inference(flattening,[],[f41])).

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
            & ( ( ! [X3] :
                    ( X1 = X3
                    | ~ r1_tarski(X1,X3)
                    | ~ v2_tex_2(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f42])).

fof(f44,plain,(
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

fof(f45,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f43,f44])).

fof(f66,plain,(
    ! [X0,X3,X1] :
      ( X1 = X3
      | ~ r1_tarski(X1,X3)
      | ~ v2_tex_2(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f5,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f5])).

cnf(c_13,plain,
    ( m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_27,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_320,plain,
    ( m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_27])).

cnf(c_321,plain,
    ( m1_subset_1(sK1(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_320])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_26,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_323,plain,
    ( m1_subset_1(sK1(sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_321,c_28,c_26])).

cnf(c_1264,plain,
    ( m1_subset_1(sK1(sK3),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_323])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_11,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_367,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | X3 != X2
    | sK0(X3) != X0
    | k1_xboole_0 = X3 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_11])).

cnf(c_368,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(sK0(X0),X1)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_367])).

cnf(c_1262,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(sK0(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_368])).

cnf(c_2692,plain,
    ( sK1(sK3) = k1_xboole_0
    | m1_subset_1(sK0(sK1(sK3)),u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1264,c_1262])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_12,plain,
    ( v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(sK1(X0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_331,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(sK1(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_27])).

cnf(c_332,plain,
    ( v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v1_xboole_0(sK1(sK3)) ),
    inference(unflattening,[status(thm)],[c_331])).

cnf(c_914,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1420,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK1(sK3))
    | sK1(sK3) != X0 ),
    inference(instantiation,[status(thm)],[c_914])).

cnf(c_1422,plain,
    ( v1_xboole_0(sK1(sK3))
    | ~ v1_xboole_0(k1_xboole_0)
    | sK1(sK3) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1420])).

cnf(c_3109,plain,
    ( m1_subset_1(sK0(sK1(sK3)),u1_struct_0(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2692,c_28,c_26,c_0,c_332,c_1422])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1268,plain,
    ( k6_domain_1(X0,X1) = k1_tarski(X1)
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3114,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK0(sK1(sK3))) = k1_tarski(sK0(sK1(sK3)))
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3109,c_1268])).

cnf(c_29,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_31,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_322,plain,
    ( m1_subset_1(sK1(sK3),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_321])).

cnf(c_333,plain,
    ( v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_xboole_0(sK1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_332])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1415,plain,
    ( ~ m1_subset_1(sK1(sK3),k1_zfmisc_1(X0))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(sK1(sK3)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1499,plain,
    ( ~ m1_subset_1(sK1(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_xboole_0(u1_struct_0(sK3))
    | v1_xboole_0(sK1(sK3)) ),
    inference(instantiation,[status(thm)],[c_1415])).

cnf(c_1500,plain,
    ( m1_subset_1(sK1(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(sK1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1499])).

cnf(c_3263,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK0(sK1(sK3))) = k1_tarski(sK0(sK1(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3114,c_29,c_31,c_322,c_333,c_1500])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1269,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3266,plain,
    ( m1_subset_1(sK0(sK1(sK3)),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k1_tarski(sK0(sK1(sK3))),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3263,c_1269])).

cnf(c_3527,plain,
    ( m1_subset_1(k1_tarski(sK0(sK1(sK3))),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3266,c_28,c_29,c_26,c_31,c_0,c_322,c_332,c_333,c_1422,c_1500,c_2692])).

cnf(c_25,negated_conjecture,
    ( v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1266,plain,
    ( v1_xboole_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1272,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2031,plain,
    ( sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1266,c_1272])).

cnf(c_23,negated_conjecture,
    ( v3_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_20,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ v3_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | ~ l1_pre_topc(X1)
    | X0 = X2 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_493,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ v3_tex_2(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | X2 = X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_26])).

cnf(c_494,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ v3_tex_2(X1,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(unflattening,[status(thm)],[c_493])).

cnf(c_620,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ v3_tex_2(X1,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | X0 != X2
    | X0 = X1
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_494])).

cnf(c_621,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ v3_tex_2(k1_xboole_0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3)))
    | X0 = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_620])).

cnf(c_5,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_635,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ v3_tex_2(k1_xboole_0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | X0 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_621,c_5])).

cnf(c_662,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | sK3 != sK3
    | sK4 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_635])).

cnf(c_801,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | sK4 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_662])).

cnf(c_1253,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = X0
    | v2_tex_2(X0,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_801])).

cnf(c_2035,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 != k1_xboole_0
    | v2_tex_2(X0,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2031,c_1253])).

cnf(c_2042,plain,
    ( k1_xboole_0 = X0
    | v2_tex_2(X0,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2035])).

cnf(c_3535,plain,
    ( k1_tarski(sK0(sK1(sK3))) = k1_xboole_0
    | v2_tex_2(k1_tarski(sK0(sK1(sK3))),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3527,c_2042])).

cnf(c_22,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_302,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_27])).

cnf(c_303,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_302])).

cnf(c_307,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_303,c_28,c_26])).

cnf(c_1265,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_307])).

cnf(c_3267,plain,
    ( v2_tex_2(k1_tarski(sK0(sK1(sK3))),sK3) = iProver_top
    | m1_subset_1(sK0(sK1(sK3)),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3263,c_1265])).

cnf(c_3552,plain,
    ( k1_tarski(sK0(sK1(sK3))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3535,c_28,c_26,c_0,c_332,c_1422,c_2692,c_3267])).

cnf(c_2,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_4,plain,
    ( k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1809,plain,
    ( k1_tarski(X0) != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2,c_4])).

cnf(c_3555,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3552,c_1809])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:38:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.01/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.01/1.00  
% 3.01/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.01/1.00  
% 3.01/1.00  ------  iProver source info
% 3.01/1.00  
% 3.01/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.01/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.01/1.00  git: non_committed_changes: false
% 3.01/1.00  git: last_make_outside_of_git: false
% 3.01/1.00  
% 3.01/1.00  ------ 
% 3.01/1.00  
% 3.01/1.00  ------ Input Options
% 3.01/1.00  
% 3.01/1.00  --out_options                           all
% 3.01/1.00  --tptp_safe_out                         true
% 3.01/1.00  --problem_path                          ""
% 3.01/1.00  --include_path                          ""
% 3.01/1.00  --clausifier                            res/vclausify_rel
% 3.01/1.00  --clausifier_options                    --mode clausify
% 3.01/1.00  --stdin                                 false
% 3.01/1.00  --stats_out                             all
% 3.01/1.00  
% 3.01/1.00  ------ General Options
% 3.01/1.00  
% 3.01/1.00  --fof                                   false
% 3.01/1.00  --time_out_real                         305.
% 3.01/1.00  --time_out_virtual                      -1.
% 3.01/1.00  --symbol_type_check                     false
% 3.01/1.00  --clausify_out                          false
% 3.01/1.00  --sig_cnt_out                           false
% 3.01/1.00  --trig_cnt_out                          false
% 3.01/1.00  --trig_cnt_out_tolerance                1.
% 3.01/1.00  --trig_cnt_out_sk_spl                   false
% 3.01/1.00  --abstr_cl_out                          false
% 3.01/1.00  
% 3.01/1.00  ------ Global Options
% 3.01/1.00  
% 3.01/1.00  --schedule                              default
% 3.01/1.00  --add_important_lit                     false
% 3.01/1.00  --prop_solver_per_cl                    1000
% 3.01/1.00  --min_unsat_core                        false
% 3.01/1.00  --soft_assumptions                      false
% 3.01/1.00  --soft_lemma_size                       3
% 3.01/1.00  --prop_impl_unit_size                   0
% 3.01/1.00  --prop_impl_unit                        []
% 3.01/1.00  --share_sel_clauses                     true
% 3.01/1.00  --reset_solvers                         false
% 3.01/1.00  --bc_imp_inh                            [conj_cone]
% 3.01/1.00  --conj_cone_tolerance                   3.
% 3.01/1.00  --extra_neg_conj                        none
% 3.01/1.00  --large_theory_mode                     true
% 3.01/1.00  --prolific_symb_bound                   200
% 3.01/1.00  --lt_threshold                          2000
% 3.01/1.00  --clause_weak_htbl                      true
% 3.01/1.00  --gc_record_bc_elim                     false
% 3.01/1.00  
% 3.01/1.00  ------ Preprocessing Options
% 3.01/1.00  
% 3.01/1.00  --preprocessing_flag                    true
% 3.01/1.00  --time_out_prep_mult                    0.1
% 3.01/1.00  --splitting_mode                        input
% 3.01/1.00  --splitting_grd                         true
% 3.01/1.00  --splitting_cvd                         false
% 3.01/1.00  --splitting_cvd_svl                     false
% 3.01/1.00  --splitting_nvd                         32
% 3.01/1.00  --sub_typing                            true
% 3.01/1.00  --prep_gs_sim                           true
% 3.01/1.00  --prep_unflatten                        true
% 3.01/1.00  --prep_res_sim                          true
% 3.01/1.00  --prep_upred                            true
% 3.01/1.00  --prep_sem_filter                       exhaustive
% 3.01/1.00  --prep_sem_filter_out                   false
% 3.01/1.00  --pred_elim                             true
% 3.01/1.00  --res_sim_input                         true
% 3.01/1.00  --eq_ax_congr_red                       true
% 3.01/1.00  --pure_diseq_elim                       true
% 3.01/1.00  --brand_transform                       false
% 3.01/1.00  --non_eq_to_eq                          false
% 3.01/1.00  --prep_def_merge                        true
% 3.01/1.00  --prep_def_merge_prop_impl              false
% 3.01/1.00  --prep_def_merge_mbd                    true
% 3.01/1.00  --prep_def_merge_tr_red                 false
% 3.01/1.00  --prep_def_merge_tr_cl                  false
% 3.01/1.00  --smt_preprocessing                     true
% 3.01/1.00  --smt_ac_axioms                         fast
% 3.01/1.00  --preprocessed_out                      false
% 3.01/1.00  --preprocessed_stats                    false
% 3.01/1.00  
% 3.01/1.00  ------ Abstraction refinement Options
% 3.01/1.00  
% 3.01/1.00  --abstr_ref                             []
% 3.01/1.00  --abstr_ref_prep                        false
% 3.01/1.00  --abstr_ref_until_sat                   false
% 3.01/1.00  --abstr_ref_sig_restrict                funpre
% 3.01/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.01/1.00  --abstr_ref_under                       []
% 3.01/1.00  
% 3.01/1.00  ------ SAT Options
% 3.01/1.00  
% 3.01/1.00  --sat_mode                              false
% 3.01/1.00  --sat_fm_restart_options                ""
% 3.01/1.00  --sat_gr_def                            false
% 3.01/1.00  --sat_epr_types                         true
% 3.01/1.00  --sat_non_cyclic_types                  false
% 3.01/1.00  --sat_finite_models                     false
% 3.01/1.00  --sat_fm_lemmas                         false
% 3.01/1.00  --sat_fm_prep                           false
% 3.01/1.00  --sat_fm_uc_incr                        true
% 3.01/1.00  --sat_out_model                         small
% 3.01/1.00  --sat_out_clauses                       false
% 3.01/1.00  
% 3.01/1.00  ------ QBF Options
% 3.01/1.00  
% 3.01/1.00  --qbf_mode                              false
% 3.01/1.00  --qbf_elim_univ                         false
% 3.01/1.00  --qbf_dom_inst                          none
% 3.01/1.00  --qbf_dom_pre_inst                      false
% 3.01/1.00  --qbf_sk_in                             false
% 3.01/1.00  --qbf_pred_elim                         true
% 3.01/1.00  --qbf_split                             512
% 3.01/1.00  
% 3.01/1.00  ------ BMC1 Options
% 3.01/1.00  
% 3.01/1.00  --bmc1_incremental                      false
% 3.01/1.00  --bmc1_axioms                           reachable_all
% 3.01/1.00  --bmc1_min_bound                        0
% 3.01/1.00  --bmc1_max_bound                        -1
% 3.01/1.00  --bmc1_max_bound_default                -1
% 3.01/1.00  --bmc1_symbol_reachability              true
% 3.01/1.00  --bmc1_property_lemmas                  false
% 3.01/1.00  --bmc1_k_induction                      false
% 3.01/1.00  --bmc1_non_equiv_states                 false
% 3.01/1.00  --bmc1_deadlock                         false
% 3.01/1.00  --bmc1_ucm                              false
% 3.01/1.00  --bmc1_add_unsat_core                   none
% 3.01/1.00  --bmc1_unsat_core_children              false
% 3.01/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.01/1.00  --bmc1_out_stat                         full
% 3.01/1.00  --bmc1_ground_init                      false
% 3.01/1.00  --bmc1_pre_inst_next_state              false
% 3.01/1.00  --bmc1_pre_inst_state                   false
% 3.01/1.00  --bmc1_pre_inst_reach_state             false
% 3.01/1.00  --bmc1_out_unsat_core                   false
% 3.01/1.00  --bmc1_aig_witness_out                  false
% 3.01/1.00  --bmc1_verbose                          false
% 3.01/1.00  --bmc1_dump_clauses_tptp                false
% 3.01/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.01/1.00  --bmc1_dump_file                        -
% 3.01/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.01/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.01/1.00  --bmc1_ucm_extend_mode                  1
% 3.01/1.00  --bmc1_ucm_init_mode                    2
% 3.01/1.00  --bmc1_ucm_cone_mode                    none
% 3.01/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.01/1.00  --bmc1_ucm_relax_model                  4
% 3.01/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.01/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.01/1.00  --bmc1_ucm_layered_model                none
% 3.01/1.00  --bmc1_ucm_max_lemma_size               10
% 3.01/1.00  
% 3.01/1.00  ------ AIG Options
% 3.01/1.00  
% 3.01/1.00  --aig_mode                              false
% 3.01/1.00  
% 3.01/1.00  ------ Instantiation Options
% 3.01/1.00  
% 3.01/1.00  --instantiation_flag                    true
% 3.01/1.00  --inst_sos_flag                         false
% 3.01/1.00  --inst_sos_phase                        true
% 3.01/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.01/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.01/1.00  --inst_lit_sel_side                     num_symb
% 3.01/1.00  --inst_solver_per_active                1400
% 3.01/1.00  --inst_solver_calls_frac                1.
% 3.01/1.00  --inst_passive_queue_type               priority_queues
% 3.01/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.01/1.00  --inst_passive_queues_freq              [25;2]
% 3.01/1.00  --inst_dismatching                      true
% 3.01/1.00  --inst_eager_unprocessed_to_passive     true
% 3.01/1.00  --inst_prop_sim_given                   true
% 3.01/1.00  --inst_prop_sim_new                     false
% 3.01/1.00  --inst_subs_new                         false
% 3.01/1.00  --inst_eq_res_simp                      false
% 3.01/1.00  --inst_subs_given                       false
% 3.01/1.00  --inst_orphan_elimination               true
% 3.01/1.00  --inst_learning_loop_flag               true
% 3.01/1.00  --inst_learning_start                   3000
% 3.01/1.00  --inst_learning_factor                  2
% 3.01/1.00  --inst_start_prop_sim_after_learn       3
% 3.01/1.00  --inst_sel_renew                        solver
% 3.01/1.00  --inst_lit_activity_flag                true
% 3.01/1.00  --inst_restr_to_given                   false
% 3.01/1.00  --inst_activity_threshold               500
% 3.01/1.00  --inst_out_proof                        true
% 3.01/1.00  
% 3.01/1.00  ------ Resolution Options
% 3.01/1.00  
% 3.01/1.00  --resolution_flag                       true
% 3.01/1.00  --res_lit_sel                           adaptive
% 3.01/1.00  --res_lit_sel_side                      none
% 3.01/1.00  --res_ordering                          kbo
% 3.01/1.00  --res_to_prop_solver                    active
% 3.01/1.00  --res_prop_simpl_new                    false
% 3.01/1.00  --res_prop_simpl_given                  true
% 3.01/1.00  --res_passive_queue_type                priority_queues
% 3.01/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.01/1.00  --res_passive_queues_freq               [15;5]
% 3.01/1.00  --res_forward_subs                      full
% 3.01/1.00  --res_backward_subs                     full
% 3.01/1.00  --res_forward_subs_resolution           true
% 3.01/1.00  --res_backward_subs_resolution          true
% 3.01/1.00  --res_orphan_elimination                true
% 3.01/1.00  --res_time_limit                        2.
% 3.01/1.00  --res_out_proof                         true
% 3.01/1.00  
% 3.01/1.00  ------ Superposition Options
% 3.01/1.00  
% 3.01/1.00  --superposition_flag                    true
% 3.01/1.00  --sup_passive_queue_type                priority_queues
% 3.01/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.01/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.01/1.00  --demod_completeness_check              fast
% 3.01/1.00  --demod_use_ground                      true
% 3.01/1.00  --sup_to_prop_solver                    passive
% 3.01/1.00  --sup_prop_simpl_new                    true
% 3.01/1.00  --sup_prop_simpl_given                  true
% 3.01/1.00  --sup_fun_splitting                     false
% 3.01/1.00  --sup_smt_interval                      50000
% 3.01/1.00  
% 3.01/1.00  ------ Superposition Simplification Setup
% 3.01/1.00  
% 3.01/1.00  --sup_indices_passive                   []
% 3.01/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.01/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/1.00  --sup_full_bw                           [BwDemod]
% 3.01/1.00  --sup_immed_triv                        [TrivRules]
% 3.01/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.01/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/1.00  --sup_immed_bw_main                     []
% 3.01/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.01/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.01/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.01/1.00  
% 3.01/1.00  ------ Combination Options
% 3.01/1.00  
% 3.01/1.00  --comb_res_mult                         3
% 3.01/1.00  --comb_sup_mult                         2
% 3.01/1.00  --comb_inst_mult                        10
% 3.01/1.00  
% 3.01/1.00  ------ Debug Options
% 3.01/1.00  
% 3.01/1.00  --dbg_backtrace                         false
% 3.01/1.00  --dbg_dump_prop_clauses                 false
% 3.01/1.00  --dbg_dump_prop_clauses_file            -
% 3.01/1.00  --dbg_out_stat                          false
% 3.01/1.00  ------ Parsing...
% 3.01/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.01/1.00  
% 3.01/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 3.01/1.00  
% 3.01/1.00  ------ Preprocessing... gs_s  sp: 3 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.01/1.00  
% 3.01/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.01/1.00  ------ Proving...
% 3.01/1.00  ------ Problem Properties 
% 3.01/1.00  
% 3.01/1.00  
% 3.01/1.00  clauses                                 25
% 3.01/1.00  conjectures                             2
% 3.01/1.00  EPR                                     4
% 3.01/1.00  Horn                                    19
% 3.01/1.00  unary                                   9
% 3.01/1.00  binary                                  5
% 3.01/1.00  lits                                    56
% 3.01/1.00  lits eq                                 16
% 3.01/1.00  fd_pure                                 0
% 3.01/1.00  fd_pseudo                               0
% 3.01/1.00  fd_cond                                 9
% 3.01/1.00  fd_pseudo_cond                          0
% 3.01/1.00  AC symbols                              0
% 3.01/1.00  
% 3.01/1.00  ------ Schedule dynamic 5 is on 
% 3.01/1.00  
% 3.01/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.01/1.00  
% 3.01/1.00  
% 3.01/1.00  ------ 
% 3.01/1.00  Current options:
% 3.01/1.00  ------ 
% 3.01/1.00  
% 3.01/1.00  ------ Input Options
% 3.01/1.00  
% 3.01/1.00  --out_options                           all
% 3.01/1.00  --tptp_safe_out                         true
% 3.01/1.00  --problem_path                          ""
% 3.01/1.00  --include_path                          ""
% 3.01/1.00  --clausifier                            res/vclausify_rel
% 3.01/1.00  --clausifier_options                    --mode clausify
% 3.01/1.00  --stdin                                 false
% 3.01/1.00  --stats_out                             all
% 3.01/1.00  
% 3.01/1.00  ------ General Options
% 3.01/1.00  
% 3.01/1.00  --fof                                   false
% 3.01/1.00  --time_out_real                         305.
% 3.01/1.00  --time_out_virtual                      -1.
% 3.01/1.00  --symbol_type_check                     false
% 3.01/1.00  --clausify_out                          false
% 3.01/1.00  --sig_cnt_out                           false
% 3.01/1.00  --trig_cnt_out                          false
% 3.01/1.00  --trig_cnt_out_tolerance                1.
% 3.01/1.00  --trig_cnt_out_sk_spl                   false
% 3.01/1.00  --abstr_cl_out                          false
% 3.01/1.00  
% 3.01/1.00  ------ Global Options
% 3.01/1.00  
% 3.01/1.00  --schedule                              default
% 3.01/1.00  --add_important_lit                     false
% 3.01/1.00  --prop_solver_per_cl                    1000
% 3.01/1.00  --min_unsat_core                        false
% 3.01/1.00  --soft_assumptions                      false
% 3.01/1.00  --soft_lemma_size                       3
% 3.01/1.00  --prop_impl_unit_size                   0
% 3.01/1.00  --prop_impl_unit                        []
% 3.01/1.00  --share_sel_clauses                     true
% 3.01/1.00  --reset_solvers                         false
% 3.01/1.00  --bc_imp_inh                            [conj_cone]
% 3.01/1.00  --conj_cone_tolerance                   3.
% 3.01/1.00  --extra_neg_conj                        none
% 3.01/1.00  --large_theory_mode                     true
% 3.01/1.00  --prolific_symb_bound                   200
% 3.01/1.00  --lt_threshold                          2000
% 3.01/1.00  --clause_weak_htbl                      true
% 3.01/1.00  --gc_record_bc_elim                     false
% 3.01/1.00  
% 3.01/1.00  ------ Preprocessing Options
% 3.01/1.00  
% 3.01/1.00  --preprocessing_flag                    true
% 3.01/1.00  --time_out_prep_mult                    0.1
% 3.01/1.00  --splitting_mode                        input
% 3.01/1.00  --splitting_grd                         true
% 3.01/1.00  --splitting_cvd                         false
% 3.01/1.00  --splitting_cvd_svl                     false
% 3.01/1.00  --splitting_nvd                         32
% 3.01/1.00  --sub_typing                            true
% 3.01/1.00  --prep_gs_sim                           true
% 3.01/1.00  --prep_unflatten                        true
% 3.01/1.00  --prep_res_sim                          true
% 3.01/1.00  --prep_upred                            true
% 3.01/1.00  --prep_sem_filter                       exhaustive
% 3.01/1.00  --prep_sem_filter_out                   false
% 3.01/1.00  --pred_elim                             true
% 3.01/1.00  --res_sim_input                         true
% 3.01/1.00  --eq_ax_congr_red                       true
% 3.01/1.00  --pure_diseq_elim                       true
% 3.01/1.00  --brand_transform                       false
% 3.01/1.00  --non_eq_to_eq                          false
% 3.01/1.00  --prep_def_merge                        true
% 3.01/1.00  --prep_def_merge_prop_impl              false
% 3.01/1.00  --prep_def_merge_mbd                    true
% 3.01/1.00  --prep_def_merge_tr_red                 false
% 3.01/1.00  --prep_def_merge_tr_cl                  false
% 3.01/1.00  --smt_preprocessing                     true
% 3.01/1.00  --smt_ac_axioms                         fast
% 3.01/1.00  --preprocessed_out                      false
% 3.01/1.00  --preprocessed_stats                    false
% 3.01/1.00  
% 3.01/1.00  ------ Abstraction refinement Options
% 3.01/1.00  
% 3.01/1.00  --abstr_ref                             []
% 3.01/1.00  --abstr_ref_prep                        false
% 3.01/1.00  --abstr_ref_until_sat                   false
% 3.01/1.00  --abstr_ref_sig_restrict                funpre
% 3.01/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.01/1.00  --abstr_ref_under                       []
% 3.01/1.00  
% 3.01/1.00  ------ SAT Options
% 3.01/1.00  
% 3.01/1.00  --sat_mode                              false
% 3.01/1.00  --sat_fm_restart_options                ""
% 3.01/1.00  --sat_gr_def                            false
% 3.01/1.00  --sat_epr_types                         true
% 3.01/1.00  --sat_non_cyclic_types                  false
% 3.01/1.00  --sat_finite_models                     false
% 3.01/1.00  --sat_fm_lemmas                         false
% 3.01/1.00  --sat_fm_prep                           false
% 3.01/1.00  --sat_fm_uc_incr                        true
% 3.01/1.00  --sat_out_model                         small
% 3.01/1.00  --sat_out_clauses                       false
% 3.01/1.00  
% 3.01/1.00  ------ QBF Options
% 3.01/1.00  
% 3.01/1.00  --qbf_mode                              false
% 3.01/1.00  --qbf_elim_univ                         false
% 3.01/1.00  --qbf_dom_inst                          none
% 3.01/1.00  --qbf_dom_pre_inst                      false
% 3.01/1.00  --qbf_sk_in                             false
% 3.01/1.00  --qbf_pred_elim                         true
% 3.01/1.00  --qbf_split                             512
% 3.01/1.00  
% 3.01/1.00  ------ BMC1 Options
% 3.01/1.00  
% 3.01/1.00  --bmc1_incremental                      false
% 3.01/1.00  --bmc1_axioms                           reachable_all
% 3.01/1.00  --bmc1_min_bound                        0
% 3.01/1.00  --bmc1_max_bound                        -1
% 3.01/1.00  --bmc1_max_bound_default                -1
% 3.01/1.00  --bmc1_symbol_reachability              true
% 3.01/1.00  --bmc1_property_lemmas                  false
% 3.01/1.00  --bmc1_k_induction                      false
% 3.01/1.00  --bmc1_non_equiv_states                 false
% 3.01/1.00  --bmc1_deadlock                         false
% 3.01/1.00  --bmc1_ucm                              false
% 3.01/1.00  --bmc1_add_unsat_core                   none
% 3.01/1.00  --bmc1_unsat_core_children              false
% 3.01/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.01/1.00  --bmc1_out_stat                         full
% 3.01/1.00  --bmc1_ground_init                      false
% 3.01/1.00  --bmc1_pre_inst_next_state              false
% 3.01/1.00  --bmc1_pre_inst_state                   false
% 3.01/1.00  --bmc1_pre_inst_reach_state             false
% 3.01/1.00  --bmc1_out_unsat_core                   false
% 3.01/1.00  --bmc1_aig_witness_out                  false
% 3.01/1.00  --bmc1_verbose                          false
% 3.01/1.00  --bmc1_dump_clauses_tptp                false
% 3.01/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.01/1.00  --bmc1_dump_file                        -
% 3.01/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.01/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.01/1.00  --bmc1_ucm_extend_mode                  1
% 3.01/1.00  --bmc1_ucm_init_mode                    2
% 3.01/1.00  --bmc1_ucm_cone_mode                    none
% 3.01/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.01/1.00  --bmc1_ucm_relax_model                  4
% 3.01/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.01/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.01/1.00  --bmc1_ucm_layered_model                none
% 3.01/1.00  --bmc1_ucm_max_lemma_size               10
% 3.01/1.00  
% 3.01/1.00  ------ AIG Options
% 3.01/1.00  
% 3.01/1.00  --aig_mode                              false
% 3.01/1.00  
% 3.01/1.00  ------ Instantiation Options
% 3.01/1.00  
% 3.01/1.00  --instantiation_flag                    true
% 3.01/1.00  --inst_sos_flag                         false
% 3.01/1.00  --inst_sos_phase                        true
% 3.01/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.01/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.01/1.00  --inst_lit_sel_side                     none
% 3.01/1.00  --inst_solver_per_active                1400
% 3.01/1.00  --inst_solver_calls_frac                1.
% 3.01/1.00  --inst_passive_queue_type               priority_queues
% 3.01/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.01/1.00  --inst_passive_queues_freq              [25;2]
% 3.01/1.00  --inst_dismatching                      true
% 3.01/1.00  --inst_eager_unprocessed_to_passive     true
% 3.01/1.00  --inst_prop_sim_given                   true
% 3.01/1.00  --inst_prop_sim_new                     false
% 3.01/1.00  --inst_subs_new                         false
% 3.01/1.00  --inst_eq_res_simp                      false
% 3.01/1.00  --inst_subs_given                       false
% 3.01/1.00  --inst_orphan_elimination               true
% 3.01/1.00  --inst_learning_loop_flag               true
% 3.01/1.00  --inst_learning_start                   3000
% 3.01/1.00  --inst_learning_factor                  2
% 3.01/1.00  --inst_start_prop_sim_after_learn       3
% 3.01/1.00  --inst_sel_renew                        solver
% 3.01/1.00  --inst_lit_activity_flag                true
% 3.01/1.00  --inst_restr_to_given                   false
% 3.01/1.00  --inst_activity_threshold               500
% 3.01/1.00  --inst_out_proof                        true
% 3.01/1.00  
% 3.01/1.00  ------ Resolution Options
% 3.01/1.00  
% 3.01/1.00  --resolution_flag                       false
% 3.01/1.00  --res_lit_sel                           adaptive
% 3.01/1.00  --res_lit_sel_side                      none
% 3.01/1.00  --res_ordering                          kbo
% 3.01/1.00  --res_to_prop_solver                    active
% 3.01/1.00  --res_prop_simpl_new                    false
% 3.01/1.00  --res_prop_simpl_given                  true
% 3.01/1.00  --res_passive_queue_type                priority_queues
% 3.01/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.01/1.00  --res_passive_queues_freq               [15;5]
% 3.01/1.00  --res_forward_subs                      full
% 3.01/1.00  --res_backward_subs                     full
% 3.01/1.00  --res_forward_subs_resolution           true
% 3.01/1.00  --res_backward_subs_resolution          true
% 3.01/1.00  --res_orphan_elimination                true
% 3.01/1.00  --res_time_limit                        2.
% 3.01/1.00  --res_out_proof                         true
% 3.01/1.00  
% 3.01/1.00  ------ Superposition Options
% 3.01/1.00  
% 3.01/1.00  --superposition_flag                    true
% 3.01/1.00  --sup_passive_queue_type                priority_queues
% 3.01/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.01/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.01/1.00  --demod_completeness_check              fast
% 3.01/1.00  --demod_use_ground                      true
% 3.01/1.00  --sup_to_prop_solver                    passive
% 3.01/1.00  --sup_prop_simpl_new                    true
% 3.01/1.00  --sup_prop_simpl_given                  true
% 3.01/1.00  --sup_fun_splitting                     false
% 3.01/1.00  --sup_smt_interval                      50000
% 3.01/1.00  
% 3.01/1.00  ------ Superposition Simplification Setup
% 3.01/1.00  
% 3.01/1.00  --sup_indices_passive                   []
% 3.01/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.01/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/1.00  --sup_full_bw                           [BwDemod]
% 3.01/1.00  --sup_immed_triv                        [TrivRules]
% 3.01/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.01/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/1.00  --sup_immed_bw_main                     []
% 3.01/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.01/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.01/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.01/1.00  
% 3.01/1.00  ------ Combination Options
% 3.01/1.00  
% 3.01/1.00  --comb_res_mult                         3
% 3.01/1.00  --comb_sup_mult                         2
% 3.01/1.00  --comb_inst_mult                        10
% 3.01/1.00  
% 3.01/1.00  ------ Debug Options
% 3.01/1.00  
% 3.01/1.00  --dbg_backtrace                         false
% 3.01/1.00  --dbg_dump_prop_clauses                 false
% 3.01/1.00  --dbg_dump_prop_clauses_file            -
% 3.01/1.00  --dbg_out_stat                          false
% 3.01/1.00  
% 3.01/1.00  
% 3.01/1.00  
% 3.01/1.00  
% 3.01/1.00  ------ Proving...
% 3.01/1.00  
% 3.01/1.00  
% 3.01/1.00  % SZS status Theorem for theBenchmark.p
% 3.01/1.00  
% 3.01/1.00   Resolution empty clause
% 3.01/1.00  
% 3.01/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.01/1.00  
% 3.01/1.00  fof(f11,axiom,(
% 3.01/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v4_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.01/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f18,plain,(
% 3.01/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.01/1.00    inference(pure_predicate_removal,[],[f11])).
% 3.01/1.00  
% 3.01/1.00  fof(f25,plain,(
% 3.01/1.00    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.01/1.00    inference(ennf_transformation,[],[f18])).
% 3.01/1.00  
% 3.01/1.00  fof(f26,plain,(
% 3.01/1.00    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.01/1.00    inference(flattening,[],[f25])).
% 3.01/1.00  
% 3.01/1.00  fof(f39,plain,(
% 3.01/1.00    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_xboole_0(sK1(X0)) & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.01/1.00    introduced(choice_axiom,[])).
% 3.01/1.00  
% 3.01/1.00  fof(f40,plain,(
% 3.01/1.00    ! [X0] : ((~v1_xboole_0(sK1(X0)) & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.01/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f39])).
% 3.01/1.00  
% 3.01/1.00  fof(f61,plain,(
% 3.01/1.00    ( ! [X0] : (m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f40])).
% 3.01/1.00  
% 3.01/1.00  fof(f16,conjecture,(
% 3.01/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => ~v3_tex_2(X1,X0)))),
% 3.01/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f17,negated_conjecture,(
% 3.01/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => ~v3_tex_2(X1,X0)))),
% 3.01/1.00    inference(negated_conjecture,[],[f16])).
% 3.01/1.00  
% 3.01/1.00  fof(f35,plain,(
% 3.01/1.00    ? [X0] : (? [X1] : (v3_tex_2(X1,X0) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.01/1.00    inference(ennf_transformation,[],[f17])).
% 3.01/1.00  
% 3.01/1.00  fof(f36,plain,(
% 3.01/1.00    ? [X0] : (? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.01/1.00    inference(flattening,[],[f35])).
% 3.01/1.00  
% 3.01/1.00  fof(f47,plain,(
% 3.01/1.00    ( ! [X0] : (? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => (v3_tex_2(sK4,X0) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(sK4))) )),
% 3.01/1.00    introduced(choice_axiom,[])).
% 3.01/1.00  
% 3.01/1.00  fof(f46,plain,(
% 3.01/1.00    ? [X0] : (? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (v3_tex_2(X1,sK3) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) & v1_xboole_0(X1)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 3.01/1.00    introduced(choice_axiom,[])).
% 3.01/1.00  
% 3.01/1.00  fof(f48,plain,(
% 3.01/1.00    (v3_tex_2(sK4,sK3) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) & v1_xboole_0(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 3.01/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f36,f47,f46])).
% 3.01/1.00  
% 3.01/1.00  fof(f73,plain,(
% 3.01/1.00    v2_pre_topc(sK3)),
% 3.01/1.00    inference(cnf_transformation,[],[f48])).
% 3.01/1.00  
% 3.01/1.00  fof(f72,plain,(
% 3.01/1.00    ~v2_struct_0(sK3)),
% 3.01/1.00    inference(cnf_transformation,[],[f48])).
% 3.01/1.00  
% 3.01/1.00  fof(f74,plain,(
% 3.01/1.00    l1_pre_topc(sK3)),
% 3.01/1.00    inference(cnf_transformation,[],[f48])).
% 3.01/1.00  
% 3.01/1.00  fof(f9,axiom,(
% 3.01/1.00    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.01/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f22,plain,(
% 3.01/1.00    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.01/1.00    inference(ennf_transformation,[],[f9])).
% 3.01/1.00  
% 3.01/1.00  fof(f23,plain,(
% 3.01/1.00    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.01/1.00    inference(flattening,[],[f22])).
% 3.01/1.00  
% 3.01/1.00  fof(f57,plain,(
% 3.01/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f23])).
% 3.01/1.00  
% 3.01/1.00  fof(f10,axiom,(
% 3.01/1.00    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 3.01/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f24,plain,(
% 3.01/1.00    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 3.01/1.00    inference(ennf_transformation,[],[f10])).
% 3.01/1.00  
% 3.01/1.00  fof(f37,plain,(
% 3.01/1.00    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X3,X2] : (k4_tarski(X2,X3) != sK0(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK0(X0),X0)))),
% 3.01/1.00    introduced(choice_axiom,[])).
% 3.01/1.00  
% 3.01/1.00  fof(f38,plain,(
% 3.01/1.00    ! [X0] : ((! [X2,X3] : (k4_tarski(X2,X3) != sK0(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK0(X0),X0)) | k1_xboole_0 = X0)),
% 3.01/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f37])).
% 3.01/1.00  
% 3.01/1.00  fof(f58,plain,(
% 3.01/1.00    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 3.01/1.00    inference(cnf_transformation,[],[f38])).
% 3.01/1.00  
% 3.01/1.00  fof(f1,axiom,(
% 3.01/1.00    v1_xboole_0(k1_xboole_0)),
% 3.01/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f49,plain,(
% 3.01/1.00    v1_xboole_0(k1_xboole_0)),
% 3.01/1.00    inference(cnf_transformation,[],[f1])).
% 3.01/1.00  
% 3.01/1.00  fof(f62,plain,(
% 3.01/1.00    ( ! [X0] : (~v1_xboole_0(sK1(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f40])).
% 3.01/1.00  
% 3.01/1.00  fof(f13,axiom,(
% 3.01/1.00    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 3.01/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f29,plain,(
% 3.01/1.00    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 3.01/1.00    inference(ennf_transformation,[],[f13])).
% 3.01/1.00  
% 3.01/1.00  fof(f30,plain,(
% 3.01/1.00    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 3.01/1.00    inference(flattening,[],[f29])).
% 3.01/1.00  
% 3.01/1.00  fof(f64,plain,(
% 3.01/1.00    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f30])).
% 3.01/1.00  
% 3.01/1.00  fof(f7,axiom,(
% 3.01/1.00    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 3.01/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f20,plain,(
% 3.01/1.00    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 3.01/1.00    inference(ennf_transformation,[],[f7])).
% 3.01/1.00  
% 3.01/1.00  fof(f55,plain,(
% 3.01/1.00    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f20])).
% 3.01/1.00  
% 3.01/1.00  fof(f12,axiom,(
% 3.01/1.00    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 3.01/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f27,plain,(
% 3.01/1.00    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 3.01/1.00    inference(ennf_transformation,[],[f12])).
% 3.01/1.00  
% 3.01/1.00  fof(f28,plain,(
% 3.01/1.00    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 3.01/1.00    inference(flattening,[],[f27])).
% 3.01/1.00  
% 3.01/1.00  fof(f63,plain,(
% 3.01/1.00    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f28])).
% 3.01/1.00  
% 3.01/1.00  fof(f75,plain,(
% 3.01/1.00    v1_xboole_0(sK4)),
% 3.01/1.00    inference(cnf_transformation,[],[f48])).
% 3.01/1.00  
% 3.01/1.00  fof(f2,axiom,(
% 3.01/1.00    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.01/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f19,plain,(
% 3.01/1.00    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.01/1.00    inference(ennf_transformation,[],[f2])).
% 3.01/1.00  
% 3.01/1.00  fof(f50,plain,(
% 3.01/1.00    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f19])).
% 3.01/1.00  
% 3.01/1.00  fof(f77,plain,(
% 3.01/1.00    v3_tex_2(sK4,sK3)),
% 3.01/1.00    inference(cnf_transformation,[],[f48])).
% 3.01/1.00  
% 3.01/1.00  fof(f4,axiom,(
% 3.01/1.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.01/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f52,plain,(
% 3.01/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f4])).
% 3.01/1.00  
% 3.01/1.00  fof(f14,axiom,(
% 3.01/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 3.01/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f31,plain,(
% 3.01/1.00    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.01/1.00    inference(ennf_transformation,[],[f14])).
% 3.01/1.00  
% 3.01/1.00  fof(f32,plain,(
% 3.01/1.00    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.01/1.00    inference(flattening,[],[f31])).
% 3.01/1.00  
% 3.01/1.00  fof(f41,plain,(
% 3.01/1.00    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.01/1.00    inference(nnf_transformation,[],[f32])).
% 3.01/1.00  
% 3.01/1.00  fof(f42,plain,(
% 3.01/1.00    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.01/1.00    inference(flattening,[],[f41])).
% 3.01/1.00  
% 3.01/1.00  fof(f43,plain,(
% 3.01/1.00    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.01/1.00    inference(rectify,[],[f42])).
% 3.01/1.00  
% 3.01/1.00  fof(f44,plain,(
% 3.01/1.00    ! [X1,X0] : (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK2(X0,X1) != X1 & r1_tarski(X1,sK2(X0,X1)) & v2_tex_2(sK2(X0,X1),X0) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.01/1.00    introduced(choice_axiom,[])).
% 3.01/1.00  
% 3.01/1.00  fof(f45,plain,(
% 3.01/1.00    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (sK2(X0,X1) != X1 & r1_tarski(X1,sK2(X0,X1)) & v2_tex_2(sK2(X0,X1),X0) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.01/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f43,f44])).
% 3.01/1.00  
% 3.01/1.00  fof(f66,plain,(
% 3.01/1.00    ( ! [X0,X3,X1] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f45])).
% 3.01/1.00  
% 3.01/1.00  fof(f6,axiom,(
% 3.01/1.00    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.01/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f54,plain,(
% 3.01/1.00    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.01/1.00    inference(cnf_transformation,[],[f6])).
% 3.01/1.00  
% 3.01/1.00  fof(f15,axiom,(
% 3.01/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 3.01/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f33,plain,(
% 3.01/1.00    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.01/1.00    inference(ennf_transformation,[],[f15])).
% 3.01/1.00  
% 3.01/1.00  fof(f34,plain,(
% 3.01/1.00    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.01/1.00    inference(flattening,[],[f33])).
% 3.01/1.00  
% 3.01/1.00  fof(f71,plain,(
% 3.01/1.00    ( ! [X0,X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f34])).
% 3.01/1.00  
% 3.01/1.00  fof(f3,axiom,(
% 3.01/1.00    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 3.01/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f51,plain,(
% 3.01/1.00    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.01/1.00    inference(cnf_transformation,[],[f3])).
% 3.01/1.00  
% 3.01/1.00  fof(f5,axiom,(
% 3.01/1.00    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 3.01/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f53,plain,(
% 3.01/1.00    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f5])).
% 3.01/1.00  
% 3.01/1.00  cnf(c_13,plain,
% 3.01/1.00      ( m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 3.01/1.00      | v2_struct_0(X0)
% 3.01/1.00      | ~ v2_pre_topc(X0)
% 3.01/1.00      | ~ l1_pre_topc(X0) ),
% 3.01/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_27,negated_conjecture,
% 3.01/1.00      ( v2_pre_topc(sK3) ),
% 3.01/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_320,plain,
% 3.01/1.00      ( m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 3.01/1.00      | v2_struct_0(X0)
% 3.01/1.00      | ~ l1_pre_topc(X0)
% 3.01/1.00      | sK3 != X0 ),
% 3.01/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_27]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_321,plain,
% 3.01/1.00      ( m1_subset_1(sK1(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.01/1.00      | v2_struct_0(sK3)
% 3.01/1.00      | ~ l1_pre_topc(sK3) ),
% 3.01/1.00      inference(unflattening,[status(thm)],[c_320]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_28,negated_conjecture,
% 3.01/1.00      ( ~ v2_struct_0(sK3) ),
% 3.01/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_26,negated_conjecture,
% 3.01/1.00      ( l1_pre_topc(sK3) ),
% 3.01/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_323,plain,
% 3.01/1.00      ( m1_subset_1(sK1(sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_321,c_28,c_26]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1264,plain,
% 3.01/1.00      ( m1_subset_1(sK1(sK3),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_323]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_8,plain,
% 3.01/1.00      ( ~ r2_hidden(X0,X1)
% 3.01/1.00      | m1_subset_1(X0,X2)
% 3.01/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 3.01/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_11,plain,
% 3.01/1.00      ( r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 3.01/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_367,plain,
% 3.01/1.00      ( m1_subset_1(X0,X1)
% 3.01/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.01/1.00      | X3 != X2
% 3.01/1.00      | sK0(X3) != X0
% 3.01/1.00      | k1_xboole_0 = X3 ),
% 3.01/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_11]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_368,plain,
% 3.01/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.01/1.00      | m1_subset_1(sK0(X0),X1)
% 3.01/1.00      | k1_xboole_0 = X0 ),
% 3.01/1.00      inference(unflattening,[status(thm)],[c_367]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1262,plain,
% 3.01/1.00      ( k1_xboole_0 = X0
% 3.01/1.00      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.01/1.00      | m1_subset_1(sK0(X0),X1) = iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_368]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_2692,plain,
% 3.01/1.00      ( sK1(sK3) = k1_xboole_0
% 3.01/1.00      | m1_subset_1(sK0(sK1(sK3)),u1_struct_0(sK3)) = iProver_top ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_1264,c_1262]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_0,plain,
% 3.01/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 3.01/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_12,plain,
% 3.01/1.00      ( v2_struct_0(X0)
% 3.01/1.00      | ~ v2_pre_topc(X0)
% 3.01/1.00      | ~ l1_pre_topc(X0)
% 3.01/1.00      | ~ v1_xboole_0(sK1(X0)) ),
% 3.01/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_331,plain,
% 3.01/1.00      ( v2_struct_0(X0)
% 3.01/1.00      | ~ l1_pre_topc(X0)
% 3.01/1.00      | ~ v1_xboole_0(sK1(X0))
% 3.01/1.00      | sK3 != X0 ),
% 3.01/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_27]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_332,plain,
% 3.01/1.00      ( v2_struct_0(sK3) | ~ l1_pre_topc(sK3) | ~ v1_xboole_0(sK1(sK3)) ),
% 3.01/1.00      inference(unflattening,[status(thm)],[c_331]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_914,plain,
% 3.01/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.01/1.00      theory(equality) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1420,plain,
% 3.01/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK1(sK3)) | sK1(sK3) != X0 ),
% 3.01/1.00      inference(instantiation,[status(thm)],[c_914]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1422,plain,
% 3.01/1.00      ( v1_xboole_0(sK1(sK3))
% 3.01/1.00      | ~ v1_xboole_0(k1_xboole_0)
% 3.01/1.00      | sK1(sK3) != k1_xboole_0 ),
% 3.01/1.00      inference(instantiation,[status(thm)],[c_1420]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3109,plain,
% 3.01/1.00      ( m1_subset_1(sK0(sK1(sK3)),u1_struct_0(sK3)) = iProver_top ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_2692,c_28,c_26,c_0,c_332,c_1422]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_15,plain,
% 3.01/1.00      ( ~ m1_subset_1(X0,X1)
% 3.01/1.00      | v1_xboole_0(X1)
% 3.01/1.00      | k6_domain_1(X1,X0) = k1_tarski(X0) ),
% 3.01/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1268,plain,
% 3.01/1.00      ( k6_domain_1(X0,X1) = k1_tarski(X1)
% 3.01/1.00      | m1_subset_1(X1,X0) != iProver_top
% 3.01/1.00      | v1_xboole_0(X0) = iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3114,plain,
% 3.01/1.00      ( k6_domain_1(u1_struct_0(sK3),sK0(sK1(sK3))) = k1_tarski(sK0(sK1(sK3)))
% 3.01/1.00      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_3109,c_1268]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_29,plain,
% 3.01/1.00      ( v2_struct_0(sK3) != iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_31,plain,
% 3.01/1.00      ( l1_pre_topc(sK3) = iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_322,plain,
% 3.01/1.00      ( m1_subset_1(sK1(sK3),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 3.01/1.00      | v2_struct_0(sK3) = iProver_top
% 3.01/1.00      | l1_pre_topc(sK3) != iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_321]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_333,plain,
% 3.01/1.00      ( v2_struct_0(sK3) = iProver_top
% 3.01/1.00      | l1_pre_topc(sK3) != iProver_top
% 3.01/1.00      | v1_xboole_0(sK1(sK3)) != iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_332]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_6,plain,
% 3.01/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.01/1.00      | ~ v1_xboole_0(X1)
% 3.01/1.00      | v1_xboole_0(X0) ),
% 3.01/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1415,plain,
% 3.01/1.00      ( ~ m1_subset_1(sK1(sK3),k1_zfmisc_1(X0))
% 3.01/1.00      | ~ v1_xboole_0(X0)
% 3.01/1.00      | v1_xboole_0(sK1(sK3)) ),
% 3.01/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1499,plain,
% 3.01/1.00      ( ~ m1_subset_1(sK1(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.01/1.00      | ~ v1_xboole_0(u1_struct_0(sK3))
% 3.01/1.00      | v1_xboole_0(sK1(sK3)) ),
% 3.01/1.00      inference(instantiation,[status(thm)],[c_1415]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1500,plain,
% 3.01/1.00      ( m1_subset_1(sK1(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.01/1.00      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top
% 3.01/1.00      | v1_xboole_0(sK1(sK3)) = iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_1499]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3263,plain,
% 3.01/1.00      ( k6_domain_1(u1_struct_0(sK3),sK0(sK1(sK3))) = k1_tarski(sK0(sK1(sK3))) ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_3114,c_29,c_31,c_322,c_333,c_1500]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_14,plain,
% 3.01/1.00      ( ~ m1_subset_1(X0,X1)
% 3.01/1.00      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
% 3.01/1.00      | v1_xboole_0(X1) ),
% 3.01/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1269,plain,
% 3.01/1.00      ( m1_subset_1(X0,X1) != iProver_top
% 3.01/1.00      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top
% 3.01/1.00      | v1_xboole_0(X1) = iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3266,plain,
% 3.01/1.00      ( m1_subset_1(sK0(sK1(sK3)),u1_struct_0(sK3)) != iProver_top
% 3.01/1.00      | m1_subset_1(k1_tarski(sK0(sK1(sK3))),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 3.01/1.00      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_3263,c_1269]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3527,plain,
% 3.01/1.00      ( m1_subset_1(k1_tarski(sK0(sK1(sK3))),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_3266,c_28,c_29,c_26,c_31,c_0,c_322,c_332,c_333,c_1422,
% 3.01/1.00                 c_1500,c_2692]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_25,negated_conjecture,
% 3.01/1.00      ( v1_xboole_0(sK4) ),
% 3.01/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1266,plain,
% 3.01/1.00      ( v1_xboole_0(sK4) = iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1,plain,
% 3.01/1.00      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 3.01/1.00      inference(cnf_transformation,[],[f50]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1272,plain,
% 3.01/1.00      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_2031,plain,
% 3.01/1.00      ( sK4 = k1_xboole_0 ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_1266,c_1272]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_23,negated_conjecture,
% 3.01/1.00      ( v3_tex_2(sK4,sK3) ),
% 3.01/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3,plain,
% 3.01/1.00      ( r1_tarski(k1_xboole_0,X0) ),
% 3.01/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_20,plain,
% 3.01/1.00      ( ~ v2_tex_2(X0,X1)
% 3.01/1.00      | ~ v3_tex_2(X2,X1)
% 3.01/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.01/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.01/1.00      | ~ r1_tarski(X2,X0)
% 3.01/1.00      | ~ l1_pre_topc(X1)
% 3.01/1.00      | X0 = X2 ),
% 3.01/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_493,plain,
% 3.01/1.00      ( ~ v2_tex_2(X0,X1)
% 3.01/1.00      | ~ v3_tex_2(X2,X1)
% 3.01/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.01/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.01/1.00      | ~ r1_tarski(X2,X0)
% 3.01/1.00      | X2 = X0
% 3.01/1.00      | sK3 != X1 ),
% 3.01/1.00      inference(resolution_lifted,[status(thm)],[c_20,c_26]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_494,plain,
% 3.01/1.00      ( ~ v2_tex_2(X0,sK3)
% 3.01/1.00      | ~ v3_tex_2(X1,sK3)
% 3.01/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.01/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.01/1.00      | ~ r1_tarski(X1,X0)
% 3.01/1.00      | X1 = X0 ),
% 3.01/1.00      inference(unflattening,[status(thm)],[c_493]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_620,plain,
% 3.01/1.00      ( ~ v2_tex_2(X0,sK3)
% 3.01/1.00      | ~ v3_tex_2(X1,sK3)
% 3.01/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.01/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.01/1.00      | X0 != X2
% 3.01/1.00      | X0 = X1
% 3.01/1.00      | k1_xboole_0 != X1 ),
% 3.01/1.00      inference(resolution_lifted,[status(thm)],[c_3,c_494]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_621,plain,
% 3.01/1.00      ( ~ v2_tex_2(X0,sK3)
% 3.01/1.00      | ~ v3_tex_2(k1_xboole_0,sK3)
% 3.01/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.01/1.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.01/1.00      | X0 = k1_xboole_0 ),
% 3.01/1.00      inference(unflattening,[status(thm)],[c_620]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_5,plain,
% 3.01/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.01/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_635,plain,
% 3.01/1.00      ( ~ v2_tex_2(X0,sK3)
% 3.01/1.00      | ~ v3_tex_2(k1_xboole_0,sK3)
% 3.01/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.01/1.00      | X0 = k1_xboole_0 ),
% 3.01/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_621,c_5]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_662,plain,
% 3.01/1.00      ( ~ v2_tex_2(X0,sK3)
% 3.01/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.01/1.00      | sK3 != sK3
% 3.01/1.00      | sK4 != k1_xboole_0
% 3.01/1.00      | k1_xboole_0 = X0 ),
% 3.01/1.00      inference(resolution_lifted,[status(thm)],[c_23,c_635]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_801,plain,
% 3.01/1.00      ( ~ v2_tex_2(X0,sK3)
% 3.01/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.01/1.00      | sK4 != k1_xboole_0
% 3.01/1.00      | k1_xboole_0 = X0 ),
% 3.01/1.00      inference(equality_resolution_simp,[status(thm)],[c_662]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1253,plain,
% 3.01/1.00      ( sK4 != k1_xboole_0
% 3.01/1.00      | k1_xboole_0 = X0
% 3.01/1.00      | v2_tex_2(X0,sK3) != iProver_top
% 3.01/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_801]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_2035,plain,
% 3.01/1.00      ( k1_xboole_0 = X0
% 3.01/1.00      | k1_xboole_0 != k1_xboole_0
% 3.01/1.00      | v2_tex_2(X0,sK3) != iProver_top
% 3.01/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 3.01/1.00      inference(demodulation,[status(thm)],[c_2031,c_1253]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_2042,plain,
% 3.01/1.00      ( k1_xboole_0 = X0
% 3.01/1.00      | v2_tex_2(X0,sK3) != iProver_top
% 3.01/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 3.01/1.00      inference(equality_resolution_simp,[status(thm)],[c_2035]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3535,plain,
% 3.01/1.00      ( k1_tarski(sK0(sK1(sK3))) = k1_xboole_0
% 3.01/1.00      | v2_tex_2(k1_tarski(sK0(sK1(sK3))),sK3) != iProver_top ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_3527,c_2042]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_22,plain,
% 3.01/1.00      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
% 3.01/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.01/1.00      | v2_struct_0(X0)
% 3.01/1.00      | ~ v2_pre_topc(X0)
% 3.01/1.00      | ~ l1_pre_topc(X0) ),
% 3.01/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_302,plain,
% 3.01/1.00      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
% 3.01/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.01/1.00      | v2_struct_0(X0)
% 3.01/1.00      | ~ l1_pre_topc(X0)
% 3.01/1.00      | sK3 != X0 ),
% 3.01/1.00      inference(resolution_lifted,[status(thm)],[c_22,c_27]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_303,plain,
% 3.01/1.00      ( v2_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3)
% 3.01/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.01/1.00      | v2_struct_0(sK3)
% 3.01/1.00      | ~ l1_pre_topc(sK3) ),
% 3.01/1.00      inference(unflattening,[status(thm)],[c_302]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_307,plain,
% 3.01/1.00      ( v2_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3)
% 3.01/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_303,c_28,c_26]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1265,plain,
% 3.01/1.00      ( v2_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3) = iProver_top
% 3.01/1.00      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_307]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3267,plain,
% 3.01/1.00      ( v2_tex_2(k1_tarski(sK0(sK1(sK3))),sK3) = iProver_top
% 3.01/1.00      | m1_subset_1(sK0(sK1(sK3)),u1_struct_0(sK3)) != iProver_top ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_3263,c_1265]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3552,plain,
% 3.01/1.00      ( k1_tarski(sK0(sK1(sK3))) = k1_xboole_0 ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_3535,c_28,c_26,c_0,c_332,c_1422,c_2692,c_3267]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_2,plain,
% 3.01/1.00      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.01/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_4,plain,
% 3.01/1.00      ( k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
% 3.01/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1809,plain,
% 3.01/1.00      ( k1_tarski(X0) != k1_xboole_0 ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_2,c_4]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3555,plain,
% 3.01/1.00      ( $false ),
% 3.01/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_3552,c_1809]) ).
% 3.01/1.00  
% 3.01/1.00  
% 3.01/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.01/1.00  
% 3.01/1.00  ------                               Statistics
% 3.01/1.00  
% 3.01/1.00  ------ General
% 3.01/1.00  
% 3.01/1.00  abstr_ref_over_cycles:                  0
% 3.01/1.00  abstr_ref_under_cycles:                 0
% 3.01/1.00  gc_basic_clause_elim:                   0
% 3.01/1.00  forced_gc_time:                         0
% 3.01/1.00  parsing_time:                           0.009
% 3.01/1.00  unif_index_cands_time:                  0.
% 3.01/1.00  unif_index_add_time:                    0.
% 3.01/1.00  orderings_time:                         0.
% 3.01/1.00  out_proof_time:                         0.009
% 3.01/1.00  total_time:                             0.13
% 3.01/1.00  num_of_symbols:                         53
% 3.01/1.00  num_of_terms:                           2432
% 3.01/1.00  
% 3.01/1.00  ------ Preprocessing
% 3.01/1.00  
% 3.01/1.00  num_of_splits:                          3
% 3.01/1.00  num_of_split_atoms:                     1
% 3.01/1.00  num_of_reused_defs:                     2
% 3.01/1.00  num_eq_ax_congr_red:                    16
% 3.01/1.00  num_of_sem_filtered_clauses:            1
% 3.01/1.00  num_of_subtypes:                        0
% 3.01/1.00  monotx_restored_types:                  0
% 3.01/1.00  sat_num_of_epr_types:                   0
% 3.01/1.00  sat_num_of_non_cyclic_types:            0
% 3.01/1.00  sat_guarded_non_collapsed_types:        0
% 3.01/1.00  num_pure_diseq_elim:                    0
% 3.01/1.00  simp_replaced_by:                       0
% 3.01/1.00  res_preprocessed:                       122
% 3.01/1.00  prep_upred:                             0
% 3.01/1.00  prep_unflattend:                        29
% 3.01/1.00  smt_new_axioms:                         0
% 3.01/1.00  pred_elim_cands:                        3
% 3.01/1.00  pred_elim:                              6
% 3.01/1.00  pred_elim_cl:                           7
% 3.01/1.00  pred_elim_cycles:                       9
% 3.01/1.00  merged_defs:                            0
% 3.01/1.00  merged_defs_ncl:                        0
% 3.01/1.00  bin_hyper_res:                          0
% 3.01/1.00  prep_cycles:                            4
% 3.01/1.00  pred_elim_time:                         0.01
% 3.01/1.00  splitting_time:                         0.
% 3.01/1.00  sem_filter_time:                        0.
% 3.01/1.00  monotx_time:                            0.001
% 3.01/1.00  subtype_inf_time:                       0.
% 3.01/1.00  
% 3.01/1.00  ------ Problem properties
% 3.01/1.00  
% 3.01/1.00  clauses:                                25
% 3.01/1.00  conjectures:                            2
% 3.01/1.00  epr:                                    4
% 3.01/1.00  horn:                                   19
% 3.01/1.00  ground:                                 9
% 3.01/1.00  unary:                                  9
% 3.01/1.00  binary:                                 5
% 3.01/1.00  lits:                                   56
% 3.01/1.00  lits_eq:                                16
% 3.01/1.00  fd_pure:                                0
% 3.01/1.00  fd_pseudo:                              0
% 3.01/1.00  fd_cond:                                9
% 3.01/1.00  fd_pseudo_cond:                         0
% 3.01/1.00  ac_symbols:                             0
% 3.01/1.00  
% 3.01/1.00  ------ Propositional Solver
% 3.01/1.00  
% 3.01/1.00  prop_solver_calls:                      27
% 3.01/1.00  prop_fast_solver_calls:                 814
% 3.01/1.00  smt_solver_calls:                       0
% 3.01/1.00  smt_fast_solver_calls:                  0
% 3.01/1.00  prop_num_of_clauses:                    1140
% 3.01/1.00  prop_preprocess_simplified:             4659
% 3.01/1.00  prop_fo_subsumed:                       29
% 3.01/1.00  prop_solver_time:                       0.
% 3.01/1.00  smt_solver_time:                        0.
% 3.01/1.00  smt_fast_solver_time:                   0.
% 3.01/1.00  prop_fast_solver_time:                  0.
% 3.01/1.00  prop_unsat_core_time:                   0.
% 3.01/1.00  
% 3.01/1.00  ------ QBF
% 3.01/1.00  
% 3.01/1.00  qbf_q_res:                              0
% 3.01/1.00  qbf_num_tautologies:                    0
% 3.01/1.00  qbf_prep_cycles:                        0
% 3.01/1.00  
% 3.01/1.00  ------ BMC1
% 3.01/1.00  
% 3.01/1.00  bmc1_current_bound:                     -1
% 3.01/1.00  bmc1_last_solved_bound:                 -1
% 3.01/1.00  bmc1_unsat_core_size:                   -1
% 3.01/1.00  bmc1_unsat_core_parents_size:           -1
% 3.01/1.00  bmc1_merge_next_fun:                    0
% 3.01/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.01/1.00  
% 3.01/1.00  ------ Instantiation
% 3.01/1.00  
% 3.01/1.00  inst_num_of_clauses:                    365
% 3.01/1.00  inst_num_in_passive:                    163
% 3.01/1.00  inst_num_in_active:                     187
% 3.01/1.00  inst_num_in_unprocessed:                16
% 3.01/1.00  inst_num_of_loops:                      220
% 3.01/1.00  inst_num_of_learning_restarts:          0
% 3.01/1.00  inst_num_moves_active_passive:          31
% 3.01/1.00  inst_lit_activity:                      0
% 3.01/1.00  inst_lit_activity_moves:                0
% 3.01/1.00  inst_num_tautologies:                   0
% 3.01/1.00  inst_num_prop_implied:                  0
% 3.01/1.00  inst_num_existing_simplified:           0
% 3.01/1.00  inst_num_eq_res_simplified:             0
% 3.01/1.00  inst_num_child_elim:                    0
% 3.01/1.00  inst_num_of_dismatching_blockings:      78
% 3.01/1.00  inst_num_of_non_proper_insts:           247
% 3.01/1.00  inst_num_of_duplicates:                 0
% 3.01/1.00  inst_inst_num_from_inst_to_res:         0
% 3.01/1.00  inst_dismatching_checking_time:         0.
% 3.01/1.00  
% 3.01/1.00  ------ Resolution
% 3.01/1.00  
% 3.01/1.00  res_num_of_clauses:                     0
% 3.01/1.00  res_num_in_passive:                     0
% 3.01/1.00  res_num_in_active:                      0
% 3.01/1.00  res_num_of_loops:                       126
% 3.01/1.00  res_forward_subset_subsumed:            23
% 3.01/1.00  res_backward_subset_subsumed:           2
% 3.01/1.00  res_forward_subsumed:                   0
% 3.01/1.00  res_backward_subsumed:                  0
% 3.01/1.00  res_forward_subsumption_resolution:     5
% 3.01/1.00  res_backward_subsumption_resolution:    0
% 3.01/1.00  res_clause_to_clause_subsumption:       97
% 3.01/1.00  res_orphan_elimination:                 0
% 3.01/1.00  res_tautology_del:                      23
% 3.01/1.00  res_num_eq_res_simplified:              1
% 3.01/1.00  res_num_sel_changes:                    0
% 3.01/1.00  res_moves_from_active_to_pass:          0
% 3.01/1.00  
% 3.01/1.00  ------ Superposition
% 3.01/1.00  
% 3.01/1.00  sup_time_total:                         0.
% 3.01/1.00  sup_time_generating:                    0.
% 3.01/1.00  sup_time_sim_full:                      0.
% 3.01/1.00  sup_time_sim_immed:                     0.
% 3.01/1.00  
% 3.01/1.00  sup_num_of_clauses:                     47
% 3.01/1.00  sup_num_in_active:                      36
% 3.01/1.00  sup_num_in_passive:                     11
% 3.01/1.00  sup_num_of_loops:                       43
% 3.01/1.00  sup_fw_superposition:                   24
% 3.01/1.00  sup_bw_superposition:                   16
% 3.01/1.00  sup_immediate_simplified:               4
% 3.01/1.00  sup_given_eliminated:                   0
% 3.01/1.00  comparisons_done:                       0
% 3.01/1.00  comparisons_avoided:                    8
% 3.01/1.00  
% 3.01/1.00  ------ Simplifications
% 3.01/1.00  
% 3.01/1.00  
% 3.01/1.00  sim_fw_subset_subsumed:                 3
% 3.01/1.00  sim_bw_subset_subsumed:                 3
% 3.01/1.00  sim_fw_subsumed:                        1
% 3.01/1.00  sim_bw_subsumed:                        0
% 3.01/1.00  sim_fw_subsumption_res:                 1
% 3.01/1.00  sim_bw_subsumption_res:                 0
% 3.01/1.00  sim_tautology_del:                      2
% 3.01/1.00  sim_eq_tautology_del:                   4
% 3.01/1.01  sim_eq_res_simp:                        1
% 3.01/1.01  sim_fw_demodulated:                     0
% 3.01/1.01  sim_bw_demodulated:                     4
% 3.01/1.01  sim_light_normalised:                   0
% 3.01/1.01  sim_joinable_taut:                      0
% 3.01/1.01  sim_joinable_simp:                      0
% 3.01/1.01  sim_ac_normalised:                      0
% 3.01/1.01  sim_smt_subsumption:                    0
% 3.01/1.01  
%------------------------------------------------------------------------------
