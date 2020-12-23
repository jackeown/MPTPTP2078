%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:27:05 EST 2020

% Result     : Theorem 2.01s
% Output     : CNFRefutation 2.01s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 253 expanded)
%              Number of clauses        :   55 (  84 expanded)
%              Number of leaves         :   17 (  61 expanded)
%              Depth                    :   21
%              Number of atoms          :  366 (1014 expanded)
%              Number of equality atoms :   87 ( 103 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] : m1_subset_1(sK0(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f5,f31])).

fof(f45,plain,(
    ! [X0] : m1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f32])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f47,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

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

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
     => ( v3_tex_2(sK3,X0)
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0)))
        & v1_xboole_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( v3_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( v3_tex_2(X1,sK2)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( v3_tex_2(sK3,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & v1_xboole_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f30,f39,f38])).

fof(f58,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f60,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f61,plain,(
    v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f41,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f63,plain,(
    v3_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

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

fof(f25,plain,(
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

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r1_tarski(X1,X2)
          & v2_tex_2(X2,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK1(X0,X1) != X1
        & r1_tarski(X1,sK1(X0,X1))
        & v2_tex_2(sK1(X0,X1),X0)
        & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ( sK1(X0,X1) != X1
                & r1_tarski(X1,sK1(X0,X1))
                & v2_tex_2(sK1(X0,X1),X0)
                & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f36])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( X1 = X3
      | ~ r1_tarski(X1,X3)
      | ~ v2_tex_2(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f59,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f2,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f4,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f4])).

cnf(c_4,plain,
    ( m1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1208,plain,
    ( m1_subset_1(sK0(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1205,plain,
    ( k6_domain_1(X0,X1) = k1_tarski(X1)
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1922,plain,
    ( k6_domain_1(X0,sK0(X0)) = k1_tarski(sK0(X0))
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1208,c_1205])).

cnf(c_6,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_7,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_240,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_6,c_7])).

cnf(c_22,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_279,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_240,c_22])).

cnf(c_280,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_279])).

cnf(c_20,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_282,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_280,c_20])).

cnf(c_1201,plain,
    ( v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_282])).

cnf(c_2061,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK0(u1_struct_0(sK2))) = k1_tarski(sK0(u1_struct_0(sK2))) ),
    inference(superposition,[status(thm)],[c_1922,c_1201])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1206,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2208,plain,
    ( m1_subset_1(sK0(u1_struct_0(sK2)),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k1_tarski(sK0(u1_struct_0(sK2))),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2061,c_1206])).

cnf(c_25,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_281,plain,
    ( l1_pre_topc(sK2) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_280])).

cnf(c_1317,plain,
    ( m1_subset_1(sK0(u1_struct_0(sK2)),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1319,plain,
    ( m1_subset_1(sK0(u1_struct_0(sK2)),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1317])).

cnf(c_2296,plain,
    ( m1_subset_1(k1_tarski(sK0(u1_struct_0(sK2))),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2208,c_25,c_281,c_1319])).

cnf(c_19,negated_conjecture,
    ( v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1203,plain,
    ( v1_xboole_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_0,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1209,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1875,plain,
    ( sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1203,c_1209])).

cnf(c_17,negated_conjecture,
    ( v3_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_14,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ v3_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | ~ l1_pre_topc(X1)
    | X0 = X2 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_455,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ v3_tex_2(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | X2 = X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_20])).

cnf(c_456,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ v3_tex_2(X1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(unflattening,[status(thm)],[c_455])).

cnf(c_582,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ v3_tex_2(X1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | X0 != X2
    | X0 = X1
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_456])).

cnf(c_583,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ v3_tex_2(k1_xboole_0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2)))
    | X0 = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_582])).

cnf(c_5,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_597,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ v3_tex_2(k1_xboole_0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | X0 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_583,c_5])).

cnf(c_624,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | sK2 != sK2
    | sK3 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_597])).

cnf(c_759,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | sK3 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_624])).

cnf(c_1193,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = X0
    | v2_tex_2(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_759])).

cnf(c_1899,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 != k1_xboole_0
    | v2_tex_2(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1875,c_1193])).

cnf(c_1908,plain,
    ( k1_xboole_0 = X0
    | v2_tex_2(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_1899])).

cnf(c_2302,plain,
    ( k1_tarski(sK0(u1_struct_0(sK2))) = k1_xboole_0
    | v2_tex_2(k1_tarski(sK0(u1_struct_0(sK2))),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2296,c_1908])).

cnf(c_16,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_21,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_258,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_21])).

cnf(c_259,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK2),X0),sK2)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_258])).

cnf(c_263,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK2),X0),sK2)
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_259,c_22,c_20])).

cnf(c_1202,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK2),X0),sK2) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_263])).

cnf(c_2209,plain,
    ( v2_tex_2(k1_tarski(sK0(u1_struct_0(sK2))),sK2) = iProver_top
    | m1_subset_1(sK0(u1_struct_0(sK2)),u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2061,c_1202])).

cnf(c_2386,plain,
    ( k1_tarski(sK0(u1_struct_0(sK2))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2302,c_1319,c_2209])).

cnf(c_1,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_3,plain,
    ( k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1633,plain,
    ( k1_tarski(X0) != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1,c_3])).

cnf(c_2389,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2386,c_1633])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : iproveropt_run.sh %d %s
% 0.10/0.31  % Computer   : n016.cluster.edu
% 0.10/0.31  % Model      : x86_64 x86_64
% 0.10/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.31  % Memory     : 8042.1875MB
% 0.10/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.32  % CPULimit   : 60
% 0.10/0.32  % WCLimit    : 600
% 0.10/0.32  % DateTime   : Tue Dec  1 13:05:49 EST 2020
% 0.10/0.32  % CPUTime    : 
% 0.10/0.32  % Running in FOF mode
% 2.01/0.96  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.01/0.96  
% 2.01/0.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.01/0.96  
% 2.01/0.96  ------  iProver source info
% 2.01/0.96  
% 2.01/0.96  git: date: 2020-06-30 10:37:57 +0100
% 2.01/0.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.01/0.96  git: non_committed_changes: false
% 2.01/0.96  git: last_make_outside_of_git: false
% 2.01/0.96  
% 2.01/0.96  ------ 
% 2.01/0.96  
% 2.01/0.96  ------ Input Options
% 2.01/0.96  
% 2.01/0.96  --out_options                           all
% 2.01/0.96  --tptp_safe_out                         true
% 2.01/0.96  --problem_path                          ""
% 2.01/0.96  --include_path                          ""
% 2.01/0.96  --clausifier                            res/vclausify_rel
% 2.01/0.96  --clausifier_options                    --mode clausify
% 2.01/0.96  --stdin                                 false
% 2.01/0.96  --stats_out                             all
% 2.01/0.96  
% 2.01/0.96  ------ General Options
% 2.01/0.96  
% 2.01/0.96  --fof                                   false
% 2.01/0.96  --time_out_real                         305.
% 2.01/0.96  --time_out_virtual                      -1.
% 2.01/0.96  --symbol_type_check                     false
% 2.01/0.96  --clausify_out                          false
% 2.01/0.96  --sig_cnt_out                           false
% 2.01/0.96  --trig_cnt_out                          false
% 2.01/0.96  --trig_cnt_out_tolerance                1.
% 2.01/0.96  --trig_cnt_out_sk_spl                   false
% 2.01/0.96  --abstr_cl_out                          false
% 2.01/0.96  
% 2.01/0.96  ------ Global Options
% 2.01/0.96  
% 2.01/0.96  --schedule                              default
% 2.01/0.96  --add_important_lit                     false
% 2.01/0.96  --prop_solver_per_cl                    1000
% 2.01/0.96  --min_unsat_core                        false
% 2.01/0.96  --soft_assumptions                      false
% 2.01/0.96  --soft_lemma_size                       3
% 2.01/0.96  --prop_impl_unit_size                   0
% 2.01/0.96  --prop_impl_unit                        []
% 2.01/0.96  --share_sel_clauses                     true
% 2.01/0.96  --reset_solvers                         false
% 2.01/0.96  --bc_imp_inh                            [conj_cone]
% 2.01/0.96  --conj_cone_tolerance                   3.
% 2.01/0.96  --extra_neg_conj                        none
% 2.01/0.96  --large_theory_mode                     true
% 2.01/0.96  --prolific_symb_bound                   200
% 2.01/0.96  --lt_threshold                          2000
% 2.01/0.96  --clause_weak_htbl                      true
% 2.01/0.96  --gc_record_bc_elim                     false
% 2.01/0.96  
% 2.01/0.96  ------ Preprocessing Options
% 2.01/0.96  
% 2.01/0.96  --preprocessing_flag                    true
% 2.01/0.96  --time_out_prep_mult                    0.1
% 2.01/0.96  --splitting_mode                        input
% 2.01/0.96  --splitting_grd                         true
% 2.01/0.96  --splitting_cvd                         false
% 2.01/0.96  --splitting_cvd_svl                     false
% 2.01/0.96  --splitting_nvd                         32
% 2.01/0.96  --sub_typing                            true
% 2.01/0.96  --prep_gs_sim                           true
% 2.01/0.96  --prep_unflatten                        true
% 2.01/0.96  --prep_res_sim                          true
% 2.01/0.96  --prep_upred                            true
% 2.01/0.96  --prep_sem_filter                       exhaustive
% 2.01/0.96  --prep_sem_filter_out                   false
% 2.01/0.96  --pred_elim                             true
% 2.01/0.96  --res_sim_input                         true
% 2.01/0.96  --eq_ax_congr_red                       true
% 2.01/0.96  --pure_diseq_elim                       true
% 2.01/0.96  --brand_transform                       false
% 2.01/0.96  --non_eq_to_eq                          false
% 2.01/0.96  --prep_def_merge                        true
% 2.01/0.96  --prep_def_merge_prop_impl              false
% 2.01/0.96  --prep_def_merge_mbd                    true
% 2.01/0.96  --prep_def_merge_tr_red                 false
% 2.01/0.96  --prep_def_merge_tr_cl                  false
% 2.01/0.96  --smt_preprocessing                     true
% 2.01/0.96  --smt_ac_axioms                         fast
% 2.01/0.96  --preprocessed_out                      false
% 2.01/0.96  --preprocessed_stats                    false
% 2.01/0.96  
% 2.01/0.96  ------ Abstraction refinement Options
% 2.01/0.96  
% 2.01/0.96  --abstr_ref                             []
% 2.01/0.96  --abstr_ref_prep                        false
% 2.01/0.96  --abstr_ref_until_sat                   false
% 2.01/0.96  --abstr_ref_sig_restrict                funpre
% 2.01/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 2.01/0.96  --abstr_ref_under                       []
% 2.01/0.96  
% 2.01/0.96  ------ SAT Options
% 2.01/0.96  
% 2.01/0.96  --sat_mode                              false
% 2.01/0.96  --sat_fm_restart_options                ""
% 2.01/0.96  --sat_gr_def                            false
% 2.01/0.96  --sat_epr_types                         true
% 2.01/0.96  --sat_non_cyclic_types                  false
% 2.01/0.96  --sat_finite_models                     false
% 2.01/0.96  --sat_fm_lemmas                         false
% 2.01/0.96  --sat_fm_prep                           false
% 2.01/0.96  --sat_fm_uc_incr                        true
% 2.01/0.96  --sat_out_model                         small
% 2.01/0.96  --sat_out_clauses                       false
% 2.01/0.96  
% 2.01/0.96  ------ QBF Options
% 2.01/0.96  
% 2.01/0.96  --qbf_mode                              false
% 2.01/0.96  --qbf_elim_univ                         false
% 2.01/0.96  --qbf_dom_inst                          none
% 2.01/0.96  --qbf_dom_pre_inst                      false
% 2.01/0.96  --qbf_sk_in                             false
% 2.01/0.96  --qbf_pred_elim                         true
% 2.01/0.96  --qbf_split                             512
% 2.01/0.96  
% 2.01/0.96  ------ BMC1 Options
% 2.01/0.96  
% 2.01/0.96  --bmc1_incremental                      false
% 2.01/0.96  --bmc1_axioms                           reachable_all
% 2.01/0.96  --bmc1_min_bound                        0
% 2.01/0.96  --bmc1_max_bound                        -1
% 2.01/0.96  --bmc1_max_bound_default                -1
% 2.01/0.96  --bmc1_symbol_reachability              true
% 2.01/0.96  --bmc1_property_lemmas                  false
% 2.01/0.96  --bmc1_k_induction                      false
% 2.01/0.96  --bmc1_non_equiv_states                 false
% 2.01/0.96  --bmc1_deadlock                         false
% 2.01/0.96  --bmc1_ucm                              false
% 2.01/0.96  --bmc1_add_unsat_core                   none
% 2.01/0.96  --bmc1_unsat_core_children              false
% 2.01/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 2.01/0.96  --bmc1_out_stat                         full
% 2.01/0.96  --bmc1_ground_init                      false
% 2.01/0.96  --bmc1_pre_inst_next_state              false
% 2.01/0.96  --bmc1_pre_inst_state                   false
% 2.01/0.96  --bmc1_pre_inst_reach_state             false
% 2.01/0.96  --bmc1_out_unsat_core                   false
% 2.01/0.96  --bmc1_aig_witness_out                  false
% 2.01/0.96  --bmc1_verbose                          false
% 2.01/0.96  --bmc1_dump_clauses_tptp                false
% 2.01/0.96  --bmc1_dump_unsat_core_tptp             false
% 2.01/0.96  --bmc1_dump_file                        -
% 2.01/0.96  --bmc1_ucm_expand_uc_limit              128
% 2.01/0.96  --bmc1_ucm_n_expand_iterations          6
% 2.01/0.96  --bmc1_ucm_extend_mode                  1
% 2.01/0.96  --bmc1_ucm_init_mode                    2
% 2.01/0.96  --bmc1_ucm_cone_mode                    none
% 2.01/0.96  --bmc1_ucm_reduced_relation_type        0
% 2.01/0.96  --bmc1_ucm_relax_model                  4
% 2.01/0.96  --bmc1_ucm_full_tr_after_sat            true
% 2.01/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 2.01/0.96  --bmc1_ucm_layered_model                none
% 2.01/0.96  --bmc1_ucm_max_lemma_size               10
% 2.01/0.96  
% 2.01/0.96  ------ AIG Options
% 2.01/0.96  
% 2.01/0.96  --aig_mode                              false
% 2.01/0.96  
% 2.01/0.96  ------ Instantiation Options
% 2.01/0.96  
% 2.01/0.96  --instantiation_flag                    true
% 2.01/0.96  --inst_sos_flag                         false
% 2.01/0.96  --inst_sos_phase                        true
% 2.01/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.01/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.01/0.96  --inst_lit_sel_side                     num_symb
% 2.01/0.96  --inst_solver_per_active                1400
% 2.01/0.96  --inst_solver_calls_frac                1.
% 2.01/0.96  --inst_passive_queue_type               priority_queues
% 2.01/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.01/0.96  --inst_passive_queues_freq              [25;2]
% 2.01/0.96  --inst_dismatching                      true
% 2.01/0.96  --inst_eager_unprocessed_to_passive     true
% 2.01/0.96  --inst_prop_sim_given                   true
% 2.01/0.96  --inst_prop_sim_new                     false
% 2.01/0.96  --inst_subs_new                         false
% 2.01/0.96  --inst_eq_res_simp                      false
% 2.01/0.96  --inst_subs_given                       false
% 2.01/0.96  --inst_orphan_elimination               true
% 2.01/0.96  --inst_learning_loop_flag               true
% 2.01/0.96  --inst_learning_start                   3000
% 2.01/0.96  --inst_learning_factor                  2
% 2.01/0.96  --inst_start_prop_sim_after_learn       3
% 2.01/0.96  --inst_sel_renew                        solver
% 2.01/0.96  --inst_lit_activity_flag                true
% 2.01/0.96  --inst_restr_to_given                   false
% 2.01/0.96  --inst_activity_threshold               500
% 2.01/0.96  --inst_out_proof                        true
% 2.01/0.96  
% 2.01/0.96  ------ Resolution Options
% 2.01/0.96  
% 2.01/0.96  --resolution_flag                       true
% 2.01/0.96  --res_lit_sel                           adaptive
% 2.01/0.96  --res_lit_sel_side                      none
% 2.01/0.96  --res_ordering                          kbo
% 2.01/0.96  --res_to_prop_solver                    active
% 2.01/0.96  --res_prop_simpl_new                    false
% 2.01/0.96  --res_prop_simpl_given                  true
% 2.01/0.96  --res_passive_queue_type                priority_queues
% 2.01/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.01/0.96  --res_passive_queues_freq               [15;5]
% 2.01/0.96  --res_forward_subs                      full
% 2.01/0.96  --res_backward_subs                     full
% 2.01/0.96  --res_forward_subs_resolution           true
% 2.01/0.96  --res_backward_subs_resolution          true
% 2.01/0.96  --res_orphan_elimination                true
% 2.01/0.96  --res_time_limit                        2.
% 2.01/0.96  --res_out_proof                         true
% 2.01/0.96  
% 2.01/0.96  ------ Superposition Options
% 2.01/0.96  
% 2.01/0.96  --superposition_flag                    true
% 2.01/0.96  --sup_passive_queue_type                priority_queues
% 2.01/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.01/0.96  --sup_passive_queues_freq               [8;1;4]
% 2.01/0.96  --demod_completeness_check              fast
% 2.01/0.96  --demod_use_ground                      true
% 2.01/0.96  --sup_to_prop_solver                    passive
% 2.01/0.96  --sup_prop_simpl_new                    true
% 2.01/0.96  --sup_prop_simpl_given                  true
% 2.01/0.96  --sup_fun_splitting                     false
% 2.01/0.96  --sup_smt_interval                      50000
% 2.01/0.96  
% 2.01/0.96  ------ Superposition Simplification Setup
% 2.01/0.96  
% 2.01/0.96  --sup_indices_passive                   []
% 2.01/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.01/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.01/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.01/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 2.01/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.01/0.96  --sup_full_bw                           [BwDemod]
% 2.01/0.96  --sup_immed_triv                        [TrivRules]
% 2.01/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.01/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.01/0.96  --sup_immed_bw_main                     []
% 2.01/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.01/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 2.01/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.01/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.01/0.96  
% 2.01/0.96  ------ Combination Options
% 2.01/0.96  
% 2.01/0.96  --comb_res_mult                         3
% 2.01/0.96  --comb_sup_mult                         2
% 2.01/0.96  --comb_inst_mult                        10
% 2.01/0.96  
% 2.01/0.96  ------ Debug Options
% 2.01/0.96  
% 2.01/0.96  --dbg_backtrace                         false
% 2.01/0.96  --dbg_dump_prop_clauses                 false
% 2.01/0.96  --dbg_dump_prop_clauses_file            -
% 2.01/0.96  --dbg_out_stat                          false
% 2.01/0.96  ------ Parsing...
% 2.01/0.96  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.01/0.96  
% 2.01/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 2.01/0.96  
% 2.01/0.96  ------ Preprocessing... gs_s  sp: 3 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.01/0.96  
% 2.01/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.01/0.96  ------ Proving...
% 2.01/0.96  ------ Problem Properties 
% 2.01/0.96  
% 2.01/0.96  
% 2.01/0.96  clauses                                 19
% 2.01/0.96  conjectures                             2
% 2.01/0.96  EPR                                     3
% 2.01/0.96  Horn                                    15
% 2.01/0.96  unary                                   8
% 2.01/0.96  binary                                  2
% 2.01/0.96  lits                                    43
% 2.01/0.96  lits eq                                 10
% 2.01/0.96  fd_pure                                 0
% 2.01/0.96  fd_pseudo                               0
% 2.01/0.96  fd_cond                                 5
% 2.01/0.96  fd_pseudo_cond                          0
% 2.01/0.96  AC symbols                              0
% 2.01/0.96  
% 2.01/0.96  ------ Schedule dynamic 5 is on 
% 2.01/0.96  
% 2.01/0.96  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.01/0.96  
% 2.01/0.96  
% 2.01/0.96  ------ 
% 2.01/0.96  Current options:
% 2.01/0.96  ------ 
% 2.01/0.96  
% 2.01/0.96  ------ Input Options
% 2.01/0.96  
% 2.01/0.96  --out_options                           all
% 2.01/0.96  --tptp_safe_out                         true
% 2.01/0.96  --problem_path                          ""
% 2.01/0.96  --include_path                          ""
% 2.01/0.96  --clausifier                            res/vclausify_rel
% 2.01/0.96  --clausifier_options                    --mode clausify
% 2.01/0.96  --stdin                                 false
% 2.01/0.96  --stats_out                             all
% 2.01/0.96  
% 2.01/0.96  ------ General Options
% 2.01/0.96  
% 2.01/0.96  --fof                                   false
% 2.01/0.96  --time_out_real                         305.
% 2.01/0.96  --time_out_virtual                      -1.
% 2.01/0.96  --symbol_type_check                     false
% 2.01/0.96  --clausify_out                          false
% 2.01/0.96  --sig_cnt_out                           false
% 2.01/0.96  --trig_cnt_out                          false
% 2.01/0.96  --trig_cnt_out_tolerance                1.
% 2.01/0.96  --trig_cnt_out_sk_spl                   false
% 2.01/0.96  --abstr_cl_out                          false
% 2.01/0.96  
% 2.01/0.96  ------ Global Options
% 2.01/0.96  
% 2.01/0.96  --schedule                              default
% 2.01/0.96  --add_important_lit                     false
% 2.01/0.96  --prop_solver_per_cl                    1000
% 2.01/0.96  --min_unsat_core                        false
% 2.01/0.96  --soft_assumptions                      false
% 2.01/0.96  --soft_lemma_size                       3
% 2.01/0.96  --prop_impl_unit_size                   0
% 2.01/0.96  --prop_impl_unit                        []
% 2.01/0.96  --share_sel_clauses                     true
% 2.01/0.96  --reset_solvers                         false
% 2.01/0.96  --bc_imp_inh                            [conj_cone]
% 2.01/0.96  --conj_cone_tolerance                   3.
% 2.01/0.96  --extra_neg_conj                        none
% 2.01/0.96  --large_theory_mode                     true
% 2.01/0.96  --prolific_symb_bound                   200
% 2.01/0.96  --lt_threshold                          2000
% 2.01/0.96  --clause_weak_htbl                      true
% 2.01/0.96  --gc_record_bc_elim                     false
% 2.01/0.96  
% 2.01/0.96  ------ Preprocessing Options
% 2.01/0.96  
% 2.01/0.96  --preprocessing_flag                    true
% 2.01/0.96  --time_out_prep_mult                    0.1
% 2.01/0.96  --splitting_mode                        input
% 2.01/0.96  --splitting_grd                         true
% 2.01/0.96  --splitting_cvd                         false
% 2.01/0.96  --splitting_cvd_svl                     false
% 2.01/0.96  --splitting_nvd                         32
% 2.01/0.96  --sub_typing                            true
% 2.01/0.96  --prep_gs_sim                           true
% 2.01/0.96  --prep_unflatten                        true
% 2.01/0.96  --prep_res_sim                          true
% 2.01/0.96  --prep_upred                            true
% 2.01/0.96  --prep_sem_filter                       exhaustive
% 2.01/0.96  --prep_sem_filter_out                   false
% 2.01/0.96  --pred_elim                             true
% 2.01/0.96  --res_sim_input                         true
% 2.01/0.96  --eq_ax_congr_red                       true
% 2.01/0.96  --pure_diseq_elim                       true
% 2.01/0.96  --brand_transform                       false
% 2.01/0.96  --non_eq_to_eq                          false
% 2.01/0.96  --prep_def_merge                        true
% 2.01/0.96  --prep_def_merge_prop_impl              false
% 2.01/0.96  --prep_def_merge_mbd                    true
% 2.01/0.96  --prep_def_merge_tr_red                 false
% 2.01/0.96  --prep_def_merge_tr_cl                  false
% 2.01/0.96  --smt_preprocessing                     true
% 2.01/0.96  --smt_ac_axioms                         fast
% 2.01/0.96  --preprocessed_out                      false
% 2.01/0.96  --preprocessed_stats                    false
% 2.01/0.96  
% 2.01/0.96  ------ Abstraction refinement Options
% 2.01/0.96  
% 2.01/0.96  --abstr_ref                             []
% 2.01/0.96  --abstr_ref_prep                        false
% 2.01/0.96  --abstr_ref_until_sat                   false
% 2.01/0.96  --abstr_ref_sig_restrict                funpre
% 2.01/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 2.01/0.96  --abstr_ref_under                       []
% 2.01/0.96  
% 2.01/0.96  ------ SAT Options
% 2.01/0.96  
% 2.01/0.96  --sat_mode                              false
% 2.01/0.96  --sat_fm_restart_options                ""
% 2.01/0.97  --sat_gr_def                            false
% 2.01/0.97  --sat_epr_types                         true
% 2.01/0.97  --sat_non_cyclic_types                  false
% 2.01/0.97  --sat_finite_models                     false
% 2.01/0.97  --sat_fm_lemmas                         false
% 2.01/0.97  --sat_fm_prep                           false
% 2.01/0.97  --sat_fm_uc_incr                        true
% 2.01/0.97  --sat_out_model                         small
% 2.01/0.97  --sat_out_clauses                       false
% 2.01/0.97  
% 2.01/0.97  ------ QBF Options
% 2.01/0.97  
% 2.01/0.97  --qbf_mode                              false
% 2.01/0.97  --qbf_elim_univ                         false
% 2.01/0.97  --qbf_dom_inst                          none
% 2.01/0.97  --qbf_dom_pre_inst                      false
% 2.01/0.97  --qbf_sk_in                             false
% 2.01/0.97  --qbf_pred_elim                         true
% 2.01/0.97  --qbf_split                             512
% 2.01/0.97  
% 2.01/0.97  ------ BMC1 Options
% 2.01/0.97  
% 2.01/0.97  --bmc1_incremental                      false
% 2.01/0.97  --bmc1_axioms                           reachable_all
% 2.01/0.97  --bmc1_min_bound                        0
% 2.01/0.97  --bmc1_max_bound                        -1
% 2.01/0.97  --bmc1_max_bound_default                -1
% 2.01/0.97  --bmc1_symbol_reachability              true
% 2.01/0.97  --bmc1_property_lemmas                  false
% 2.01/0.97  --bmc1_k_induction                      false
% 2.01/0.97  --bmc1_non_equiv_states                 false
% 2.01/0.97  --bmc1_deadlock                         false
% 2.01/0.97  --bmc1_ucm                              false
% 2.01/0.97  --bmc1_add_unsat_core                   none
% 2.01/0.97  --bmc1_unsat_core_children              false
% 2.01/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.01/0.97  --bmc1_out_stat                         full
% 2.01/0.97  --bmc1_ground_init                      false
% 2.01/0.97  --bmc1_pre_inst_next_state              false
% 2.01/0.97  --bmc1_pre_inst_state                   false
% 2.01/0.97  --bmc1_pre_inst_reach_state             false
% 2.01/0.97  --bmc1_out_unsat_core                   false
% 2.01/0.97  --bmc1_aig_witness_out                  false
% 2.01/0.97  --bmc1_verbose                          false
% 2.01/0.97  --bmc1_dump_clauses_tptp                false
% 2.01/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.01/0.97  --bmc1_dump_file                        -
% 2.01/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.01/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.01/0.97  --bmc1_ucm_extend_mode                  1
% 2.01/0.97  --bmc1_ucm_init_mode                    2
% 2.01/0.97  --bmc1_ucm_cone_mode                    none
% 2.01/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.01/0.97  --bmc1_ucm_relax_model                  4
% 2.01/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.01/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.01/0.97  --bmc1_ucm_layered_model                none
% 2.01/0.97  --bmc1_ucm_max_lemma_size               10
% 2.01/0.97  
% 2.01/0.97  ------ AIG Options
% 2.01/0.97  
% 2.01/0.97  --aig_mode                              false
% 2.01/0.97  
% 2.01/0.97  ------ Instantiation Options
% 2.01/0.97  
% 2.01/0.97  --instantiation_flag                    true
% 2.01/0.97  --inst_sos_flag                         false
% 2.01/0.97  --inst_sos_phase                        true
% 2.01/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.01/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.01/0.97  --inst_lit_sel_side                     none
% 2.01/0.97  --inst_solver_per_active                1400
% 2.01/0.97  --inst_solver_calls_frac                1.
% 2.01/0.97  --inst_passive_queue_type               priority_queues
% 2.01/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.01/0.97  --inst_passive_queues_freq              [25;2]
% 2.01/0.97  --inst_dismatching                      true
% 2.01/0.97  --inst_eager_unprocessed_to_passive     true
% 2.01/0.97  --inst_prop_sim_given                   true
% 2.01/0.97  --inst_prop_sim_new                     false
% 2.01/0.97  --inst_subs_new                         false
% 2.01/0.97  --inst_eq_res_simp                      false
% 2.01/0.97  --inst_subs_given                       false
% 2.01/0.97  --inst_orphan_elimination               true
% 2.01/0.97  --inst_learning_loop_flag               true
% 2.01/0.97  --inst_learning_start                   3000
% 2.01/0.97  --inst_learning_factor                  2
% 2.01/0.97  --inst_start_prop_sim_after_learn       3
% 2.01/0.97  --inst_sel_renew                        solver
% 2.01/0.97  --inst_lit_activity_flag                true
% 2.01/0.97  --inst_restr_to_given                   false
% 2.01/0.97  --inst_activity_threshold               500
% 2.01/0.97  --inst_out_proof                        true
% 2.01/0.97  
% 2.01/0.97  ------ Resolution Options
% 2.01/0.97  
% 2.01/0.97  --resolution_flag                       false
% 2.01/0.97  --res_lit_sel                           adaptive
% 2.01/0.97  --res_lit_sel_side                      none
% 2.01/0.97  --res_ordering                          kbo
% 2.01/0.97  --res_to_prop_solver                    active
% 2.01/0.97  --res_prop_simpl_new                    false
% 2.01/0.97  --res_prop_simpl_given                  true
% 2.01/0.97  --res_passive_queue_type                priority_queues
% 2.01/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.01/0.97  --res_passive_queues_freq               [15;5]
% 2.01/0.97  --res_forward_subs                      full
% 2.01/0.97  --res_backward_subs                     full
% 2.01/0.97  --res_forward_subs_resolution           true
% 2.01/0.97  --res_backward_subs_resolution          true
% 2.01/0.97  --res_orphan_elimination                true
% 2.01/0.97  --res_time_limit                        2.
% 2.01/0.97  --res_out_proof                         true
% 2.01/0.97  
% 2.01/0.97  ------ Superposition Options
% 2.01/0.97  
% 2.01/0.97  --superposition_flag                    true
% 2.01/0.97  --sup_passive_queue_type                priority_queues
% 2.01/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.01/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.01/0.97  --demod_completeness_check              fast
% 2.01/0.97  --demod_use_ground                      true
% 2.01/0.97  --sup_to_prop_solver                    passive
% 2.01/0.97  --sup_prop_simpl_new                    true
% 2.01/0.97  --sup_prop_simpl_given                  true
% 2.01/0.97  --sup_fun_splitting                     false
% 2.01/0.97  --sup_smt_interval                      50000
% 2.01/0.97  
% 2.01/0.97  ------ Superposition Simplification Setup
% 2.01/0.97  
% 2.01/0.97  --sup_indices_passive                   []
% 2.01/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.01/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.01/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.01/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.01/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.01/0.97  --sup_full_bw                           [BwDemod]
% 2.01/0.97  --sup_immed_triv                        [TrivRules]
% 2.01/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.01/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.01/0.97  --sup_immed_bw_main                     []
% 2.01/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.01/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.01/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.01/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.01/0.97  
% 2.01/0.97  ------ Combination Options
% 2.01/0.97  
% 2.01/0.97  --comb_res_mult                         3
% 2.01/0.97  --comb_sup_mult                         2
% 2.01/0.97  --comb_inst_mult                        10
% 2.01/0.97  
% 2.01/0.97  ------ Debug Options
% 2.01/0.97  
% 2.01/0.97  --dbg_backtrace                         false
% 2.01/0.97  --dbg_dump_prop_clauses                 false
% 2.01/0.97  --dbg_dump_prop_clauses_file            -
% 2.01/0.97  --dbg_out_stat                          false
% 2.01/0.97  
% 2.01/0.97  
% 2.01/0.97  
% 2.01/0.97  
% 2.01/0.97  ------ Proving...
% 2.01/0.97  
% 2.01/0.97  
% 2.01/0.97  % SZS status Theorem for theBenchmark.p
% 2.01/0.97  
% 2.01/0.97   Resolution empty clause
% 2.01/0.97  
% 2.01/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 2.01/0.97  
% 2.01/0.97  fof(f5,axiom,(
% 2.01/0.97    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 2.01/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.01/0.97  
% 2.01/0.97  fof(f31,plain,(
% 2.01/0.97    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK0(X0),X0))),
% 2.01/0.97    introduced(choice_axiom,[])).
% 2.01/0.97  
% 2.01/0.97  fof(f32,plain,(
% 2.01/0.97    ! [X0] : m1_subset_1(sK0(X0),X0)),
% 2.01/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f5,f31])).
% 2.01/0.97  
% 2.01/0.97  fof(f45,plain,(
% 2.01/0.97    ( ! [X0] : (m1_subset_1(sK0(X0),X0)) )),
% 2.01/0.97    inference(cnf_transformation,[],[f32])).
% 2.01/0.97  
% 2.01/0.97  fof(f11,axiom,(
% 2.01/0.97    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 2.01/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.01/0.97  
% 2.01/0.97  fof(f23,plain,(
% 2.01/0.97    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.01/0.97    inference(ennf_transformation,[],[f11])).
% 2.01/0.97  
% 2.01/0.97  fof(f24,plain,(
% 2.01/0.97    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.01/0.97    inference(flattening,[],[f23])).
% 2.01/0.97  
% 2.01/0.97  fof(f50,plain,(
% 2.01/0.97    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.01/0.97    inference(cnf_transformation,[],[f24])).
% 2.01/0.97  
% 2.01/0.97  fof(f8,axiom,(
% 2.01/0.97    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.01/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.01/0.97  
% 2.01/0.97  fof(f18,plain,(
% 2.01/0.97    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.01/0.97    inference(ennf_transformation,[],[f8])).
% 2.01/0.97  
% 2.01/0.97  fof(f47,plain,(
% 2.01/0.97    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.01/0.97    inference(cnf_transformation,[],[f18])).
% 2.01/0.97  
% 2.01/0.97  fof(f9,axiom,(
% 2.01/0.97    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.01/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.01/0.97  
% 2.01/0.97  fof(f19,plain,(
% 2.01/0.97    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.01/0.97    inference(ennf_transformation,[],[f9])).
% 2.01/0.97  
% 2.01/0.97  fof(f20,plain,(
% 2.01/0.97    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.01/0.97    inference(flattening,[],[f19])).
% 2.01/0.97  
% 2.01/0.97  fof(f48,plain,(
% 2.01/0.97    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.01/0.97    inference(cnf_transformation,[],[f20])).
% 2.01/0.97  
% 2.01/0.97  fof(f14,conjecture,(
% 2.01/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => ~v3_tex_2(X1,X0)))),
% 2.01/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.01/0.97  
% 2.01/0.97  fof(f15,negated_conjecture,(
% 2.01/0.97    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => ~v3_tex_2(X1,X0)))),
% 2.01/0.97    inference(negated_conjecture,[],[f14])).
% 2.01/0.97  
% 2.01/0.97  fof(f29,plain,(
% 2.01/0.97    ? [X0] : (? [X1] : (v3_tex_2(X1,X0) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.01/0.97    inference(ennf_transformation,[],[f15])).
% 2.01/0.97  
% 2.01/0.97  fof(f30,plain,(
% 2.01/0.97    ? [X0] : (? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.01/0.97    inference(flattening,[],[f29])).
% 2.01/0.97  
% 2.01/0.97  fof(f39,plain,(
% 2.01/0.97    ( ! [X0] : (? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => (v3_tex_2(sK3,X0) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(sK3))) )),
% 2.01/0.97    introduced(choice_axiom,[])).
% 2.01/0.97  
% 2.01/0.97  fof(f38,plain,(
% 2.01/0.97    ? [X0] : (? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (v3_tex_2(X1,sK2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) & v1_xboole_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 2.01/0.97    introduced(choice_axiom,[])).
% 2.01/0.97  
% 2.01/0.97  fof(f40,plain,(
% 2.01/0.97    (v3_tex_2(sK3,sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) & v1_xboole_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 2.01/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f30,f39,f38])).
% 2.01/0.97  
% 2.01/0.97  fof(f58,plain,(
% 2.01/0.97    ~v2_struct_0(sK2)),
% 2.01/0.97    inference(cnf_transformation,[],[f40])).
% 2.01/0.97  
% 2.01/0.97  fof(f60,plain,(
% 2.01/0.97    l1_pre_topc(sK2)),
% 2.01/0.97    inference(cnf_transformation,[],[f40])).
% 2.01/0.97  
% 2.01/0.97  fof(f10,axiom,(
% 2.01/0.97    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.01/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.01/0.97  
% 2.01/0.97  fof(f21,plain,(
% 2.01/0.97    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.01/0.97    inference(ennf_transformation,[],[f10])).
% 2.01/0.97  
% 2.01/0.97  fof(f22,plain,(
% 2.01/0.97    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.01/0.97    inference(flattening,[],[f21])).
% 2.01/0.97  
% 2.01/0.97  fof(f49,plain,(
% 2.01/0.97    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.01/0.97    inference(cnf_transformation,[],[f22])).
% 2.01/0.97  
% 2.01/0.97  fof(f61,plain,(
% 2.01/0.97    v1_xboole_0(sK3)),
% 2.01/0.97    inference(cnf_transformation,[],[f40])).
% 2.01/0.97  
% 2.01/0.97  fof(f1,axiom,(
% 2.01/0.97    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.01/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.01/0.97  
% 2.01/0.97  fof(f17,plain,(
% 2.01/0.97    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.01/0.97    inference(ennf_transformation,[],[f1])).
% 2.01/0.97  
% 2.01/0.97  fof(f41,plain,(
% 2.01/0.97    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.01/0.97    inference(cnf_transformation,[],[f17])).
% 2.01/0.97  
% 2.01/0.97  fof(f63,plain,(
% 2.01/0.97    v3_tex_2(sK3,sK2)),
% 2.01/0.97    inference(cnf_transformation,[],[f40])).
% 2.01/0.97  
% 2.01/0.97  fof(f3,axiom,(
% 2.01/0.97    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.01/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.01/0.97  
% 2.01/0.97  fof(f43,plain,(
% 2.01/0.97    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.01/0.97    inference(cnf_transformation,[],[f3])).
% 2.01/0.97  
% 2.01/0.97  fof(f12,axiom,(
% 2.01/0.97    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 2.01/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.01/0.97  
% 2.01/0.97  fof(f25,plain,(
% 2.01/0.97    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.01/0.97    inference(ennf_transformation,[],[f12])).
% 2.01/0.97  
% 2.01/0.97  fof(f26,plain,(
% 2.01/0.97    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.01/0.97    inference(flattening,[],[f25])).
% 2.01/0.97  
% 2.01/0.97  fof(f33,plain,(
% 2.01/0.97    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.01/0.97    inference(nnf_transformation,[],[f26])).
% 2.01/0.97  
% 2.01/0.97  fof(f34,plain,(
% 2.01/0.97    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.01/0.97    inference(flattening,[],[f33])).
% 2.01/0.97  
% 2.01/0.97  fof(f35,plain,(
% 2.01/0.97    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.01/0.97    inference(rectify,[],[f34])).
% 2.01/0.97  
% 2.01/0.97  fof(f36,plain,(
% 2.01/0.97    ! [X1,X0] : (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK1(X0,X1) != X1 & r1_tarski(X1,sK1(X0,X1)) & v2_tex_2(sK1(X0,X1),X0) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.01/0.97    introduced(choice_axiom,[])).
% 2.01/0.97  
% 2.01/0.97  fof(f37,plain,(
% 2.01/0.97    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (sK1(X0,X1) != X1 & r1_tarski(X1,sK1(X0,X1)) & v2_tex_2(sK1(X0,X1),X0) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.01/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f36])).
% 2.01/0.97  
% 2.01/0.97  fof(f52,plain,(
% 2.01/0.97    ( ! [X0,X3,X1] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.01/0.97    inference(cnf_transformation,[],[f37])).
% 2.01/0.97  
% 2.01/0.97  fof(f6,axiom,(
% 2.01/0.97    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.01/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.01/0.97  
% 2.01/0.97  fof(f46,plain,(
% 2.01/0.97    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.01/0.97    inference(cnf_transformation,[],[f6])).
% 2.01/0.97  
% 2.01/0.97  fof(f13,axiom,(
% 2.01/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 2.01/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.01/0.97  
% 2.01/0.97  fof(f27,plain,(
% 2.01/0.97    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.01/0.97    inference(ennf_transformation,[],[f13])).
% 2.01/0.97  
% 2.01/0.97  fof(f28,plain,(
% 2.01/0.97    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.01/0.97    inference(flattening,[],[f27])).
% 2.01/0.97  
% 2.01/0.97  fof(f57,plain,(
% 2.01/0.97    ( ! [X0,X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.01/0.97    inference(cnf_transformation,[],[f28])).
% 2.01/0.97  
% 2.01/0.97  fof(f59,plain,(
% 2.01/0.97    v2_pre_topc(sK2)),
% 2.01/0.97    inference(cnf_transformation,[],[f40])).
% 2.01/0.97  
% 2.01/0.97  fof(f2,axiom,(
% 2.01/0.97    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 2.01/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.01/0.97  
% 2.01/0.97  fof(f42,plain,(
% 2.01/0.97    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.01/0.97    inference(cnf_transformation,[],[f2])).
% 2.01/0.97  
% 2.01/0.97  fof(f4,axiom,(
% 2.01/0.97    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 2.01/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.01/0.97  
% 2.01/0.97  fof(f44,plain,(
% 2.01/0.97    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 2.01/0.97    inference(cnf_transformation,[],[f4])).
% 2.01/0.97  
% 2.01/0.97  cnf(c_4,plain,
% 2.01/0.97      ( m1_subset_1(sK0(X0),X0) ),
% 2.01/0.97      inference(cnf_transformation,[],[f45]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_1208,plain,
% 2.01/0.97      ( m1_subset_1(sK0(X0),X0) = iProver_top ),
% 2.01/0.97      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_9,plain,
% 2.01/0.97      ( ~ m1_subset_1(X0,X1)
% 2.01/0.97      | v1_xboole_0(X1)
% 2.01/0.97      | k6_domain_1(X1,X0) = k1_tarski(X0) ),
% 2.01/0.97      inference(cnf_transformation,[],[f50]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_1205,plain,
% 2.01/0.97      ( k6_domain_1(X0,X1) = k1_tarski(X1)
% 2.01/0.97      | m1_subset_1(X1,X0) != iProver_top
% 2.01/0.97      | v1_xboole_0(X0) = iProver_top ),
% 2.01/0.97      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_1922,plain,
% 2.01/0.97      ( k6_domain_1(X0,sK0(X0)) = k1_tarski(sK0(X0))
% 2.01/0.97      | v1_xboole_0(X0) = iProver_top ),
% 2.01/0.97      inference(superposition,[status(thm)],[c_1208,c_1205]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_6,plain,
% 2.01/0.97      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 2.01/0.97      inference(cnf_transformation,[],[f47]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_7,plain,
% 2.01/0.97      ( v2_struct_0(X0) | ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.01/0.97      inference(cnf_transformation,[],[f48]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_240,plain,
% 2.01/0.97      ( v2_struct_0(X0) | ~ l1_pre_topc(X0) | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.01/0.97      inference(resolution,[status(thm)],[c_6,c_7]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_22,negated_conjecture,
% 2.01/0.97      ( ~ v2_struct_0(sK2) ),
% 2.01/0.97      inference(cnf_transformation,[],[f58]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_279,plain,
% 2.01/0.97      ( ~ l1_pre_topc(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK2 != X0 ),
% 2.01/0.97      inference(resolution_lifted,[status(thm)],[c_240,c_22]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_280,plain,
% 2.01/0.97      ( ~ l1_pre_topc(sK2) | ~ v1_xboole_0(u1_struct_0(sK2)) ),
% 2.01/0.97      inference(unflattening,[status(thm)],[c_279]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_20,negated_conjecture,
% 2.01/0.97      ( l1_pre_topc(sK2) ),
% 2.01/0.97      inference(cnf_transformation,[],[f60]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_282,plain,
% 2.01/0.97      ( ~ v1_xboole_0(u1_struct_0(sK2)) ),
% 2.01/0.97      inference(global_propositional_subsumption,[status(thm)],[c_280,c_20]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_1201,plain,
% 2.01/0.97      ( v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 2.01/0.97      inference(predicate_to_equality,[status(thm)],[c_282]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_2061,plain,
% 2.01/0.97      ( k6_domain_1(u1_struct_0(sK2),sK0(u1_struct_0(sK2))) = k1_tarski(sK0(u1_struct_0(sK2))) ),
% 2.01/0.97      inference(superposition,[status(thm)],[c_1922,c_1201]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_8,plain,
% 2.01/0.97      ( ~ m1_subset_1(X0,X1)
% 2.01/0.97      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
% 2.01/0.97      | v1_xboole_0(X1) ),
% 2.01/0.97      inference(cnf_transformation,[],[f49]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_1206,plain,
% 2.01/0.97      ( m1_subset_1(X0,X1) != iProver_top
% 2.01/0.97      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top
% 2.01/0.97      | v1_xboole_0(X1) = iProver_top ),
% 2.01/0.97      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_2208,plain,
% 2.01/0.97      ( m1_subset_1(sK0(u1_struct_0(sK2)),u1_struct_0(sK2)) != iProver_top
% 2.01/0.97      | m1_subset_1(k1_tarski(sK0(u1_struct_0(sK2))),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 2.01/0.97      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 2.01/0.97      inference(superposition,[status(thm)],[c_2061,c_1206]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_25,plain,
% 2.01/0.97      ( l1_pre_topc(sK2) = iProver_top ),
% 2.01/0.97      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_281,plain,
% 2.01/0.97      ( l1_pre_topc(sK2) != iProver_top
% 2.01/0.97      | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 2.01/0.97      inference(predicate_to_equality,[status(thm)],[c_280]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_1317,plain,
% 2.01/0.97      ( m1_subset_1(sK0(u1_struct_0(sK2)),u1_struct_0(sK2)) ),
% 2.01/0.97      inference(instantiation,[status(thm)],[c_4]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_1319,plain,
% 2.01/0.97      ( m1_subset_1(sK0(u1_struct_0(sK2)),u1_struct_0(sK2)) = iProver_top ),
% 2.01/0.97      inference(predicate_to_equality,[status(thm)],[c_1317]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_2296,plain,
% 2.01/0.97      ( m1_subset_1(k1_tarski(sK0(u1_struct_0(sK2))),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 2.01/0.97      inference(global_propositional_subsumption,
% 2.01/0.97                [status(thm)],
% 2.01/0.97                [c_2208,c_25,c_281,c_1319]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_19,negated_conjecture,
% 2.01/0.97      ( v1_xboole_0(sK3) ),
% 2.01/0.97      inference(cnf_transformation,[],[f61]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_1203,plain,
% 2.01/0.97      ( v1_xboole_0(sK3) = iProver_top ),
% 2.01/0.97      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_0,plain,
% 2.01/0.97      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 2.01/0.97      inference(cnf_transformation,[],[f41]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_1209,plain,
% 2.01/0.97      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 2.01/0.97      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_1875,plain,
% 2.01/0.97      ( sK3 = k1_xboole_0 ),
% 2.01/0.97      inference(superposition,[status(thm)],[c_1203,c_1209]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_17,negated_conjecture,
% 2.01/0.97      ( v3_tex_2(sK3,sK2) ),
% 2.01/0.97      inference(cnf_transformation,[],[f63]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_2,plain,
% 2.01/0.97      ( r1_tarski(k1_xboole_0,X0) ),
% 2.01/0.97      inference(cnf_transformation,[],[f43]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_14,plain,
% 2.01/0.97      ( ~ v2_tex_2(X0,X1)
% 2.01/0.97      | ~ v3_tex_2(X2,X1)
% 2.01/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.01/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.01/0.97      | ~ r1_tarski(X2,X0)
% 2.01/0.97      | ~ l1_pre_topc(X1)
% 2.01/0.97      | X0 = X2 ),
% 2.01/0.97      inference(cnf_transformation,[],[f52]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_455,plain,
% 2.01/0.97      ( ~ v2_tex_2(X0,X1)
% 2.01/0.97      | ~ v3_tex_2(X2,X1)
% 2.01/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.01/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.01/0.97      | ~ r1_tarski(X2,X0)
% 2.01/0.97      | X2 = X0
% 2.01/0.97      | sK2 != X1 ),
% 2.01/0.97      inference(resolution_lifted,[status(thm)],[c_14,c_20]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_456,plain,
% 2.01/0.97      ( ~ v2_tex_2(X0,sK2)
% 2.01/0.97      | ~ v3_tex_2(X1,sK2)
% 2.01/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.01/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.01/0.97      | ~ r1_tarski(X1,X0)
% 2.01/0.97      | X1 = X0 ),
% 2.01/0.97      inference(unflattening,[status(thm)],[c_455]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_582,plain,
% 2.01/0.97      ( ~ v2_tex_2(X0,sK2)
% 2.01/0.97      | ~ v3_tex_2(X1,sK2)
% 2.01/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.01/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.01/0.97      | X0 != X2
% 2.01/0.97      | X0 = X1
% 2.01/0.97      | k1_xboole_0 != X1 ),
% 2.01/0.97      inference(resolution_lifted,[status(thm)],[c_2,c_456]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_583,plain,
% 2.01/0.97      ( ~ v2_tex_2(X0,sK2)
% 2.01/0.97      | ~ v3_tex_2(k1_xboole_0,sK2)
% 2.01/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.01/0.97      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.01/0.97      | X0 = k1_xboole_0 ),
% 2.01/0.97      inference(unflattening,[status(thm)],[c_582]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_5,plain,
% 2.01/0.97      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.01/0.97      inference(cnf_transformation,[],[f46]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_597,plain,
% 2.01/0.97      ( ~ v2_tex_2(X0,sK2)
% 2.01/0.97      | ~ v3_tex_2(k1_xboole_0,sK2)
% 2.01/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.01/0.97      | X0 = k1_xboole_0 ),
% 2.01/0.97      inference(forward_subsumption_resolution,[status(thm)],[c_583,c_5]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_624,plain,
% 2.01/0.97      ( ~ v2_tex_2(X0,sK2)
% 2.01/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.01/0.97      | sK2 != sK2
% 2.01/0.97      | sK3 != k1_xboole_0
% 2.01/0.97      | k1_xboole_0 = X0 ),
% 2.01/0.97      inference(resolution_lifted,[status(thm)],[c_17,c_597]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_759,plain,
% 2.01/0.97      ( ~ v2_tex_2(X0,sK2)
% 2.01/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.01/0.97      | sK3 != k1_xboole_0
% 2.01/0.97      | k1_xboole_0 = X0 ),
% 2.01/0.97      inference(equality_resolution_simp,[status(thm)],[c_624]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_1193,plain,
% 2.01/0.97      ( sK3 != k1_xboole_0
% 2.01/0.97      | k1_xboole_0 = X0
% 2.01/0.97      | v2_tex_2(X0,sK2) != iProver_top
% 2.01/0.97      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 2.01/0.97      inference(predicate_to_equality,[status(thm)],[c_759]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_1899,plain,
% 2.01/0.97      ( k1_xboole_0 = X0
% 2.01/0.97      | k1_xboole_0 != k1_xboole_0
% 2.01/0.97      | v2_tex_2(X0,sK2) != iProver_top
% 2.01/0.97      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 2.01/0.97      inference(demodulation,[status(thm)],[c_1875,c_1193]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_1908,plain,
% 2.01/0.97      ( k1_xboole_0 = X0
% 2.01/0.97      | v2_tex_2(X0,sK2) != iProver_top
% 2.01/0.97      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 2.01/0.97      inference(equality_resolution_simp,[status(thm)],[c_1899]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_2302,plain,
% 2.01/0.97      ( k1_tarski(sK0(u1_struct_0(sK2))) = k1_xboole_0
% 2.01/0.97      | v2_tex_2(k1_tarski(sK0(u1_struct_0(sK2))),sK2) != iProver_top ),
% 2.01/0.97      inference(superposition,[status(thm)],[c_2296,c_1908]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_16,plain,
% 2.01/0.97      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
% 2.01/0.97      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.01/0.97      | ~ v2_pre_topc(X0)
% 2.01/0.97      | v2_struct_0(X0)
% 2.01/0.97      | ~ l1_pre_topc(X0) ),
% 2.01/0.97      inference(cnf_transformation,[],[f57]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_21,negated_conjecture,
% 2.01/0.97      ( v2_pre_topc(sK2) ),
% 2.01/0.97      inference(cnf_transformation,[],[f59]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_258,plain,
% 2.01/0.97      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
% 2.01/0.97      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.01/0.97      | v2_struct_0(X0)
% 2.01/0.97      | ~ l1_pre_topc(X0)
% 2.01/0.97      | sK2 != X0 ),
% 2.01/0.97      inference(resolution_lifted,[status(thm)],[c_16,c_21]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_259,plain,
% 2.01/0.97      ( v2_tex_2(k6_domain_1(u1_struct_0(sK2),X0),sK2)
% 2.01/0.97      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.01/0.97      | v2_struct_0(sK2)
% 2.01/0.97      | ~ l1_pre_topc(sK2) ),
% 2.01/0.97      inference(unflattening,[status(thm)],[c_258]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_263,plain,
% 2.01/0.97      ( v2_tex_2(k6_domain_1(u1_struct_0(sK2),X0),sK2)
% 2.01/0.97      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 2.01/0.97      inference(global_propositional_subsumption,
% 2.01/0.97                [status(thm)],
% 2.01/0.97                [c_259,c_22,c_20]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_1202,plain,
% 2.01/0.97      ( v2_tex_2(k6_domain_1(u1_struct_0(sK2),X0),sK2) = iProver_top
% 2.01/0.97      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
% 2.01/0.97      inference(predicate_to_equality,[status(thm)],[c_263]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_2209,plain,
% 2.01/0.97      ( v2_tex_2(k1_tarski(sK0(u1_struct_0(sK2))),sK2) = iProver_top
% 2.01/0.97      | m1_subset_1(sK0(u1_struct_0(sK2)),u1_struct_0(sK2)) != iProver_top ),
% 2.01/0.97      inference(superposition,[status(thm)],[c_2061,c_1202]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_2386,plain,
% 2.01/0.97      ( k1_tarski(sK0(u1_struct_0(sK2))) = k1_xboole_0 ),
% 2.01/0.97      inference(global_propositional_subsumption,
% 2.01/0.97                [status(thm)],
% 2.01/0.97                [c_2302,c_1319,c_2209]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_1,plain,
% 2.01/0.97      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 2.01/0.97      inference(cnf_transformation,[],[f42]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_3,plain,
% 2.01/0.97      ( k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
% 2.01/0.97      inference(cnf_transformation,[],[f44]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_1633,plain,
% 2.01/0.97      ( k1_tarski(X0) != k1_xboole_0 ),
% 2.01/0.97      inference(superposition,[status(thm)],[c_1,c_3]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_2389,plain,
% 2.01/0.97      ( $false ),
% 2.01/0.97      inference(forward_subsumption_resolution,[status(thm)],[c_2386,c_1633]) ).
% 2.01/0.97  
% 2.01/0.97  
% 2.01/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 2.01/0.97  
% 2.01/0.97  ------                               Statistics
% 2.01/0.97  
% 2.01/0.97  ------ General
% 2.01/0.97  
% 2.01/0.97  abstr_ref_over_cycles:                  0
% 2.01/0.97  abstr_ref_under_cycles:                 0
% 2.01/0.97  gc_basic_clause_elim:                   0
% 2.01/0.97  forced_gc_time:                         0
% 2.01/0.97  parsing_time:                           0.01
% 2.01/0.97  unif_index_cands_time:                  0.
% 2.01/0.97  unif_index_add_time:                    0.
% 2.01/0.97  orderings_time:                         0.
% 2.01/0.97  out_proof_time:                         0.01
% 2.01/0.97  total_time:                             0.119
% 2.01/0.97  num_of_symbols:                         51
% 2.01/0.97  num_of_terms:                           1801
% 2.01/0.97  
% 2.01/0.97  ------ Preprocessing
% 2.01/0.97  
% 2.01/0.97  num_of_splits:                          3
% 2.01/0.97  num_of_split_atoms:                     1
% 2.01/0.97  num_of_reused_defs:                     2
% 2.01/0.97  num_eq_ax_congr_red:                    13
% 2.01/0.97  num_of_sem_filtered_clauses:            1
% 2.01/0.97  num_of_subtypes:                        0
% 2.01/0.97  monotx_restored_types:                  0
% 2.01/0.97  sat_num_of_epr_types:                   0
% 2.01/0.97  sat_num_of_non_cyclic_types:            0
% 2.01/0.97  sat_guarded_non_collapsed_types:        0
% 2.01/0.97  num_pure_diseq_elim:                    0
% 2.01/0.97  simp_replaced_by:                       0
% 2.01/0.97  res_preprocessed:                       94
% 2.01/0.97  prep_upred:                             0
% 2.01/0.97  prep_unflattend:                        30
% 2.01/0.97  smt_new_axioms:                         0
% 2.01/0.97  pred_elim_cands:                        3
% 2.01/0.97  pred_elim:                              6
% 2.01/0.97  pred_elim_cl:                           7
% 2.01/0.97  pred_elim_cycles:                       10
% 2.01/0.97  merged_defs:                            0
% 2.01/0.97  merged_defs_ncl:                        0
% 2.01/0.97  bin_hyper_res:                          0
% 2.01/0.97  prep_cycles:                            4
% 2.01/0.97  pred_elim_time:                         0.01
% 2.01/0.97  splitting_time:                         0.
% 2.01/0.97  sem_filter_time:                        0.
% 2.01/0.97  monotx_time:                            0.001
% 2.01/0.97  subtype_inf_time:                       0.
% 2.01/0.97  
% 2.01/0.97  ------ Problem properties
% 2.01/0.97  
% 2.01/0.97  clauses:                                19
% 2.01/0.97  conjectures:                            2
% 2.01/0.97  epr:                                    3
% 2.01/0.97  horn:                                   15
% 2.01/0.97  ground:                                 7
% 2.01/0.97  unary:                                  8
% 2.01/0.97  binary:                                 2
% 2.01/0.97  lits:                                   43
% 2.01/0.97  lits_eq:                                10
% 2.01/0.97  fd_pure:                                0
% 2.01/0.97  fd_pseudo:                              0
% 2.01/0.97  fd_cond:                                5
% 2.01/0.97  fd_pseudo_cond:                         0
% 2.01/0.97  ac_symbols:                             0
% 2.01/0.97  
% 2.01/0.97  ------ Propositional Solver
% 2.01/0.97  
% 2.01/0.97  prop_solver_calls:                      25
% 2.01/0.97  prop_fast_solver_calls:                 640
% 2.01/0.97  smt_solver_calls:                       0
% 2.01/0.97  smt_fast_solver_calls:                  0
% 2.01/0.97  prop_num_of_clauses:                    773
% 2.01/0.97  prop_preprocess_simplified:             3251
% 2.01/0.97  prop_fo_subsumed:                       13
% 2.01/0.97  prop_solver_time:                       0.
% 2.01/0.97  smt_solver_time:                        0.
% 2.01/0.97  smt_fast_solver_time:                   0.
% 2.01/0.97  prop_fast_solver_time:                  0.
% 2.01/0.97  prop_unsat_core_time:                   0.
% 2.01/0.97  
% 2.01/0.97  ------ QBF
% 2.01/0.97  
% 2.01/0.97  qbf_q_res:                              0
% 2.01/0.97  qbf_num_tautologies:                    0
% 2.01/0.97  qbf_prep_cycles:                        0
% 2.01/0.97  
% 2.01/0.97  ------ BMC1
% 2.01/0.97  
% 2.01/0.97  bmc1_current_bound:                     -1
% 2.01/0.97  bmc1_last_solved_bound:                 -1
% 2.01/0.97  bmc1_unsat_core_size:                   -1
% 2.01/0.97  bmc1_unsat_core_parents_size:           -1
% 2.01/0.97  bmc1_merge_next_fun:                    0
% 2.01/0.97  bmc1_unsat_core_clauses_time:           0.
% 2.01/0.97  
% 2.01/0.97  ------ Instantiation
% 2.01/0.97  
% 2.01/0.97  inst_num_of_clauses:                    231
% 2.01/0.97  inst_num_in_passive:                    98
% 2.01/0.97  inst_num_in_active:                     133
% 2.01/0.97  inst_num_in_unprocessed:                0
% 2.01/0.97  inst_num_of_loops:                      150
% 2.01/0.97  inst_num_of_learning_restarts:          0
% 2.01/0.97  inst_num_moves_active_passive:          15
% 2.01/0.97  inst_lit_activity:                      0
% 2.01/0.97  inst_lit_activity_moves:                0
% 2.01/0.97  inst_num_tautologies:                   0
% 2.01/0.97  inst_num_prop_implied:                  0
% 2.01/0.97  inst_num_existing_simplified:           0
% 2.01/0.97  inst_num_eq_res_simplified:             0
% 2.01/0.97  inst_num_child_elim:                    0
% 2.01/0.97  inst_num_of_dismatching_blockings:      28
% 2.01/0.97  inst_num_of_non_proper_insts:           153
% 2.01/0.97  inst_num_of_duplicates:                 0
% 2.01/0.97  inst_inst_num_from_inst_to_res:         0
% 2.01/0.97  inst_dismatching_checking_time:         0.
% 2.01/0.97  
% 2.01/0.97  ------ Resolution
% 2.01/0.97  
% 2.01/0.97  res_num_of_clauses:                     0
% 2.01/0.97  res_num_in_passive:                     0
% 2.01/0.97  res_num_in_active:                      0
% 2.01/0.97  res_num_of_loops:                       98
% 2.01/0.97  res_forward_subset_subsumed:            20
% 2.01/0.97  res_backward_subset_subsumed:           0
% 2.01/0.97  res_forward_subsumed:                   0
% 2.01/0.97  res_backward_subsumed:                  0
% 2.01/0.97  res_forward_subsumption_resolution:     5
% 2.01/0.97  res_backward_subsumption_resolution:    0
% 2.01/0.97  res_clause_to_clause_subsumption:       63
% 2.01/0.97  res_orphan_elimination:                 0
% 2.01/0.97  res_tautology_del:                      19
% 2.01/0.97  res_num_eq_res_simplified:              1
% 2.01/0.97  res_num_sel_changes:                    0
% 2.01/0.97  res_moves_from_active_to_pass:          0
% 2.01/0.97  
% 2.01/0.97  ------ Superposition
% 2.01/0.97  
% 2.01/0.97  sup_time_total:                         0.
% 2.01/0.97  sup_time_generating:                    0.
% 2.01/0.97  sup_time_sim_full:                      0.
% 2.01/0.97  sup_time_sim_immed:                     0.
% 2.01/0.97  
% 2.01/0.97  sup_num_of_clauses:                     31
% 2.01/0.97  sup_num_in_active:                      22
% 2.01/0.97  sup_num_in_passive:                     9
% 2.01/0.97  sup_num_of_loops:                       29
% 2.01/0.97  sup_fw_superposition:                   10
% 2.01/0.97  sup_bw_superposition:                   11
% 2.01/0.97  sup_immediate_simplified:               1
% 2.01/0.97  sup_given_eliminated:                   0
% 2.01/0.97  comparisons_done:                       0
% 2.01/0.97  comparisons_avoided:                    0
% 2.01/0.97  
% 2.01/0.97  ------ Simplifications
% 2.01/0.97  
% 2.01/0.97  
% 2.01/0.97  sim_fw_subset_subsumed:                 0
% 2.01/0.97  sim_bw_subset_subsumed:                 4
% 2.01/0.97  sim_fw_subsumed:                        1
% 2.01/0.97  sim_bw_subsumed:                        0
% 2.01/0.97  sim_fw_subsumption_res:                 1
% 2.01/0.97  sim_bw_subsumption_res:                 0
% 2.01/0.97  sim_tautology_del:                      1
% 2.01/0.97  sim_eq_tautology_del:                   3
% 2.01/0.97  sim_eq_res_simp:                        1
% 2.01/0.97  sim_fw_demodulated:                     0
% 2.01/0.97  sim_bw_demodulated:                     4
% 2.01/0.97  sim_light_normalised:                   0
% 2.01/0.97  sim_joinable_taut:                      0
% 2.01/0.97  sim_joinable_simp:                      0
% 2.01/0.97  sim_ac_normalised:                      0
% 2.01/0.97  sim_smt_subsumption:                    0
% 2.01/0.97  
%------------------------------------------------------------------------------
