%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:27:04 EST 2020

% Result     : Theorem 1.09s
% Output     : CNFRefutation 1.09s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 371 expanded)
%              Number of clauses        :   79 ( 124 expanded)
%              Number of leaves         :   19 (  89 expanded)
%              Depth                    :   26
%              Number of atoms          :  445 (1612 expanded)
%              Number of equality atoms :  118 ( 169 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f62,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f40])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f42,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f61,plain,(
    v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f63,plain,(
    v3_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f4,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

cnf(c_4,plain,
    ( m1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1360,plain,
    ( m1_subset_1(sK0(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1357,plain,
    ( k6_domain_1(X0,X1) = k1_tarski(X1)
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2059,plain,
    ( k6_domain_1(X0,sK0(X0)) = k1_tarski(sK0(X0))
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1360,c_1357])).

cnf(c_6,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_7,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_255,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_6,c_7])).

cnf(c_22,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_294,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_255,c_22])).

cnf(c_295,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_294])).

cnf(c_20,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_57,plain,
    ( v2_struct_0(sK2)
    | ~ l1_struct_0(sK2)
    | ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_60,plain,
    ( ~ l1_pre_topc(sK2)
    | l1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_297,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_295,c_22,c_20,c_57,c_60])).

cnf(c_1353,plain,
    ( v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_297])).

cnf(c_2149,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK0(u1_struct_0(sK2))) = k1_tarski(sK0(u1_struct_0(sK2))) ),
    inference(superposition,[status(thm)],[c_2059,c_1353])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1358,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2245,plain,
    ( m1_subset_1(sK0(u1_struct_0(sK2)),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k1_tarski(sK0(u1_struct_0(sK2))),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2149,c_1358])).

cnf(c_23,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_25,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_56,plain,
    ( v2_struct_0(X0) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_58,plain,
    ( v2_struct_0(sK2) = iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_56])).

cnf(c_59,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_61,plain,
    ( l1_pre_topc(sK2) != iProver_top
    | l1_struct_0(sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_59])).

cnf(c_1481,plain,
    ( m1_subset_1(sK0(u1_struct_0(sK2)),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1483,plain,
    ( m1_subset_1(sK0(u1_struct_0(sK2)),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1481])).

cnf(c_2326,plain,
    ( m1_subset_1(k1_tarski(sK0(u1_struct_0(sK2))),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2245,c_23,c_25,c_58,c_61,c_1483])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1356,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

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

cnf(c_519,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ v3_tex_2(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | X2 = X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_20])).

cnf(c_520,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ v3_tex_2(X1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(unflattening,[status(thm)],[c_519])).

cnf(c_646,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ v3_tex_2(X1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | X0 != X2
    | X0 = X1
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_520])).

cnf(c_647,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ v3_tex_2(k1_xboole_0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2)))
    | X0 = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_646])).

cnf(c_5,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_661,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ v3_tex_2(k1_xboole_0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | X0 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_647,c_5])).

cnf(c_13,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_543,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_20])).

cnf(c_544,plain,
    ( ~ v2_tex_2(X0,sK2)
    | v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK1(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unflattening,[status(thm)],[c_543])).

cnf(c_762,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ v2_tex_2(X1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK1(sK2,X1),k1_zfmisc_1(u1_struct_0(sK2)))
    | sK2 != sK2
    | k1_xboole_0 != X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_661,c_544])).

cnf(c_763,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ v2_tex_2(k1_xboole_0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK1(sK2,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_762])).

cnf(c_779,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ v2_tex_2(k1_xboole_0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK1(sK2,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_xboole_0 = X0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_763,c_5])).

cnf(c_1033,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_xboole_0 = X0
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_779])).

cnf(c_1347,plain,
    ( k1_xboole_0 = X0
    | v2_tex_2(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1033])).

cnf(c_1640,plain,
    ( sK3 = k1_xboole_0
    | v2_tex_2(sK3,sK2) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_1356,c_1347])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_19,negated_conjecture,
    ( v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_348,plain,
    ( sK3 != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_19])).

cnf(c_349,plain,
    ( k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_348])).

cnf(c_1038,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1574,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1038])).

cnf(c_1039,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1542,plain,
    ( sK3 != X0
    | sK3 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1039])).

cnf(c_1647,plain,
    ( sK3 != sK3
    | sK3 = k1_xboole_0
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_1542])).

cnf(c_1838,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1640,c_349,c_1574,c_1647])).

cnf(c_17,negated_conjecture,
    ( v3_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_679,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | sK2 != sK2
    | sK3 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_661])).

cnf(c_834,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | sK3 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_679])).

cnf(c_1345,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = X0
    | v2_tex_2(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_834])).

cnf(c_1841,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 != k1_xboole_0
    | v2_tex_2(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1838,c_1345])).

cnf(c_1848,plain,
    ( k1_xboole_0 = X0
    | v2_tex_2(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_1841])).

cnf(c_2332,plain,
    ( k1_tarski(sK0(u1_struct_0(sK2))) = k1_xboole_0
    | v2_tex_2(k1_tarski(sK0(u1_struct_0(sK2))),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2326,c_1848])).

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

cnf(c_273,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_21])).

cnf(c_274,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK2),X0),sK2)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_273])).

cnf(c_278,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK2),X0),sK2)
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_274,c_22,c_20])).

cnf(c_1354,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK2),X0),sK2) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_278])).

cnf(c_2246,plain,
    ( v2_tex_2(k1_tarski(sK0(u1_struct_0(sK2))),sK2) = iProver_top
    | m1_subset_1(sK0(u1_struct_0(sK2)),u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2149,c_1354])).

cnf(c_2344,plain,
    ( k1_tarski(sK0(u1_struct_0(sK2))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2332,c_1483,c_2246])).

cnf(c_3,plain,
    ( ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1361,plain,
    ( v1_xboole_0(k1_tarski(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2352,plain,
    ( v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2344,c_1361])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_77,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2352,c_77])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:36:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.09/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.09/1.01  
% 1.09/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.09/1.01  
% 1.09/1.01  ------  iProver source info
% 1.09/1.01  
% 1.09/1.01  git: date: 2020-06-30 10:37:57 +0100
% 1.09/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.09/1.01  git: non_committed_changes: false
% 1.09/1.01  git: last_make_outside_of_git: false
% 1.09/1.01  
% 1.09/1.01  ------ 
% 1.09/1.01  
% 1.09/1.01  ------ Input Options
% 1.09/1.01  
% 1.09/1.01  --out_options                           all
% 1.09/1.01  --tptp_safe_out                         true
% 1.09/1.01  --problem_path                          ""
% 1.09/1.01  --include_path                          ""
% 1.09/1.01  --clausifier                            res/vclausify_rel
% 1.09/1.01  --clausifier_options                    --mode clausify
% 1.09/1.01  --stdin                                 false
% 1.09/1.01  --stats_out                             all
% 1.09/1.01  
% 1.09/1.01  ------ General Options
% 1.09/1.01  
% 1.09/1.01  --fof                                   false
% 1.09/1.01  --time_out_real                         305.
% 1.09/1.01  --time_out_virtual                      -1.
% 1.09/1.01  --symbol_type_check                     false
% 1.09/1.01  --clausify_out                          false
% 1.09/1.01  --sig_cnt_out                           false
% 1.09/1.01  --trig_cnt_out                          false
% 1.09/1.01  --trig_cnt_out_tolerance                1.
% 1.09/1.01  --trig_cnt_out_sk_spl                   false
% 1.09/1.01  --abstr_cl_out                          false
% 1.09/1.01  
% 1.09/1.01  ------ Global Options
% 1.09/1.01  
% 1.09/1.01  --schedule                              default
% 1.09/1.01  --add_important_lit                     false
% 1.09/1.01  --prop_solver_per_cl                    1000
% 1.09/1.01  --min_unsat_core                        false
% 1.09/1.01  --soft_assumptions                      false
% 1.09/1.01  --soft_lemma_size                       3
% 1.09/1.01  --prop_impl_unit_size                   0
% 1.09/1.01  --prop_impl_unit                        []
% 1.09/1.01  --share_sel_clauses                     true
% 1.09/1.01  --reset_solvers                         false
% 1.09/1.01  --bc_imp_inh                            [conj_cone]
% 1.09/1.01  --conj_cone_tolerance                   3.
% 1.09/1.01  --extra_neg_conj                        none
% 1.09/1.01  --large_theory_mode                     true
% 1.09/1.01  --prolific_symb_bound                   200
% 1.09/1.01  --lt_threshold                          2000
% 1.09/1.01  --clause_weak_htbl                      true
% 1.09/1.01  --gc_record_bc_elim                     false
% 1.09/1.01  
% 1.09/1.01  ------ Preprocessing Options
% 1.09/1.01  
% 1.09/1.01  --preprocessing_flag                    true
% 1.09/1.01  --time_out_prep_mult                    0.1
% 1.09/1.01  --splitting_mode                        input
% 1.09/1.01  --splitting_grd                         true
% 1.09/1.01  --splitting_cvd                         false
% 1.09/1.01  --splitting_cvd_svl                     false
% 1.09/1.01  --splitting_nvd                         32
% 1.09/1.01  --sub_typing                            true
% 1.09/1.01  --prep_gs_sim                           true
% 1.09/1.01  --prep_unflatten                        true
% 1.09/1.01  --prep_res_sim                          true
% 1.09/1.01  --prep_upred                            true
% 1.09/1.01  --prep_sem_filter                       exhaustive
% 1.09/1.01  --prep_sem_filter_out                   false
% 1.09/1.01  --pred_elim                             true
% 1.09/1.01  --res_sim_input                         true
% 1.09/1.01  --eq_ax_congr_red                       true
% 1.09/1.01  --pure_diseq_elim                       true
% 1.09/1.01  --brand_transform                       false
% 1.09/1.01  --non_eq_to_eq                          false
% 1.09/1.01  --prep_def_merge                        true
% 1.09/1.01  --prep_def_merge_prop_impl              false
% 1.09/1.01  --prep_def_merge_mbd                    true
% 1.09/1.01  --prep_def_merge_tr_red                 false
% 1.09/1.01  --prep_def_merge_tr_cl                  false
% 1.09/1.01  --smt_preprocessing                     true
% 1.09/1.01  --smt_ac_axioms                         fast
% 1.09/1.01  --preprocessed_out                      false
% 1.09/1.01  --preprocessed_stats                    false
% 1.09/1.01  
% 1.09/1.01  ------ Abstraction refinement Options
% 1.09/1.01  
% 1.09/1.01  --abstr_ref                             []
% 1.09/1.01  --abstr_ref_prep                        false
% 1.09/1.01  --abstr_ref_until_sat                   false
% 1.09/1.01  --abstr_ref_sig_restrict                funpre
% 1.09/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 1.09/1.01  --abstr_ref_under                       []
% 1.09/1.01  
% 1.09/1.01  ------ SAT Options
% 1.09/1.01  
% 1.09/1.01  --sat_mode                              false
% 1.09/1.01  --sat_fm_restart_options                ""
% 1.09/1.01  --sat_gr_def                            false
% 1.09/1.01  --sat_epr_types                         true
% 1.09/1.01  --sat_non_cyclic_types                  false
% 1.09/1.01  --sat_finite_models                     false
% 1.09/1.01  --sat_fm_lemmas                         false
% 1.09/1.01  --sat_fm_prep                           false
% 1.09/1.01  --sat_fm_uc_incr                        true
% 1.09/1.01  --sat_out_model                         small
% 1.09/1.01  --sat_out_clauses                       false
% 1.09/1.01  
% 1.09/1.01  ------ QBF Options
% 1.09/1.01  
% 1.09/1.01  --qbf_mode                              false
% 1.09/1.01  --qbf_elim_univ                         false
% 1.09/1.01  --qbf_dom_inst                          none
% 1.09/1.01  --qbf_dom_pre_inst                      false
% 1.09/1.01  --qbf_sk_in                             false
% 1.09/1.01  --qbf_pred_elim                         true
% 1.09/1.01  --qbf_split                             512
% 1.09/1.01  
% 1.09/1.01  ------ BMC1 Options
% 1.09/1.01  
% 1.09/1.01  --bmc1_incremental                      false
% 1.09/1.01  --bmc1_axioms                           reachable_all
% 1.09/1.01  --bmc1_min_bound                        0
% 1.09/1.01  --bmc1_max_bound                        -1
% 1.09/1.01  --bmc1_max_bound_default                -1
% 1.09/1.01  --bmc1_symbol_reachability              true
% 1.09/1.01  --bmc1_property_lemmas                  false
% 1.09/1.01  --bmc1_k_induction                      false
% 1.09/1.01  --bmc1_non_equiv_states                 false
% 1.09/1.01  --bmc1_deadlock                         false
% 1.09/1.01  --bmc1_ucm                              false
% 1.09/1.01  --bmc1_add_unsat_core                   none
% 1.09/1.01  --bmc1_unsat_core_children              false
% 1.09/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 1.09/1.01  --bmc1_out_stat                         full
% 1.09/1.01  --bmc1_ground_init                      false
% 1.09/1.01  --bmc1_pre_inst_next_state              false
% 1.09/1.01  --bmc1_pre_inst_state                   false
% 1.09/1.01  --bmc1_pre_inst_reach_state             false
% 1.09/1.01  --bmc1_out_unsat_core                   false
% 1.09/1.01  --bmc1_aig_witness_out                  false
% 1.09/1.01  --bmc1_verbose                          false
% 1.09/1.01  --bmc1_dump_clauses_tptp                false
% 1.09/1.01  --bmc1_dump_unsat_core_tptp             false
% 1.09/1.01  --bmc1_dump_file                        -
% 1.09/1.01  --bmc1_ucm_expand_uc_limit              128
% 1.09/1.01  --bmc1_ucm_n_expand_iterations          6
% 1.09/1.01  --bmc1_ucm_extend_mode                  1
% 1.09/1.01  --bmc1_ucm_init_mode                    2
% 1.09/1.01  --bmc1_ucm_cone_mode                    none
% 1.09/1.01  --bmc1_ucm_reduced_relation_type        0
% 1.09/1.01  --bmc1_ucm_relax_model                  4
% 1.09/1.01  --bmc1_ucm_full_tr_after_sat            true
% 1.09/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 1.09/1.01  --bmc1_ucm_layered_model                none
% 1.09/1.01  --bmc1_ucm_max_lemma_size               10
% 1.09/1.01  
% 1.09/1.01  ------ AIG Options
% 1.09/1.01  
% 1.09/1.01  --aig_mode                              false
% 1.09/1.01  
% 1.09/1.01  ------ Instantiation Options
% 1.09/1.01  
% 1.09/1.01  --instantiation_flag                    true
% 1.09/1.01  --inst_sos_flag                         false
% 1.09/1.01  --inst_sos_phase                        true
% 1.09/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.09/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.09/1.01  --inst_lit_sel_side                     num_symb
% 1.09/1.01  --inst_solver_per_active                1400
% 1.09/1.01  --inst_solver_calls_frac                1.
% 1.09/1.01  --inst_passive_queue_type               priority_queues
% 1.09/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.09/1.01  --inst_passive_queues_freq              [25;2]
% 1.09/1.01  --inst_dismatching                      true
% 1.09/1.01  --inst_eager_unprocessed_to_passive     true
% 1.09/1.01  --inst_prop_sim_given                   true
% 1.09/1.01  --inst_prop_sim_new                     false
% 1.09/1.01  --inst_subs_new                         false
% 1.09/1.02  --inst_eq_res_simp                      false
% 1.09/1.02  --inst_subs_given                       false
% 1.09/1.02  --inst_orphan_elimination               true
% 1.09/1.02  --inst_learning_loop_flag               true
% 1.09/1.02  --inst_learning_start                   3000
% 1.09/1.02  --inst_learning_factor                  2
% 1.09/1.02  --inst_start_prop_sim_after_learn       3
% 1.09/1.02  --inst_sel_renew                        solver
% 1.09/1.02  --inst_lit_activity_flag                true
% 1.09/1.02  --inst_restr_to_given                   false
% 1.09/1.02  --inst_activity_threshold               500
% 1.09/1.02  --inst_out_proof                        true
% 1.09/1.02  
% 1.09/1.02  ------ Resolution Options
% 1.09/1.02  
% 1.09/1.02  --resolution_flag                       true
% 1.09/1.02  --res_lit_sel                           adaptive
% 1.09/1.02  --res_lit_sel_side                      none
% 1.09/1.02  --res_ordering                          kbo
% 1.09/1.02  --res_to_prop_solver                    active
% 1.09/1.02  --res_prop_simpl_new                    false
% 1.09/1.02  --res_prop_simpl_given                  true
% 1.09/1.02  --res_passive_queue_type                priority_queues
% 1.09/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.09/1.02  --res_passive_queues_freq               [15;5]
% 1.09/1.02  --res_forward_subs                      full
% 1.09/1.02  --res_backward_subs                     full
% 1.09/1.02  --res_forward_subs_resolution           true
% 1.09/1.02  --res_backward_subs_resolution          true
% 1.09/1.02  --res_orphan_elimination                true
% 1.09/1.02  --res_time_limit                        2.
% 1.09/1.02  --res_out_proof                         true
% 1.09/1.02  
% 1.09/1.02  ------ Superposition Options
% 1.09/1.02  
% 1.09/1.02  --superposition_flag                    true
% 1.09/1.02  --sup_passive_queue_type                priority_queues
% 1.09/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.09/1.02  --sup_passive_queues_freq               [8;1;4]
% 1.09/1.02  --demod_completeness_check              fast
% 1.09/1.02  --demod_use_ground                      true
% 1.09/1.02  --sup_to_prop_solver                    passive
% 1.09/1.02  --sup_prop_simpl_new                    true
% 1.09/1.02  --sup_prop_simpl_given                  true
% 1.09/1.02  --sup_fun_splitting                     false
% 1.09/1.02  --sup_smt_interval                      50000
% 1.09/1.02  
% 1.09/1.02  ------ Superposition Simplification Setup
% 1.09/1.02  
% 1.09/1.02  --sup_indices_passive                   []
% 1.09/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.09/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.09/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.09/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 1.09/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.09/1.02  --sup_full_bw                           [BwDemod]
% 1.09/1.02  --sup_immed_triv                        [TrivRules]
% 1.09/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.09/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.09/1.02  --sup_immed_bw_main                     []
% 1.09/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.09/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 1.09/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.09/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.09/1.02  
% 1.09/1.02  ------ Combination Options
% 1.09/1.02  
% 1.09/1.02  --comb_res_mult                         3
% 1.09/1.02  --comb_sup_mult                         2
% 1.09/1.02  --comb_inst_mult                        10
% 1.09/1.02  
% 1.09/1.02  ------ Debug Options
% 1.09/1.02  
% 1.09/1.02  --dbg_backtrace                         false
% 1.09/1.02  --dbg_dump_prop_clauses                 false
% 1.09/1.02  --dbg_dump_prop_clauses_file            -
% 1.09/1.02  --dbg_out_stat                          false
% 1.09/1.02  ------ Parsing...
% 1.09/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.09/1.02  
% 1.09/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 1.09/1.02  
% 1.09/1.02  ------ Preprocessing... gs_s  sp: 3 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.09/1.02  
% 1.09/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.09/1.02  ------ Proving...
% 1.09/1.02  ------ Problem Properties 
% 1.09/1.02  
% 1.09/1.02  
% 1.09/1.02  clauses                                 19
% 1.09/1.02  conjectures                             2
% 1.09/1.02  EPR                                     4
% 1.09/1.02  Horn                                    15
% 1.09/1.02  unary                                   8
% 1.09/1.02  binary                                  2
% 1.09/1.02  lits                                    43
% 1.09/1.02  lits eq                                 8
% 1.09/1.02  fd_pure                                 0
% 1.09/1.02  fd_pseudo                               0
% 1.09/1.02  fd_cond                                 5
% 1.09/1.02  fd_pseudo_cond                          0
% 1.09/1.02  AC symbols                              0
% 1.09/1.02  
% 1.09/1.02  ------ Schedule dynamic 5 is on 
% 1.09/1.02  
% 1.09/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.09/1.02  
% 1.09/1.02  
% 1.09/1.02  ------ 
% 1.09/1.02  Current options:
% 1.09/1.02  ------ 
% 1.09/1.02  
% 1.09/1.02  ------ Input Options
% 1.09/1.02  
% 1.09/1.02  --out_options                           all
% 1.09/1.02  --tptp_safe_out                         true
% 1.09/1.02  --problem_path                          ""
% 1.09/1.02  --include_path                          ""
% 1.09/1.02  --clausifier                            res/vclausify_rel
% 1.09/1.02  --clausifier_options                    --mode clausify
% 1.09/1.02  --stdin                                 false
% 1.09/1.02  --stats_out                             all
% 1.09/1.02  
% 1.09/1.02  ------ General Options
% 1.09/1.02  
% 1.09/1.02  --fof                                   false
% 1.09/1.02  --time_out_real                         305.
% 1.09/1.02  --time_out_virtual                      -1.
% 1.09/1.02  --symbol_type_check                     false
% 1.09/1.02  --clausify_out                          false
% 1.09/1.02  --sig_cnt_out                           false
% 1.09/1.02  --trig_cnt_out                          false
% 1.09/1.02  --trig_cnt_out_tolerance                1.
% 1.09/1.02  --trig_cnt_out_sk_spl                   false
% 1.09/1.02  --abstr_cl_out                          false
% 1.09/1.02  
% 1.09/1.02  ------ Global Options
% 1.09/1.02  
% 1.09/1.02  --schedule                              default
% 1.09/1.02  --add_important_lit                     false
% 1.09/1.02  --prop_solver_per_cl                    1000
% 1.09/1.02  --min_unsat_core                        false
% 1.09/1.02  --soft_assumptions                      false
% 1.09/1.02  --soft_lemma_size                       3
% 1.09/1.02  --prop_impl_unit_size                   0
% 1.09/1.02  --prop_impl_unit                        []
% 1.09/1.02  --share_sel_clauses                     true
% 1.09/1.02  --reset_solvers                         false
% 1.09/1.02  --bc_imp_inh                            [conj_cone]
% 1.09/1.02  --conj_cone_tolerance                   3.
% 1.09/1.02  --extra_neg_conj                        none
% 1.09/1.02  --large_theory_mode                     true
% 1.09/1.02  --prolific_symb_bound                   200
% 1.09/1.02  --lt_threshold                          2000
% 1.09/1.02  --clause_weak_htbl                      true
% 1.09/1.02  --gc_record_bc_elim                     false
% 1.09/1.02  
% 1.09/1.02  ------ Preprocessing Options
% 1.09/1.02  
% 1.09/1.02  --preprocessing_flag                    true
% 1.09/1.02  --time_out_prep_mult                    0.1
% 1.09/1.02  --splitting_mode                        input
% 1.09/1.02  --splitting_grd                         true
% 1.09/1.02  --splitting_cvd                         false
% 1.09/1.02  --splitting_cvd_svl                     false
% 1.09/1.02  --splitting_nvd                         32
% 1.09/1.02  --sub_typing                            true
% 1.09/1.02  --prep_gs_sim                           true
% 1.09/1.02  --prep_unflatten                        true
% 1.09/1.02  --prep_res_sim                          true
% 1.09/1.02  --prep_upred                            true
% 1.09/1.02  --prep_sem_filter                       exhaustive
% 1.09/1.02  --prep_sem_filter_out                   false
% 1.09/1.02  --pred_elim                             true
% 1.09/1.02  --res_sim_input                         true
% 1.09/1.02  --eq_ax_congr_red                       true
% 1.09/1.02  --pure_diseq_elim                       true
% 1.09/1.02  --brand_transform                       false
% 1.09/1.02  --non_eq_to_eq                          false
% 1.09/1.02  --prep_def_merge                        true
% 1.09/1.02  --prep_def_merge_prop_impl              false
% 1.09/1.02  --prep_def_merge_mbd                    true
% 1.09/1.02  --prep_def_merge_tr_red                 false
% 1.09/1.02  --prep_def_merge_tr_cl                  false
% 1.09/1.02  --smt_preprocessing                     true
% 1.09/1.02  --smt_ac_axioms                         fast
% 1.09/1.02  --preprocessed_out                      false
% 1.09/1.02  --preprocessed_stats                    false
% 1.09/1.02  
% 1.09/1.02  ------ Abstraction refinement Options
% 1.09/1.02  
% 1.09/1.02  --abstr_ref                             []
% 1.09/1.02  --abstr_ref_prep                        false
% 1.09/1.02  --abstr_ref_until_sat                   false
% 1.09/1.02  --abstr_ref_sig_restrict                funpre
% 1.09/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 1.09/1.02  --abstr_ref_under                       []
% 1.09/1.02  
% 1.09/1.02  ------ SAT Options
% 1.09/1.02  
% 1.09/1.02  --sat_mode                              false
% 1.09/1.02  --sat_fm_restart_options                ""
% 1.09/1.02  --sat_gr_def                            false
% 1.09/1.02  --sat_epr_types                         true
% 1.09/1.02  --sat_non_cyclic_types                  false
% 1.09/1.02  --sat_finite_models                     false
% 1.09/1.02  --sat_fm_lemmas                         false
% 1.09/1.02  --sat_fm_prep                           false
% 1.09/1.02  --sat_fm_uc_incr                        true
% 1.09/1.02  --sat_out_model                         small
% 1.09/1.02  --sat_out_clauses                       false
% 1.09/1.02  
% 1.09/1.02  ------ QBF Options
% 1.09/1.02  
% 1.09/1.02  --qbf_mode                              false
% 1.09/1.02  --qbf_elim_univ                         false
% 1.09/1.02  --qbf_dom_inst                          none
% 1.09/1.02  --qbf_dom_pre_inst                      false
% 1.09/1.02  --qbf_sk_in                             false
% 1.09/1.02  --qbf_pred_elim                         true
% 1.09/1.02  --qbf_split                             512
% 1.09/1.02  
% 1.09/1.02  ------ BMC1 Options
% 1.09/1.02  
% 1.09/1.02  --bmc1_incremental                      false
% 1.09/1.02  --bmc1_axioms                           reachable_all
% 1.09/1.02  --bmc1_min_bound                        0
% 1.09/1.02  --bmc1_max_bound                        -1
% 1.09/1.02  --bmc1_max_bound_default                -1
% 1.09/1.02  --bmc1_symbol_reachability              true
% 1.09/1.02  --bmc1_property_lemmas                  false
% 1.09/1.02  --bmc1_k_induction                      false
% 1.09/1.02  --bmc1_non_equiv_states                 false
% 1.09/1.02  --bmc1_deadlock                         false
% 1.09/1.02  --bmc1_ucm                              false
% 1.09/1.02  --bmc1_add_unsat_core                   none
% 1.09/1.02  --bmc1_unsat_core_children              false
% 1.09/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 1.09/1.02  --bmc1_out_stat                         full
% 1.09/1.02  --bmc1_ground_init                      false
% 1.09/1.02  --bmc1_pre_inst_next_state              false
% 1.09/1.02  --bmc1_pre_inst_state                   false
% 1.09/1.02  --bmc1_pre_inst_reach_state             false
% 1.09/1.02  --bmc1_out_unsat_core                   false
% 1.09/1.02  --bmc1_aig_witness_out                  false
% 1.09/1.02  --bmc1_verbose                          false
% 1.09/1.02  --bmc1_dump_clauses_tptp                false
% 1.09/1.02  --bmc1_dump_unsat_core_tptp             false
% 1.09/1.02  --bmc1_dump_file                        -
% 1.09/1.02  --bmc1_ucm_expand_uc_limit              128
% 1.09/1.02  --bmc1_ucm_n_expand_iterations          6
% 1.09/1.02  --bmc1_ucm_extend_mode                  1
% 1.09/1.02  --bmc1_ucm_init_mode                    2
% 1.09/1.02  --bmc1_ucm_cone_mode                    none
% 1.09/1.02  --bmc1_ucm_reduced_relation_type        0
% 1.09/1.02  --bmc1_ucm_relax_model                  4
% 1.09/1.02  --bmc1_ucm_full_tr_after_sat            true
% 1.09/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 1.09/1.02  --bmc1_ucm_layered_model                none
% 1.09/1.02  --bmc1_ucm_max_lemma_size               10
% 1.09/1.02  
% 1.09/1.02  ------ AIG Options
% 1.09/1.02  
% 1.09/1.02  --aig_mode                              false
% 1.09/1.02  
% 1.09/1.02  ------ Instantiation Options
% 1.09/1.02  
% 1.09/1.02  --instantiation_flag                    true
% 1.09/1.02  --inst_sos_flag                         false
% 1.09/1.02  --inst_sos_phase                        true
% 1.09/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.09/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.09/1.02  --inst_lit_sel_side                     none
% 1.09/1.02  --inst_solver_per_active                1400
% 1.09/1.02  --inst_solver_calls_frac                1.
% 1.09/1.02  --inst_passive_queue_type               priority_queues
% 1.09/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.09/1.02  --inst_passive_queues_freq              [25;2]
% 1.09/1.02  --inst_dismatching                      true
% 1.09/1.02  --inst_eager_unprocessed_to_passive     true
% 1.09/1.02  --inst_prop_sim_given                   true
% 1.09/1.02  --inst_prop_sim_new                     false
% 1.09/1.02  --inst_subs_new                         false
% 1.09/1.02  --inst_eq_res_simp                      false
% 1.09/1.02  --inst_subs_given                       false
% 1.09/1.02  --inst_orphan_elimination               true
% 1.09/1.02  --inst_learning_loop_flag               true
% 1.09/1.02  --inst_learning_start                   3000
% 1.09/1.02  --inst_learning_factor                  2
% 1.09/1.02  --inst_start_prop_sim_after_learn       3
% 1.09/1.02  --inst_sel_renew                        solver
% 1.09/1.02  --inst_lit_activity_flag                true
% 1.09/1.02  --inst_restr_to_given                   false
% 1.09/1.02  --inst_activity_threshold               500
% 1.09/1.02  --inst_out_proof                        true
% 1.09/1.02  
% 1.09/1.02  ------ Resolution Options
% 1.09/1.02  
% 1.09/1.02  --resolution_flag                       false
% 1.09/1.02  --res_lit_sel                           adaptive
% 1.09/1.02  --res_lit_sel_side                      none
% 1.09/1.02  --res_ordering                          kbo
% 1.09/1.02  --res_to_prop_solver                    active
% 1.09/1.02  --res_prop_simpl_new                    false
% 1.09/1.02  --res_prop_simpl_given                  true
% 1.09/1.02  --res_passive_queue_type                priority_queues
% 1.09/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.09/1.02  --res_passive_queues_freq               [15;5]
% 1.09/1.02  --res_forward_subs                      full
% 1.09/1.02  --res_backward_subs                     full
% 1.09/1.02  --res_forward_subs_resolution           true
% 1.09/1.02  --res_backward_subs_resolution          true
% 1.09/1.02  --res_orphan_elimination                true
% 1.09/1.02  --res_time_limit                        2.
% 1.09/1.02  --res_out_proof                         true
% 1.09/1.02  
% 1.09/1.02  ------ Superposition Options
% 1.09/1.02  
% 1.09/1.02  --superposition_flag                    true
% 1.09/1.02  --sup_passive_queue_type                priority_queues
% 1.09/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.09/1.02  --sup_passive_queues_freq               [8;1;4]
% 1.09/1.02  --demod_completeness_check              fast
% 1.09/1.02  --demod_use_ground                      true
% 1.09/1.02  --sup_to_prop_solver                    passive
% 1.09/1.02  --sup_prop_simpl_new                    true
% 1.09/1.02  --sup_prop_simpl_given                  true
% 1.09/1.02  --sup_fun_splitting                     false
% 1.09/1.02  --sup_smt_interval                      50000
% 1.09/1.02  
% 1.09/1.02  ------ Superposition Simplification Setup
% 1.09/1.02  
% 1.09/1.02  --sup_indices_passive                   []
% 1.09/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.09/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.09/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.09/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 1.09/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.09/1.02  --sup_full_bw                           [BwDemod]
% 1.09/1.02  --sup_immed_triv                        [TrivRules]
% 1.09/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.09/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.09/1.02  --sup_immed_bw_main                     []
% 1.09/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.09/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 1.09/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.09/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.09/1.02  
% 1.09/1.02  ------ Combination Options
% 1.09/1.02  
% 1.09/1.02  --comb_res_mult                         3
% 1.09/1.02  --comb_sup_mult                         2
% 1.09/1.02  --comb_inst_mult                        10
% 1.09/1.02  
% 1.09/1.02  ------ Debug Options
% 1.09/1.02  
% 1.09/1.02  --dbg_backtrace                         false
% 1.09/1.02  --dbg_dump_prop_clauses                 false
% 1.09/1.02  --dbg_dump_prop_clauses_file            -
% 1.09/1.02  --dbg_out_stat                          false
% 1.09/1.02  
% 1.09/1.02  
% 1.09/1.02  
% 1.09/1.02  
% 1.09/1.02  ------ Proving...
% 1.09/1.02  
% 1.09/1.02  
% 1.09/1.02  % SZS status Theorem for theBenchmark.p
% 1.09/1.02  
% 1.09/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 1.09/1.02  
% 1.09/1.02  fof(f5,axiom,(
% 1.09/1.02    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 1.09/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.09/1.02  
% 1.09/1.02  fof(f31,plain,(
% 1.09/1.02    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK0(X0),X0))),
% 1.09/1.02    introduced(choice_axiom,[])).
% 1.09/1.02  
% 1.09/1.02  fof(f32,plain,(
% 1.09/1.02    ! [X0] : m1_subset_1(sK0(X0),X0)),
% 1.09/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f5,f31])).
% 1.09/1.02  
% 1.09/1.02  fof(f45,plain,(
% 1.09/1.02    ( ! [X0] : (m1_subset_1(sK0(X0),X0)) )),
% 1.09/1.02    inference(cnf_transformation,[],[f32])).
% 1.09/1.02  
% 1.09/1.02  fof(f11,axiom,(
% 1.09/1.02    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 1.09/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.09/1.02  
% 1.09/1.02  fof(f23,plain,(
% 1.09/1.02    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.09/1.02    inference(ennf_transformation,[],[f11])).
% 1.09/1.02  
% 1.09/1.02  fof(f24,plain,(
% 1.09/1.02    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.09/1.02    inference(flattening,[],[f23])).
% 1.09/1.02  
% 1.09/1.02  fof(f50,plain,(
% 1.09/1.02    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.09/1.02    inference(cnf_transformation,[],[f24])).
% 1.09/1.02  
% 1.09/1.02  fof(f8,axiom,(
% 1.09/1.02    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.09/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.09/1.02  
% 1.09/1.02  fof(f18,plain,(
% 1.09/1.02    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.09/1.02    inference(ennf_transformation,[],[f8])).
% 1.09/1.02  
% 1.09/1.02  fof(f47,plain,(
% 1.09/1.02    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.09/1.02    inference(cnf_transformation,[],[f18])).
% 1.09/1.02  
% 1.09/1.02  fof(f9,axiom,(
% 1.09/1.02    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.09/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.09/1.02  
% 1.09/1.02  fof(f19,plain,(
% 1.09/1.02    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.09/1.02    inference(ennf_transformation,[],[f9])).
% 1.09/1.02  
% 1.09/1.02  fof(f20,plain,(
% 1.09/1.02    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.09/1.02    inference(flattening,[],[f19])).
% 1.09/1.02  
% 1.09/1.02  fof(f48,plain,(
% 1.09/1.02    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.09/1.02    inference(cnf_transformation,[],[f20])).
% 1.09/1.02  
% 1.09/1.02  fof(f14,conjecture,(
% 1.09/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => ~v3_tex_2(X1,X0)))),
% 1.09/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.09/1.02  
% 1.09/1.02  fof(f15,negated_conjecture,(
% 1.09/1.02    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => ~v3_tex_2(X1,X0)))),
% 1.09/1.02    inference(negated_conjecture,[],[f14])).
% 1.09/1.02  
% 1.09/1.02  fof(f29,plain,(
% 1.09/1.02    ? [X0] : (? [X1] : (v3_tex_2(X1,X0) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.09/1.02    inference(ennf_transformation,[],[f15])).
% 1.09/1.02  
% 1.09/1.02  fof(f30,plain,(
% 1.09/1.02    ? [X0] : (? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.09/1.02    inference(flattening,[],[f29])).
% 1.09/1.02  
% 1.09/1.02  fof(f39,plain,(
% 1.09/1.02    ( ! [X0] : (? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => (v3_tex_2(sK3,X0) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(sK3))) )),
% 1.09/1.02    introduced(choice_axiom,[])).
% 1.09/1.02  
% 1.09/1.02  fof(f38,plain,(
% 1.09/1.02    ? [X0] : (? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (v3_tex_2(X1,sK2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) & v1_xboole_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 1.09/1.02    introduced(choice_axiom,[])).
% 1.09/1.02  
% 1.09/1.02  fof(f40,plain,(
% 1.09/1.02    (v3_tex_2(sK3,sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) & v1_xboole_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 1.09/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f30,f39,f38])).
% 1.09/1.02  
% 1.09/1.02  fof(f58,plain,(
% 1.09/1.02    ~v2_struct_0(sK2)),
% 1.09/1.02    inference(cnf_transformation,[],[f40])).
% 1.09/1.02  
% 1.09/1.02  fof(f60,plain,(
% 1.09/1.02    l1_pre_topc(sK2)),
% 1.09/1.02    inference(cnf_transformation,[],[f40])).
% 1.09/1.02  
% 1.09/1.02  fof(f10,axiom,(
% 1.09/1.02    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.09/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.09/1.02  
% 1.09/1.02  fof(f21,plain,(
% 1.09/1.02    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.09/1.02    inference(ennf_transformation,[],[f10])).
% 1.09/1.02  
% 1.09/1.02  fof(f22,plain,(
% 1.09/1.02    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.09/1.02    inference(flattening,[],[f21])).
% 1.09/1.02  
% 1.09/1.02  fof(f49,plain,(
% 1.09/1.02    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.09/1.02    inference(cnf_transformation,[],[f22])).
% 1.09/1.02  
% 1.09/1.02  fof(f62,plain,(
% 1.09/1.02    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.09/1.02    inference(cnf_transformation,[],[f40])).
% 1.09/1.02  
% 1.09/1.02  fof(f3,axiom,(
% 1.09/1.02    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.09/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.09/1.02  
% 1.09/1.02  fof(f43,plain,(
% 1.09/1.02    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.09/1.02    inference(cnf_transformation,[],[f3])).
% 1.09/1.02  
% 1.09/1.02  fof(f12,axiom,(
% 1.09/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 1.09/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.09/1.02  
% 1.09/1.02  fof(f25,plain,(
% 1.09/1.02    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.09/1.02    inference(ennf_transformation,[],[f12])).
% 1.09/1.02  
% 1.09/1.02  fof(f26,plain,(
% 1.09/1.02    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.09/1.02    inference(flattening,[],[f25])).
% 1.09/1.02  
% 1.09/1.02  fof(f33,plain,(
% 1.09/1.02    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.09/1.02    inference(nnf_transformation,[],[f26])).
% 1.09/1.02  
% 1.09/1.02  fof(f34,plain,(
% 1.09/1.02    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.09/1.02    inference(flattening,[],[f33])).
% 1.09/1.02  
% 1.09/1.02  fof(f35,plain,(
% 1.09/1.02    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.09/1.02    inference(rectify,[],[f34])).
% 1.09/1.02  
% 1.09/1.02  fof(f36,plain,(
% 1.09/1.02    ! [X1,X0] : (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK1(X0,X1) != X1 & r1_tarski(X1,sK1(X0,X1)) & v2_tex_2(sK1(X0,X1),X0) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.09/1.02    introduced(choice_axiom,[])).
% 1.09/1.02  
% 1.09/1.02  fof(f37,plain,(
% 1.09/1.02    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (sK1(X0,X1) != X1 & r1_tarski(X1,sK1(X0,X1)) & v2_tex_2(sK1(X0,X1),X0) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.09/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f36])).
% 1.09/1.02  
% 1.09/1.02  fof(f52,plain,(
% 1.09/1.02    ( ! [X0,X3,X1] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.09/1.02    inference(cnf_transformation,[],[f37])).
% 1.09/1.02  
% 1.09/1.02  fof(f6,axiom,(
% 1.09/1.02    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.09/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.09/1.02  
% 1.09/1.02  fof(f46,plain,(
% 1.09/1.02    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.09/1.02    inference(cnf_transformation,[],[f6])).
% 1.09/1.02  
% 1.09/1.02  fof(f53,plain,(
% 1.09/1.02    ( ! [X0,X1] : (v3_tex_2(X1,X0) | m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.09/1.02    inference(cnf_transformation,[],[f37])).
% 1.09/1.02  
% 1.09/1.02  fof(f2,axiom,(
% 1.09/1.02    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.09/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.09/1.02  
% 1.09/1.02  fof(f17,plain,(
% 1.09/1.02    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.09/1.02    inference(ennf_transformation,[],[f2])).
% 1.09/1.02  
% 1.09/1.02  fof(f42,plain,(
% 1.09/1.02    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 1.09/1.02    inference(cnf_transformation,[],[f17])).
% 1.09/1.02  
% 1.09/1.02  fof(f61,plain,(
% 1.09/1.02    v1_xboole_0(sK3)),
% 1.09/1.02    inference(cnf_transformation,[],[f40])).
% 1.09/1.02  
% 1.09/1.02  fof(f63,plain,(
% 1.09/1.02    v3_tex_2(sK3,sK2)),
% 1.09/1.02    inference(cnf_transformation,[],[f40])).
% 1.09/1.02  
% 1.09/1.02  fof(f13,axiom,(
% 1.09/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 1.09/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.09/1.02  
% 1.09/1.02  fof(f27,plain,(
% 1.09/1.02    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.09/1.02    inference(ennf_transformation,[],[f13])).
% 1.09/1.02  
% 1.09/1.02  fof(f28,plain,(
% 1.09/1.02    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.09/1.02    inference(flattening,[],[f27])).
% 1.09/1.02  
% 1.09/1.02  fof(f57,plain,(
% 1.09/1.02    ( ! [X0,X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.09/1.02    inference(cnf_transformation,[],[f28])).
% 1.09/1.02  
% 1.09/1.02  fof(f59,plain,(
% 1.09/1.02    v2_pre_topc(sK2)),
% 1.09/1.02    inference(cnf_transformation,[],[f40])).
% 1.09/1.02  
% 1.09/1.02  fof(f4,axiom,(
% 1.09/1.02    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 1.09/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.09/1.02  
% 1.09/1.02  fof(f44,plain,(
% 1.09/1.02    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 1.09/1.02    inference(cnf_transformation,[],[f4])).
% 1.09/1.02  
% 1.09/1.02  fof(f1,axiom,(
% 1.09/1.02    v1_xboole_0(k1_xboole_0)),
% 1.09/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.09/1.02  
% 1.09/1.02  fof(f41,plain,(
% 1.09/1.02    v1_xboole_0(k1_xboole_0)),
% 1.09/1.02    inference(cnf_transformation,[],[f1])).
% 1.09/1.02  
% 1.09/1.02  cnf(c_4,plain,
% 1.09/1.02      ( m1_subset_1(sK0(X0),X0) ),
% 1.09/1.02      inference(cnf_transformation,[],[f45]) ).
% 1.09/1.02  
% 1.09/1.02  cnf(c_1360,plain,
% 1.09/1.02      ( m1_subset_1(sK0(X0),X0) = iProver_top ),
% 1.09/1.02      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 1.09/1.02  
% 1.09/1.02  cnf(c_9,plain,
% 1.09/1.02      ( ~ m1_subset_1(X0,X1)
% 1.09/1.02      | v1_xboole_0(X1)
% 1.09/1.02      | k6_domain_1(X1,X0) = k1_tarski(X0) ),
% 1.09/1.02      inference(cnf_transformation,[],[f50]) ).
% 1.09/1.02  
% 1.09/1.02  cnf(c_1357,plain,
% 1.09/1.02      ( k6_domain_1(X0,X1) = k1_tarski(X1)
% 1.09/1.02      | m1_subset_1(X1,X0) != iProver_top
% 1.09/1.02      | v1_xboole_0(X0) = iProver_top ),
% 1.09/1.02      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 1.09/1.02  
% 1.09/1.02  cnf(c_2059,plain,
% 1.09/1.02      ( k6_domain_1(X0,sK0(X0)) = k1_tarski(sK0(X0))
% 1.09/1.02      | v1_xboole_0(X0) = iProver_top ),
% 1.09/1.02      inference(superposition,[status(thm)],[c_1360,c_1357]) ).
% 1.09/1.02  
% 1.09/1.02  cnf(c_6,plain,
% 1.09/1.02      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 1.09/1.02      inference(cnf_transformation,[],[f47]) ).
% 1.09/1.02  
% 1.09/1.02  cnf(c_7,plain,
% 1.09/1.02      ( v2_struct_0(X0)
% 1.09/1.02      | ~ l1_struct_0(X0)
% 1.09/1.02      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 1.09/1.02      inference(cnf_transformation,[],[f48]) ).
% 1.09/1.02  
% 1.09/1.02  cnf(c_255,plain,
% 1.09/1.02      ( v2_struct_0(X0)
% 1.09/1.02      | ~ l1_pre_topc(X0)
% 1.09/1.02      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 1.09/1.02      inference(resolution,[status(thm)],[c_6,c_7]) ).
% 1.09/1.02  
% 1.09/1.02  cnf(c_22,negated_conjecture,
% 1.09/1.02      ( ~ v2_struct_0(sK2) ),
% 1.09/1.02      inference(cnf_transformation,[],[f58]) ).
% 1.09/1.02  
% 1.09/1.02  cnf(c_294,plain,
% 1.09/1.02      ( ~ l1_pre_topc(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK2 != X0 ),
% 1.09/1.02      inference(resolution_lifted,[status(thm)],[c_255,c_22]) ).
% 1.09/1.02  
% 1.09/1.02  cnf(c_295,plain,
% 1.09/1.02      ( ~ l1_pre_topc(sK2) | ~ v1_xboole_0(u1_struct_0(sK2)) ),
% 1.09/1.02      inference(unflattening,[status(thm)],[c_294]) ).
% 1.09/1.02  
% 1.09/1.02  cnf(c_20,negated_conjecture,
% 1.09/1.02      ( l1_pre_topc(sK2) ),
% 1.09/1.02      inference(cnf_transformation,[],[f60]) ).
% 1.09/1.02  
% 1.09/1.02  cnf(c_57,plain,
% 1.09/1.02      ( v2_struct_0(sK2)
% 1.09/1.02      | ~ l1_struct_0(sK2)
% 1.09/1.02      | ~ v1_xboole_0(u1_struct_0(sK2)) ),
% 1.09/1.02      inference(instantiation,[status(thm)],[c_7]) ).
% 1.09/1.02  
% 1.09/1.02  cnf(c_60,plain,
% 1.09/1.02      ( ~ l1_pre_topc(sK2) | l1_struct_0(sK2) ),
% 1.09/1.02      inference(instantiation,[status(thm)],[c_6]) ).
% 1.09/1.02  
% 1.09/1.02  cnf(c_297,plain,
% 1.09/1.02      ( ~ v1_xboole_0(u1_struct_0(sK2)) ),
% 1.09/1.02      inference(global_propositional_subsumption,
% 1.09/1.02                [status(thm)],
% 1.09/1.02                [c_295,c_22,c_20,c_57,c_60]) ).
% 1.09/1.02  
% 1.09/1.02  cnf(c_1353,plain,
% 1.09/1.02      ( v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 1.09/1.02      inference(predicate_to_equality,[status(thm)],[c_297]) ).
% 1.09/1.02  
% 1.09/1.02  cnf(c_2149,plain,
% 1.09/1.02      ( k6_domain_1(u1_struct_0(sK2),sK0(u1_struct_0(sK2))) = k1_tarski(sK0(u1_struct_0(sK2))) ),
% 1.09/1.02      inference(superposition,[status(thm)],[c_2059,c_1353]) ).
% 1.09/1.02  
% 1.09/1.02  cnf(c_8,plain,
% 1.09/1.02      ( ~ m1_subset_1(X0,X1)
% 1.09/1.02      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
% 1.09/1.02      | v1_xboole_0(X1) ),
% 1.09/1.02      inference(cnf_transformation,[],[f49]) ).
% 1.09/1.02  
% 1.09/1.02  cnf(c_1358,plain,
% 1.09/1.02      ( m1_subset_1(X0,X1) != iProver_top
% 1.09/1.02      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top
% 1.09/1.02      | v1_xboole_0(X1) = iProver_top ),
% 1.09/1.02      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 1.09/1.02  
% 1.09/1.02  cnf(c_2245,plain,
% 1.09/1.02      ( m1_subset_1(sK0(u1_struct_0(sK2)),u1_struct_0(sK2)) != iProver_top
% 1.09/1.02      | m1_subset_1(k1_tarski(sK0(u1_struct_0(sK2))),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 1.09/1.02      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 1.09/1.02      inference(superposition,[status(thm)],[c_2149,c_1358]) ).
% 1.09/1.02  
% 1.09/1.02  cnf(c_23,plain,
% 1.09/1.02      ( v2_struct_0(sK2) != iProver_top ),
% 1.09/1.02      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 1.09/1.02  
% 1.09/1.02  cnf(c_25,plain,
% 1.09/1.02      ( l1_pre_topc(sK2) = iProver_top ),
% 1.09/1.02      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 1.09/1.02  
% 1.09/1.02  cnf(c_56,plain,
% 1.09/1.02      ( v2_struct_0(X0) = iProver_top
% 1.09/1.02      | l1_struct_0(X0) != iProver_top
% 1.09/1.02      | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
% 1.09/1.02      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 1.09/1.02  
% 1.09/1.02  cnf(c_58,plain,
% 1.09/1.02      ( v2_struct_0(sK2) = iProver_top
% 1.09/1.02      | l1_struct_0(sK2) != iProver_top
% 1.09/1.02      | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 1.09/1.02      inference(instantiation,[status(thm)],[c_56]) ).
% 1.09/1.02  
% 1.09/1.02  cnf(c_59,plain,
% 1.09/1.02      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 1.09/1.02      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 1.09/1.02  
% 1.09/1.02  cnf(c_61,plain,
% 1.09/1.02      ( l1_pre_topc(sK2) != iProver_top
% 1.09/1.02      | l1_struct_0(sK2) = iProver_top ),
% 1.09/1.02      inference(instantiation,[status(thm)],[c_59]) ).
% 1.09/1.02  
% 1.09/1.02  cnf(c_1481,plain,
% 1.09/1.02      ( m1_subset_1(sK0(u1_struct_0(sK2)),u1_struct_0(sK2)) ),
% 1.09/1.02      inference(instantiation,[status(thm)],[c_4]) ).
% 1.09/1.02  
% 1.09/1.02  cnf(c_1483,plain,
% 1.09/1.02      ( m1_subset_1(sK0(u1_struct_0(sK2)),u1_struct_0(sK2)) = iProver_top ),
% 1.09/1.02      inference(predicate_to_equality,[status(thm)],[c_1481]) ).
% 1.09/1.02  
% 1.09/1.02  cnf(c_2326,plain,
% 1.09/1.02      ( m1_subset_1(k1_tarski(sK0(u1_struct_0(sK2))),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 1.09/1.02      inference(global_propositional_subsumption,
% 1.09/1.02                [status(thm)],
% 1.09/1.02                [c_2245,c_23,c_25,c_58,c_61,c_1483]) ).
% 1.09/1.02  
% 1.09/1.02  cnf(c_18,negated_conjecture,
% 1.09/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 1.09/1.02      inference(cnf_transformation,[],[f62]) ).
% 1.09/1.02  
% 1.09/1.02  cnf(c_1356,plain,
% 1.09/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 1.09/1.02      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 1.09/1.02  
% 1.09/1.02  cnf(c_2,plain,
% 1.09/1.02      ( r1_tarski(k1_xboole_0,X0) ),
% 1.09/1.02      inference(cnf_transformation,[],[f43]) ).
% 1.09/1.02  
% 1.09/1.02  cnf(c_14,plain,
% 1.09/1.02      ( ~ v2_tex_2(X0,X1)
% 1.09/1.02      | ~ v3_tex_2(X2,X1)
% 1.09/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.09/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.09/1.02      | ~ r1_tarski(X2,X0)
% 1.09/1.02      | ~ l1_pre_topc(X1)
% 1.09/1.02      | X0 = X2 ),
% 1.09/1.02      inference(cnf_transformation,[],[f52]) ).
% 1.09/1.02  
% 1.09/1.02  cnf(c_519,plain,
% 1.09/1.02      ( ~ v2_tex_2(X0,X1)
% 1.09/1.02      | ~ v3_tex_2(X2,X1)
% 1.09/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.09/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.09/1.02      | ~ r1_tarski(X2,X0)
% 1.09/1.02      | X2 = X0
% 1.09/1.02      | sK2 != X1 ),
% 1.09/1.02      inference(resolution_lifted,[status(thm)],[c_14,c_20]) ).
% 1.09/1.02  
% 1.09/1.02  cnf(c_520,plain,
% 1.09/1.02      ( ~ v2_tex_2(X0,sK2)
% 1.09/1.02      | ~ v3_tex_2(X1,sK2)
% 1.09/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.09/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.09/1.02      | ~ r1_tarski(X1,X0)
% 1.09/1.02      | X1 = X0 ),
% 1.09/1.02      inference(unflattening,[status(thm)],[c_519]) ).
% 1.09/1.02  
% 1.09/1.02  cnf(c_646,plain,
% 1.09/1.02      ( ~ v2_tex_2(X0,sK2)
% 1.09/1.02      | ~ v3_tex_2(X1,sK2)
% 1.09/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.09/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.09/1.02      | X0 != X2
% 1.09/1.02      | X0 = X1
% 1.09/1.02      | k1_xboole_0 != X1 ),
% 1.09/1.02      inference(resolution_lifted,[status(thm)],[c_2,c_520]) ).
% 1.09/1.02  
% 1.09/1.02  cnf(c_647,plain,
% 1.09/1.02      ( ~ v2_tex_2(X0,sK2)
% 1.09/1.02      | ~ v3_tex_2(k1_xboole_0,sK2)
% 1.09/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.09/1.02      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.09/1.02      | X0 = k1_xboole_0 ),
% 1.09/1.02      inference(unflattening,[status(thm)],[c_646]) ).
% 1.09/1.02  
% 1.09/1.02  cnf(c_5,plain,
% 1.09/1.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 1.09/1.02      inference(cnf_transformation,[],[f46]) ).
% 1.09/1.02  
% 1.09/1.02  cnf(c_661,plain,
% 1.09/1.02      ( ~ v2_tex_2(X0,sK2)
% 1.09/1.02      | ~ v3_tex_2(k1_xboole_0,sK2)
% 1.09/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.09/1.02      | X0 = k1_xboole_0 ),
% 1.09/1.02      inference(forward_subsumption_resolution,[status(thm)],[c_647,c_5]) ).
% 1.09/1.02  
% 1.09/1.02  cnf(c_13,plain,
% 1.09/1.02      ( ~ v2_tex_2(X0,X1)
% 1.09/1.02      | v3_tex_2(X0,X1)
% 1.09/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.09/1.02      | m1_subset_1(sK1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.09/1.02      | ~ l1_pre_topc(X1) ),
% 1.09/1.02      inference(cnf_transformation,[],[f53]) ).
% 1.09/1.02  
% 1.09/1.02  cnf(c_543,plain,
% 1.09/1.02      ( ~ v2_tex_2(X0,X1)
% 1.09/1.02      | v3_tex_2(X0,X1)
% 1.09/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.09/1.02      | m1_subset_1(sK1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.09/1.02      | sK2 != X1 ),
% 1.09/1.02      inference(resolution_lifted,[status(thm)],[c_13,c_20]) ).
% 1.09/1.02  
% 1.09/1.02  cnf(c_544,plain,
% 1.09/1.02      ( ~ v2_tex_2(X0,sK2)
% 1.09/1.02      | v3_tex_2(X0,sK2)
% 1.09/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.09/1.02      | m1_subset_1(sK1(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 1.09/1.02      inference(unflattening,[status(thm)],[c_543]) ).
% 1.09/1.02  
% 1.09/1.02  cnf(c_762,plain,
% 1.09/1.02      ( ~ v2_tex_2(X0,sK2)
% 1.09/1.02      | ~ v2_tex_2(X1,sK2)
% 1.09/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.09/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.09/1.02      | m1_subset_1(sK1(sK2,X1),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.09/1.02      | sK2 != sK2
% 1.09/1.02      | k1_xboole_0 != X1
% 1.09/1.02      | k1_xboole_0 = X0 ),
% 1.09/1.02      inference(resolution_lifted,[status(thm)],[c_661,c_544]) ).
% 1.09/1.02  
% 1.09/1.02  cnf(c_763,plain,
% 1.09/1.02      ( ~ v2_tex_2(X0,sK2)
% 1.09/1.02      | ~ v2_tex_2(k1_xboole_0,sK2)
% 1.09/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.09/1.02      | m1_subset_1(sK1(sK2,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.09/1.02      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.09/1.02      | k1_xboole_0 = X0 ),
% 1.09/1.02      inference(unflattening,[status(thm)],[c_762]) ).
% 1.09/1.02  
% 1.09/1.02  cnf(c_779,plain,
% 1.09/1.02      ( ~ v2_tex_2(X0,sK2)
% 1.09/1.02      | ~ v2_tex_2(k1_xboole_0,sK2)
% 1.09/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.09/1.02      | m1_subset_1(sK1(sK2,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.09/1.02      | k1_xboole_0 = X0 ),
% 1.09/1.02      inference(forward_subsumption_resolution,[status(thm)],[c_763,c_5]) ).
% 1.09/1.02  
% 1.09/1.02  cnf(c_1033,plain,
% 1.09/1.02      ( ~ v2_tex_2(X0,sK2)
% 1.09/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.09/1.02      | k1_xboole_0 = X0
% 1.09/1.02      | ~ sP0_iProver_split ),
% 1.09/1.02      inference(splitting,
% 1.09/1.02                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 1.09/1.02                [c_779]) ).
% 1.09/1.02  
% 1.09/1.02  cnf(c_1347,plain,
% 1.09/1.02      ( k1_xboole_0 = X0
% 1.09/1.02      | v2_tex_2(X0,sK2) != iProver_top
% 1.09/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.09/1.02      | sP0_iProver_split != iProver_top ),
% 1.09/1.02      inference(predicate_to_equality,[status(thm)],[c_1033]) ).
% 1.09/1.02  
% 1.09/1.02  cnf(c_1640,plain,
% 1.09/1.02      ( sK3 = k1_xboole_0
% 1.09/1.02      | v2_tex_2(sK3,sK2) != iProver_top
% 1.09/1.02      | sP0_iProver_split != iProver_top ),
% 1.09/1.02      inference(superposition,[status(thm)],[c_1356,c_1347]) ).
% 1.09/1.02  
% 1.09/1.02  cnf(c_1,plain,
% 1.09/1.02      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 1.09/1.02      inference(cnf_transformation,[],[f42]) ).
% 1.09/1.02  
% 1.09/1.02  cnf(c_19,negated_conjecture,
% 1.09/1.02      ( v1_xboole_0(sK3) ),
% 1.09/1.02      inference(cnf_transformation,[],[f61]) ).
% 1.09/1.02  
% 1.09/1.02  cnf(c_348,plain,
% 1.09/1.02      ( sK3 != X0 | k1_xboole_0 = X0 ),
% 1.09/1.02      inference(resolution_lifted,[status(thm)],[c_1,c_19]) ).
% 1.09/1.02  
% 1.09/1.02  cnf(c_349,plain,
% 1.09/1.02      ( k1_xboole_0 = sK3 ),
% 1.09/1.02      inference(unflattening,[status(thm)],[c_348]) ).
% 1.09/1.02  
% 1.09/1.02  cnf(c_1038,plain,( X0 = X0 ),theory(equality) ).
% 1.09/1.02  
% 1.09/1.02  cnf(c_1574,plain,
% 1.09/1.02      ( sK3 = sK3 ),
% 1.09/1.02      inference(instantiation,[status(thm)],[c_1038]) ).
% 1.09/1.02  
% 1.09/1.02  cnf(c_1039,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 1.09/1.02  
% 1.09/1.02  cnf(c_1542,plain,
% 1.09/1.02      ( sK3 != X0 | sK3 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 1.09/1.02      inference(instantiation,[status(thm)],[c_1039]) ).
% 1.09/1.02  
% 1.09/1.02  cnf(c_1647,plain,
% 1.09/1.02      ( sK3 != sK3 | sK3 = k1_xboole_0 | k1_xboole_0 != sK3 ),
% 1.09/1.02      inference(instantiation,[status(thm)],[c_1542]) ).
% 1.09/1.02  
% 1.09/1.02  cnf(c_1838,plain,
% 1.09/1.02      ( sK3 = k1_xboole_0 ),
% 1.09/1.02      inference(global_propositional_subsumption,
% 1.09/1.02                [status(thm)],
% 1.09/1.02                [c_1640,c_349,c_1574,c_1647]) ).
% 1.09/1.02  
% 1.09/1.02  cnf(c_17,negated_conjecture,
% 1.09/1.02      ( v3_tex_2(sK3,sK2) ),
% 1.09/1.02      inference(cnf_transformation,[],[f63]) ).
% 1.09/1.02  
% 1.09/1.02  cnf(c_679,plain,
% 1.09/1.02      ( ~ v2_tex_2(X0,sK2)
% 1.09/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.09/1.02      | sK2 != sK2
% 1.09/1.02      | sK3 != k1_xboole_0
% 1.09/1.02      | k1_xboole_0 = X0 ),
% 1.09/1.02      inference(resolution_lifted,[status(thm)],[c_17,c_661]) ).
% 1.09/1.02  
% 1.09/1.02  cnf(c_834,plain,
% 1.09/1.02      ( ~ v2_tex_2(X0,sK2)
% 1.09/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.09/1.02      | sK3 != k1_xboole_0
% 1.09/1.02      | k1_xboole_0 = X0 ),
% 1.09/1.02      inference(equality_resolution_simp,[status(thm)],[c_679]) ).
% 1.09/1.02  
% 1.09/1.02  cnf(c_1345,plain,
% 1.09/1.02      ( sK3 != k1_xboole_0
% 1.09/1.02      | k1_xboole_0 = X0
% 1.09/1.02      | v2_tex_2(X0,sK2) != iProver_top
% 1.09/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 1.09/1.02      inference(predicate_to_equality,[status(thm)],[c_834]) ).
% 1.09/1.02  
% 1.09/1.02  cnf(c_1841,plain,
% 1.09/1.02      ( k1_xboole_0 = X0
% 1.09/1.02      | k1_xboole_0 != k1_xboole_0
% 1.09/1.02      | v2_tex_2(X0,sK2) != iProver_top
% 1.09/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 1.09/1.02      inference(demodulation,[status(thm)],[c_1838,c_1345]) ).
% 1.09/1.02  
% 1.09/1.02  cnf(c_1848,plain,
% 1.09/1.02      ( k1_xboole_0 = X0
% 1.09/1.02      | v2_tex_2(X0,sK2) != iProver_top
% 1.09/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 1.09/1.02      inference(equality_resolution_simp,[status(thm)],[c_1841]) ).
% 1.09/1.02  
% 1.09/1.02  cnf(c_2332,plain,
% 1.09/1.02      ( k1_tarski(sK0(u1_struct_0(sK2))) = k1_xboole_0
% 1.09/1.02      | v2_tex_2(k1_tarski(sK0(u1_struct_0(sK2))),sK2) != iProver_top ),
% 1.09/1.02      inference(superposition,[status(thm)],[c_2326,c_1848]) ).
% 1.09/1.02  
% 1.09/1.02  cnf(c_16,plain,
% 1.09/1.02      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
% 1.09/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.09/1.02      | ~ v2_pre_topc(X0)
% 1.09/1.02      | v2_struct_0(X0)
% 1.09/1.02      | ~ l1_pre_topc(X0) ),
% 1.09/1.02      inference(cnf_transformation,[],[f57]) ).
% 1.09/1.02  
% 1.09/1.02  cnf(c_21,negated_conjecture,
% 1.09/1.02      ( v2_pre_topc(sK2) ),
% 1.09/1.02      inference(cnf_transformation,[],[f59]) ).
% 1.09/1.02  
% 1.09/1.02  cnf(c_273,plain,
% 1.09/1.02      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
% 1.09/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.09/1.02      | v2_struct_0(X0)
% 1.09/1.02      | ~ l1_pre_topc(X0)
% 1.09/1.02      | sK2 != X0 ),
% 1.09/1.02      inference(resolution_lifted,[status(thm)],[c_16,c_21]) ).
% 1.09/1.02  
% 1.09/1.02  cnf(c_274,plain,
% 1.09/1.02      ( v2_tex_2(k6_domain_1(u1_struct_0(sK2),X0),sK2)
% 1.09/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.09/1.02      | v2_struct_0(sK2)
% 1.09/1.02      | ~ l1_pre_topc(sK2) ),
% 1.09/1.02      inference(unflattening,[status(thm)],[c_273]) ).
% 1.09/1.02  
% 1.09/1.02  cnf(c_278,plain,
% 1.09/1.02      ( v2_tex_2(k6_domain_1(u1_struct_0(sK2),X0),sK2)
% 1.09/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 1.09/1.02      inference(global_propositional_subsumption,
% 1.09/1.02                [status(thm)],
% 1.09/1.02                [c_274,c_22,c_20]) ).
% 1.09/1.02  
% 1.09/1.02  cnf(c_1354,plain,
% 1.09/1.02      ( v2_tex_2(k6_domain_1(u1_struct_0(sK2),X0),sK2) = iProver_top
% 1.09/1.02      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
% 1.09/1.02      inference(predicate_to_equality,[status(thm)],[c_278]) ).
% 1.09/1.02  
% 1.09/1.02  cnf(c_2246,plain,
% 1.09/1.02      ( v2_tex_2(k1_tarski(sK0(u1_struct_0(sK2))),sK2) = iProver_top
% 1.09/1.02      | m1_subset_1(sK0(u1_struct_0(sK2)),u1_struct_0(sK2)) != iProver_top ),
% 1.09/1.02      inference(superposition,[status(thm)],[c_2149,c_1354]) ).
% 1.09/1.02  
% 1.09/1.02  cnf(c_2344,plain,
% 1.09/1.02      ( k1_tarski(sK0(u1_struct_0(sK2))) = k1_xboole_0 ),
% 1.09/1.02      inference(global_propositional_subsumption,
% 1.09/1.02                [status(thm)],
% 1.09/1.02                [c_2332,c_1483,c_2246]) ).
% 1.09/1.02  
% 1.09/1.02  cnf(c_3,plain,
% 1.09/1.02      ( ~ v1_xboole_0(k1_tarski(X0)) ),
% 1.09/1.02      inference(cnf_transformation,[],[f44]) ).
% 1.09/1.02  
% 1.09/1.02  cnf(c_1361,plain,
% 1.09/1.02      ( v1_xboole_0(k1_tarski(X0)) != iProver_top ),
% 1.09/1.02      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 1.09/1.02  
% 1.09/1.02  cnf(c_2352,plain,
% 1.09/1.02      ( v1_xboole_0(k1_xboole_0) != iProver_top ),
% 1.09/1.02      inference(superposition,[status(thm)],[c_2344,c_1361]) ).
% 1.09/1.02  
% 1.09/1.02  cnf(c_0,plain,
% 1.09/1.02      ( v1_xboole_0(k1_xboole_0) ),
% 1.09/1.02      inference(cnf_transformation,[],[f41]) ).
% 1.09/1.02  
% 1.09/1.02  cnf(c_77,plain,
% 1.09/1.02      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 1.09/1.02      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 1.09/1.02  
% 1.09/1.02  cnf(contradiction,plain,
% 1.09/1.02      ( $false ),
% 1.09/1.02      inference(minisat,[status(thm)],[c_2352,c_77]) ).
% 1.09/1.02  
% 1.09/1.02  
% 1.09/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 1.09/1.02  
% 1.09/1.02  ------                               Statistics
% 1.09/1.02  
% 1.09/1.02  ------ General
% 1.09/1.02  
% 1.09/1.02  abstr_ref_over_cycles:                  0
% 1.09/1.02  abstr_ref_under_cycles:                 0
% 1.09/1.02  gc_basic_clause_elim:                   0
% 1.09/1.02  forced_gc_time:                         0
% 1.09/1.02  parsing_time:                           0.008
% 1.09/1.02  unif_index_cands_time:                  0.
% 1.09/1.02  unif_index_add_time:                    0.
% 1.09/1.02  orderings_time:                         0.
% 1.09/1.02  out_proof_time:                         0.009
% 1.09/1.02  total_time:                             0.156
% 1.09/1.02  num_of_symbols:                         50
% 1.09/1.02  num_of_terms:                           1463
% 1.09/1.02  
% 1.09/1.02  ------ Preprocessing
% 1.09/1.02  
% 1.09/1.02  num_of_splits:                          3
% 1.09/1.02  num_of_split_atoms:                     1
% 1.09/1.02  num_of_reused_defs:                     2
% 1.09/1.02  num_eq_ax_congr_red:                    13
% 1.09/1.02  num_of_sem_filtered_clauses:            1
% 1.09/1.02  num_of_subtypes:                        0
% 1.09/1.02  monotx_restored_types:                  0
% 1.09/1.02  sat_num_of_epr_types:                   0
% 1.09/1.02  sat_num_of_non_cyclic_types:            0
% 1.09/1.02  sat_guarded_non_collapsed_types:        0
% 1.09/1.02  num_pure_diseq_elim:                    0
% 1.09/1.02  simp_replaced_by:                       0
% 1.09/1.02  res_preprocessed:                       92
% 1.09/1.02  prep_upred:                             0
% 1.09/1.02  prep_unflattend:                        36
% 1.09/1.02  smt_new_axioms:                         0
% 1.09/1.02  pred_elim_cands:                        3
% 1.09/1.02  pred_elim:                              6
% 1.09/1.02  pred_elim_cl:                           7
% 1.09/1.02  pred_elim_cycles:                       10
% 1.09/1.02  merged_defs:                            0
% 1.09/1.02  merged_defs_ncl:                        0
% 1.09/1.02  bin_hyper_res:                          0
% 1.09/1.02  prep_cycles:                            4
% 1.09/1.02  pred_elim_time:                         0.028
% 1.09/1.02  splitting_time:                         0.
% 1.09/1.02  sem_filter_time:                        0.
% 1.09/1.02  monotx_time:                            0.
% 1.09/1.02  subtype_inf_time:                       0.
% 1.09/1.02  
% 1.09/1.02  ------ Problem properties
% 1.09/1.02  
% 1.09/1.02  clauses:                                19
% 1.09/1.02  conjectures:                            2
% 1.09/1.02  epr:                                    4
% 1.09/1.02  horn:                                   15
% 1.09/1.02  ground:                                 8
% 1.09/1.02  unary:                                  8
% 1.09/1.02  binary:                                 2
% 1.09/1.02  lits:                                   43
% 1.09/1.02  lits_eq:                                8
% 1.09/1.02  fd_pure:                                0
% 1.09/1.02  fd_pseudo:                              0
% 1.09/1.02  fd_cond:                                5
% 1.09/1.02  fd_pseudo_cond:                         0
% 1.09/1.02  ac_symbols:                             0
% 1.09/1.02  
% 1.09/1.02  ------ Propositional Solver
% 1.09/1.02  
% 1.09/1.02  prop_solver_calls:                      27
% 1.09/1.02  prop_fast_solver_calls:                 638
% 1.09/1.02  smt_solver_calls:                       0
% 1.09/1.02  smt_fast_solver_calls:                  0
% 1.09/1.02  prop_num_of_clauses:                    689
% 1.09/1.02  prop_preprocess_simplified:             2974
% 1.09/1.02  prop_fo_subsumed:                       17
% 1.09/1.02  prop_solver_time:                       0.
% 1.09/1.02  smt_solver_time:                        0.
% 1.09/1.02  smt_fast_solver_time:                   0.
% 1.09/1.02  prop_fast_solver_time:                  0.
% 1.09/1.02  prop_unsat_core_time:                   0.
% 1.09/1.02  
% 1.09/1.02  ------ QBF
% 1.09/1.02  
% 1.09/1.02  qbf_q_res:                              0
% 1.09/1.02  qbf_num_tautologies:                    0
% 1.09/1.02  qbf_prep_cycles:                        0
% 1.09/1.02  
% 1.09/1.02  ------ BMC1
% 1.09/1.02  
% 1.09/1.02  bmc1_current_bound:                     -1
% 1.09/1.02  bmc1_last_solved_bound:                 -1
% 1.09/1.02  bmc1_unsat_core_size:                   -1
% 1.09/1.02  bmc1_unsat_core_parents_size:           -1
% 1.09/1.02  bmc1_merge_next_fun:                    0
% 1.09/1.02  bmc1_unsat_core_clauses_time:           0.
% 1.09/1.02  
% 1.09/1.02  ------ Instantiation
% 1.09/1.02  
% 1.09/1.02  inst_num_of_clauses:                    187
% 1.09/1.02  inst_num_in_passive:                    72
% 1.09/1.02  inst_num_in_active:                     115
% 1.09/1.02  inst_num_in_unprocessed:                0
% 1.09/1.02  inst_num_of_loops:                      130
% 1.09/1.02  inst_num_of_learning_restarts:          0
% 1.09/1.02  inst_num_moves_active_passive:          12
% 1.09/1.02  inst_lit_activity:                      0
% 1.09/1.02  inst_lit_activity_moves:                0
% 1.09/1.02  inst_num_tautologies:                   0
% 1.09/1.02  inst_num_prop_implied:                  0
% 1.09/1.02  inst_num_existing_simplified:           0
% 1.09/1.02  inst_num_eq_res_simplified:             0
% 1.09/1.02  inst_num_child_elim:                    0
% 1.09/1.02  inst_num_of_dismatching_blockings:      19
% 1.09/1.02  inst_num_of_non_proper_insts:           118
% 1.09/1.02  inst_num_of_duplicates:                 0
% 1.09/1.02  inst_inst_num_from_inst_to_res:         0
% 1.09/1.02  inst_dismatching_checking_time:         0.
% 1.09/1.02  
% 1.09/1.02  ------ Resolution
% 1.09/1.02  
% 1.09/1.02  res_num_of_clauses:                     0
% 1.09/1.02  res_num_in_passive:                     0
% 1.09/1.02  res_num_in_active:                      0
% 1.09/1.02  res_num_of_loops:                       96
% 1.09/1.02  res_forward_subset_subsumed:            21
% 1.09/1.02  res_backward_subset_subsumed:           0
% 1.09/1.02  res_forward_subsumed:                   0
% 1.09/1.02  res_backward_subsumed:                  0
% 1.09/1.02  res_forward_subsumption_resolution:     5
% 1.09/1.02  res_backward_subsumption_resolution:    0
% 1.09/1.02  res_clause_to_clause_subsumption:       66
% 1.09/1.02  res_orphan_elimination:                 0
% 1.09/1.02  res_tautology_del:                      17
% 1.09/1.02  res_num_eq_res_simplified:              1
% 1.09/1.02  res_num_sel_changes:                    0
% 1.09/1.02  res_moves_from_active_to_pass:          0
% 1.09/1.02  
% 1.09/1.02  ------ Superposition
% 1.09/1.02  
% 1.09/1.02  sup_time_total:                         0.
% 1.09/1.02  sup_time_generating:                    0.
% 1.09/1.02  sup_time_sim_full:                      0.
% 1.09/1.02  sup_time_sim_immed:                     0.
% 1.09/1.02  
% 1.09/1.02  sup_num_of_clauses:                     28
% 1.09/1.02  sup_num_in_active:                      18
% 1.09/1.02  sup_num_in_passive:                     10
% 1.09/1.02  sup_num_of_loops:                       25
% 1.09/1.02  sup_fw_superposition:                   8
% 1.09/1.02  sup_bw_superposition:                   13
% 1.09/1.02  sup_immediate_simplified:               2
% 1.09/1.02  sup_given_eliminated:                   0
% 1.09/1.02  comparisons_done:                       0
% 1.09/1.02  comparisons_avoided:                    0
% 1.09/1.02  
% 1.09/1.02  ------ Simplifications
% 1.09/1.02  
% 1.09/1.02  
% 1.09/1.02  sim_fw_subset_subsumed:                 1
% 1.09/1.02  sim_bw_subset_subsumed:                 3
% 1.09/1.02  sim_fw_subsumed:                        1
% 1.09/1.02  sim_bw_subsumed:                        0
% 1.09/1.02  sim_fw_subsumption_res:                 0
% 1.09/1.02  sim_bw_subsumption_res:                 0
% 1.09/1.02  sim_tautology_del:                      0
% 1.09/1.02  sim_eq_tautology_del:                   3
% 1.09/1.02  sim_eq_res_simp:                        1
% 1.09/1.02  sim_fw_demodulated:                     0
% 1.09/1.02  sim_bw_demodulated:                     7
% 1.09/1.02  sim_light_normalised:                   0
% 1.09/1.02  sim_joinable_taut:                      0
% 1.09/1.02  sim_joinable_simp:                      0
% 1.09/1.02  sim_ac_normalised:                      0
% 1.09/1.02  sim_smt_subsumption:                    0
% 1.09/1.02  
%------------------------------------------------------------------------------
