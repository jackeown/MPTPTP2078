%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1878+1.004 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:46 EST 2020

% Result     : Theorem 2.70s
% Output     : CNFRefutation 2.70s
% Verified   : 
% Statistics : Number of formulae       :  191 (1292 expanded)
%              Number of clauses        :  130 ( 438 expanded)
%              Number of leaves         :   21 ( 311 expanded)
%              Depth                    :   28
%              Number of atoms          :  664 (6504 expanded)
%              Number of equality atoms :  282 ( 913 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] : m1_subset_1(sK1(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f4,f33])).

fof(f49,plain,(
    ! [X0] : m1_subset_1(sK1(X0),X0) ),
    inference(cnf_transformation,[],[f34])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f1,axiom,(
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

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r1_tarski(X1,X2)
          & v2_tex_2(X2,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK0(X0,X1) != X1
        & r1_tarski(X1,sK0(X0,X1))
        & v2_tex_2(sK0(X0,X1),X0)
        & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ( sK0(X0,X1) != X1
                & r1_tarski(X1,sK0(X0,X1))
                & v2_tex_2(sK0(X0,X1),X0)
                & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => ~ v3_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => ~ v3_tex_2(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
     => ( v3_tex_2(sK4,X0)
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0)))
        & v1_xboole_0(sK4) ) ) ),
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
          ( v3_tex_2(X1,sK3)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( v3_tex_2(sK4,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    & v1_xboole_0(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f27,f39,f38])).

fof(f61,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f62,plain,(
    v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f58,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f63,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f40])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( X1 = X3
      | ~ r1_tarski(X1,X3)
      | ~ v2_tex_2(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f64,plain,(
    v3_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f7,axiom,(
    ! [X0] :
    ? [X1] :
      ( v1_xboole_0(X1)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( v1_xboole_0(sK2(X0))
        & m1_subset_1(sK2(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( v1_xboole_0(sK2(X0))
      & m1_subset_1(sK2(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f7,f35])).

fof(f53,plain,(
    ! [X0] : v1_xboole_0(sK2(X0)) ),
    inference(cnf_transformation,[],[f36])).

fof(f52,plain,(
    ! [X0] : m1_subset_1(sK2(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f36])).

fof(f59,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f5,axiom,(
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
    inference(ennf_transformation,[],[f5])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f50,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f48,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f60,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | v2_tex_2(sK0(X0,X1),X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f6,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f6])).

cnf(c_8,plain,
    ( m1_subset_1(sK1(X0),X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1721,plain,
    ( m1_subset_1(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1722,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_21,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_620,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_21])).

cnf(c_621,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(sK0(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_tex_2(X0,sK3)
    | v3_tex_2(X0,sK3) ),
    inference(unflattening,[status(thm)],[c_620])).

cnf(c_1709,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK0(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | v2_tex_2(X0,sK3) != iProver_top
    | v3_tex_2(X0,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_621])).

cnf(c_20,negated_conjecture,
    ( v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1713,plain,
    ( v1_xboole_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_17,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1716,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2627,plain,
    ( sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1713,c_1716])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1714,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_16,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_184,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_16])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_tex_2(X1,X2)
    | ~ v3_tex_2(X0,X2)
    | ~ l1_pre_topc(X2)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_692,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_tex_2(X1,X2)
    | ~ v3_tex_2(X0,X2)
    | X1 = X0
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_21])).

cnf(c_693,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_tex_2(X1,sK3)
    | ~ v3_tex_2(X0,sK3)
    | X1 = X0 ),
    inference(unflattening,[status(thm)],[c_692])).

cnf(c_747,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_tex_2(X1,sK3)
    | ~ v3_tex_2(X0,sK3)
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_184,c_693])).

cnf(c_1706,plain,
    ( X0 = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_tex_2(X0,sK3) != iProver_top
    | v3_tex_2(X1,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_747])).

cnf(c_2433,plain,
    ( sK4 = X0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK4)) != iProver_top
    | v2_tex_2(sK4,sK3) != iProver_top
    | v3_tex_2(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1714,c_1706])).

cnf(c_28,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_18,negated_conjecture,
    ( v3_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_tex_2(X0,X1)
    | ~ v3_tex_2(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_605,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_tex_2(X0,X1)
    | ~ v3_tex_2(X0,X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_21])).

cnf(c_606,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_tex_2(X0,sK3)
    | ~ v3_tex_2(X0,sK3) ),
    inference(unflattening,[status(thm)],[c_605])).

cnf(c_935,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_tex_2(X0,sK3)
    | sK3 != sK3
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_606])).

cnf(c_936,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_tex_2(sK4,sK3) ),
    inference(unflattening,[status(thm)],[c_935])).

cnf(c_937,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_tex_2(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_936])).

cnf(c_2110,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(sK4))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_tex_2(sK4,sK3)
    | ~ v3_tex_2(X0,sK3)
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_747])).

cnf(c_2111,plain,
    ( sK4 = X0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK4)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_tex_2(sK4,sK3) != iProver_top
    | v3_tex_2(X0,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2110])).

cnf(c_2511,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK4)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | sK4 = X0
    | v3_tex_2(X0,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2433,c_28,c_937,c_2111])).

cnf(c_2512,plain,
    ( sK4 = X0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK4)) != iProver_top
    | v3_tex_2(X0,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_2511])).

cnf(c_2928,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v3_tex_2(X0,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2627,c_2512])).

cnf(c_29,plain,
    ( v3_tex_2(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_472,plain,
    ( sK4 != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_20])).

cnf(c_473,plain,
    ( k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_472])).

cnf(c_607,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_tex_2(X0,sK3) = iProver_top
    | v3_tex_2(X0,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_606])).

cnf(c_1377,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1396,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1377])).

cnf(c_1386,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1873,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(sK4)
    | X0 != sK4 ),
    inference(instantiation,[status(thm)],[c_1386])).

cnf(c_1962,plain,
    ( ~ v1_xboole_0(sK4)
    | v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 != sK4 ),
    inference(instantiation,[status(thm)],[c_1873])).

cnf(c_1379,plain,
    ( ~ v3_tex_2(X0,X1)
    | v3_tex_2(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1908,plain,
    ( v3_tex_2(X0,X1)
    | ~ v3_tex_2(sK4,sK3)
    | X1 != sK3
    | X0 != sK4 ),
    inference(instantiation,[status(thm)],[c_1379])).

cnf(c_1971,plain,
    ( ~ v3_tex_2(sK4,sK3)
    | v3_tex_2(k1_xboole_0,X0)
    | X0 != sK3
    | k1_xboole_0 != sK4 ),
    inference(instantiation,[status(thm)],[c_1908])).

cnf(c_1972,plain,
    ( X0 != sK3
    | k1_xboole_0 != sK4
    | v3_tex_2(sK4,sK3) != iProver_top
    | v3_tex_2(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1971])).

cnf(c_1974,plain,
    ( sK3 != sK3
    | k1_xboole_0 != sK4
    | v3_tex_2(sK4,sK3) != iProver_top
    | v3_tex_2(k1_xboole_0,sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1972])).

cnf(c_1384,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1923,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | X1 != k1_zfmisc_1(u1_struct_0(sK3))
    | X0 != sK4 ),
    inference(instantiation,[status(thm)],[c_1384])).

cnf(c_1980,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(k1_xboole_0,X0)
    | X0 != k1_zfmisc_1(u1_struct_0(sK3))
    | k1_xboole_0 != sK4 ),
    inference(instantiation,[status(thm)],[c_1923])).

cnf(c_2079,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3)))
    | k1_zfmisc_1(u1_struct_0(sK3)) != k1_zfmisc_1(u1_struct_0(sK3))
    | k1_xboole_0 != sK4 ),
    inference(instantiation,[status(thm)],[c_1980])).

cnf(c_2081,plain,
    ( k1_zfmisc_1(u1_struct_0(sK3)) != k1_zfmisc_1(u1_struct_0(sK3))
    | k1_xboole_0 != sK4
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2079])).

cnf(c_2080,plain,
    ( k1_zfmisc_1(u1_struct_0(sK3)) = k1_zfmisc_1(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1377])).

cnf(c_2658,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_tex_2(X0,sK3)
    | ~ v3_tex_2(k1_xboole_0,sK3)
    | X0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_747])).

cnf(c_2659,plain,
    ( X0 = k1_xboole_0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_tex_2(X0,sK3) != iProver_top
    | v3_tex_2(k1_xboole_0,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2658])).

cnf(c_11,plain,
    ( v1_xboole_0(sK2(X0)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1719,plain,
    ( v1_xboole_0(sK2(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2626,plain,
    ( sK2(X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1719,c_1716])).

cnf(c_12,plain,
    ( m1_subset_1(sK2(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1718,plain,
    ( m1_subset_1(sK2(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2971,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2626,c_1718])).

cnf(c_3293,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(k1_xboole_0)
    | X0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1386])).

cnf(c_3534,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | k1_xboole_0 = X0
    | v3_tex_2(X0,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2928,c_20,c_28,c_29,c_17,c_473,c_607,c_1396,c_1962,c_1974,c_2081,c_2080,c_2659,c_2971,c_3293])).

cnf(c_3535,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v3_tex_2(X0,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_3534])).

cnf(c_3545,plain,
    ( sK0(sK3,X0) = k1_xboole_0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_tex_2(X0,sK3) != iProver_top
    | v3_tex_2(X0,sK3) = iProver_top
    | v3_tex_2(sK0(sK3,X0),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1709,c_3535])).

cnf(c_3626,plain,
    ( sK0(sK3,k6_domain_1(u1_struct_0(sK3),X0)) = k1_xboole_0
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | v2_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3) != iProver_top
    | v3_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3) = iProver_top
    | v3_tex_2(sK0(sK3,k6_domain_1(u1_struct_0(sK3),X0)),sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1722,c_3545])).

cnf(c_23,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_24,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_26,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_9,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_54,plain,
    ( v2_struct_0(X0) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_56,plain,
    ( v2_struct_0(sK3) = iProver_top
    | l1_struct_0(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_54])).

cnf(c_7,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_60,plain,
    ( l1_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_62,plain,
    ( l1_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_60])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_tex_2(k6_domain_1(u1_struct_0(X1),X0),X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_22,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_339,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_tex_2(k6_domain_1(u1_struct_0(X1),X0),X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_22])).

cnf(c_340,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | v2_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_339])).

cnf(c_344,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | v2_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_340,c_23,c_21])).

cnf(c_346,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | v2_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_344])).

cnf(c_2434,plain,
    ( sK0(sK3,X0) = X1
    | m1_subset_1(X1,k1_zfmisc_1(sK0(sK3,X0))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_tex_2(X0,sK3) != iProver_top
    | v2_tex_2(sK0(sK3,X0),sK3) != iProver_top
    | v3_tex_2(X1,sK3) != iProver_top
    | v3_tex_2(X0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1709,c_1706])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X0,X1)
    | v2_tex_2(sK0(X1,X0),X1)
    | v3_tex_2(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_638,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X0,X1)
    | v2_tex_2(sK0(X1,X0),X1)
    | v3_tex_2(X0,X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_21])).

cnf(c_639,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_tex_2(X0,sK3)
    | v2_tex_2(sK0(sK3,X0),sK3)
    | v3_tex_2(X0,sK3) ),
    inference(unflattening,[status(thm)],[c_638])).

cnf(c_640,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_tex_2(X0,sK3) != iProver_top
    | v2_tex_2(sK0(sK3,X0),sK3) = iProver_top
    | v3_tex_2(X0,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_639])).

cnf(c_4059,plain,
    ( v2_tex_2(X0,sK3) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(sK0(sK3,X0))) != iProver_top
    | sK0(sK3,X0) = X1
    | v3_tex_2(X1,sK3) != iProver_top
    | v3_tex_2(X0,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2434,c_640])).

cnf(c_4060,plain,
    ( sK0(sK3,X0) = X1
    | m1_subset_1(X1,k1_zfmisc_1(sK0(sK3,X0))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_tex_2(X0,sK3) != iProver_top
    | v3_tex_2(X1,sK3) != iProver_top
    | v3_tex_2(X0,sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_4059])).

cnf(c_4073,plain,
    ( sK0(sK3,X0) = k1_xboole_0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_tex_2(X0,sK3) != iProver_top
    | v3_tex_2(X0,sK3) = iProver_top
    | v3_tex_2(k1_xboole_0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2971,c_4060])).

cnf(c_5519,plain,
    ( v3_tex_2(X0,sK3) = iProver_top
    | v2_tex_2(X0,sK3) != iProver_top
    | sK0(sK3,X0) = k1_xboole_0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4073,c_28,c_29,c_473,c_1396,c_1974,c_2081,c_2080])).

cnf(c_5520,plain,
    ( sK0(sK3,X0) = k1_xboole_0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_tex_2(X0,sK3) != iProver_top
    | v3_tex_2(X0,sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_5519])).

cnf(c_5529,plain,
    ( sK0(sK3,k6_domain_1(u1_struct_0(sK3),X0)) = k1_xboole_0
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | v2_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3) != iProver_top
    | v3_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1722,c_5520])).

cnf(c_7116,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | sK0(sK3,k6_domain_1(u1_struct_0(sK3),X0)) = k1_xboole_0
    | v3_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3626,c_24,c_26,c_56,c_62,c_346,c_5529])).

cnf(c_7117,plain,
    ( sK0(sK3,k6_domain_1(u1_struct_0(sK3),X0)) = k1_xboole_0
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | v3_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_7116])).

cnf(c_2799,plain,
    ( k6_domain_1(u1_struct_0(sK3),X0) = sK4
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k6_domain_1(u1_struct_0(sK3),X0),k1_zfmisc_1(sK4)) != iProver_top
    | v3_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1722,c_2512])).

cnf(c_3845,plain,
    ( v3_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3) != iProver_top
    | m1_subset_1(k6_domain_1(u1_struct_0(sK3),X0),k1_zfmisc_1(sK4)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | k6_domain_1(u1_struct_0(sK3),X0) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2799,c_24,c_26,c_56,c_62])).

cnf(c_3846,plain,
    ( k6_domain_1(u1_struct_0(sK3),X0) = sK4
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k6_domain_1(u1_struct_0(sK3),X0),k1_zfmisc_1(sK4)) != iProver_top
    | v3_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_3845])).

cnf(c_3851,plain,
    ( k6_domain_1(u1_struct_0(sK3),X0) = k1_xboole_0
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k6_domain_1(u1_struct_0(sK3),X0),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v3_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3846,c_2627])).

cnf(c_3543,plain,
    ( k6_domain_1(u1_struct_0(sK3),X0) = k1_xboole_0
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | v3_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1722,c_3535])).

cnf(c_3859,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | k6_domain_1(u1_struct_0(sK3),X0) = k1_xboole_0
    | v3_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3851,c_24,c_26,c_56,c_62,c_3543])).

cnf(c_3860,plain,
    ( k6_domain_1(u1_struct_0(sK3),X0) = k1_xboole_0
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | v3_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_3859])).

cnf(c_7127,plain,
    ( k6_domain_1(u1_struct_0(sK3),X0) = k1_xboole_0
    | sK0(sK3,k6_domain_1(u1_struct_0(sK3),X0)) = k1_xboole_0
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7117,c_3860])).

cnf(c_2800,plain,
    ( k6_domain_1(u1_struct_0(sK3),X0) = X1
    | m1_subset_1(X1,k1_zfmisc_1(k6_domain_1(u1_struct_0(sK3),X0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | v2_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3) != iProver_top
    | v3_tex_2(X1,sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1722,c_1706])).

cnf(c_6813,plain,
    ( v3_tex_2(X1,sK3) != iProver_top
    | k6_domain_1(u1_struct_0(sK3),X0) = X1
    | m1_subset_1(X1,k1_zfmisc_1(k6_domain_1(u1_struct_0(sK3),X0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2800,c_24,c_26,c_56,c_62,c_346])).

cnf(c_6814,plain,
    ( k6_domain_1(u1_struct_0(sK3),X0) = X1
    | m1_subset_1(X1,k1_zfmisc_1(k6_domain_1(u1_struct_0(sK3),X0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | v3_tex_2(X1,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_6813])).

cnf(c_6826,plain,
    ( k6_domain_1(u1_struct_0(sK3),X0) = k1_xboole_0
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v3_tex_2(k1_xboole_0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2971,c_6814])).

cnf(c_7250,plain,
    ( k6_domain_1(u1_struct_0(sK3),X0) = k1_xboole_0
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7127,c_28,c_29,c_473,c_1396,c_1974,c_2081,c_2080,c_6826])).

cnf(c_7258,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK1(u1_struct_0(sK3))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1721,c_7250])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1717,plain,
    ( k6_domain_1(X0,X1) = k1_tarski(X1)
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2744,plain,
    ( k6_domain_1(X0,sK1(X0)) = k1_tarski(sK1(X0))
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1721,c_1717])).

cnf(c_321,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_7,c_9])).

cnf(c_360,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_pre_topc(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_321,c_23])).

cnf(c_361,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK3))
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_360])).

cnf(c_55,plain,
    ( v2_struct_0(sK3)
    | ~ l1_struct_0(sK3)
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_61,plain,
    ( l1_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_363,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_361,c_23,c_21,c_55,c_61])).

cnf(c_1711,plain,
    ( v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_363])).

cnf(c_3327,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK1(u1_struct_0(sK3))) = k1_tarski(sK1(u1_struct_0(sK3))) ),
    inference(superposition,[status(thm)],[c_2744,c_1711])).

cnf(c_7955,plain,
    ( k1_tarski(sK1(u1_struct_0(sK3))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7258,c_3327])).

cnf(c_10,plain,
    ( ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1720,plain,
    ( v1_xboole_0(k1_tarski(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_8302,plain,
    ( v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7955,c_1720])).

cnf(c_1963,plain,
    ( k1_xboole_0 != sK4
    | v1_xboole_0(sK4) != iProver_top
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1962])).

cnf(c_27,plain,
    ( v1_xboole_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8302,c_1963,c_473,c_27])).


%------------------------------------------------------------------------------
