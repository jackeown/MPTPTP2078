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
% DateTime   : Thu Dec  3 12:27:06 EST 2020

% Result     : Theorem 2.05s
% Output     : CNFRefutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 261 expanded)
%              Number of clauses        :   69 (  96 expanded)
%              Number of leaves         :   22 (  62 expanded)
%              Depth                    :   22
%              Number of atoms          :  414 ( 987 expanded)
%              Number of equality atoms :  125 ( 167 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f35])).

fof(f47,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f46,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

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

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
     => ( v3_tex_2(sK3,X0)
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0)))
        & v1_xboole_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
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

fof(f44,plain,
    ( v3_tex_2(sK3,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & v1_xboole_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f34,f43,f42])).

fof(f66,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f65,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f67,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f68,plain,(
    v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f70,plain,(
    v3_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

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
    inference(ennf_transformation,[],[f14])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

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
            & ( ( ! [X3] :
                    ( X1 = X3
                    | ~ r1_tarski(X1,X3)
                    | ~ v2_tex_2(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f38])).

fof(f40,plain,(
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

fof(f41,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f39,f40])).

fof(f59,plain,(
    ! [X0,X3,X1] :
      ( X1 = X3
      | ~ r1_tarski(X1,X3)
      | ~ v2_tex_2(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f55,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f6,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f6])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_8,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_377,plain,
    ( m1_subset_1(X0,X1)
    | X1 != X2
    | sK0(X2) != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_8])).

cnf(c_378,plain,
    ( m1_subset_1(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_377])).

cnf(c_1290,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(sK0(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_378])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1295,plain,
    ( k6_domain_1(X0,X1) = k1_tarski(X1)
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2232,plain,
    ( k6_domain_1(X0,sK0(X0)) = k1_tarski(sK0(X0))
    | k1_xboole_0 = X0
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1290,c_1295])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_2253,plain,
    ( v1_xboole_0(X0)
    | k6_domain_1(X0,sK0(X0)) = k1_tarski(sK0(X0))
    | k1_xboole_0 = X0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2232])).

cnf(c_2462,plain,
    ( k1_xboole_0 = X0
    | k6_domain_1(X0,sK0(X0)) = k1_tarski(sK0(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2232,c_1,c_2253])).

cnf(c_2463,plain,
    ( k6_domain_1(X0,sK0(X0)) = k1_tarski(sK0(X0))
    | k1_xboole_0 = X0 ),
    inference(renaming,[status(thm)],[c_2462])).

cnf(c_19,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_24,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_293,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_24])).

cnf(c_294,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK2),X0),sK2)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_293])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_23,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_298,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK2),X0),sK2)
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_294,c_25,c_23])).

cnf(c_1292,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK2),X0),sK2) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_298])).

cnf(c_2466,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | v2_tex_2(k1_tarski(sK0(u1_struct_0(sK2))),sK2) = iProver_top
    | m1_subset_1(sK0(u1_struct_0(sK2)),u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2463,c_1292])).

cnf(c_7,plain,
    ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_389,plain,
    ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
    | X1 != X2
    | sK0(X2) != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_7])).

cnf(c_390,plain,
    ( m1_subset_1(k1_tarski(sK0(X0)),k1_zfmisc_1(X0))
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_389])).

cnf(c_1289,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(k1_tarski(sK0(X0)),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_390])).

cnf(c_22,negated_conjecture,
    ( v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1293,plain,
    ( v1_xboole_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1297,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1768,plain,
    ( sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1293,c_1297])).

cnf(c_20,negated_conjecture,
    ( v3_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_4,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_17,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ v3_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | ~ l1_pre_topc(X1)
    | X0 = X2 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_514,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ v3_tex_2(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | X2 = X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_23])).

cnf(c_515,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ v3_tex_2(X1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(unflattening,[status(thm)],[c_514])).

cnf(c_641,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ v3_tex_2(X1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | X0 != X2
    | X0 = X1
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_515])).

cnf(c_642,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ v3_tex_2(k1_xboole_0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2)))
    | X0 = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_641])).

cnf(c_6,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_656,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ v3_tex_2(k1_xboole_0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | X0 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_642,c_6])).

cnf(c_683,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | sK2 != sK2
    | sK3 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_656])).

cnf(c_820,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | sK3 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_683])).

cnf(c_1280,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = X0
    | v2_tex_2(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_820])).

cnf(c_1772,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 != k1_xboole_0
    | v2_tex_2(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1768,c_1280])).

cnf(c_1779,plain,
    ( k1_xboole_0 = X0
    | v2_tex_2(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_1772])).

cnf(c_2344,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | k1_tarski(sK0(u1_struct_0(sK2))) = k1_xboole_0
    | v2_tex_2(k1_tarski(sK0(u1_struct_0(sK2))),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1289,c_1779])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_10,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_11,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_275,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_10,c_11])).

cnf(c_314,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_275,c_25])).

cnf(c_315,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_314])).

cnf(c_317,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_315,c_23])).

cnf(c_329,plain,
    ( u1_struct_0(sK2) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_317])).

cnf(c_2367,plain,
    ( k1_tarski(sK0(u1_struct_0(sK2))) = k1_xboole_0
    | v2_tex_2(k1_tarski(sK0(u1_struct_0(sK2))),sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2344,c_329])).

cnf(c_3,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_5,plain,
    ( k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1616,plain,
    ( k1_tarski(X0) != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3,c_5])).

cnf(c_2373,plain,
    ( v2_tex_2(k1_tarski(sK0(u1_struct_0(sK2))),sK2) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2367,c_1616])).

cnf(c_968,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1494,plain,
    ( X0 != X1
    | u1_struct_0(sK2) != X1
    | u1_struct_0(sK2) = X0 ),
    inference(instantiation,[status(thm)],[c_968])).

cnf(c_1637,plain,
    ( X0 != u1_struct_0(sK2)
    | u1_struct_0(sK2) = X0
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1494])).

cnf(c_1639,plain,
    ( u1_struct_0(sK2) != u1_struct_0(sK2)
    | u1_struct_0(sK2) = k1_xboole_0
    | k1_xboole_0 != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1637])).

cnf(c_974,plain,
    ( X0 != X1
    | u1_struct_0(X0) = u1_struct_0(X1) ),
    theory(equality)).

cnf(c_1496,plain,
    ( u1_struct_0(sK2) = u1_struct_0(X0)
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_974])).

cnf(c_1633,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1496])).

cnf(c_1576,plain,
    ( m1_subset_1(sK0(u1_struct_0(sK2)),u1_struct_0(sK2))
    | k1_xboole_0 = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_378])).

cnf(c_1581,plain,
    ( k1_xboole_0 = u1_struct_0(sK2)
    | m1_subset_1(sK0(u1_struct_0(sK2)),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1576])).

cnf(c_967,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1529,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_967])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2466,c_2373,c_1639,c_1633,c_1581,c_1529,c_329])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n001.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 13:47:30 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 2.05/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/0.98  
% 2.05/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.05/0.98  
% 2.05/0.98  ------  iProver source info
% 2.05/0.98  
% 2.05/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.05/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.05/0.98  git: non_committed_changes: false
% 2.05/0.98  git: last_make_outside_of_git: false
% 2.05/0.98  
% 2.05/0.98  ------ 
% 2.05/0.98  
% 2.05/0.98  ------ Input Options
% 2.05/0.98  
% 2.05/0.98  --out_options                           all
% 2.05/0.98  --tptp_safe_out                         true
% 2.05/0.98  --problem_path                          ""
% 2.05/0.98  --include_path                          ""
% 2.05/0.98  --clausifier                            res/vclausify_rel
% 2.05/0.98  --clausifier_options                    --mode clausify
% 2.05/0.98  --stdin                                 false
% 2.05/0.98  --stats_out                             all
% 2.05/0.98  
% 2.05/0.98  ------ General Options
% 2.05/0.98  
% 2.05/0.98  --fof                                   false
% 2.05/0.98  --time_out_real                         305.
% 2.05/0.98  --time_out_virtual                      -1.
% 2.05/0.98  --symbol_type_check                     false
% 2.05/0.98  --clausify_out                          false
% 2.05/0.98  --sig_cnt_out                           false
% 2.05/0.98  --trig_cnt_out                          false
% 2.05/0.98  --trig_cnt_out_tolerance                1.
% 2.05/0.98  --trig_cnt_out_sk_spl                   false
% 2.05/0.98  --abstr_cl_out                          false
% 2.05/0.98  
% 2.05/0.98  ------ Global Options
% 2.05/0.98  
% 2.05/0.98  --schedule                              default
% 2.05/0.98  --add_important_lit                     false
% 2.05/0.98  --prop_solver_per_cl                    1000
% 2.05/0.98  --min_unsat_core                        false
% 2.05/0.98  --soft_assumptions                      false
% 2.05/0.98  --soft_lemma_size                       3
% 2.05/0.98  --prop_impl_unit_size                   0
% 2.05/0.98  --prop_impl_unit                        []
% 2.05/0.98  --share_sel_clauses                     true
% 2.05/0.98  --reset_solvers                         false
% 2.05/0.98  --bc_imp_inh                            [conj_cone]
% 2.05/0.98  --conj_cone_tolerance                   3.
% 2.05/0.98  --extra_neg_conj                        none
% 2.05/0.98  --large_theory_mode                     true
% 2.05/0.98  --prolific_symb_bound                   200
% 2.05/0.98  --lt_threshold                          2000
% 2.05/0.98  --clause_weak_htbl                      true
% 2.05/0.98  --gc_record_bc_elim                     false
% 2.05/0.98  
% 2.05/0.98  ------ Preprocessing Options
% 2.05/0.98  
% 2.05/0.98  --preprocessing_flag                    true
% 2.05/0.98  --time_out_prep_mult                    0.1
% 2.05/0.98  --splitting_mode                        input
% 2.05/0.98  --splitting_grd                         true
% 2.05/0.98  --splitting_cvd                         false
% 2.05/0.98  --splitting_cvd_svl                     false
% 2.05/0.98  --splitting_nvd                         32
% 2.05/0.98  --sub_typing                            true
% 2.05/0.98  --prep_gs_sim                           true
% 2.05/0.98  --prep_unflatten                        true
% 2.05/0.98  --prep_res_sim                          true
% 2.05/0.98  --prep_upred                            true
% 2.05/0.98  --prep_sem_filter                       exhaustive
% 2.05/0.98  --prep_sem_filter_out                   false
% 2.05/0.98  --pred_elim                             true
% 2.05/0.98  --res_sim_input                         true
% 2.05/0.98  --eq_ax_congr_red                       true
% 2.05/0.98  --pure_diseq_elim                       true
% 2.05/0.98  --brand_transform                       false
% 2.05/0.98  --non_eq_to_eq                          false
% 2.05/0.98  --prep_def_merge                        true
% 2.05/0.98  --prep_def_merge_prop_impl              false
% 2.05/0.98  --prep_def_merge_mbd                    true
% 2.05/0.98  --prep_def_merge_tr_red                 false
% 2.05/0.98  --prep_def_merge_tr_cl                  false
% 2.05/0.98  --smt_preprocessing                     true
% 2.05/0.98  --smt_ac_axioms                         fast
% 2.05/0.98  --preprocessed_out                      false
% 2.05/0.98  --preprocessed_stats                    false
% 2.05/0.98  
% 2.05/0.98  ------ Abstraction refinement Options
% 2.05/0.98  
% 2.05/0.98  --abstr_ref                             []
% 2.05/0.98  --abstr_ref_prep                        false
% 2.05/0.98  --abstr_ref_until_sat                   false
% 2.05/0.98  --abstr_ref_sig_restrict                funpre
% 2.05/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.05/0.98  --abstr_ref_under                       []
% 2.05/0.98  
% 2.05/0.98  ------ SAT Options
% 2.05/0.98  
% 2.05/0.98  --sat_mode                              false
% 2.05/0.98  --sat_fm_restart_options                ""
% 2.05/0.98  --sat_gr_def                            false
% 2.05/0.98  --sat_epr_types                         true
% 2.05/0.98  --sat_non_cyclic_types                  false
% 2.05/0.98  --sat_finite_models                     false
% 2.05/0.98  --sat_fm_lemmas                         false
% 2.05/0.98  --sat_fm_prep                           false
% 2.05/0.98  --sat_fm_uc_incr                        true
% 2.05/0.98  --sat_out_model                         small
% 2.05/0.98  --sat_out_clauses                       false
% 2.05/0.98  
% 2.05/0.98  ------ QBF Options
% 2.05/0.98  
% 2.05/0.98  --qbf_mode                              false
% 2.05/0.98  --qbf_elim_univ                         false
% 2.05/0.98  --qbf_dom_inst                          none
% 2.05/0.98  --qbf_dom_pre_inst                      false
% 2.05/0.98  --qbf_sk_in                             false
% 2.05/0.98  --qbf_pred_elim                         true
% 2.05/0.98  --qbf_split                             512
% 2.05/0.98  
% 2.05/0.98  ------ BMC1 Options
% 2.05/0.98  
% 2.05/0.98  --bmc1_incremental                      false
% 2.05/0.98  --bmc1_axioms                           reachable_all
% 2.05/0.98  --bmc1_min_bound                        0
% 2.05/0.98  --bmc1_max_bound                        -1
% 2.05/0.98  --bmc1_max_bound_default                -1
% 2.05/0.98  --bmc1_symbol_reachability              true
% 2.05/0.98  --bmc1_property_lemmas                  false
% 2.05/0.98  --bmc1_k_induction                      false
% 2.05/0.98  --bmc1_non_equiv_states                 false
% 2.05/0.98  --bmc1_deadlock                         false
% 2.05/0.98  --bmc1_ucm                              false
% 2.05/0.98  --bmc1_add_unsat_core                   none
% 2.05/0.98  --bmc1_unsat_core_children              false
% 2.05/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.05/0.98  --bmc1_out_stat                         full
% 2.05/0.98  --bmc1_ground_init                      false
% 2.05/0.98  --bmc1_pre_inst_next_state              false
% 2.05/0.98  --bmc1_pre_inst_state                   false
% 2.05/0.98  --bmc1_pre_inst_reach_state             false
% 2.05/0.98  --bmc1_out_unsat_core                   false
% 2.05/0.98  --bmc1_aig_witness_out                  false
% 2.05/0.98  --bmc1_verbose                          false
% 2.05/0.98  --bmc1_dump_clauses_tptp                false
% 2.05/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.05/0.98  --bmc1_dump_file                        -
% 2.05/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.05/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.05/0.98  --bmc1_ucm_extend_mode                  1
% 2.05/0.98  --bmc1_ucm_init_mode                    2
% 2.05/0.98  --bmc1_ucm_cone_mode                    none
% 2.05/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.05/0.98  --bmc1_ucm_relax_model                  4
% 2.05/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.05/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.05/0.98  --bmc1_ucm_layered_model                none
% 2.05/0.98  --bmc1_ucm_max_lemma_size               10
% 2.05/0.98  
% 2.05/0.98  ------ AIG Options
% 2.05/0.98  
% 2.05/0.98  --aig_mode                              false
% 2.05/0.98  
% 2.05/0.98  ------ Instantiation Options
% 2.05/0.98  
% 2.05/0.98  --instantiation_flag                    true
% 2.05/0.98  --inst_sos_flag                         false
% 2.05/0.98  --inst_sos_phase                        true
% 2.05/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.05/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.05/0.98  --inst_lit_sel_side                     num_symb
% 2.05/0.98  --inst_solver_per_active                1400
% 2.05/0.98  --inst_solver_calls_frac                1.
% 2.05/0.98  --inst_passive_queue_type               priority_queues
% 2.05/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.05/0.98  --inst_passive_queues_freq              [25;2]
% 2.05/0.98  --inst_dismatching                      true
% 2.05/0.98  --inst_eager_unprocessed_to_passive     true
% 2.05/0.98  --inst_prop_sim_given                   true
% 2.05/0.98  --inst_prop_sim_new                     false
% 2.05/0.98  --inst_subs_new                         false
% 2.05/0.98  --inst_eq_res_simp                      false
% 2.05/0.98  --inst_subs_given                       false
% 2.05/0.98  --inst_orphan_elimination               true
% 2.05/0.98  --inst_learning_loop_flag               true
% 2.05/0.98  --inst_learning_start                   3000
% 2.05/0.98  --inst_learning_factor                  2
% 2.05/0.98  --inst_start_prop_sim_after_learn       3
% 2.05/0.98  --inst_sel_renew                        solver
% 2.05/0.98  --inst_lit_activity_flag                true
% 2.05/0.98  --inst_restr_to_given                   false
% 2.05/0.98  --inst_activity_threshold               500
% 2.05/0.98  --inst_out_proof                        true
% 2.05/0.98  
% 2.05/0.98  ------ Resolution Options
% 2.05/0.98  
% 2.05/0.98  --resolution_flag                       true
% 2.05/0.98  --res_lit_sel                           adaptive
% 2.05/0.98  --res_lit_sel_side                      none
% 2.05/0.98  --res_ordering                          kbo
% 2.05/0.98  --res_to_prop_solver                    active
% 2.05/0.98  --res_prop_simpl_new                    false
% 2.05/0.98  --res_prop_simpl_given                  true
% 2.05/0.98  --res_passive_queue_type                priority_queues
% 2.05/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.05/0.98  --res_passive_queues_freq               [15;5]
% 2.05/0.98  --res_forward_subs                      full
% 2.05/0.98  --res_backward_subs                     full
% 2.05/0.98  --res_forward_subs_resolution           true
% 2.05/0.98  --res_backward_subs_resolution          true
% 2.05/0.98  --res_orphan_elimination                true
% 2.05/0.98  --res_time_limit                        2.
% 2.05/0.98  --res_out_proof                         true
% 2.05/0.98  
% 2.05/0.98  ------ Superposition Options
% 2.05/0.98  
% 2.05/0.98  --superposition_flag                    true
% 2.05/0.98  --sup_passive_queue_type                priority_queues
% 2.05/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.05/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.05/0.98  --demod_completeness_check              fast
% 2.05/0.98  --demod_use_ground                      true
% 2.05/0.98  --sup_to_prop_solver                    passive
% 2.05/0.98  --sup_prop_simpl_new                    true
% 2.05/0.98  --sup_prop_simpl_given                  true
% 2.05/0.98  --sup_fun_splitting                     false
% 2.05/0.98  --sup_smt_interval                      50000
% 2.05/0.98  
% 2.05/0.98  ------ Superposition Simplification Setup
% 2.05/0.98  
% 2.05/0.98  --sup_indices_passive                   []
% 2.05/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.05/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.05/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.05/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.05/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.05/0.98  --sup_full_bw                           [BwDemod]
% 2.05/0.98  --sup_immed_triv                        [TrivRules]
% 2.05/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.05/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.05/0.98  --sup_immed_bw_main                     []
% 2.05/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.05/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.05/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.05/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.05/0.98  
% 2.05/0.98  ------ Combination Options
% 2.05/0.98  
% 2.05/0.98  --comb_res_mult                         3
% 2.05/0.98  --comb_sup_mult                         2
% 2.05/0.98  --comb_inst_mult                        10
% 2.05/0.98  
% 2.05/0.98  ------ Debug Options
% 2.05/0.98  
% 2.05/0.98  --dbg_backtrace                         false
% 2.05/0.98  --dbg_dump_prop_clauses                 false
% 2.05/0.98  --dbg_dump_prop_clauses_file            -
% 2.05/0.98  --dbg_out_stat                          false
% 2.05/0.98  ------ Parsing...
% 2.05/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.05/0.98  
% 2.05/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 2.05/0.98  
% 2.05/0.98  ------ Preprocessing... gs_s  sp: 3 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.05/0.98  
% 2.05/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.05/0.98  ------ Proving...
% 2.05/0.98  ------ Problem Properties 
% 2.05/0.98  
% 2.05/0.98  
% 2.05/0.98  clauses                                 21
% 2.05/0.98  conjectures                             2
% 2.05/0.98  EPR                                     4
% 2.05/0.98  Horn                                    15
% 2.05/0.98  unary                                   8
% 2.05/0.98  binary                                  4
% 2.05/0.98  lits                                    47
% 2.05/0.98  lits eq                                 13
% 2.05/0.98  fd_pure                                 0
% 2.05/0.98  fd_pseudo                               0
% 2.05/0.98  fd_cond                                 8
% 2.05/0.98  fd_pseudo_cond                          0
% 2.05/0.98  AC symbols                              0
% 2.05/0.98  
% 2.05/0.98  ------ Schedule dynamic 5 is on 
% 2.05/0.98  
% 2.05/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.05/0.98  
% 2.05/0.98  
% 2.05/0.98  ------ 
% 2.05/0.98  Current options:
% 2.05/0.98  ------ 
% 2.05/0.98  
% 2.05/0.98  ------ Input Options
% 2.05/0.98  
% 2.05/0.98  --out_options                           all
% 2.05/0.98  --tptp_safe_out                         true
% 2.05/0.98  --problem_path                          ""
% 2.05/0.98  --include_path                          ""
% 2.05/0.98  --clausifier                            res/vclausify_rel
% 2.05/0.98  --clausifier_options                    --mode clausify
% 2.05/0.98  --stdin                                 false
% 2.05/0.98  --stats_out                             all
% 2.05/0.98  
% 2.05/0.98  ------ General Options
% 2.05/0.98  
% 2.05/0.98  --fof                                   false
% 2.05/0.98  --time_out_real                         305.
% 2.05/0.98  --time_out_virtual                      -1.
% 2.05/0.98  --symbol_type_check                     false
% 2.05/0.98  --clausify_out                          false
% 2.05/0.98  --sig_cnt_out                           false
% 2.05/0.98  --trig_cnt_out                          false
% 2.05/0.98  --trig_cnt_out_tolerance                1.
% 2.05/0.98  --trig_cnt_out_sk_spl                   false
% 2.05/0.98  --abstr_cl_out                          false
% 2.05/0.98  
% 2.05/0.98  ------ Global Options
% 2.05/0.98  
% 2.05/0.98  --schedule                              default
% 2.05/0.98  --add_important_lit                     false
% 2.05/0.98  --prop_solver_per_cl                    1000
% 2.05/0.98  --min_unsat_core                        false
% 2.05/0.98  --soft_assumptions                      false
% 2.05/0.98  --soft_lemma_size                       3
% 2.05/0.98  --prop_impl_unit_size                   0
% 2.05/0.98  --prop_impl_unit                        []
% 2.05/0.98  --share_sel_clauses                     true
% 2.05/0.98  --reset_solvers                         false
% 2.05/0.98  --bc_imp_inh                            [conj_cone]
% 2.05/0.98  --conj_cone_tolerance                   3.
% 2.05/0.98  --extra_neg_conj                        none
% 2.05/0.98  --large_theory_mode                     true
% 2.05/0.98  --prolific_symb_bound                   200
% 2.05/0.98  --lt_threshold                          2000
% 2.05/0.98  --clause_weak_htbl                      true
% 2.05/0.98  --gc_record_bc_elim                     false
% 2.05/0.98  
% 2.05/0.98  ------ Preprocessing Options
% 2.05/0.98  
% 2.05/0.98  --preprocessing_flag                    true
% 2.05/0.98  --time_out_prep_mult                    0.1
% 2.05/0.98  --splitting_mode                        input
% 2.05/0.98  --splitting_grd                         true
% 2.05/0.98  --splitting_cvd                         false
% 2.05/0.98  --splitting_cvd_svl                     false
% 2.05/0.98  --splitting_nvd                         32
% 2.05/0.98  --sub_typing                            true
% 2.05/0.98  --prep_gs_sim                           true
% 2.05/0.98  --prep_unflatten                        true
% 2.05/0.98  --prep_res_sim                          true
% 2.05/0.98  --prep_upred                            true
% 2.05/0.98  --prep_sem_filter                       exhaustive
% 2.05/0.98  --prep_sem_filter_out                   false
% 2.05/0.98  --pred_elim                             true
% 2.05/0.98  --res_sim_input                         true
% 2.05/0.98  --eq_ax_congr_red                       true
% 2.05/0.98  --pure_diseq_elim                       true
% 2.05/0.98  --brand_transform                       false
% 2.05/0.98  --non_eq_to_eq                          false
% 2.05/0.98  --prep_def_merge                        true
% 2.05/0.98  --prep_def_merge_prop_impl              false
% 2.05/0.98  --prep_def_merge_mbd                    true
% 2.05/0.98  --prep_def_merge_tr_red                 false
% 2.05/0.98  --prep_def_merge_tr_cl                  false
% 2.05/0.98  --smt_preprocessing                     true
% 2.05/0.98  --smt_ac_axioms                         fast
% 2.05/0.98  --preprocessed_out                      false
% 2.05/0.98  --preprocessed_stats                    false
% 2.05/0.98  
% 2.05/0.98  ------ Abstraction refinement Options
% 2.05/0.98  
% 2.05/0.98  --abstr_ref                             []
% 2.05/0.98  --abstr_ref_prep                        false
% 2.05/0.98  --abstr_ref_until_sat                   false
% 2.05/0.98  --abstr_ref_sig_restrict                funpre
% 2.05/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.05/0.98  --abstr_ref_under                       []
% 2.05/0.98  
% 2.05/0.98  ------ SAT Options
% 2.05/0.98  
% 2.05/0.98  --sat_mode                              false
% 2.05/0.98  --sat_fm_restart_options                ""
% 2.05/0.98  --sat_gr_def                            false
% 2.05/0.98  --sat_epr_types                         true
% 2.05/0.98  --sat_non_cyclic_types                  false
% 2.05/0.98  --sat_finite_models                     false
% 2.05/0.98  --sat_fm_lemmas                         false
% 2.05/0.98  --sat_fm_prep                           false
% 2.05/0.98  --sat_fm_uc_incr                        true
% 2.05/0.98  --sat_out_model                         small
% 2.05/0.98  --sat_out_clauses                       false
% 2.05/0.98  
% 2.05/0.98  ------ QBF Options
% 2.05/0.98  
% 2.05/0.98  --qbf_mode                              false
% 2.05/0.98  --qbf_elim_univ                         false
% 2.05/0.98  --qbf_dom_inst                          none
% 2.05/0.98  --qbf_dom_pre_inst                      false
% 2.05/0.98  --qbf_sk_in                             false
% 2.05/0.98  --qbf_pred_elim                         true
% 2.05/0.98  --qbf_split                             512
% 2.05/0.98  
% 2.05/0.98  ------ BMC1 Options
% 2.05/0.98  
% 2.05/0.98  --bmc1_incremental                      false
% 2.05/0.98  --bmc1_axioms                           reachable_all
% 2.05/0.98  --bmc1_min_bound                        0
% 2.05/0.98  --bmc1_max_bound                        -1
% 2.05/0.98  --bmc1_max_bound_default                -1
% 2.05/0.98  --bmc1_symbol_reachability              true
% 2.05/0.98  --bmc1_property_lemmas                  false
% 2.05/0.98  --bmc1_k_induction                      false
% 2.05/0.98  --bmc1_non_equiv_states                 false
% 2.05/0.98  --bmc1_deadlock                         false
% 2.05/0.98  --bmc1_ucm                              false
% 2.05/0.98  --bmc1_add_unsat_core                   none
% 2.05/0.98  --bmc1_unsat_core_children              false
% 2.05/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.05/0.98  --bmc1_out_stat                         full
% 2.05/0.98  --bmc1_ground_init                      false
% 2.05/0.98  --bmc1_pre_inst_next_state              false
% 2.05/0.98  --bmc1_pre_inst_state                   false
% 2.05/0.98  --bmc1_pre_inst_reach_state             false
% 2.05/0.98  --bmc1_out_unsat_core                   false
% 2.05/0.98  --bmc1_aig_witness_out                  false
% 2.05/0.98  --bmc1_verbose                          false
% 2.05/0.98  --bmc1_dump_clauses_tptp                false
% 2.05/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.05/0.98  --bmc1_dump_file                        -
% 2.05/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.05/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.05/0.98  --bmc1_ucm_extend_mode                  1
% 2.05/0.98  --bmc1_ucm_init_mode                    2
% 2.05/0.98  --bmc1_ucm_cone_mode                    none
% 2.05/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.05/0.98  --bmc1_ucm_relax_model                  4
% 2.05/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.05/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.05/0.98  --bmc1_ucm_layered_model                none
% 2.05/0.98  --bmc1_ucm_max_lemma_size               10
% 2.05/0.98  
% 2.05/0.98  ------ AIG Options
% 2.05/0.98  
% 2.05/0.98  --aig_mode                              false
% 2.05/0.98  
% 2.05/0.98  ------ Instantiation Options
% 2.05/0.98  
% 2.05/0.98  --instantiation_flag                    true
% 2.05/0.98  --inst_sos_flag                         false
% 2.05/0.98  --inst_sos_phase                        true
% 2.05/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.05/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.05/0.98  --inst_lit_sel_side                     none
% 2.05/0.98  --inst_solver_per_active                1400
% 2.05/0.98  --inst_solver_calls_frac                1.
% 2.05/0.98  --inst_passive_queue_type               priority_queues
% 2.05/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.05/0.98  --inst_passive_queues_freq              [25;2]
% 2.05/0.98  --inst_dismatching                      true
% 2.05/0.98  --inst_eager_unprocessed_to_passive     true
% 2.05/0.98  --inst_prop_sim_given                   true
% 2.05/0.98  --inst_prop_sim_new                     false
% 2.05/0.98  --inst_subs_new                         false
% 2.05/0.98  --inst_eq_res_simp                      false
% 2.05/0.98  --inst_subs_given                       false
% 2.05/0.98  --inst_orphan_elimination               true
% 2.05/0.98  --inst_learning_loop_flag               true
% 2.05/0.98  --inst_learning_start                   3000
% 2.05/0.98  --inst_learning_factor                  2
% 2.05/0.98  --inst_start_prop_sim_after_learn       3
% 2.05/0.98  --inst_sel_renew                        solver
% 2.05/0.98  --inst_lit_activity_flag                true
% 2.05/0.98  --inst_restr_to_given                   false
% 2.05/0.98  --inst_activity_threshold               500
% 2.05/0.98  --inst_out_proof                        true
% 2.05/0.98  
% 2.05/0.98  ------ Resolution Options
% 2.05/0.98  
% 2.05/0.98  --resolution_flag                       false
% 2.05/0.98  --res_lit_sel                           adaptive
% 2.05/0.98  --res_lit_sel_side                      none
% 2.05/0.98  --res_ordering                          kbo
% 2.05/0.98  --res_to_prop_solver                    active
% 2.05/0.98  --res_prop_simpl_new                    false
% 2.05/0.98  --res_prop_simpl_given                  true
% 2.05/0.98  --res_passive_queue_type                priority_queues
% 2.05/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.05/0.98  --res_passive_queues_freq               [15;5]
% 2.05/0.98  --res_forward_subs                      full
% 2.05/0.98  --res_backward_subs                     full
% 2.05/0.98  --res_forward_subs_resolution           true
% 2.05/0.98  --res_backward_subs_resolution          true
% 2.05/0.98  --res_orphan_elimination                true
% 2.05/0.98  --res_time_limit                        2.
% 2.05/0.98  --res_out_proof                         true
% 2.05/0.98  
% 2.05/0.98  ------ Superposition Options
% 2.05/0.98  
% 2.05/0.98  --superposition_flag                    true
% 2.05/0.98  --sup_passive_queue_type                priority_queues
% 2.05/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.05/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.05/0.98  --demod_completeness_check              fast
% 2.05/0.98  --demod_use_ground                      true
% 2.05/0.98  --sup_to_prop_solver                    passive
% 2.05/0.98  --sup_prop_simpl_new                    true
% 2.05/0.98  --sup_prop_simpl_given                  true
% 2.05/0.98  --sup_fun_splitting                     false
% 2.05/0.98  --sup_smt_interval                      50000
% 2.05/0.98  
% 2.05/0.98  ------ Superposition Simplification Setup
% 2.05/0.98  
% 2.05/0.98  --sup_indices_passive                   []
% 2.05/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.05/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.05/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.05/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.05/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.05/0.98  --sup_full_bw                           [BwDemod]
% 2.05/0.98  --sup_immed_triv                        [TrivRules]
% 2.05/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.05/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.05/0.98  --sup_immed_bw_main                     []
% 2.05/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.05/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.05/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.05/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.05/0.98  
% 2.05/0.98  ------ Combination Options
% 2.05/0.98  
% 2.05/0.98  --comb_res_mult                         3
% 2.05/0.98  --comb_sup_mult                         2
% 2.05/0.98  --comb_inst_mult                        10
% 2.05/0.98  
% 2.05/0.98  ------ Debug Options
% 2.05/0.98  
% 2.05/0.98  --dbg_backtrace                         false
% 2.05/0.98  --dbg_dump_prop_clauses                 false
% 2.05/0.98  --dbg_dump_prop_clauses_file            -
% 2.05/0.98  --dbg_out_stat                          false
% 2.05/0.98  
% 2.05/0.98  
% 2.05/0.98  
% 2.05/0.98  
% 2.05/0.98  ------ Proving...
% 2.05/0.98  
% 2.05/0.98  
% 2.05/0.98  % SZS status Theorem for theBenchmark.p
% 2.05/0.98  
% 2.05/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.05/0.98  
% 2.05/0.98  fof(f3,axiom,(
% 2.05/0.98    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 2.05/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.05/0.98  
% 2.05/0.98  fof(f19,plain,(
% 2.05/0.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 2.05/0.98    inference(ennf_transformation,[],[f3])).
% 2.05/0.98  
% 2.05/0.98  fof(f35,plain,(
% 2.05/0.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.05/0.98    introduced(choice_axiom,[])).
% 2.05/0.98  
% 2.05/0.98  fof(f36,plain,(
% 2.05/0.98    ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0)),
% 2.05/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f35])).
% 2.05/0.98  
% 2.05/0.98  fof(f47,plain,(
% 2.05/0.98    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 2.05/0.98    inference(cnf_transformation,[],[f36])).
% 2.05/0.98  
% 2.05/0.98  fof(f9,axiom,(
% 2.05/0.98    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 2.05/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.05/0.98  
% 2.05/0.98  fof(f21,plain,(
% 2.05/0.98    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 2.05/0.98    inference(ennf_transformation,[],[f9])).
% 2.05/0.98  
% 2.05/0.98  fof(f53,plain,(
% 2.05/0.98    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 2.05/0.98    inference(cnf_transformation,[],[f21])).
% 2.05/0.98  
% 2.05/0.98  fof(f13,axiom,(
% 2.05/0.98    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 2.05/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.05/0.98  
% 2.05/0.98  fof(f27,plain,(
% 2.05/0.98    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.05/0.98    inference(ennf_transformation,[],[f13])).
% 2.05/0.98  
% 2.05/0.98  fof(f28,plain,(
% 2.05/0.98    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.05/0.98    inference(flattening,[],[f27])).
% 2.05/0.98  
% 2.05/0.98  fof(f57,plain,(
% 2.05/0.98    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.05/0.98    inference(cnf_transformation,[],[f28])).
% 2.05/0.98  
% 2.05/0.98  fof(f2,axiom,(
% 2.05/0.98    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.05/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.05/0.98  
% 2.05/0.98  fof(f18,plain,(
% 2.05/0.98    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.05/0.98    inference(ennf_transformation,[],[f2])).
% 2.05/0.98  
% 2.05/0.98  fof(f46,plain,(
% 2.05/0.98    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.05/0.98    inference(cnf_transformation,[],[f18])).
% 2.05/0.98  
% 2.05/0.98  fof(f15,axiom,(
% 2.05/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 2.05/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.05/0.98  
% 2.05/0.98  fof(f31,plain,(
% 2.05/0.98    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.05/0.98    inference(ennf_transformation,[],[f15])).
% 2.05/0.98  
% 2.05/0.98  fof(f32,plain,(
% 2.05/0.98    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.05/0.98    inference(flattening,[],[f31])).
% 2.05/0.98  
% 2.05/0.98  fof(f64,plain,(
% 2.05/0.98    ( ! [X0,X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.05/0.98    inference(cnf_transformation,[],[f32])).
% 2.05/0.98  
% 2.05/0.98  fof(f16,conjecture,(
% 2.05/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => ~v3_tex_2(X1,X0)))),
% 2.05/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.05/0.98  
% 2.05/0.98  fof(f17,negated_conjecture,(
% 2.05/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => ~v3_tex_2(X1,X0)))),
% 2.05/0.98    inference(negated_conjecture,[],[f16])).
% 2.05/0.98  
% 2.05/0.98  fof(f33,plain,(
% 2.05/0.98    ? [X0] : (? [X1] : (v3_tex_2(X1,X0) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.05/0.98    inference(ennf_transformation,[],[f17])).
% 2.05/0.98  
% 2.05/0.98  fof(f34,plain,(
% 2.05/0.98    ? [X0] : (? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.05/0.98    inference(flattening,[],[f33])).
% 2.05/0.98  
% 2.05/0.98  fof(f43,plain,(
% 2.05/0.98    ( ! [X0] : (? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => (v3_tex_2(sK3,X0) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(sK3))) )),
% 2.05/0.98    introduced(choice_axiom,[])).
% 2.05/0.99  
% 2.05/0.99  fof(f42,plain,(
% 2.05/0.99    ? [X0] : (? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (v3_tex_2(X1,sK2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) & v1_xboole_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 2.05/0.99    introduced(choice_axiom,[])).
% 2.05/0.99  
% 2.05/0.99  fof(f44,plain,(
% 2.05/0.99    (v3_tex_2(sK3,sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) & v1_xboole_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 2.05/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f34,f43,f42])).
% 2.05/0.99  
% 2.05/0.99  fof(f66,plain,(
% 2.05/0.99    v2_pre_topc(sK2)),
% 2.05/0.99    inference(cnf_transformation,[],[f44])).
% 2.05/0.99  
% 2.05/0.99  fof(f65,plain,(
% 2.05/0.99    ~v2_struct_0(sK2)),
% 2.05/0.99    inference(cnf_transformation,[],[f44])).
% 2.05/0.99  
% 2.05/0.99  fof(f67,plain,(
% 2.05/0.99    l1_pre_topc(sK2)),
% 2.05/0.99    inference(cnf_transformation,[],[f44])).
% 2.05/0.99  
% 2.05/0.99  fof(f8,axiom,(
% 2.05/0.99    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 2.05/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.05/0.99  
% 2.05/0.99  fof(f20,plain,(
% 2.05/0.99    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 2.05/0.99    inference(ennf_transformation,[],[f8])).
% 2.05/0.99  
% 2.05/0.99  fof(f52,plain,(
% 2.05/0.99    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 2.05/0.99    inference(cnf_transformation,[],[f20])).
% 2.05/0.99  
% 2.05/0.99  fof(f68,plain,(
% 2.05/0.99    v1_xboole_0(sK3)),
% 2.05/0.99    inference(cnf_transformation,[],[f44])).
% 2.05/0.99  
% 2.05/0.99  fof(f70,plain,(
% 2.05/0.99    v3_tex_2(sK3,sK2)),
% 2.05/0.99    inference(cnf_transformation,[],[f44])).
% 2.05/0.99  
% 2.05/0.99  fof(f5,axiom,(
% 2.05/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.05/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.05/0.99  
% 2.05/0.99  fof(f49,plain,(
% 2.05/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.05/0.99    inference(cnf_transformation,[],[f5])).
% 2.05/0.99  
% 2.05/0.99  fof(f14,axiom,(
% 2.05/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 2.05/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.05/0.99  
% 2.05/0.99  fof(f29,plain,(
% 2.05/0.99    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.05/0.99    inference(ennf_transformation,[],[f14])).
% 2.05/0.99  
% 2.05/0.99  fof(f30,plain,(
% 2.05/0.99    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.05/0.99    inference(flattening,[],[f29])).
% 2.05/0.99  
% 2.05/0.99  fof(f37,plain,(
% 2.05/0.99    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.05/0.99    inference(nnf_transformation,[],[f30])).
% 2.05/0.99  
% 2.05/0.99  fof(f38,plain,(
% 2.05/0.99    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.05/0.99    inference(flattening,[],[f37])).
% 2.05/0.99  
% 2.05/0.99  fof(f39,plain,(
% 2.05/0.99    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.05/0.99    inference(rectify,[],[f38])).
% 2.05/0.99  
% 2.05/0.99  fof(f40,plain,(
% 2.05/0.99    ! [X1,X0] : (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK1(X0,X1) != X1 & r1_tarski(X1,sK1(X0,X1)) & v2_tex_2(sK1(X0,X1),X0) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.05/0.99    introduced(choice_axiom,[])).
% 2.05/0.99  
% 2.05/0.99  fof(f41,plain,(
% 2.05/0.99    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (sK1(X0,X1) != X1 & r1_tarski(X1,sK1(X0,X1)) & v2_tex_2(sK1(X0,X1),X0) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.05/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f39,f40])).
% 2.05/0.99  
% 2.05/0.99  fof(f59,plain,(
% 2.05/0.99    ( ! [X0,X3,X1] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.05/0.99    inference(cnf_transformation,[],[f41])).
% 2.05/0.99  
% 2.05/0.99  fof(f7,axiom,(
% 2.05/0.99    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.05/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.05/0.99  
% 2.05/0.99  fof(f51,plain,(
% 2.05/0.99    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.05/0.99    inference(cnf_transformation,[],[f7])).
% 2.05/0.99  
% 2.05/0.99  fof(f1,axiom,(
% 2.05/0.99    v1_xboole_0(k1_xboole_0)),
% 2.05/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.05/0.99  
% 2.05/0.99  fof(f45,plain,(
% 2.05/0.99    v1_xboole_0(k1_xboole_0)),
% 2.05/0.99    inference(cnf_transformation,[],[f1])).
% 2.05/0.99  
% 2.05/0.99  fof(f11,axiom,(
% 2.05/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.05/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.05/0.99  
% 2.05/0.99  fof(f24,plain,(
% 2.05/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.05/0.99    inference(ennf_transformation,[],[f11])).
% 2.05/0.99  
% 2.05/0.99  fof(f55,plain,(
% 2.05/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.05/0.99    inference(cnf_transformation,[],[f24])).
% 2.05/0.99  
% 2.05/0.99  fof(f12,axiom,(
% 2.05/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.05/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.05/0.99  
% 2.05/0.99  fof(f25,plain,(
% 2.05/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.05/0.99    inference(ennf_transformation,[],[f12])).
% 2.05/0.99  
% 2.05/0.99  fof(f26,plain,(
% 2.05/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.05/0.99    inference(flattening,[],[f25])).
% 2.05/0.99  
% 2.05/0.99  fof(f56,plain,(
% 2.05/0.99    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.05/0.99    inference(cnf_transformation,[],[f26])).
% 2.05/0.99  
% 2.05/0.99  fof(f4,axiom,(
% 2.05/0.99    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 2.05/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.05/0.99  
% 2.05/0.99  fof(f48,plain,(
% 2.05/0.99    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.05/0.99    inference(cnf_transformation,[],[f4])).
% 2.05/0.99  
% 2.05/0.99  fof(f6,axiom,(
% 2.05/0.99    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 2.05/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.05/0.99  
% 2.05/0.99  fof(f50,plain,(
% 2.05/0.99    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 2.05/0.99    inference(cnf_transformation,[],[f6])).
% 2.05/0.99  
% 2.05/0.99  cnf(c_2,plain,
% 2.05/0.99      ( r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 2.05/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_8,plain,
% 2.05/0.99      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 2.05/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_377,plain,
% 2.05/0.99      ( m1_subset_1(X0,X1)
% 2.05/0.99      | X1 != X2
% 2.05/0.99      | sK0(X2) != X0
% 2.05/0.99      | k1_xboole_0 = X2 ),
% 2.05/0.99      inference(resolution_lifted,[status(thm)],[c_2,c_8]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_378,plain,
% 2.05/0.99      ( m1_subset_1(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 2.05/0.99      inference(unflattening,[status(thm)],[c_377]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1290,plain,
% 2.05/0.99      ( k1_xboole_0 = X0 | m1_subset_1(sK0(X0),X0) = iProver_top ),
% 2.05/0.99      inference(predicate_to_equality,[status(thm)],[c_378]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_12,plain,
% 2.05/0.99      ( ~ m1_subset_1(X0,X1)
% 2.05/0.99      | v1_xboole_0(X1)
% 2.05/0.99      | k6_domain_1(X1,X0) = k1_tarski(X0) ),
% 2.05/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1295,plain,
% 2.05/0.99      ( k6_domain_1(X0,X1) = k1_tarski(X1)
% 2.05/0.99      | m1_subset_1(X1,X0) != iProver_top
% 2.05/0.99      | v1_xboole_0(X0) = iProver_top ),
% 2.05/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_2232,plain,
% 2.05/0.99      ( k6_domain_1(X0,sK0(X0)) = k1_tarski(sK0(X0))
% 2.05/0.99      | k1_xboole_0 = X0
% 2.05/0.99      | v1_xboole_0(X0) = iProver_top ),
% 2.05/0.99      inference(superposition,[status(thm)],[c_1290,c_1295]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1,plain,
% 2.05/0.99      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 2.05/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_2253,plain,
% 2.05/0.99      ( v1_xboole_0(X0)
% 2.05/0.99      | k6_domain_1(X0,sK0(X0)) = k1_tarski(sK0(X0))
% 2.05/0.99      | k1_xboole_0 = X0 ),
% 2.05/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_2232]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_2462,plain,
% 2.05/0.99      ( k1_xboole_0 = X0 | k6_domain_1(X0,sK0(X0)) = k1_tarski(sK0(X0)) ),
% 2.05/0.99      inference(global_propositional_subsumption,
% 2.05/0.99                [status(thm)],
% 2.05/0.99                [c_2232,c_1,c_2253]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_2463,plain,
% 2.05/0.99      ( k6_domain_1(X0,sK0(X0)) = k1_tarski(sK0(X0)) | k1_xboole_0 = X0 ),
% 2.05/0.99      inference(renaming,[status(thm)],[c_2462]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_19,plain,
% 2.05/0.99      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
% 2.05/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.05/0.99      | ~ v2_pre_topc(X0)
% 2.05/0.99      | v2_struct_0(X0)
% 2.05/0.99      | ~ l1_pre_topc(X0) ),
% 2.05/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_24,negated_conjecture,
% 2.05/0.99      ( v2_pre_topc(sK2) ),
% 2.05/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_293,plain,
% 2.05/0.99      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
% 2.05/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.05/0.99      | v2_struct_0(X0)
% 2.05/0.99      | ~ l1_pre_topc(X0)
% 2.05/0.99      | sK2 != X0 ),
% 2.05/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_24]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_294,plain,
% 2.05/0.99      ( v2_tex_2(k6_domain_1(u1_struct_0(sK2),X0),sK2)
% 2.05/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.05/0.99      | v2_struct_0(sK2)
% 2.05/0.99      | ~ l1_pre_topc(sK2) ),
% 2.05/0.99      inference(unflattening,[status(thm)],[c_293]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_25,negated_conjecture,
% 2.05/0.99      ( ~ v2_struct_0(sK2) ),
% 2.05/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_23,negated_conjecture,
% 2.05/0.99      ( l1_pre_topc(sK2) ),
% 2.05/0.99      inference(cnf_transformation,[],[f67]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_298,plain,
% 2.05/0.99      ( v2_tex_2(k6_domain_1(u1_struct_0(sK2),X0),sK2)
% 2.05/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 2.05/0.99      inference(global_propositional_subsumption,
% 2.05/0.99                [status(thm)],
% 2.05/0.99                [c_294,c_25,c_23]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1292,plain,
% 2.05/0.99      ( v2_tex_2(k6_domain_1(u1_struct_0(sK2),X0),sK2) = iProver_top
% 2.05/0.99      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
% 2.05/0.99      inference(predicate_to_equality,[status(thm)],[c_298]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_2466,plain,
% 2.05/0.99      ( u1_struct_0(sK2) = k1_xboole_0
% 2.05/0.99      | v2_tex_2(k1_tarski(sK0(u1_struct_0(sK2))),sK2) = iProver_top
% 2.05/0.99      | m1_subset_1(sK0(u1_struct_0(sK2)),u1_struct_0(sK2)) != iProver_top ),
% 2.05/0.99      inference(superposition,[status(thm)],[c_2463,c_1292]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_7,plain,
% 2.05/0.99      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~ r2_hidden(X0,X1) ),
% 2.05/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_389,plain,
% 2.05/0.99      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
% 2.05/0.99      | X1 != X2
% 2.05/0.99      | sK0(X2) != X0
% 2.05/0.99      | k1_xboole_0 = X2 ),
% 2.05/0.99      inference(resolution_lifted,[status(thm)],[c_2,c_7]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_390,plain,
% 2.05/0.99      ( m1_subset_1(k1_tarski(sK0(X0)),k1_zfmisc_1(X0))
% 2.05/0.99      | k1_xboole_0 = X0 ),
% 2.05/0.99      inference(unflattening,[status(thm)],[c_389]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1289,plain,
% 2.05/0.99      ( k1_xboole_0 = X0
% 2.05/0.99      | m1_subset_1(k1_tarski(sK0(X0)),k1_zfmisc_1(X0)) = iProver_top ),
% 2.05/0.99      inference(predicate_to_equality,[status(thm)],[c_390]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_22,negated_conjecture,
% 2.05/0.99      ( v1_xboole_0(sK3) ),
% 2.05/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1293,plain,
% 2.05/0.99      ( v1_xboole_0(sK3) = iProver_top ),
% 2.05/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1297,plain,
% 2.05/0.99      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 2.05/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1768,plain,
% 2.05/0.99      ( sK3 = k1_xboole_0 ),
% 2.05/0.99      inference(superposition,[status(thm)],[c_1293,c_1297]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_20,negated_conjecture,
% 2.05/0.99      ( v3_tex_2(sK3,sK2) ),
% 2.05/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_4,plain,
% 2.05/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 2.05/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_17,plain,
% 2.05/0.99      ( ~ v2_tex_2(X0,X1)
% 2.05/0.99      | ~ v3_tex_2(X2,X1)
% 2.05/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/0.99      | ~ r1_tarski(X2,X0)
% 2.05/0.99      | ~ l1_pre_topc(X1)
% 2.05/0.99      | X0 = X2 ),
% 2.05/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_514,plain,
% 2.05/0.99      ( ~ v2_tex_2(X0,X1)
% 2.05/0.99      | ~ v3_tex_2(X2,X1)
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/0.99      | ~ r1_tarski(X2,X0)
% 2.05/0.99      | X2 = X0
% 2.05/0.99      | sK2 != X1 ),
% 2.05/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_23]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_515,plain,
% 2.05/0.99      ( ~ v2_tex_2(X0,sK2)
% 2.05/0.99      | ~ v3_tex_2(X1,sK2)
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.05/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.05/0.99      | ~ r1_tarski(X1,X0)
% 2.05/0.99      | X1 = X0 ),
% 2.05/0.99      inference(unflattening,[status(thm)],[c_514]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_641,plain,
% 2.05/0.99      ( ~ v2_tex_2(X0,sK2)
% 2.05/0.99      | ~ v3_tex_2(X1,sK2)
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.05/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.05/0.99      | X0 != X2
% 2.05/0.99      | X0 = X1
% 2.05/0.99      | k1_xboole_0 != X1 ),
% 2.05/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_515]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_642,plain,
% 2.05/0.99      ( ~ v2_tex_2(X0,sK2)
% 2.05/0.99      | ~ v3_tex_2(k1_xboole_0,sK2)
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.05/0.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.05/0.99      | X0 = k1_xboole_0 ),
% 2.05/0.99      inference(unflattening,[status(thm)],[c_641]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_6,plain,
% 2.05/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.05/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_656,plain,
% 2.05/0.99      ( ~ v2_tex_2(X0,sK2)
% 2.05/0.99      | ~ v3_tex_2(k1_xboole_0,sK2)
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.05/0.99      | X0 = k1_xboole_0 ),
% 2.05/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_642,c_6]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_683,plain,
% 2.05/0.99      ( ~ v2_tex_2(X0,sK2)
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.05/0.99      | sK2 != sK2
% 2.05/0.99      | sK3 != k1_xboole_0
% 2.05/0.99      | k1_xboole_0 = X0 ),
% 2.05/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_656]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_820,plain,
% 2.05/0.99      ( ~ v2_tex_2(X0,sK2)
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.05/0.99      | sK3 != k1_xboole_0
% 2.05/0.99      | k1_xboole_0 = X0 ),
% 2.05/0.99      inference(equality_resolution_simp,[status(thm)],[c_683]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1280,plain,
% 2.05/0.99      ( sK3 != k1_xboole_0
% 2.05/0.99      | k1_xboole_0 = X0
% 2.05/0.99      | v2_tex_2(X0,sK2) != iProver_top
% 2.05/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 2.05/0.99      inference(predicate_to_equality,[status(thm)],[c_820]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1772,plain,
% 2.05/0.99      ( k1_xboole_0 = X0
% 2.05/0.99      | k1_xboole_0 != k1_xboole_0
% 2.05/0.99      | v2_tex_2(X0,sK2) != iProver_top
% 2.05/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 2.05/0.99      inference(demodulation,[status(thm)],[c_1768,c_1280]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1779,plain,
% 2.05/0.99      ( k1_xboole_0 = X0
% 2.05/0.99      | v2_tex_2(X0,sK2) != iProver_top
% 2.05/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 2.05/0.99      inference(equality_resolution_simp,[status(thm)],[c_1772]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_2344,plain,
% 2.05/0.99      ( u1_struct_0(sK2) = k1_xboole_0
% 2.05/0.99      | k1_tarski(sK0(u1_struct_0(sK2))) = k1_xboole_0
% 2.05/0.99      | v2_tex_2(k1_tarski(sK0(u1_struct_0(sK2))),sK2) != iProver_top ),
% 2.05/0.99      inference(superposition,[status(thm)],[c_1289,c_1779]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_0,plain,
% 2.05/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 2.05/0.99      inference(cnf_transformation,[],[f45]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_10,plain,
% 2.05/0.99      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 2.05/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_11,plain,
% 2.05/0.99      ( v2_struct_0(X0)
% 2.05/0.99      | ~ l1_struct_0(X0)
% 2.05/0.99      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.05/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_275,plain,
% 2.05/0.99      ( v2_struct_0(X0)
% 2.05/0.99      | ~ l1_pre_topc(X0)
% 2.05/0.99      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.05/0.99      inference(resolution,[status(thm)],[c_10,c_11]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_314,plain,
% 2.05/0.99      ( ~ l1_pre_topc(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK2 != X0 ),
% 2.05/0.99      inference(resolution_lifted,[status(thm)],[c_275,c_25]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_315,plain,
% 2.05/0.99      ( ~ l1_pre_topc(sK2) | ~ v1_xboole_0(u1_struct_0(sK2)) ),
% 2.05/0.99      inference(unflattening,[status(thm)],[c_314]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_317,plain,
% 2.05/0.99      ( ~ v1_xboole_0(u1_struct_0(sK2)) ),
% 2.05/0.99      inference(global_propositional_subsumption,
% 2.05/0.99                [status(thm)],
% 2.05/0.99                [c_315,c_23]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_329,plain,
% 2.05/0.99      ( u1_struct_0(sK2) != k1_xboole_0 ),
% 2.05/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_317]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_2367,plain,
% 2.05/0.99      ( k1_tarski(sK0(u1_struct_0(sK2))) = k1_xboole_0
% 2.05/0.99      | v2_tex_2(k1_tarski(sK0(u1_struct_0(sK2))),sK2) != iProver_top ),
% 2.05/0.99      inference(global_propositional_subsumption,
% 2.05/0.99                [status(thm)],
% 2.05/0.99                [c_2344,c_329]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_3,plain,
% 2.05/0.99      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 2.05/0.99      inference(cnf_transformation,[],[f48]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_5,plain,
% 2.05/0.99      ( k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
% 2.05/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1616,plain,
% 2.05/0.99      ( k1_tarski(X0) != k1_xboole_0 ),
% 2.05/0.99      inference(superposition,[status(thm)],[c_3,c_5]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_2373,plain,
% 2.05/0.99      ( v2_tex_2(k1_tarski(sK0(u1_struct_0(sK2))),sK2) != iProver_top ),
% 2.05/0.99      inference(forward_subsumption_resolution,
% 2.05/0.99                [status(thm)],
% 2.05/0.99                [c_2367,c_1616]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_968,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1494,plain,
% 2.05/0.99      ( X0 != X1 | u1_struct_0(sK2) != X1 | u1_struct_0(sK2) = X0 ),
% 2.05/0.99      inference(instantiation,[status(thm)],[c_968]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1637,plain,
% 2.05/0.99      ( X0 != u1_struct_0(sK2)
% 2.05/0.99      | u1_struct_0(sK2) = X0
% 2.05/0.99      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.05/0.99      inference(instantiation,[status(thm)],[c_1494]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1639,plain,
% 2.05/0.99      ( u1_struct_0(sK2) != u1_struct_0(sK2)
% 2.05/0.99      | u1_struct_0(sK2) = k1_xboole_0
% 2.05/0.99      | k1_xboole_0 != u1_struct_0(sK2) ),
% 2.05/0.99      inference(instantiation,[status(thm)],[c_1637]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_974,plain,
% 2.05/0.99      ( X0 != X1 | u1_struct_0(X0) = u1_struct_0(X1) ),
% 2.05/0.99      theory(equality) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1496,plain,
% 2.05/0.99      ( u1_struct_0(sK2) = u1_struct_0(X0) | sK2 != X0 ),
% 2.05/0.99      inference(instantiation,[status(thm)],[c_974]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1633,plain,
% 2.05/0.99      ( u1_struct_0(sK2) = u1_struct_0(sK2) | sK2 != sK2 ),
% 2.05/0.99      inference(instantiation,[status(thm)],[c_1496]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1576,plain,
% 2.05/0.99      ( m1_subset_1(sK0(u1_struct_0(sK2)),u1_struct_0(sK2))
% 2.05/0.99      | k1_xboole_0 = u1_struct_0(sK2) ),
% 2.05/0.99      inference(instantiation,[status(thm)],[c_378]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1581,plain,
% 2.05/0.99      ( k1_xboole_0 = u1_struct_0(sK2)
% 2.05/0.99      | m1_subset_1(sK0(u1_struct_0(sK2)),u1_struct_0(sK2)) = iProver_top ),
% 2.05/0.99      inference(predicate_to_equality,[status(thm)],[c_1576]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_967,plain,( X0 = X0 ),theory(equality) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1529,plain,
% 2.05/0.99      ( sK2 = sK2 ),
% 2.05/0.99      inference(instantiation,[status(thm)],[c_967]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(contradiction,plain,
% 2.05/0.99      ( $false ),
% 2.05/0.99      inference(minisat,
% 2.05/0.99                [status(thm)],
% 2.05/0.99                [c_2466,c_2373,c_1639,c_1633,c_1581,c_1529,c_329]) ).
% 2.05/0.99  
% 2.05/0.99  
% 2.05/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.05/0.99  
% 2.05/0.99  ------                               Statistics
% 2.05/0.99  
% 2.05/0.99  ------ General
% 2.05/0.99  
% 2.05/0.99  abstr_ref_over_cycles:                  0
% 2.05/0.99  abstr_ref_under_cycles:                 0
% 2.05/0.99  gc_basic_clause_elim:                   0
% 2.05/0.99  forced_gc_time:                         0
% 2.05/0.99  parsing_time:                           0.007
% 2.05/0.99  unif_index_cands_time:                  0.
% 2.05/0.99  unif_index_add_time:                    0.
% 2.05/0.99  orderings_time:                         0.
% 2.05/0.99  out_proof_time:                         0.008
% 2.05/0.99  total_time:                             0.075
% 2.05/0.99  num_of_symbols:                         52
% 2.05/0.99  num_of_terms:                           1700
% 2.05/0.99  
% 2.05/0.99  ------ Preprocessing
% 2.05/0.99  
% 2.05/0.99  num_of_splits:                          3
% 2.05/0.99  num_of_split_atoms:                     1
% 2.05/0.99  num_of_reused_defs:                     2
% 2.05/0.99  num_eq_ax_congr_red:                    12
% 2.05/0.99  num_of_sem_filtered_clauses:            1
% 2.05/0.99  num_of_subtypes:                        0
% 2.05/0.99  monotx_restored_types:                  0
% 2.05/0.99  sat_num_of_epr_types:                   0
% 2.05/0.99  sat_num_of_non_cyclic_types:            0
% 2.05/0.99  sat_guarded_non_collapsed_types:        0
% 2.05/0.99  num_pure_diseq_elim:                    0
% 2.05/0.99  simp_replaced_by:                       0
% 2.05/0.99  res_preprocessed:                       105
% 2.05/0.99  prep_upred:                             0
% 2.05/0.99  prep_unflattend:                        34
% 2.05/0.99  smt_new_axioms:                         0
% 2.05/0.99  pred_elim_cands:                        3
% 2.05/0.99  pred_elim:                              7
% 2.05/0.99  pred_elim_cl:                           8
% 2.05/0.99  pred_elim_cycles:                       11
% 2.05/0.99  merged_defs:                            0
% 2.05/0.99  merged_defs_ncl:                        0
% 2.05/0.99  bin_hyper_res:                          0
% 2.05/0.99  prep_cycles:                            4
% 2.05/0.99  pred_elim_time:                         0.008
% 2.05/0.99  splitting_time:                         0.
% 2.05/0.99  sem_filter_time:                        0.
% 2.05/0.99  monotx_time:                            0.
% 2.05/0.99  subtype_inf_time:                       0.
% 2.05/0.99  
% 2.05/0.99  ------ Problem properties
% 2.05/0.99  
% 2.05/0.99  clauses:                                21
% 2.05/0.99  conjectures:                            2
% 2.05/0.99  epr:                                    4
% 2.05/0.99  horn:                                   15
% 2.05/0.99  ground:                                 8
% 2.05/0.99  unary:                                  8
% 2.05/0.99  binary:                                 4
% 2.05/0.99  lits:                                   47
% 2.05/0.99  lits_eq:                                13
% 2.05/0.99  fd_pure:                                0
% 2.05/0.99  fd_pseudo:                              0
% 2.05/0.99  fd_cond:                                8
% 2.05/0.99  fd_pseudo_cond:                         0
% 2.05/0.99  ac_symbols:                             0
% 2.05/0.99  
% 2.05/0.99  ------ Propositional Solver
% 2.05/0.99  
% 2.05/0.99  prop_solver_calls:                      27
% 2.05/0.99  prop_fast_solver_calls:                 701
% 2.05/0.99  smt_solver_calls:                       0
% 2.05/0.99  smt_fast_solver_calls:                  0
% 2.05/0.99  prop_num_of_clauses:                    692
% 2.05/0.99  prop_preprocess_simplified:             3344
% 2.05/0.99  prop_fo_subsumed:                       17
% 2.05/0.99  prop_solver_time:                       0.
% 2.05/0.99  smt_solver_time:                        0.
% 2.05/0.99  smt_fast_solver_time:                   0.
% 2.05/0.99  prop_fast_solver_time:                  0.
% 2.05/0.99  prop_unsat_core_time:                   0.
% 2.05/0.99  
% 2.05/0.99  ------ QBF
% 2.05/0.99  
% 2.05/0.99  qbf_q_res:                              0
% 2.05/0.99  qbf_num_tautologies:                    0
% 2.05/0.99  qbf_prep_cycles:                        0
% 2.05/0.99  
% 2.05/0.99  ------ BMC1
% 2.05/0.99  
% 2.05/0.99  bmc1_current_bound:                     -1
% 2.05/0.99  bmc1_last_solved_bound:                 -1
% 2.05/0.99  bmc1_unsat_core_size:                   -1
% 2.05/0.99  bmc1_unsat_core_parents_size:           -1
% 2.05/0.99  bmc1_merge_next_fun:                    0
% 2.05/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.05/0.99  
% 2.05/0.99  ------ Instantiation
% 2.05/0.99  
% 2.05/0.99  inst_num_of_clauses:                    209
% 2.05/0.99  inst_num_in_passive:                    50
% 2.05/0.99  inst_num_in_active:                     137
% 2.05/0.99  inst_num_in_unprocessed:                22
% 2.05/0.99  inst_num_of_loops:                      160
% 2.05/0.99  inst_num_of_learning_restarts:          0
% 2.05/0.99  inst_num_moves_active_passive:          20
% 2.05/0.99  inst_lit_activity:                      0
% 2.05/0.99  inst_lit_activity_moves:                0
% 2.05/0.99  inst_num_tautologies:                   0
% 2.05/0.99  inst_num_prop_implied:                  0
% 2.05/0.99  inst_num_existing_simplified:           0
% 2.05/0.99  inst_num_eq_res_simplified:             0
% 2.05/0.99  inst_num_child_elim:                    0
% 2.05/0.99  inst_num_of_dismatching_blockings:      30
% 2.05/0.99  inst_num_of_non_proper_insts:           163
% 2.05/0.99  inst_num_of_duplicates:                 0
% 2.05/0.99  inst_inst_num_from_inst_to_res:         0
% 2.05/0.99  inst_dismatching_checking_time:         0.
% 2.05/0.99  
% 2.05/0.99  ------ Resolution
% 2.05/0.99  
% 2.05/0.99  res_num_of_clauses:                     0
% 2.05/0.99  res_num_in_passive:                     0
% 2.05/0.99  res_num_in_active:                      0
% 2.05/0.99  res_num_of_loops:                       109
% 2.05/0.99  res_forward_subset_subsumed:            18
% 2.05/0.99  res_backward_subset_subsumed:           2
% 2.05/0.99  res_forward_subsumed:                   0
% 2.05/0.99  res_backward_subsumed:                  0
% 2.05/0.99  res_forward_subsumption_resolution:     5
% 2.05/0.99  res_backward_subsumption_resolution:    0
% 2.05/0.99  res_clause_to_clause_subsumption:       71
% 2.05/0.99  res_orphan_elimination:                 0
% 2.05/0.99  res_tautology_del:                      29
% 2.05/0.99  res_num_eq_res_simplified:              1
% 2.05/0.99  res_num_sel_changes:                    0
% 2.05/0.99  res_moves_from_active_to_pass:          0
% 2.05/0.99  
% 2.05/0.99  ------ Superposition
% 2.05/0.99  
% 2.05/0.99  sup_time_total:                         0.
% 2.05/0.99  sup_time_generating:                    0.
% 2.05/0.99  sup_time_sim_full:                      0.
% 2.05/0.99  sup_time_sim_immed:                     0.
% 2.05/0.99  
% 2.05/0.99  sup_num_of_clauses:                     31
% 2.05/0.99  sup_num_in_active:                      25
% 2.05/0.99  sup_num_in_passive:                     6
% 2.05/0.99  sup_num_of_loops:                       30
% 2.05/0.99  sup_fw_superposition:                   10
% 2.05/0.99  sup_bw_superposition:                   11
% 2.05/0.99  sup_immediate_simplified:               1
% 2.05/0.99  sup_given_eliminated:                   0
% 2.05/0.99  comparisons_done:                       0
% 2.05/0.99  comparisons_avoided:                    5
% 2.05/0.99  
% 2.05/0.99  ------ Simplifications
% 2.05/0.99  
% 2.05/0.99  
% 2.05/0.99  sim_fw_subset_subsumed:                 0
% 2.05/0.99  sim_bw_subset_subsumed:                 2
% 2.05/0.99  sim_fw_subsumed:                        1
% 2.05/0.99  sim_bw_subsumed:                        0
% 2.05/0.99  sim_fw_subsumption_res:                 1
% 2.05/0.99  sim_bw_subsumption_res:                 0
% 2.05/0.99  sim_tautology_del:                      1
% 2.05/0.99  sim_eq_tautology_del:                   4
% 2.05/0.99  sim_eq_res_simp:                        1
% 2.05/0.99  sim_fw_demodulated:                     0
% 2.05/0.99  sim_bw_demodulated:                     4
% 2.05/0.99  sim_light_normalised:                   0
% 2.05/0.99  sim_joinable_taut:                      0
% 2.05/0.99  sim_joinable_simp:                      0
% 2.05/0.99  sim_ac_normalised:                      0
% 2.05/0.99  sim_smt_subsumption:                    0
% 2.05/0.99  
%------------------------------------------------------------------------------
