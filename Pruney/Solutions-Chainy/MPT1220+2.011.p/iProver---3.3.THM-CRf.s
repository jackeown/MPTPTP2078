%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:13:26 EST 2020

% Result     : Theorem 3.13s
% Output     : CNFRefutation 3.13s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 327 expanded)
%              Number of clauses        :   75 ( 141 expanded)
%              Number of leaves         :   17 (  57 expanded)
%              Depth                    :   17
%              Number of atoms          :  353 ( 829 expanded)
%              Number of equality atoms :   79 ( 178 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f39])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f71,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f51])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f33])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f64,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f16,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => k2_pre_topc(X0,k2_struct_0(X0)) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => k2_pre_topc(X0,k2_struct_0(X0)) = k2_struct_0(X0) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f32,plain,(
    ? [X0] :
      ( k2_pre_topc(X0,k2_struct_0(X0)) != k2_struct_0(X0)
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f43,plain,
    ( ? [X0] :
        ( k2_pre_topc(X0,k2_struct_0(X0)) != k2_struct_0(X0)
        & l1_pre_topc(X0) )
   => ( k2_pre_topc(sK2,k2_struct_0(sK2)) != k2_struct_0(sK2)
      & l1_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( k2_pre_topc(sK2,k2_struct_0(sK2)) != k2_struct_0(sK2)
    & l1_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f32,f43])).

fof(f68,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => v1_xboole_0(k1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f65,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k3_subset_1(u1_struct_0(X0),k1_struct_0(X0)) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( k3_subset_1(u1_struct_0(X0),k1_struct_0(X0)) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f66,plain,(
    ! [X0] :
      ( k3_subset_1(u1_struct_0(X0),k1_struct_0(X0)) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_xboole_0(X1,X2)
              | ~ r1_tarski(X1,k3_subset_1(X0,X2)) )
            & ( r1_tarski(X1,k3_subset_1(X0,X2))
              | ~ r1_xboole_0(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,k3_subset_1(X0,X2))
      | ~ r1_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f37])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f53,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f63,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f69,plain,(
    k2_pre_topc(sK2,k2_struct_0(sK2)) != k2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_8,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1274,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1280,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_19,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_333,plain,
    ( l1_struct_0(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_24])).

cnf(c_334,plain,
    ( l1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_333])).

cnf(c_20,plain,
    ( ~ l1_struct_0(X0)
    | v1_xboole_0(k1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_14,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_184,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_14])).

cnf(c_185,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_184])).

cnf(c_229,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(bin_hyper_res,[status(thm)],[c_16,c_185])).

cnf(c_314,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | ~ l1_struct_0(X3)
    | k1_struct_0(X3) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_229])).

cnf(c_315,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,k1_struct_0(X2))
    | ~ l1_struct_0(X2) ),
    inference(unflattening,[status(thm)],[c_314])).

cnf(c_384,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,k1_struct_0(X2))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_334,c_315])).

cnf(c_385,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,k1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_384])).

cnf(c_1266,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,k1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_385])).

cnf(c_1721,plain,
    ( r2_hidden(X0,k1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1274,c_1266])).

cnf(c_2484,plain,
    ( r1_tarski(k1_struct_0(sK2),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1280,c_1721])).

cnf(c_21,plain,
    ( ~ l1_struct_0(X0)
    | k3_subset_1(u1_struct_0(X0),k1_struct_0(X0)) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_372,plain,
    ( k3_subset_1(u1_struct_0(X0),k1_struct_0(X0)) = k2_struct_0(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_334])).

cnf(c_373,plain,
    ( k3_subset_1(u1_struct_0(sK2),k1_struct_0(sK2)) = k2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_372])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,X0)
    | r1_tarski(X2,k3_subset_1(X1,X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_226,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X0,X2)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(X0,k3_subset_1(X1,X2)) ),
    inference(bin_hyper_res,[status(thm)],[c_13,c_185])).

cnf(c_594,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_14])).

cnf(c_595,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_594])).

cnf(c_632,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X2)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,k3_subset_1(X2,X1)) ),
    inference(bin_hyper_res,[status(thm)],[c_226,c_595])).

cnf(c_1264,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,k3_subset_1(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_632])).

cnf(c_1624,plain,
    ( r1_xboole_0(X0,k1_struct_0(sK2)) != iProver_top
    | r1_tarski(X0,k2_struct_0(sK2)) = iProver_top
    | r1_tarski(X0,u1_struct_0(sK2)) != iProver_top
    | r1_tarski(k1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_373,c_1264])).

cnf(c_3489,plain,
    ( r1_xboole_0(X0,k1_struct_0(sK2)) != iProver_top
    | r1_tarski(X0,k2_struct_0(sK2)) = iProver_top
    | r1_tarski(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2484,c_1624])).

cnf(c_1435,plain,
    ( r1_tarski(k1_struct_0(sK2),k1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1437,plain,
    ( r1_tarski(k1_struct_0(sK2),k1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1435])).

cnf(c_1552,plain,
    ( r2_hidden(sK0(X0,u1_struct_0(sK2)),X0)
    | r1_tarski(X0,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2334,plain,
    ( r2_hidden(sK0(k1_struct_0(sK2),u1_struct_0(sK2)),k1_struct_0(sK2))
    | r1_tarski(k1_struct_0(sK2),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1552])).

cnf(c_2336,plain,
    ( r2_hidden(sK0(k1_struct_0(sK2),u1_struct_0(sK2)),k1_struct_0(sK2)) = iProver_top
    | r1_tarski(k1_struct_0(sK2),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2334])).

cnf(c_1436,plain,
    ( ~ r2_hidden(X0,k1_struct_0(sK2))
    | ~ r1_tarski(k1_struct_0(sK2),k1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_385])).

cnf(c_2335,plain,
    ( ~ r2_hidden(sK0(k1_struct_0(sK2),u1_struct_0(sK2)),k1_struct_0(sK2))
    | ~ r1_tarski(k1_struct_0(sK2),k1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1436])).

cnf(c_2338,plain,
    ( r2_hidden(sK0(k1_struct_0(sK2),u1_struct_0(sK2)),k1_struct_0(sK2)) != iProver_top
    | r1_tarski(k1_struct_0(sK2),k1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2335])).

cnf(c_4,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1277,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2366,plain,
    ( r1_xboole_0(X0,k1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1277,c_1721])).

cnf(c_3975,plain,
    ( r1_tarski(X0,k2_struct_0(sK2)) = iProver_top
    | r1_tarski(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3489,c_1437,c_1624,c_2336,c_2338,c_2366])).

cnf(c_3983,plain,
    ( r1_tarski(u1_struct_0(sK2),k2_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1274,c_3975])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1510,plain,
    ( ~ r1_tarski(X0,k2_struct_0(sK2))
    | ~ r1_tarski(k2_pre_topc(sK2,k2_struct_0(sK2)),X0)
    | r1_tarski(k2_pre_topc(sK2,k2_struct_0(sK2)),k2_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_3382,plain,
    ( r1_tarski(k2_pre_topc(sK2,k2_struct_0(sK2)),k2_struct_0(sK2))
    | ~ r1_tarski(k2_pre_topc(sK2,k2_struct_0(sK2)),u1_struct_0(sK2))
    | ~ r1_tarski(u1_struct_0(sK2),k2_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1510])).

cnf(c_3386,plain,
    ( r1_tarski(k2_pre_topc(sK2,k2_struct_0(sK2)),k2_struct_0(sK2)) = iProver_top
    | r1_tarski(k2_pre_topc(sK2,k2_struct_0(sK2)),u1_struct_0(sK2)) != iProver_top
    | r1_tarski(u1_struct_0(sK2),k2_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3382])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1554,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(X0,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1880,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(k2_pre_topc(sK2,X0),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1554])).

cnf(c_2052,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK2,k2_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(k2_pre_topc(sK2,k2_struct_0(sK2)),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1880])).

cnf(c_2053,plain,
    ( m1_subset_1(k2_pre_topc(sK2,k2_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(k2_pre_topc(sK2,k2_struct_0(sK2)),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2052])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1420,plain,
    ( ~ r1_tarski(k2_pre_topc(sK2,k2_struct_0(sK2)),k2_struct_0(sK2))
    | ~ r1_tarski(k2_struct_0(sK2),k2_pre_topc(sK2,k2_struct_0(sK2)))
    | k2_pre_topc(sK2,k2_struct_0(sK2)) = k2_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1421,plain,
    ( k2_pre_topc(sK2,k2_struct_0(sK2)) = k2_struct_0(sK2)
    | r1_tarski(k2_pre_topc(sK2,k2_struct_0(sK2)),k2_struct_0(sK2)) != iProver_top
    | r1_tarski(k2_struct_0(sK2),k2_pre_topc(sK2,k2_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1420])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_340,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_24])).

cnf(c_341,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(X0,k2_pre_topc(sK2,X0)) ),
    inference(unflattening,[status(thm)],[c_340])).

cnf(c_1412,plain,
    ( ~ m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(k2_struct_0(sK2),k2_pre_topc(sK2,k2_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_341])).

cnf(c_1416,plain,
    ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(k2_struct_0(sK2),k2_pre_topc(sK2,k2_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1412])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_352,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_24])).

cnf(c_353,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(k2_pre_topc(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unflattening,[status(thm)],[c_352])).

cnf(c_1413,plain,
    ( m1_subset_1(k2_pre_topc(sK2,k2_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_353])).

cnf(c_1414,plain,
    ( m1_subset_1(k2_pre_topc(sK2,k2_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1413])).

cnf(c_18,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_38,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_40,plain,
    ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | l1_struct_0(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_38])).

cnf(c_35,plain,
    ( l1_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_37,plain,
    ( l1_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_35])).

cnf(c_23,negated_conjecture,
    ( k2_pre_topc(sK2,k2_struct_0(sK2)) != k2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_25,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3983,c_3386,c_2053,c_1421,c_1416,c_1414,c_40,c_37,c_23,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:40:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.13/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.13/1.00  
% 3.13/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.13/1.00  
% 3.13/1.00  ------  iProver source info
% 3.13/1.00  
% 3.13/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.13/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.13/1.00  git: non_committed_changes: false
% 3.13/1.00  git: last_make_outside_of_git: false
% 3.13/1.00  
% 3.13/1.00  ------ 
% 3.13/1.00  
% 3.13/1.00  ------ Input Options
% 3.13/1.00  
% 3.13/1.00  --out_options                           all
% 3.13/1.00  --tptp_safe_out                         true
% 3.13/1.00  --problem_path                          ""
% 3.13/1.00  --include_path                          ""
% 3.13/1.00  --clausifier                            res/vclausify_rel
% 3.13/1.00  --clausifier_options                    --mode clausify
% 3.13/1.00  --stdin                                 false
% 3.13/1.00  --stats_out                             all
% 3.13/1.00  
% 3.13/1.00  ------ General Options
% 3.13/1.00  
% 3.13/1.00  --fof                                   false
% 3.13/1.00  --time_out_real                         305.
% 3.13/1.00  --time_out_virtual                      -1.
% 3.13/1.00  --symbol_type_check                     false
% 3.13/1.00  --clausify_out                          false
% 3.13/1.00  --sig_cnt_out                           false
% 3.13/1.00  --trig_cnt_out                          false
% 3.13/1.00  --trig_cnt_out_tolerance                1.
% 3.13/1.00  --trig_cnt_out_sk_spl                   false
% 3.13/1.00  --abstr_cl_out                          false
% 3.13/1.00  
% 3.13/1.00  ------ Global Options
% 3.13/1.00  
% 3.13/1.00  --schedule                              default
% 3.13/1.00  --add_important_lit                     false
% 3.13/1.00  --prop_solver_per_cl                    1000
% 3.13/1.00  --min_unsat_core                        false
% 3.13/1.00  --soft_assumptions                      false
% 3.13/1.00  --soft_lemma_size                       3
% 3.13/1.00  --prop_impl_unit_size                   0
% 3.13/1.00  --prop_impl_unit                        []
% 3.13/1.00  --share_sel_clauses                     true
% 3.13/1.00  --reset_solvers                         false
% 3.13/1.00  --bc_imp_inh                            [conj_cone]
% 3.13/1.00  --conj_cone_tolerance                   3.
% 3.13/1.00  --extra_neg_conj                        none
% 3.13/1.00  --large_theory_mode                     true
% 3.13/1.00  --prolific_symb_bound                   200
% 3.13/1.00  --lt_threshold                          2000
% 3.13/1.00  --clause_weak_htbl                      true
% 3.13/1.00  --gc_record_bc_elim                     false
% 3.13/1.00  
% 3.13/1.00  ------ Preprocessing Options
% 3.13/1.00  
% 3.13/1.00  --preprocessing_flag                    true
% 3.13/1.00  --time_out_prep_mult                    0.1
% 3.13/1.00  --splitting_mode                        input
% 3.13/1.00  --splitting_grd                         true
% 3.13/1.00  --splitting_cvd                         false
% 3.13/1.00  --splitting_cvd_svl                     false
% 3.13/1.00  --splitting_nvd                         32
% 3.13/1.00  --sub_typing                            true
% 3.13/1.00  --prep_gs_sim                           true
% 3.13/1.00  --prep_unflatten                        true
% 3.13/1.00  --prep_res_sim                          true
% 3.13/1.00  --prep_upred                            true
% 3.13/1.00  --prep_sem_filter                       exhaustive
% 3.13/1.00  --prep_sem_filter_out                   false
% 3.13/1.00  --pred_elim                             true
% 3.13/1.00  --res_sim_input                         true
% 3.13/1.00  --eq_ax_congr_red                       true
% 3.13/1.00  --pure_diseq_elim                       true
% 3.13/1.00  --brand_transform                       false
% 3.13/1.00  --non_eq_to_eq                          false
% 3.13/1.00  --prep_def_merge                        true
% 3.13/1.00  --prep_def_merge_prop_impl              false
% 3.13/1.00  --prep_def_merge_mbd                    true
% 3.13/1.00  --prep_def_merge_tr_red                 false
% 3.13/1.00  --prep_def_merge_tr_cl                  false
% 3.13/1.00  --smt_preprocessing                     true
% 3.13/1.00  --smt_ac_axioms                         fast
% 3.13/1.00  --preprocessed_out                      false
% 3.13/1.00  --preprocessed_stats                    false
% 3.13/1.00  
% 3.13/1.00  ------ Abstraction refinement Options
% 3.13/1.00  
% 3.13/1.00  --abstr_ref                             []
% 3.13/1.00  --abstr_ref_prep                        false
% 3.13/1.00  --abstr_ref_until_sat                   false
% 3.13/1.00  --abstr_ref_sig_restrict                funpre
% 3.13/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.13/1.00  --abstr_ref_under                       []
% 3.13/1.00  
% 3.13/1.00  ------ SAT Options
% 3.13/1.00  
% 3.13/1.00  --sat_mode                              false
% 3.13/1.00  --sat_fm_restart_options                ""
% 3.13/1.00  --sat_gr_def                            false
% 3.13/1.00  --sat_epr_types                         true
% 3.13/1.00  --sat_non_cyclic_types                  false
% 3.13/1.00  --sat_finite_models                     false
% 3.13/1.00  --sat_fm_lemmas                         false
% 3.13/1.00  --sat_fm_prep                           false
% 3.13/1.00  --sat_fm_uc_incr                        true
% 3.13/1.00  --sat_out_model                         small
% 3.13/1.00  --sat_out_clauses                       false
% 3.13/1.00  
% 3.13/1.00  ------ QBF Options
% 3.13/1.00  
% 3.13/1.00  --qbf_mode                              false
% 3.13/1.00  --qbf_elim_univ                         false
% 3.13/1.00  --qbf_dom_inst                          none
% 3.13/1.00  --qbf_dom_pre_inst                      false
% 3.13/1.00  --qbf_sk_in                             false
% 3.13/1.00  --qbf_pred_elim                         true
% 3.13/1.00  --qbf_split                             512
% 3.13/1.00  
% 3.13/1.00  ------ BMC1 Options
% 3.13/1.00  
% 3.13/1.00  --bmc1_incremental                      false
% 3.13/1.00  --bmc1_axioms                           reachable_all
% 3.13/1.00  --bmc1_min_bound                        0
% 3.13/1.00  --bmc1_max_bound                        -1
% 3.13/1.00  --bmc1_max_bound_default                -1
% 3.13/1.00  --bmc1_symbol_reachability              true
% 3.13/1.00  --bmc1_property_lemmas                  false
% 3.13/1.00  --bmc1_k_induction                      false
% 3.13/1.00  --bmc1_non_equiv_states                 false
% 3.13/1.00  --bmc1_deadlock                         false
% 3.13/1.00  --bmc1_ucm                              false
% 3.13/1.00  --bmc1_add_unsat_core                   none
% 3.13/1.00  --bmc1_unsat_core_children              false
% 3.13/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.13/1.00  --bmc1_out_stat                         full
% 3.13/1.00  --bmc1_ground_init                      false
% 3.13/1.00  --bmc1_pre_inst_next_state              false
% 3.13/1.00  --bmc1_pre_inst_state                   false
% 3.13/1.00  --bmc1_pre_inst_reach_state             false
% 3.13/1.00  --bmc1_out_unsat_core                   false
% 3.13/1.00  --bmc1_aig_witness_out                  false
% 3.13/1.00  --bmc1_verbose                          false
% 3.13/1.00  --bmc1_dump_clauses_tptp                false
% 3.13/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.13/1.00  --bmc1_dump_file                        -
% 3.13/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.13/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.13/1.00  --bmc1_ucm_extend_mode                  1
% 3.13/1.00  --bmc1_ucm_init_mode                    2
% 3.13/1.00  --bmc1_ucm_cone_mode                    none
% 3.13/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.13/1.00  --bmc1_ucm_relax_model                  4
% 3.13/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.13/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.13/1.00  --bmc1_ucm_layered_model                none
% 3.13/1.00  --bmc1_ucm_max_lemma_size               10
% 3.13/1.00  
% 3.13/1.00  ------ AIG Options
% 3.13/1.00  
% 3.13/1.00  --aig_mode                              false
% 3.13/1.00  
% 3.13/1.00  ------ Instantiation Options
% 3.13/1.00  
% 3.13/1.00  --instantiation_flag                    true
% 3.13/1.00  --inst_sos_flag                         false
% 3.13/1.00  --inst_sos_phase                        true
% 3.13/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.13/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.13/1.00  --inst_lit_sel_side                     num_symb
% 3.13/1.00  --inst_solver_per_active                1400
% 3.13/1.00  --inst_solver_calls_frac                1.
% 3.13/1.00  --inst_passive_queue_type               priority_queues
% 3.13/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.13/1.00  --inst_passive_queues_freq              [25;2]
% 3.13/1.00  --inst_dismatching                      true
% 3.13/1.00  --inst_eager_unprocessed_to_passive     true
% 3.13/1.00  --inst_prop_sim_given                   true
% 3.13/1.00  --inst_prop_sim_new                     false
% 3.13/1.00  --inst_subs_new                         false
% 3.13/1.00  --inst_eq_res_simp                      false
% 3.13/1.00  --inst_subs_given                       false
% 3.13/1.00  --inst_orphan_elimination               true
% 3.13/1.00  --inst_learning_loop_flag               true
% 3.13/1.00  --inst_learning_start                   3000
% 3.13/1.00  --inst_learning_factor                  2
% 3.13/1.00  --inst_start_prop_sim_after_learn       3
% 3.13/1.00  --inst_sel_renew                        solver
% 3.13/1.00  --inst_lit_activity_flag                true
% 3.13/1.00  --inst_restr_to_given                   false
% 3.13/1.00  --inst_activity_threshold               500
% 3.13/1.00  --inst_out_proof                        true
% 3.13/1.00  
% 3.13/1.00  ------ Resolution Options
% 3.13/1.00  
% 3.13/1.00  --resolution_flag                       true
% 3.13/1.00  --res_lit_sel                           adaptive
% 3.13/1.00  --res_lit_sel_side                      none
% 3.13/1.00  --res_ordering                          kbo
% 3.13/1.00  --res_to_prop_solver                    active
% 3.13/1.00  --res_prop_simpl_new                    false
% 3.13/1.00  --res_prop_simpl_given                  true
% 3.13/1.00  --res_passive_queue_type                priority_queues
% 3.13/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.13/1.00  --res_passive_queues_freq               [15;5]
% 3.13/1.00  --res_forward_subs                      full
% 3.13/1.00  --res_backward_subs                     full
% 3.13/1.00  --res_forward_subs_resolution           true
% 3.13/1.00  --res_backward_subs_resolution          true
% 3.13/1.00  --res_orphan_elimination                true
% 3.13/1.00  --res_time_limit                        2.
% 3.13/1.00  --res_out_proof                         true
% 3.13/1.00  
% 3.13/1.00  ------ Superposition Options
% 3.13/1.00  
% 3.13/1.00  --superposition_flag                    true
% 3.13/1.00  --sup_passive_queue_type                priority_queues
% 3.13/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.13/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.13/1.00  --demod_completeness_check              fast
% 3.13/1.00  --demod_use_ground                      true
% 3.13/1.00  --sup_to_prop_solver                    passive
% 3.13/1.00  --sup_prop_simpl_new                    true
% 3.13/1.00  --sup_prop_simpl_given                  true
% 3.13/1.00  --sup_fun_splitting                     false
% 3.13/1.00  --sup_smt_interval                      50000
% 3.13/1.00  
% 3.13/1.00  ------ Superposition Simplification Setup
% 3.13/1.00  
% 3.13/1.00  --sup_indices_passive                   []
% 3.13/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.13/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.13/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.13/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.13/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.13/1.00  --sup_full_bw                           [BwDemod]
% 3.13/1.00  --sup_immed_triv                        [TrivRules]
% 3.13/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.13/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.13/1.00  --sup_immed_bw_main                     []
% 3.13/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.13/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.13/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.13/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.13/1.00  
% 3.13/1.00  ------ Combination Options
% 3.13/1.00  
% 3.13/1.00  --comb_res_mult                         3
% 3.13/1.00  --comb_sup_mult                         2
% 3.13/1.00  --comb_inst_mult                        10
% 3.13/1.00  
% 3.13/1.00  ------ Debug Options
% 3.13/1.00  
% 3.13/1.00  --dbg_backtrace                         false
% 3.13/1.00  --dbg_dump_prop_clauses                 false
% 3.13/1.00  --dbg_dump_prop_clauses_file            -
% 3.13/1.00  --dbg_out_stat                          false
% 3.13/1.00  ------ Parsing...
% 3.13/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.13/1.00  
% 3.13/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.13/1.00  
% 3.13/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.13/1.00  
% 3.13/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.13/1.00  ------ Proving...
% 3.13/1.00  ------ Problem Properties 
% 3.13/1.00  
% 3.13/1.00  
% 3.13/1.00  clauses                                 21
% 3.13/1.00  conjectures                             1
% 3.13/1.00  EPR                                     5
% 3.13/1.00  Horn                                    18
% 3.13/1.00  unary                                   6
% 3.13/1.00  binary                                  9
% 3.13/1.00  lits                                    44
% 3.13/1.00  lits eq                                 4
% 3.13/1.00  fd_pure                                 0
% 3.13/1.00  fd_pseudo                               0
% 3.13/1.00  fd_cond                                 0
% 3.13/1.00  fd_pseudo_cond                          1
% 3.13/1.00  AC symbols                              0
% 3.13/1.00  
% 3.13/1.00  ------ Schedule dynamic 5 is on 
% 3.13/1.00  
% 3.13/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.13/1.00  
% 3.13/1.00  
% 3.13/1.00  ------ 
% 3.13/1.00  Current options:
% 3.13/1.00  ------ 
% 3.13/1.00  
% 3.13/1.00  ------ Input Options
% 3.13/1.00  
% 3.13/1.00  --out_options                           all
% 3.13/1.00  --tptp_safe_out                         true
% 3.13/1.00  --problem_path                          ""
% 3.13/1.00  --include_path                          ""
% 3.13/1.00  --clausifier                            res/vclausify_rel
% 3.13/1.00  --clausifier_options                    --mode clausify
% 3.13/1.00  --stdin                                 false
% 3.13/1.00  --stats_out                             all
% 3.13/1.00  
% 3.13/1.00  ------ General Options
% 3.13/1.00  
% 3.13/1.00  --fof                                   false
% 3.13/1.00  --time_out_real                         305.
% 3.13/1.00  --time_out_virtual                      -1.
% 3.13/1.00  --symbol_type_check                     false
% 3.13/1.00  --clausify_out                          false
% 3.13/1.00  --sig_cnt_out                           false
% 3.13/1.00  --trig_cnt_out                          false
% 3.13/1.00  --trig_cnt_out_tolerance                1.
% 3.13/1.00  --trig_cnt_out_sk_spl                   false
% 3.13/1.00  --abstr_cl_out                          false
% 3.13/1.00  
% 3.13/1.00  ------ Global Options
% 3.13/1.00  
% 3.13/1.00  --schedule                              default
% 3.13/1.00  --add_important_lit                     false
% 3.13/1.00  --prop_solver_per_cl                    1000
% 3.13/1.00  --min_unsat_core                        false
% 3.13/1.00  --soft_assumptions                      false
% 3.13/1.00  --soft_lemma_size                       3
% 3.13/1.00  --prop_impl_unit_size                   0
% 3.13/1.00  --prop_impl_unit                        []
% 3.13/1.00  --share_sel_clauses                     true
% 3.13/1.00  --reset_solvers                         false
% 3.13/1.00  --bc_imp_inh                            [conj_cone]
% 3.13/1.00  --conj_cone_tolerance                   3.
% 3.13/1.00  --extra_neg_conj                        none
% 3.13/1.00  --large_theory_mode                     true
% 3.13/1.00  --prolific_symb_bound                   200
% 3.13/1.00  --lt_threshold                          2000
% 3.13/1.00  --clause_weak_htbl                      true
% 3.13/1.00  --gc_record_bc_elim                     false
% 3.13/1.00  
% 3.13/1.00  ------ Preprocessing Options
% 3.13/1.00  
% 3.13/1.00  --preprocessing_flag                    true
% 3.13/1.00  --time_out_prep_mult                    0.1
% 3.13/1.00  --splitting_mode                        input
% 3.13/1.00  --splitting_grd                         true
% 3.13/1.00  --splitting_cvd                         false
% 3.13/1.00  --splitting_cvd_svl                     false
% 3.13/1.00  --splitting_nvd                         32
% 3.13/1.00  --sub_typing                            true
% 3.13/1.00  --prep_gs_sim                           true
% 3.13/1.00  --prep_unflatten                        true
% 3.13/1.00  --prep_res_sim                          true
% 3.13/1.00  --prep_upred                            true
% 3.13/1.00  --prep_sem_filter                       exhaustive
% 3.13/1.00  --prep_sem_filter_out                   false
% 3.13/1.00  --pred_elim                             true
% 3.13/1.00  --res_sim_input                         true
% 3.13/1.00  --eq_ax_congr_red                       true
% 3.13/1.00  --pure_diseq_elim                       true
% 3.13/1.00  --brand_transform                       false
% 3.13/1.00  --non_eq_to_eq                          false
% 3.13/1.00  --prep_def_merge                        true
% 3.13/1.00  --prep_def_merge_prop_impl              false
% 3.13/1.00  --prep_def_merge_mbd                    true
% 3.13/1.00  --prep_def_merge_tr_red                 false
% 3.13/1.00  --prep_def_merge_tr_cl                  false
% 3.13/1.00  --smt_preprocessing                     true
% 3.13/1.00  --smt_ac_axioms                         fast
% 3.13/1.00  --preprocessed_out                      false
% 3.13/1.00  --preprocessed_stats                    false
% 3.13/1.00  
% 3.13/1.00  ------ Abstraction refinement Options
% 3.13/1.00  
% 3.13/1.00  --abstr_ref                             []
% 3.13/1.00  --abstr_ref_prep                        false
% 3.13/1.00  --abstr_ref_until_sat                   false
% 3.13/1.00  --abstr_ref_sig_restrict                funpre
% 3.13/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.13/1.00  --abstr_ref_under                       []
% 3.13/1.00  
% 3.13/1.00  ------ SAT Options
% 3.13/1.00  
% 3.13/1.00  --sat_mode                              false
% 3.13/1.00  --sat_fm_restart_options                ""
% 3.13/1.00  --sat_gr_def                            false
% 3.13/1.00  --sat_epr_types                         true
% 3.13/1.00  --sat_non_cyclic_types                  false
% 3.13/1.00  --sat_finite_models                     false
% 3.13/1.00  --sat_fm_lemmas                         false
% 3.13/1.00  --sat_fm_prep                           false
% 3.13/1.00  --sat_fm_uc_incr                        true
% 3.13/1.00  --sat_out_model                         small
% 3.13/1.00  --sat_out_clauses                       false
% 3.13/1.00  
% 3.13/1.00  ------ QBF Options
% 3.13/1.00  
% 3.13/1.00  --qbf_mode                              false
% 3.13/1.00  --qbf_elim_univ                         false
% 3.13/1.00  --qbf_dom_inst                          none
% 3.13/1.00  --qbf_dom_pre_inst                      false
% 3.13/1.00  --qbf_sk_in                             false
% 3.13/1.00  --qbf_pred_elim                         true
% 3.13/1.00  --qbf_split                             512
% 3.13/1.00  
% 3.13/1.00  ------ BMC1 Options
% 3.13/1.00  
% 3.13/1.00  --bmc1_incremental                      false
% 3.13/1.00  --bmc1_axioms                           reachable_all
% 3.13/1.00  --bmc1_min_bound                        0
% 3.13/1.00  --bmc1_max_bound                        -1
% 3.13/1.00  --bmc1_max_bound_default                -1
% 3.13/1.00  --bmc1_symbol_reachability              true
% 3.13/1.00  --bmc1_property_lemmas                  false
% 3.13/1.00  --bmc1_k_induction                      false
% 3.13/1.00  --bmc1_non_equiv_states                 false
% 3.13/1.00  --bmc1_deadlock                         false
% 3.13/1.00  --bmc1_ucm                              false
% 3.13/1.00  --bmc1_add_unsat_core                   none
% 3.13/1.00  --bmc1_unsat_core_children              false
% 3.13/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.13/1.00  --bmc1_out_stat                         full
% 3.13/1.00  --bmc1_ground_init                      false
% 3.13/1.00  --bmc1_pre_inst_next_state              false
% 3.13/1.00  --bmc1_pre_inst_state                   false
% 3.13/1.00  --bmc1_pre_inst_reach_state             false
% 3.13/1.00  --bmc1_out_unsat_core                   false
% 3.13/1.00  --bmc1_aig_witness_out                  false
% 3.13/1.00  --bmc1_verbose                          false
% 3.13/1.00  --bmc1_dump_clauses_tptp                false
% 3.13/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.13/1.00  --bmc1_dump_file                        -
% 3.13/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.13/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.13/1.00  --bmc1_ucm_extend_mode                  1
% 3.13/1.00  --bmc1_ucm_init_mode                    2
% 3.13/1.00  --bmc1_ucm_cone_mode                    none
% 3.13/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.13/1.00  --bmc1_ucm_relax_model                  4
% 3.13/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.13/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.13/1.00  --bmc1_ucm_layered_model                none
% 3.13/1.00  --bmc1_ucm_max_lemma_size               10
% 3.13/1.00  
% 3.13/1.00  ------ AIG Options
% 3.13/1.00  
% 3.13/1.00  --aig_mode                              false
% 3.13/1.00  
% 3.13/1.00  ------ Instantiation Options
% 3.13/1.00  
% 3.13/1.00  --instantiation_flag                    true
% 3.13/1.00  --inst_sos_flag                         false
% 3.13/1.00  --inst_sos_phase                        true
% 3.13/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.13/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.13/1.00  --inst_lit_sel_side                     none
% 3.13/1.00  --inst_solver_per_active                1400
% 3.13/1.00  --inst_solver_calls_frac                1.
% 3.13/1.00  --inst_passive_queue_type               priority_queues
% 3.13/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.13/1.00  --inst_passive_queues_freq              [25;2]
% 3.13/1.00  --inst_dismatching                      true
% 3.13/1.00  --inst_eager_unprocessed_to_passive     true
% 3.13/1.00  --inst_prop_sim_given                   true
% 3.13/1.00  --inst_prop_sim_new                     false
% 3.13/1.00  --inst_subs_new                         false
% 3.13/1.00  --inst_eq_res_simp                      false
% 3.13/1.00  --inst_subs_given                       false
% 3.13/1.00  --inst_orphan_elimination               true
% 3.13/1.00  --inst_learning_loop_flag               true
% 3.13/1.00  --inst_learning_start                   3000
% 3.13/1.00  --inst_learning_factor                  2
% 3.13/1.00  --inst_start_prop_sim_after_learn       3
% 3.13/1.00  --inst_sel_renew                        solver
% 3.13/1.00  --inst_lit_activity_flag                true
% 3.13/1.00  --inst_restr_to_given                   false
% 3.13/1.00  --inst_activity_threshold               500
% 3.13/1.00  --inst_out_proof                        true
% 3.13/1.00  
% 3.13/1.00  ------ Resolution Options
% 3.13/1.00  
% 3.13/1.00  --resolution_flag                       false
% 3.13/1.00  --res_lit_sel                           adaptive
% 3.13/1.00  --res_lit_sel_side                      none
% 3.13/1.00  --res_ordering                          kbo
% 3.13/1.00  --res_to_prop_solver                    active
% 3.13/1.00  --res_prop_simpl_new                    false
% 3.13/1.00  --res_prop_simpl_given                  true
% 3.13/1.00  --res_passive_queue_type                priority_queues
% 3.13/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.13/1.00  --res_passive_queues_freq               [15;5]
% 3.13/1.00  --res_forward_subs                      full
% 3.13/1.00  --res_backward_subs                     full
% 3.13/1.00  --res_forward_subs_resolution           true
% 3.13/1.00  --res_backward_subs_resolution          true
% 3.13/1.00  --res_orphan_elimination                true
% 3.13/1.00  --res_time_limit                        2.
% 3.13/1.00  --res_out_proof                         true
% 3.13/1.00  
% 3.13/1.00  ------ Superposition Options
% 3.13/1.00  
% 3.13/1.00  --superposition_flag                    true
% 3.13/1.00  --sup_passive_queue_type                priority_queues
% 3.13/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.13/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.13/1.00  --demod_completeness_check              fast
% 3.13/1.00  --demod_use_ground                      true
% 3.13/1.00  --sup_to_prop_solver                    passive
% 3.13/1.00  --sup_prop_simpl_new                    true
% 3.13/1.00  --sup_prop_simpl_given                  true
% 3.13/1.00  --sup_fun_splitting                     false
% 3.13/1.00  --sup_smt_interval                      50000
% 3.13/1.00  
% 3.13/1.00  ------ Superposition Simplification Setup
% 3.13/1.00  
% 3.13/1.00  --sup_indices_passive                   []
% 3.13/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.13/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.13/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.13/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.13/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.13/1.00  --sup_full_bw                           [BwDemod]
% 3.13/1.00  --sup_immed_triv                        [TrivRules]
% 3.13/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.13/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.13/1.00  --sup_immed_bw_main                     []
% 3.13/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.13/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.13/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.13/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.13/1.00  
% 3.13/1.00  ------ Combination Options
% 3.13/1.00  
% 3.13/1.00  --comb_res_mult                         3
% 3.13/1.00  --comb_sup_mult                         2
% 3.13/1.00  --comb_inst_mult                        10
% 3.13/1.00  
% 3.13/1.00  ------ Debug Options
% 3.13/1.00  
% 3.13/1.00  --dbg_backtrace                         false
% 3.13/1.00  --dbg_dump_prop_clauses                 false
% 3.13/1.00  --dbg_dump_prop_clauses_file            -
% 3.13/1.00  --dbg_out_stat                          false
% 3.13/1.00  
% 3.13/1.00  
% 3.13/1.00  
% 3.13/1.00  
% 3.13/1.00  ------ Proving...
% 3.13/1.00  
% 3.13/1.00  
% 3.13/1.00  % SZS status Theorem for theBenchmark.p
% 3.13/1.00  
% 3.13/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.13/1.00  
% 3.13/1.00  fof(f3,axiom,(
% 3.13/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.13/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f39,plain,(
% 3.13/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.13/1.00    inference(nnf_transformation,[],[f3])).
% 3.13/1.00  
% 3.13/1.00  fof(f40,plain,(
% 3.13/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.13/1.00    inference(flattening,[],[f39])).
% 3.13/1.00  
% 3.13/1.00  fof(f51,plain,(
% 3.13/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.13/1.00    inference(cnf_transformation,[],[f40])).
% 3.13/1.00  
% 3.13/1.00  fof(f71,plain,(
% 3.13/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.13/1.00    inference(equality_resolution,[],[f51])).
% 3.13/1.00  
% 3.13/1.00  fof(f1,axiom,(
% 3.13/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.13/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f19,plain,(
% 3.13/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.13/1.00    inference(ennf_transformation,[],[f1])).
% 3.13/1.00  
% 3.13/1.00  fof(f33,plain,(
% 3.13/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.13/1.00    inference(nnf_transformation,[],[f19])).
% 3.13/1.00  
% 3.13/1.00  fof(f34,plain,(
% 3.13/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.13/1.00    inference(rectify,[],[f33])).
% 3.13/1.00  
% 3.13/1.00  fof(f35,plain,(
% 3.13/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.13/1.00    introduced(choice_axiom,[])).
% 3.13/1.00  
% 3.13/1.00  fof(f36,plain,(
% 3.13/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.13/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).
% 3.13/1.00  
% 3.13/1.00  fof(f46,plain,(
% 3.13/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.13/1.00    inference(cnf_transformation,[],[f36])).
% 3.13/1.00  
% 3.13/1.00  fof(f12,axiom,(
% 3.13/1.00    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.13/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f28,plain,(
% 3.13/1.00    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.13/1.00    inference(ennf_transformation,[],[f12])).
% 3.13/1.00  
% 3.13/1.00  fof(f64,plain,(
% 3.13/1.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.13/1.00    inference(cnf_transformation,[],[f28])).
% 3.13/1.00  
% 3.13/1.00  fof(f16,conjecture,(
% 3.13/1.00    ! [X0] : (l1_pre_topc(X0) => k2_pre_topc(X0,k2_struct_0(X0)) = k2_struct_0(X0))),
% 3.13/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f17,negated_conjecture,(
% 3.13/1.00    ~! [X0] : (l1_pre_topc(X0) => k2_pre_topc(X0,k2_struct_0(X0)) = k2_struct_0(X0))),
% 3.13/1.00    inference(negated_conjecture,[],[f16])).
% 3.13/1.00  
% 3.13/1.00  fof(f32,plain,(
% 3.13/1.00    ? [X0] : (k2_pre_topc(X0,k2_struct_0(X0)) != k2_struct_0(X0) & l1_pre_topc(X0))),
% 3.13/1.00    inference(ennf_transformation,[],[f17])).
% 3.13/1.00  
% 3.13/1.00  fof(f43,plain,(
% 3.13/1.00    ? [X0] : (k2_pre_topc(X0,k2_struct_0(X0)) != k2_struct_0(X0) & l1_pre_topc(X0)) => (k2_pre_topc(sK2,k2_struct_0(sK2)) != k2_struct_0(sK2) & l1_pre_topc(sK2))),
% 3.13/1.00    introduced(choice_axiom,[])).
% 3.13/1.00  
% 3.13/1.00  fof(f44,plain,(
% 3.13/1.00    k2_pre_topc(sK2,k2_struct_0(sK2)) != k2_struct_0(sK2) & l1_pre_topc(sK2)),
% 3.13/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f32,f43])).
% 3.13/1.00  
% 3.13/1.00  fof(f68,plain,(
% 3.13/1.00    l1_pre_topc(sK2)),
% 3.13/1.00    inference(cnf_transformation,[],[f44])).
% 3.13/1.00  
% 3.13/1.00  fof(f13,axiom,(
% 3.13/1.00    ! [X0] : (l1_struct_0(X0) => v1_xboole_0(k1_struct_0(X0)))),
% 3.13/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f29,plain,(
% 3.13/1.00    ! [X0] : (v1_xboole_0(k1_struct_0(X0)) | ~l1_struct_0(X0))),
% 3.13/1.00    inference(ennf_transformation,[],[f13])).
% 3.13/1.00  
% 3.13/1.00  fof(f65,plain,(
% 3.13/1.00    ( ! [X0] : (v1_xboole_0(k1_struct_0(X0)) | ~l1_struct_0(X0)) )),
% 3.13/1.00    inference(cnf_transformation,[],[f29])).
% 3.13/1.00  
% 3.13/1.00  fof(f9,axiom,(
% 3.13/1.00    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 3.13/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f24,plain,(
% 3.13/1.00    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.13/1.00    inference(ennf_transformation,[],[f9])).
% 3.13/1.00  
% 3.13/1.00  fof(f61,plain,(
% 3.13/1.00    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.13/1.00    inference(cnf_transformation,[],[f24])).
% 3.13/1.00  
% 3.13/1.00  fof(f8,axiom,(
% 3.13/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.13/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f42,plain,(
% 3.13/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.13/1.00    inference(nnf_transformation,[],[f8])).
% 3.13/1.00  
% 3.13/1.00  fof(f60,plain,(
% 3.13/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.13/1.00    inference(cnf_transformation,[],[f42])).
% 3.13/1.00  
% 3.13/1.00  fof(f14,axiom,(
% 3.13/1.00    ! [X0] : (l1_struct_0(X0) => k3_subset_1(u1_struct_0(X0),k1_struct_0(X0)) = k2_struct_0(X0))),
% 3.13/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f30,plain,(
% 3.13/1.00    ! [X0] : (k3_subset_1(u1_struct_0(X0),k1_struct_0(X0)) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 3.13/1.00    inference(ennf_transformation,[],[f14])).
% 3.13/1.00  
% 3.13/1.00  fof(f66,plain,(
% 3.13/1.00    ( ! [X0] : (k3_subset_1(u1_struct_0(X0),k1_struct_0(X0)) = k2_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.13/1.00    inference(cnf_transformation,[],[f30])).
% 3.13/1.00  
% 3.13/1.00  fof(f7,axiom,(
% 3.13/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2)))))),
% 3.13/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f23,plain,(
% 3.13/1.00    ! [X0,X1] : (! [X2] : ((r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.13/1.00    inference(ennf_transformation,[],[f7])).
% 3.13/1.00  
% 3.13/1.00  fof(f41,plain,(
% 3.13/1.00    ! [X0,X1] : (! [X2] : (((r1_xboole_0(X1,X2) | ~r1_tarski(X1,k3_subset_1(X0,X2))) & (r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_xboole_0(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.13/1.00    inference(nnf_transformation,[],[f23])).
% 3.13/1.00  
% 3.13/1.00  fof(f57,plain,(
% 3.13/1.00    ( ! [X2,X0,X1] : (r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.13/1.00    inference(cnf_transformation,[],[f41])).
% 3.13/1.00  
% 3.13/1.00  fof(f2,axiom,(
% 3.13/1.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.13/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f18,plain,(
% 3.13/1.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.13/1.00    inference(rectify,[],[f2])).
% 3.13/1.00  
% 3.13/1.00  fof(f20,plain,(
% 3.13/1.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 3.13/1.00    inference(ennf_transformation,[],[f18])).
% 3.13/1.00  
% 3.13/1.00  fof(f37,plain,(
% 3.13/1.00    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 3.13/1.00    introduced(choice_axiom,[])).
% 3.13/1.00  
% 3.13/1.00  fof(f38,plain,(
% 3.13/1.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 3.13/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f37])).
% 3.13/1.00  
% 3.13/1.00  fof(f49,plain,(
% 3.13/1.00    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 3.13/1.00    inference(cnf_transformation,[],[f38])).
% 3.13/1.00  
% 3.13/1.00  fof(f4,axiom,(
% 3.13/1.00    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.13/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f21,plain,(
% 3.13/1.00    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.13/1.00    inference(ennf_transformation,[],[f4])).
% 3.13/1.00  
% 3.13/1.00  fof(f22,plain,(
% 3.13/1.00    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.13/1.00    inference(flattening,[],[f21])).
% 3.13/1.00  
% 3.13/1.00  fof(f54,plain,(
% 3.13/1.00    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 3.13/1.00    inference(cnf_transformation,[],[f22])).
% 3.13/1.00  
% 3.13/1.00  fof(f59,plain,(
% 3.13/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.13/1.00    inference(cnf_transformation,[],[f42])).
% 3.13/1.00  
% 3.13/1.00  fof(f53,plain,(
% 3.13/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.13/1.00    inference(cnf_transformation,[],[f40])).
% 3.13/1.00  
% 3.13/1.00  fof(f15,axiom,(
% 3.13/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 3.13/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f31,plain,(
% 3.13/1.00    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.13/1.00    inference(ennf_transformation,[],[f15])).
% 3.13/1.00  
% 3.13/1.00  fof(f67,plain,(
% 3.13/1.00    ( ! [X0,X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.13/1.00    inference(cnf_transformation,[],[f31])).
% 3.13/1.00  
% 3.13/1.00  fof(f10,axiom,(
% 3.13/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.13/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f25,plain,(
% 3.13/1.00    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.13/1.00    inference(ennf_transformation,[],[f10])).
% 3.13/1.00  
% 3.13/1.00  fof(f26,plain,(
% 3.13/1.00    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.13/1.00    inference(flattening,[],[f25])).
% 3.13/1.00  
% 3.13/1.00  fof(f62,plain,(
% 3.13/1.00    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.13/1.00    inference(cnf_transformation,[],[f26])).
% 3.13/1.00  
% 3.13/1.00  fof(f11,axiom,(
% 3.13/1.00    ! [X0] : (l1_struct_0(X0) => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.13/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f27,plain,(
% 3.13/1.00    ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0))),
% 3.13/1.00    inference(ennf_transformation,[],[f11])).
% 3.13/1.00  
% 3.13/1.00  fof(f63,plain,(
% 3.13/1.00    ( ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0)) )),
% 3.13/1.00    inference(cnf_transformation,[],[f27])).
% 3.13/1.00  
% 3.13/1.00  fof(f69,plain,(
% 3.13/1.00    k2_pre_topc(sK2,k2_struct_0(sK2)) != k2_struct_0(sK2)),
% 3.13/1.00    inference(cnf_transformation,[],[f44])).
% 3.13/1.00  
% 3.13/1.00  cnf(c_8,plain,
% 3.13/1.00      ( r1_tarski(X0,X0) ),
% 3.13/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1274,plain,
% 3.13/1.00      ( r1_tarski(X0,X0) = iProver_top ),
% 3.13/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1,plain,
% 3.13/1.00      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.13/1.00      inference(cnf_transformation,[],[f46]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1280,plain,
% 3.13/1.00      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 3.13/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.13/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_19,plain,
% 3.13/1.00      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 3.13/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_24,negated_conjecture,
% 3.13/1.00      ( l1_pre_topc(sK2) ),
% 3.13/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_333,plain,
% 3.13/1.00      ( l1_struct_0(X0) | sK2 != X0 ),
% 3.13/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_24]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_334,plain,
% 3.13/1.00      ( l1_struct_0(sK2) ),
% 3.13/1.00      inference(unflattening,[status(thm)],[c_333]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_20,plain,
% 3.13/1.00      ( ~ l1_struct_0(X0) | v1_xboole_0(k1_struct_0(X0)) ),
% 3.13/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_16,plain,
% 3.13/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.13/1.00      | ~ r2_hidden(X2,X0)
% 3.13/1.00      | ~ v1_xboole_0(X1) ),
% 3.13/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_14,plain,
% 3.13/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.13/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_184,plain,
% 3.13/1.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.13/1.00      inference(prop_impl,[status(thm)],[c_14]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_185,plain,
% 3.13/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.13/1.00      inference(renaming,[status(thm)],[c_184]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_229,plain,
% 3.13/1.00      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X2) | ~ v1_xboole_0(X2) ),
% 3.13/1.00      inference(bin_hyper_res,[status(thm)],[c_16,c_185]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_314,plain,
% 3.13/1.00      ( ~ r2_hidden(X0,X1)
% 3.13/1.00      | ~ r1_tarski(X1,X2)
% 3.13/1.00      | ~ l1_struct_0(X3)
% 3.13/1.00      | k1_struct_0(X3) != X2 ),
% 3.13/1.00      inference(resolution_lifted,[status(thm)],[c_20,c_229]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_315,plain,
% 3.13/1.00      ( ~ r2_hidden(X0,X1)
% 3.13/1.00      | ~ r1_tarski(X1,k1_struct_0(X2))
% 3.13/1.00      | ~ l1_struct_0(X2) ),
% 3.13/1.00      inference(unflattening,[status(thm)],[c_314]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_384,plain,
% 3.13/1.00      ( ~ r2_hidden(X0,X1)
% 3.13/1.00      | ~ r1_tarski(X1,k1_struct_0(X2))
% 3.13/1.00      | sK2 != X2 ),
% 3.13/1.00      inference(resolution_lifted,[status(thm)],[c_334,c_315]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_385,plain,
% 3.13/1.00      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,k1_struct_0(sK2)) ),
% 3.13/1.00      inference(unflattening,[status(thm)],[c_384]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1266,plain,
% 3.13/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.13/1.00      | r1_tarski(X1,k1_struct_0(sK2)) != iProver_top ),
% 3.13/1.00      inference(predicate_to_equality,[status(thm)],[c_385]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1721,plain,
% 3.13/1.00      ( r2_hidden(X0,k1_struct_0(sK2)) != iProver_top ),
% 3.13/1.00      inference(superposition,[status(thm)],[c_1274,c_1266]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_2484,plain,
% 3.13/1.00      ( r1_tarski(k1_struct_0(sK2),X0) = iProver_top ),
% 3.13/1.00      inference(superposition,[status(thm)],[c_1280,c_1721]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_21,plain,
% 3.13/1.00      ( ~ l1_struct_0(X0)
% 3.13/1.00      | k3_subset_1(u1_struct_0(X0),k1_struct_0(X0)) = k2_struct_0(X0) ),
% 3.13/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_372,plain,
% 3.13/1.00      ( k3_subset_1(u1_struct_0(X0),k1_struct_0(X0)) = k2_struct_0(X0)
% 3.13/1.00      | sK2 != X0 ),
% 3.13/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_334]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_373,plain,
% 3.13/1.00      ( k3_subset_1(u1_struct_0(sK2),k1_struct_0(sK2)) = k2_struct_0(sK2) ),
% 3.13/1.00      inference(unflattening,[status(thm)],[c_372]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_13,plain,
% 3.13/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.13/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.13/1.00      | ~ r1_xboole_0(X2,X0)
% 3.13/1.00      | r1_tarski(X2,k3_subset_1(X1,X0)) ),
% 3.13/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_226,plain,
% 3.13/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.13/1.00      | ~ r1_xboole_0(X0,X2)
% 3.13/1.00      | ~ r1_tarski(X2,X1)
% 3.13/1.00      | r1_tarski(X0,k3_subset_1(X1,X2)) ),
% 3.13/1.00      inference(bin_hyper_res,[status(thm)],[c_13,c_185]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_594,plain,
% 3.13/1.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.13/1.00      inference(prop_impl,[status(thm)],[c_14]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_595,plain,
% 3.13/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.13/1.00      inference(renaming,[status(thm)],[c_594]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_632,plain,
% 3.13/1.00      ( ~ r1_xboole_0(X0,X1)
% 3.13/1.00      | ~ r1_tarski(X0,X2)
% 3.13/1.00      | ~ r1_tarski(X1,X2)
% 3.13/1.00      | r1_tarski(X0,k3_subset_1(X2,X1)) ),
% 3.13/1.00      inference(bin_hyper_res,[status(thm)],[c_226,c_595]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1264,plain,
% 3.13/1.00      ( r1_xboole_0(X0,X1) != iProver_top
% 3.13/1.00      | r1_tarski(X1,X2) != iProver_top
% 3.13/1.00      | r1_tarski(X0,X2) != iProver_top
% 3.13/1.00      | r1_tarski(X0,k3_subset_1(X2,X1)) = iProver_top ),
% 3.13/1.00      inference(predicate_to_equality,[status(thm)],[c_632]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1624,plain,
% 3.13/1.00      ( r1_xboole_0(X0,k1_struct_0(sK2)) != iProver_top
% 3.13/1.00      | r1_tarski(X0,k2_struct_0(sK2)) = iProver_top
% 3.13/1.00      | r1_tarski(X0,u1_struct_0(sK2)) != iProver_top
% 3.13/1.00      | r1_tarski(k1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top ),
% 3.13/1.00      inference(superposition,[status(thm)],[c_373,c_1264]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_3489,plain,
% 3.13/1.00      ( r1_xboole_0(X0,k1_struct_0(sK2)) != iProver_top
% 3.13/1.00      | r1_tarski(X0,k2_struct_0(sK2)) = iProver_top
% 3.13/1.00      | r1_tarski(X0,u1_struct_0(sK2)) != iProver_top ),
% 3.13/1.00      inference(superposition,[status(thm)],[c_2484,c_1624]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1435,plain,
% 3.13/1.00      ( r1_tarski(k1_struct_0(sK2),k1_struct_0(sK2)) ),
% 3.13/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1437,plain,
% 3.13/1.00      ( r1_tarski(k1_struct_0(sK2),k1_struct_0(sK2)) = iProver_top ),
% 3.13/1.00      inference(predicate_to_equality,[status(thm)],[c_1435]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1552,plain,
% 3.13/1.00      ( r2_hidden(sK0(X0,u1_struct_0(sK2)),X0)
% 3.13/1.00      | r1_tarski(X0,u1_struct_0(sK2)) ),
% 3.13/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_2334,plain,
% 3.13/1.00      ( r2_hidden(sK0(k1_struct_0(sK2),u1_struct_0(sK2)),k1_struct_0(sK2))
% 3.13/1.00      | r1_tarski(k1_struct_0(sK2),u1_struct_0(sK2)) ),
% 3.13/1.00      inference(instantiation,[status(thm)],[c_1552]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_2336,plain,
% 3.13/1.00      ( r2_hidden(sK0(k1_struct_0(sK2),u1_struct_0(sK2)),k1_struct_0(sK2)) = iProver_top
% 3.13/1.00      | r1_tarski(k1_struct_0(sK2),u1_struct_0(sK2)) = iProver_top ),
% 3.13/1.00      inference(predicate_to_equality,[status(thm)],[c_2334]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1436,plain,
% 3.13/1.00      ( ~ r2_hidden(X0,k1_struct_0(sK2))
% 3.13/1.00      | ~ r1_tarski(k1_struct_0(sK2),k1_struct_0(sK2)) ),
% 3.13/1.00      inference(instantiation,[status(thm)],[c_385]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_2335,plain,
% 3.13/1.00      ( ~ r2_hidden(sK0(k1_struct_0(sK2),u1_struct_0(sK2)),k1_struct_0(sK2))
% 3.13/1.00      | ~ r1_tarski(k1_struct_0(sK2),k1_struct_0(sK2)) ),
% 3.13/1.00      inference(instantiation,[status(thm)],[c_1436]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_2338,plain,
% 3.13/1.00      ( r2_hidden(sK0(k1_struct_0(sK2),u1_struct_0(sK2)),k1_struct_0(sK2)) != iProver_top
% 3.13/1.00      | r1_tarski(k1_struct_0(sK2),k1_struct_0(sK2)) != iProver_top ),
% 3.13/1.00      inference(predicate_to_equality,[status(thm)],[c_2335]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_4,plain,
% 3.13/1.00      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X1) ),
% 3.13/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1277,plain,
% 3.13/1.00      ( r1_xboole_0(X0,X1) = iProver_top
% 3.13/1.00      | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
% 3.13/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_2366,plain,
% 3.13/1.00      ( r1_xboole_0(X0,k1_struct_0(sK2)) = iProver_top ),
% 3.13/1.00      inference(superposition,[status(thm)],[c_1277,c_1721]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_3975,plain,
% 3.13/1.00      ( r1_tarski(X0,k2_struct_0(sK2)) = iProver_top
% 3.13/1.00      | r1_tarski(X0,u1_struct_0(sK2)) != iProver_top ),
% 3.13/1.00      inference(global_propositional_subsumption,
% 3.13/1.00                [status(thm)],
% 3.13/1.00                [c_3489,c_1437,c_1624,c_2336,c_2338,c_2366]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_3983,plain,
% 3.13/1.00      ( r1_tarski(u1_struct_0(sK2),k2_struct_0(sK2)) = iProver_top ),
% 3.13/1.00      inference(superposition,[status(thm)],[c_1274,c_3975]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_9,plain,
% 3.13/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 3.13/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1510,plain,
% 3.13/1.00      ( ~ r1_tarski(X0,k2_struct_0(sK2))
% 3.13/1.00      | ~ r1_tarski(k2_pre_topc(sK2,k2_struct_0(sK2)),X0)
% 3.13/1.00      | r1_tarski(k2_pre_topc(sK2,k2_struct_0(sK2)),k2_struct_0(sK2)) ),
% 3.13/1.00      inference(instantiation,[status(thm)],[c_9]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_3382,plain,
% 3.13/1.00      ( r1_tarski(k2_pre_topc(sK2,k2_struct_0(sK2)),k2_struct_0(sK2))
% 3.13/1.00      | ~ r1_tarski(k2_pre_topc(sK2,k2_struct_0(sK2)),u1_struct_0(sK2))
% 3.13/1.00      | ~ r1_tarski(u1_struct_0(sK2),k2_struct_0(sK2)) ),
% 3.13/1.00      inference(instantiation,[status(thm)],[c_1510]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_3386,plain,
% 3.13/1.00      ( r1_tarski(k2_pre_topc(sK2,k2_struct_0(sK2)),k2_struct_0(sK2)) = iProver_top
% 3.13/1.00      | r1_tarski(k2_pre_topc(sK2,k2_struct_0(sK2)),u1_struct_0(sK2)) != iProver_top
% 3.13/1.00      | r1_tarski(u1_struct_0(sK2),k2_struct_0(sK2)) != iProver_top ),
% 3.13/1.00      inference(predicate_to_equality,[status(thm)],[c_3382]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_15,plain,
% 3.13/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.13/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1554,plain,
% 3.13/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.13/1.00      | r1_tarski(X0,u1_struct_0(sK2)) ),
% 3.13/1.00      inference(instantiation,[status(thm)],[c_15]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1880,plain,
% 3.13/1.00      ( ~ m1_subset_1(k2_pre_topc(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.13/1.00      | r1_tarski(k2_pre_topc(sK2,X0),u1_struct_0(sK2)) ),
% 3.13/1.00      inference(instantiation,[status(thm)],[c_1554]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_2052,plain,
% 3.13/1.00      ( ~ m1_subset_1(k2_pre_topc(sK2,k2_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.13/1.00      | r1_tarski(k2_pre_topc(sK2,k2_struct_0(sK2)),u1_struct_0(sK2)) ),
% 3.13/1.00      inference(instantiation,[status(thm)],[c_1880]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_2053,plain,
% 3.13/1.00      ( m1_subset_1(k2_pre_topc(sK2,k2_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.13/1.00      | r1_tarski(k2_pre_topc(sK2,k2_struct_0(sK2)),u1_struct_0(sK2)) = iProver_top ),
% 3.13/1.00      inference(predicate_to_equality,[status(thm)],[c_2052]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_6,plain,
% 3.13/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.13/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1420,plain,
% 3.13/1.00      ( ~ r1_tarski(k2_pre_topc(sK2,k2_struct_0(sK2)),k2_struct_0(sK2))
% 3.13/1.00      | ~ r1_tarski(k2_struct_0(sK2),k2_pre_topc(sK2,k2_struct_0(sK2)))
% 3.13/1.00      | k2_pre_topc(sK2,k2_struct_0(sK2)) = k2_struct_0(sK2) ),
% 3.13/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1421,plain,
% 3.13/1.00      ( k2_pre_topc(sK2,k2_struct_0(sK2)) = k2_struct_0(sK2)
% 3.13/1.00      | r1_tarski(k2_pre_topc(sK2,k2_struct_0(sK2)),k2_struct_0(sK2)) != iProver_top
% 3.13/1.00      | r1_tarski(k2_struct_0(sK2),k2_pre_topc(sK2,k2_struct_0(sK2))) != iProver_top ),
% 3.13/1.00      inference(predicate_to_equality,[status(thm)],[c_1420]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_22,plain,
% 3.13/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.13/1.00      | r1_tarski(X0,k2_pre_topc(X1,X0))
% 3.13/1.00      | ~ l1_pre_topc(X1) ),
% 3.13/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_340,plain,
% 3.13/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.13/1.00      | r1_tarski(X0,k2_pre_topc(X1,X0))
% 3.13/1.00      | sK2 != X1 ),
% 3.13/1.00      inference(resolution_lifted,[status(thm)],[c_22,c_24]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_341,plain,
% 3.13/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.13/1.00      | r1_tarski(X0,k2_pre_topc(sK2,X0)) ),
% 3.13/1.00      inference(unflattening,[status(thm)],[c_340]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1412,plain,
% 3.13/1.00      ( ~ m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.13/1.00      | r1_tarski(k2_struct_0(sK2),k2_pre_topc(sK2,k2_struct_0(sK2))) ),
% 3.13/1.00      inference(instantiation,[status(thm)],[c_341]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1416,plain,
% 3.13/1.00      ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.13/1.00      | r1_tarski(k2_struct_0(sK2),k2_pre_topc(sK2,k2_struct_0(sK2))) = iProver_top ),
% 3.13/1.00      inference(predicate_to_equality,[status(thm)],[c_1412]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_17,plain,
% 3.13/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.13/1.00      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.13/1.00      | ~ l1_pre_topc(X1) ),
% 3.13/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_352,plain,
% 3.13/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.13/1.00      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.13/1.00      | sK2 != X1 ),
% 3.13/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_24]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_353,plain,
% 3.13/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.13/1.00      | m1_subset_1(k2_pre_topc(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.13/1.00      inference(unflattening,[status(thm)],[c_352]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1413,plain,
% 3.13/1.00      ( m1_subset_1(k2_pre_topc(sK2,k2_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.13/1.00      | ~ m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.13/1.00      inference(instantiation,[status(thm)],[c_353]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1414,plain,
% 3.13/1.00      ( m1_subset_1(k2_pre_topc(sK2,k2_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 3.13/1.00      | m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 3.13/1.00      inference(predicate_to_equality,[status(thm)],[c_1413]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_18,plain,
% 3.13/1.00      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 3.13/1.00      | ~ l1_struct_0(X0) ),
% 3.13/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_38,plain,
% 3.13/1.00      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 3.13/1.00      | l1_struct_0(X0) != iProver_top ),
% 3.13/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_40,plain,
% 3.13/1.00      ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 3.13/1.00      | l1_struct_0(sK2) != iProver_top ),
% 3.13/1.00      inference(instantiation,[status(thm)],[c_38]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_35,plain,
% 3.13/1.00      ( l1_struct_0(X0) = iProver_top | l1_pre_topc(X0) != iProver_top ),
% 3.13/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_37,plain,
% 3.13/1.00      ( l1_struct_0(sK2) = iProver_top
% 3.13/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.13/1.00      inference(instantiation,[status(thm)],[c_35]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_23,negated_conjecture,
% 3.13/1.00      ( k2_pre_topc(sK2,k2_struct_0(sK2)) != k2_struct_0(sK2) ),
% 3.13/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_25,plain,
% 3.13/1.00      ( l1_pre_topc(sK2) = iProver_top ),
% 3.13/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(contradiction,plain,
% 3.13/1.00      ( $false ),
% 3.13/1.00      inference(minisat,
% 3.13/1.00                [status(thm)],
% 3.13/1.00                [c_3983,c_3386,c_2053,c_1421,c_1416,c_1414,c_40,c_37,
% 3.13/1.00                 c_23,c_25]) ).
% 3.13/1.00  
% 3.13/1.00  
% 3.13/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.13/1.00  
% 3.13/1.00  ------                               Statistics
% 3.13/1.00  
% 3.13/1.00  ------ General
% 3.13/1.00  
% 3.13/1.00  abstr_ref_over_cycles:                  0
% 3.13/1.00  abstr_ref_under_cycles:                 0
% 3.13/1.00  gc_basic_clause_elim:                   0
% 3.13/1.00  forced_gc_time:                         0
% 3.13/1.00  parsing_time:                           0.008
% 3.13/1.00  unif_index_cands_time:                  0.
% 3.13/1.00  unif_index_add_time:                    0.
% 3.13/1.00  orderings_time:                         0.
% 3.13/1.00  out_proof_time:                         0.014
% 3.13/1.00  total_time:                             0.134
% 3.13/1.00  num_of_symbols:                         48
% 3.13/1.00  num_of_terms:                           2705
% 3.13/1.00  
% 3.13/1.00  ------ Preprocessing
% 3.13/1.00  
% 3.13/1.00  num_of_splits:                          0
% 3.13/1.00  num_of_split_atoms:                     0
% 3.13/1.00  num_of_reused_defs:                     0
% 3.13/1.00  num_eq_ax_congr_red:                    30
% 3.13/1.00  num_of_sem_filtered_clauses:            1
% 3.13/1.00  num_of_subtypes:                        0
% 3.13/1.00  monotx_restored_types:                  0
% 3.13/1.00  sat_num_of_epr_types:                   0
% 3.13/1.00  sat_num_of_non_cyclic_types:            0
% 3.13/1.00  sat_guarded_non_collapsed_types:        0
% 3.13/1.00  num_pure_diseq_elim:                    0
% 3.13/1.00  simp_replaced_by:                       0
% 3.13/1.00  res_preprocessed:                       110
% 3.13/1.00  prep_upred:                             0
% 3.13/1.00  prep_unflattend:                        13
% 3.13/1.00  smt_new_axioms:                         0
% 3.13/1.00  pred_elim_cands:                        4
% 3.13/1.00  pred_elim:                              3
% 3.13/1.00  pred_elim_cl:                           3
% 3.13/1.00  pred_elim_cycles:                       5
% 3.13/1.00  merged_defs:                            8
% 3.13/1.00  merged_defs_ncl:                        0
% 3.13/1.00  bin_hyper_res:                          13
% 3.13/1.00  prep_cycles:                            4
% 3.13/1.00  pred_elim_time:                         0.005
% 3.13/1.00  splitting_time:                         0.
% 3.13/1.00  sem_filter_time:                        0.
% 3.13/1.00  monotx_time:                            0.
% 3.13/1.00  subtype_inf_time:                       0.
% 3.13/1.00  
% 3.13/1.00  ------ Problem properties
% 3.13/1.00  
% 3.13/1.00  clauses:                                21
% 3.13/1.00  conjectures:                            1
% 3.13/1.00  epr:                                    5
% 3.13/1.00  horn:                                   18
% 3.13/1.00  ground:                                 3
% 3.13/1.00  unary:                                  6
% 3.13/1.00  binary:                                 9
% 3.13/1.00  lits:                                   44
% 3.13/1.00  lits_eq:                                4
% 3.13/1.00  fd_pure:                                0
% 3.13/1.00  fd_pseudo:                              0
% 3.13/1.00  fd_cond:                                0
% 3.13/1.00  fd_pseudo_cond:                         1
% 3.13/1.00  ac_symbols:                             0
% 3.13/1.00  
% 3.13/1.00  ------ Propositional Solver
% 3.13/1.00  
% 3.13/1.00  prop_solver_calls:                      27
% 3.13/1.00  prop_fast_solver_calls:                 645
% 3.13/1.00  smt_solver_calls:                       0
% 3.13/1.00  smt_fast_solver_calls:                  0
% 3.13/1.00  prop_num_of_clauses:                    1399
% 3.13/1.00  prop_preprocess_simplified:             4539
% 3.13/1.00  prop_fo_subsumed:                       4
% 3.13/1.00  prop_solver_time:                       0.
% 3.13/1.00  smt_solver_time:                        0.
% 3.13/1.00  smt_fast_solver_time:                   0.
% 3.13/1.00  prop_fast_solver_time:                  0.
% 3.13/1.00  prop_unsat_core_time:                   0.
% 3.13/1.00  
% 3.13/1.00  ------ QBF
% 3.13/1.00  
% 3.13/1.00  qbf_q_res:                              0
% 3.13/1.00  qbf_num_tautologies:                    0
% 3.13/1.00  qbf_prep_cycles:                        0
% 3.13/1.00  
% 3.13/1.00  ------ BMC1
% 3.13/1.00  
% 3.13/1.00  bmc1_current_bound:                     -1
% 3.13/1.00  bmc1_last_solved_bound:                 -1
% 3.13/1.00  bmc1_unsat_core_size:                   -1
% 3.13/1.00  bmc1_unsat_core_parents_size:           -1
% 3.13/1.00  bmc1_merge_next_fun:                    0
% 3.13/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.13/1.00  
% 3.13/1.00  ------ Instantiation
% 3.13/1.00  
% 3.13/1.00  inst_num_of_clauses:                    396
% 3.13/1.00  inst_num_in_passive:                    118
% 3.13/1.00  inst_num_in_active:                     168
% 3.13/1.00  inst_num_in_unprocessed:                110
% 3.13/1.00  inst_num_of_loops:                      220
% 3.13/1.00  inst_num_of_learning_restarts:          0
% 3.13/1.00  inst_num_moves_active_passive:          49
% 3.13/1.00  inst_lit_activity:                      0
% 3.13/1.00  inst_lit_activity_moves:                0
% 3.13/1.00  inst_num_tautologies:                   0
% 3.13/1.00  inst_num_prop_implied:                  0
% 3.13/1.00  inst_num_existing_simplified:           0
% 3.13/1.00  inst_num_eq_res_simplified:             0
% 3.13/1.00  inst_num_child_elim:                    0
% 3.13/1.00  inst_num_of_dismatching_blockings:      122
% 3.13/1.00  inst_num_of_non_proper_insts:           341
% 3.13/1.00  inst_num_of_duplicates:                 0
% 3.13/1.00  inst_inst_num_from_inst_to_res:         0
% 3.13/1.00  inst_dismatching_checking_time:         0.
% 3.13/1.00  
% 3.13/1.00  ------ Resolution
% 3.13/1.00  
% 3.13/1.00  res_num_of_clauses:                     0
% 3.13/1.00  res_num_in_passive:                     0
% 3.13/1.00  res_num_in_active:                      0
% 3.13/1.00  res_num_of_loops:                       114
% 3.13/1.00  res_forward_subset_subsumed:            28
% 3.13/1.00  res_backward_subset_subsumed:           0
% 3.13/1.00  res_forward_subsumed:                   0
% 3.13/1.00  res_backward_subsumed:                  0
% 3.13/1.00  res_forward_subsumption_resolution:     0
% 3.13/1.00  res_backward_subsumption_resolution:    0
% 3.13/1.00  res_clause_to_clause_subsumption:       396
% 3.13/1.00  res_orphan_elimination:                 0
% 3.13/1.00  res_tautology_del:                      43
% 3.13/1.00  res_num_eq_res_simplified:              0
% 3.13/1.00  res_num_sel_changes:                    0
% 3.13/1.00  res_moves_from_active_to_pass:          0
% 3.13/1.00  
% 3.13/1.00  ------ Superposition
% 3.13/1.00  
% 3.13/1.00  sup_time_total:                         0.
% 3.13/1.00  sup_time_generating:                    0.
% 3.13/1.00  sup_time_sim_full:                      0.
% 3.13/1.00  sup_time_sim_immed:                     0.
% 3.13/1.00  
% 3.13/1.00  sup_num_of_clauses:                     70
% 3.13/1.00  sup_num_in_active:                      41
% 3.13/1.00  sup_num_in_passive:                     29
% 3.13/1.00  sup_num_of_loops:                       43
% 3.13/1.00  sup_fw_superposition:                   56
% 3.13/1.00  sup_bw_superposition:                   28
% 3.13/1.00  sup_immediate_simplified:               11
% 3.13/1.00  sup_given_eliminated:                   0
% 3.13/1.00  comparisons_done:                       0
% 3.13/1.00  comparisons_avoided:                    0
% 3.13/1.00  
% 3.13/1.00  ------ Simplifications
% 3.13/1.00  
% 3.13/1.00  
% 3.13/1.00  sim_fw_subset_subsumed:                 5
% 3.13/1.00  sim_bw_subset_subsumed:                 3
% 3.13/1.00  sim_fw_subsumed:                        6
% 3.13/1.00  sim_bw_subsumed:                        0
% 3.13/1.00  sim_fw_subsumption_res:                 0
% 3.13/1.00  sim_bw_subsumption_res:                 0
% 3.13/1.00  sim_tautology_del:                      9
% 3.13/1.00  sim_eq_tautology_del:                   2
% 3.13/1.00  sim_eq_res_simp:                        0
% 3.13/1.00  sim_fw_demodulated:                     0
% 3.13/1.00  sim_bw_demodulated:                     1
% 3.13/1.00  sim_light_normalised:                   3
% 3.13/1.00  sim_joinable_taut:                      0
% 3.13/1.00  sim_joinable_simp:                      0
% 3.13/1.00  sim_ac_normalised:                      0
% 3.13/1.00  sim_smt_subsumption:                    0
% 3.13/1.00  
%------------------------------------------------------------------------------
