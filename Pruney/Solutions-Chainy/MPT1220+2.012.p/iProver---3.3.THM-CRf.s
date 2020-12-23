%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:13:26 EST 2020

% Result     : Theorem 3.11s
% Output     : CNFRefutation 3.11s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 280 expanded)
%              Number of clauses        :   66 ( 117 expanded)
%              Number of leaves         :   14 (  51 expanded)
%              Depth                    :   19
%              Number of atoms          :  285 ( 673 expanded)
%              Number of equality atoms :   81 ( 175 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f14,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => k2_pre_topc(X0,k2_struct_0(X0)) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => k2_pre_topc(X0,k2_struct_0(X0)) = k2_struct_0(X0) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f27,plain,(
    ? [X0] :
      ( k2_pre_topc(X0,k2_struct_0(X0)) != k2_struct_0(X0)
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f35,plain,
    ( ? [X0] :
        ( k2_pre_topc(X0,k2_struct_0(X0)) != k2_struct_0(X0)
        & l1_pre_topc(X0) )
   => ( k2_pre_topc(sK1,k2_struct_0(sK1)) != k2_struct_0(sK1)
      & l1_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( k2_pre_topc(sK1,k2_struct_0(sK1)) != k2_struct_0(sK1)
    & l1_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f35])).

fof(f55,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k3_subset_1(u1_struct_0(X0),k1_struct_0(X0)) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( k3_subset_1(u1_struct_0(X0),k1_struct_0(X0)) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f53,plain,(
    ! [X0] :
      ( k3_subset_1(u1_struct_0(X0),k1_struct_0(X0)) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f51,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f58,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f40])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => v1_xboole_0(k1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f52,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,k3_subset_1(X0,X2))
           => r1_tarski(X2,k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f17])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,k3_subset_1(X0,X1))
      | ~ r1_tarski(X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f50,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f42,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f56,plain,(
    k2_pre_topc(sK1,k2_struct_0(sK1)) != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_19,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_284,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_19])).

cnf(c_285,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k2_pre_topc(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_284])).

cnf(c_818,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_285])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_820,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1355,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(k2_pre_topc(sK1,X0),u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_818,c_820])).

cnf(c_16,plain,
    ( ~ l1_struct_0(X0)
    | k3_subset_1(u1_struct_0(X0),k1_struct_0(X0)) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_14,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_265,plain,
    ( l1_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_19])).

cnf(c_266,plain,
    ( l1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_265])).

cnf(c_304,plain,
    ( k3_subset_1(u1_struct_0(X0),k1_struct_0(X0)) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_266])).

cnf(c_305,plain,
    ( k3_subset_1(u1_struct_0(sK1),k1_struct_0(sK1)) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_304])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_826,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_823,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_15,plain,
    ( ~ l1_struct_0(X0)
    | v1_xboole_0(k1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_9,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_144,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_9])).

cnf(c_145,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_144])).

cnf(c_180,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(bin_hyper_res,[status(thm)],[c_11,c_145])).

cnf(c_246,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | ~ l1_struct_0(X3)
    | k1_struct_0(X3) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_180])).

cnf(c_247,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,k1_struct_0(X2))
    | ~ l1_struct_0(X2) ),
    inference(unflattening,[status(thm)],[c_246])).

cnf(c_316,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,k1_struct_0(X2))
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_266,c_247])).

cnf(c_317,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,k1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_316])).

cnf(c_816,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,k1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_317])).

cnf(c_1247,plain,
    ( r2_hidden(X0,k1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_823,c_816])).

cnf(c_2033,plain,
    ( r1_tarski(k1_struct_0(sK1),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_826,c_1247])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,k3_subset_1(X1,X0))
    | r1_tarski(X0,k3_subset_1(X1,X2)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_177,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X1)
    | ~ r1_tarski(X0,k3_subset_1(X1,X2))
    | r1_tarski(X2,k3_subset_1(X1,X0)) ),
    inference(bin_hyper_res,[status(thm)],[c_8,c_145])).

cnf(c_382,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_9])).

cnf(c_383,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_382])).

cnf(c_410,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | ~ r1_tarski(X0,k3_subset_1(X1,X2))
    | r1_tarski(X2,k3_subset_1(X1,X0)) ),
    inference(bin_hyper_res,[status(thm)],[c_177,c_383])).

cnf(c_815,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(X0,k3_subset_1(X1,X2)) != iProver_top
    | r1_tarski(X2,k3_subset_1(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_410])).

cnf(c_2266,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k3_subset_1(X1,k1_struct_0(sK1))) = iProver_top
    | r1_tarski(k1_struct_0(sK1),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2033,c_815])).

cnf(c_2271,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k3_subset_1(X1,k1_struct_0(sK1))) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2266,c_2033])).

cnf(c_2631,plain,
    ( r1_tarski(X0,k2_struct_0(sK1)) = iProver_top
    | r1_tarski(X0,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_305,c_2271])).

cnf(c_3177,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(k2_pre_topc(sK1,X0),k2_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1355,c_2631])).

cnf(c_13,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_309,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_266])).

cnf(c_310,plain,
    ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_309])).

cnf(c_817,plain,
    ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_310])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_272,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_19])).

cnf(c_273,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(X0,k2_pre_topc(sK1,X0)) ),
    inference(unflattening,[status(thm)],[c_272])).

cnf(c_819,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_273])).

cnf(c_1055,plain,
    ( r1_tarski(k2_struct_0(sK1),k2_pre_topc(sK1,k2_struct_0(sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_817,c_819])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_824,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1834,plain,
    ( k2_pre_topc(sK1,k2_struct_0(sK1)) = k2_struct_0(sK1)
    | r1_tarski(k2_pre_topc(sK1,k2_struct_0(sK1)),k2_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1055,c_824])).

cnf(c_20,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_18,negated_conjecture,
    ( k2_pre_topc(sK1,k2_struct_0(sK1)) != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_30,plain,
    ( l1_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_32,plain,
    ( l1_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_33,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_35,plain,
    ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | l1_struct_0(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_920,plain,
    ( ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(k2_struct_0(sK1),k2_pre_topc(sK1,k2_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_273])).

cnf(c_924,plain,
    ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(k2_struct_0(sK1),k2_pre_topc(sK1,k2_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_920])).

cnf(c_928,plain,
    ( ~ r1_tarski(k2_pre_topc(sK1,k2_struct_0(sK1)),k2_struct_0(sK1))
    | ~ r1_tarski(k2_struct_0(sK1),k2_pre_topc(sK1,k2_struct_0(sK1)))
    | k2_pre_topc(sK1,k2_struct_0(sK1)) = k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_929,plain,
    ( k2_pre_topc(sK1,k2_struct_0(sK1)) = k2_struct_0(sK1)
    | r1_tarski(k2_pre_topc(sK1,k2_struct_0(sK1)),k2_struct_0(sK1)) != iProver_top
    | r1_tarski(k2_struct_0(sK1),k2_pre_topc(sK1,k2_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_928])).

cnf(c_2352,plain,
    ( r1_tarski(k2_pre_topc(sK1,k2_struct_0(sK1)),k2_struct_0(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1834,c_20,c_18,c_32,c_35,c_924,c_929])).

cnf(c_3469,plain,
    ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3177,c_2352])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3469,c_35,c_32,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:35:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.11/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.11/1.01  
% 3.11/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.11/1.01  
% 3.11/1.01  ------  iProver source info
% 3.11/1.01  
% 3.11/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.11/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.11/1.01  git: non_committed_changes: false
% 3.11/1.01  git: last_make_outside_of_git: false
% 3.11/1.01  
% 3.11/1.01  ------ 
% 3.11/1.01  
% 3.11/1.01  ------ Input Options
% 3.11/1.01  
% 3.11/1.01  --out_options                           all
% 3.11/1.01  --tptp_safe_out                         true
% 3.11/1.01  --problem_path                          ""
% 3.11/1.01  --include_path                          ""
% 3.11/1.01  --clausifier                            res/vclausify_rel
% 3.11/1.01  --clausifier_options                    --mode clausify
% 3.11/1.01  --stdin                                 false
% 3.11/1.01  --stats_out                             all
% 3.11/1.01  
% 3.11/1.01  ------ General Options
% 3.11/1.01  
% 3.11/1.01  --fof                                   false
% 3.11/1.01  --time_out_real                         305.
% 3.11/1.01  --time_out_virtual                      -1.
% 3.11/1.01  --symbol_type_check                     false
% 3.11/1.01  --clausify_out                          false
% 3.11/1.01  --sig_cnt_out                           false
% 3.11/1.01  --trig_cnt_out                          false
% 3.11/1.01  --trig_cnt_out_tolerance                1.
% 3.11/1.01  --trig_cnt_out_sk_spl                   false
% 3.11/1.01  --abstr_cl_out                          false
% 3.11/1.01  
% 3.11/1.01  ------ Global Options
% 3.11/1.01  
% 3.11/1.01  --schedule                              default
% 3.11/1.01  --add_important_lit                     false
% 3.11/1.01  --prop_solver_per_cl                    1000
% 3.11/1.01  --min_unsat_core                        false
% 3.11/1.01  --soft_assumptions                      false
% 3.11/1.01  --soft_lemma_size                       3
% 3.11/1.01  --prop_impl_unit_size                   0
% 3.11/1.01  --prop_impl_unit                        []
% 3.11/1.01  --share_sel_clauses                     true
% 3.11/1.01  --reset_solvers                         false
% 3.11/1.01  --bc_imp_inh                            [conj_cone]
% 3.11/1.01  --conj_cone_tolerance                   3.
% 3.11/1.01  --extra_neg_conj                        none
% 3.11/1.01  --large_theory_mode                     true
% 3.11/1.01  --prolific_symb_bound                   200
% 3.11/1.01  --lt_threshold                          2000
% 3.11/1.01  --clause_weak_htbl                      true
% 3.11/1.01  --gc_record_bc_elim                     false
% 3.11/1.01  
% 3.11/1.01  ------ Preprocessing Options
% 3.11/1.01  
% 3.11/1.01  --preprocessing_flag                    true
% 3.11/1.01  --time_out_prep_mult                    0.1
% 3.11/1.01  --splitting_mode                        input
% 3.11/1.01  --splitting_grd                         true
% 3.11/1.01  --splitting_cvd                         false
% 3.11/1.01  --splitting_cvd_svl                     false
% 3.11/1.01  --splitting_nvd                         32
% 3.11/1.01  --sub_typing                            true
% 3.11/1.01  --prep_gs_sim                           true
% 3.11/1.01  --prep_unflatten                        true
% 3.11/1.01  --prep_res_sim                          true
% 3.11/1.01  --prep_upred                            true
% 3.11/1.01  --prep_sem_filter                       exhaustive
% 3.11/1.01  --prep_sem_filter_out                   false
% 3.11/1.01  --pred_elim                             true
% 3.11/1.01  --res_sim_input                         true
% 3.11/1.01  --eq_ax_congr_red                       true
% 3.11/1.01  --pure_diseq_elim                       true
% 3.11/1.01  --brand_transform                       false
% 3.11/1.01  --non_eq_to_eq                          false
% 3.11/1.01  --prep_def_merge                        true
% 3.11/1.01  --prep_def_merge_prop_impl              false
% 3.11/1.01  --prep_def_merge_mbd                    true
% 3.11/1.01  --prep_def_merge_tr_red                 false
% 3.11/1.01  --prep_def_merge_tr_cl                  false
% 3.11/1.01  --smt_preprocessing                     true
% 3.11/1.01  --smt_ac_axioms                         fast
% 3.11/1.01  --preprocessed_out                      false
% 3.11/1.01  --preprocessed_stats                    false
% 3.11/1.01  
% 3.11/1.01  ------ Abstraction refinement Options
% 3.11/1.01  
% 3.11/1.01  --abstr_ref                             []
% 3.11/1.01  --abstr_ref_prep                        false
% 3.11/1.01  --abstr_ref_until_sat                   false
% 3.11/1.01  --abstr_ref_sig_restrict                funpre
% 3.11/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.11/1.01  --abstr_ref_under                       []
% 3.11/1.01  
% 3.11/1.01  ------ SAT Options
% 3.11/1.01  
% 3.11/1.01  --sat_mode                              false
% 3.11/1.01  --sat_fm_restart_options                ""
% 3.11/1.01  --sat_gr_def                            false
% 3.11/1.01  --sat_epr_types                         true
% 3.11/1.01  --sat_non_cyclic_types                  false
% 3.11/1.01  --sat_finite_models                     false
% 3.11/1.01  --sat_fm_lemmas                         false
% 3.11/1.01  --sat_fm_prep                           false
% 3.11/1.01  --sat_fm_uc_incr                        true
% 3.11/1.01  --sat_out_model                         small
% 3.11/1.01  --sat_out_clauses                       false
% 3.11/1.01  
% 3.11/1.01  ------ QBF Options
% 3.11/1.01  
% 3.11/1.01  --qbf_mode                              false
% 3.11/1.01  --qbf_elim_univ                         false
% 3.11/1.01  --qbf_dom_inst                          none
% 3.11/1.01  --qbf_dom_pre_inst                      false
% 3.11/1.01  --qbf_sk_in                             false
% 3.11/1.01  --qbf_pred_elim                         true
% 3.11/1.01  --qbf_split                             512
% 3.11/1.01  
% 3.11/1.01  ------ BMC1 Options
% 3.11/1.01  
% 3.11/1.01  --bmc1_incremental                      false
% 3.11/1.01  --bmc1_axioms                           reachable_all
% 3.11/1.01  --bmc1_min_bound                        0
% 3.11/1.01  --bmc1_max_bound                        -1
% 3.11/1.01  --bmc1_max_bound_default                -1
% 3.11/1.01  --bmc1_symbol_reachability              true
% 3.11/1.01  --bmc1_property_lemmas                  false
% 3.11/1.01  --bmc1_k_induction                      false
% 3.11/1.01  --bmc1_non_equiv_states                 false
% 3.11/1.01  --bmc1_deadlock                         false
% 3.11/1.01  --bmc1_ucm                              false
% 3.11/1.01  --bmc1_add_unsat_core                   none
% 3.11/1.01  --bmc1_unsat_core_children              false
% 3.11/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.11/1.01  --bmc1_out_stat                         full
% 3.11/1.01  --bmc1_ground_init                      false
% 3.11/1.01  --bmc1_pre_inst_next_state              false
% 3.11/1.01  --bmc1_pre_inst_state                   false
% 3.11/1.01  --bmc1_pre_inst_reach_state             false
% 3.11/1.01  --bmc1_out_unsat_core                   false
% 3.11/1.01  --bmc1_aig_witness_out                  false
% 3.11/1.01  --bmc1_verbose                          false
% 3.11/1.01  --bmc1_dump_clauses_tptp                false
% 3.11/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.11/1.01  --bmc1_dump_file                        -
% 3.11/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.11/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.11/1.01  --bmc1_ucm_extend_mode                  1
% 3.11/1.01  --bmc1_ucm_init_mode                    2
% 3.11/1.01  --bmc1_ucm_cone_mode                    none
% 3.11/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.11/1.01  --bmc1_ucm_relax_model                  4
% 3.11/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.11/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.11/1.01  --bmc1_ucm_layered_model                none
% 3.11/1.01  --bmc1_ucm_max_lemma_size               10
% 3.11/1.01  
% 3.11/1.01  ------ AIG Options
% 3.11/1.01  
% 3.11/1.01  --aig_mode                              false
% 3.11/1.01  
% 3.11/1.01  ------ Instantiation Options
% 3.11/1.01  
% 3.11/1.01  --instantiation_flag                    true
% 3.11/1.01  --inst_sos_flag                         false
% 3.11/1.01  --inst_sos_phase                        true
% 3.11/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.11/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.11/1.01  --inst_lit_sel_side                     num_symb
% 3.11/1.01  --inst_solver_per_active                1400
% 3.11/1.01  --inst_solver_calls_frac                1.
% 3.11/1.01  --inst_passive_queue_type               priority_queues
% 3.11/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.11/1.01  --inst_passive_queues_freq              [25;2]
% 3.11/1.01  --inst_dismatching                      true
% 3.11/1.01  --inst_eager_unprocessed_to_passive     true
% 3.11/1.01  --inst_prop_sim_given                   true
% 3.11/1.01  --inst_prop_sim_new                     false
% 3.11/1.01  --inst_subs_new                         false
% 3.11/1.01  --inst_eq_res_simp                      false
% 3.11/1.01  --inst_subs_given                       false
% 3.11/1.01  --inst_orphan_elimination               true
% 3.11/1.01  --inst_learning_loop_flag               true
% 3.11/1.01  --inst_learning_start                   3000
% 3.11/1.01  --inst_learning_factor                  2
% 3.11/1.01  --inst_start_prop_sim_after_learn       3
% 3.11/1.01  --inst_sel_renew                        solver
% 3.11/1.01  --inst_lit_activity_flag                true
% 3.11/1.01  --inst_restr_to_given                   false
% 3.11/1.01  --inst_activity_threshold               500
% 3.11/1.01  --inst_out_proof                        true
% 3.11/1.01  
% 3.11/1.01  ------ Resolution Options
% 3.11/1.01  
% 3.11/1.01  --resolution_flag                       true
% 3.11/1.01  --res_lit_sel                           adaptive
% 3.11/1.01  --res_lit_sel_side                      none
% 3.11/1.01  --res_ordering                          kbo
% 3.11/1.01  --res_to_prop_solver                    active
% 3.11/1.01  --res_prop_simpl_new                    false
% 3.11/1.01  --res_prop_simpl_given                  true
% 3.11/1.01  --res_passive_queue_type                priority_queues
% 3.11/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.11/1.01  --res_passive_queues_freq               [15;5]
% 3.11/1.01  --res_forward_subs                      full
% 3.11/1.01  --res_backward_subs                     full
% 3.11/1.01  --res_forward_subs_resolution           true
% 3.11/1.01  --res_backward_subs_resolution          true
% 3.11/1.01  --res_orphan_elimination                true
% 3.11/1.01  --res_time_limit                        2.
% 3.11/1.01  --res_out_proof                         true
% 3.11/1.01  
% 3.11/1.01  ------ Superposition Options
% 3.11/1.01  
% 3.11/1.01  --superposition_flag                    true
% 3.11/1.01  --sup_passive_queue_type                priority_queues
% 3.11/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.11/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.11/1.01  --demod_completeness_check              fast
% 3.11/1.01  --demod_use_ground                      true
% 3.11/1.01  --sup_to_prop_solver                    passive
% 3.11/1.01  --sup_prop_simpl_new                    true
% 3.11/1.01  --sup_prop_simpl_given                  true
% 3.11/1.01  --sup_fun_splitting                     false
% 3.11/1.01  --sup_smt_interval                      50000
% 3.11/1.01  
% 3.11/1.01  ------ Superposition Simplification Setup
% 3.11/1.01  
% 3.11/1.01  --sup_indices_passive                   []
% 3.11/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.11/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.11/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.11/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.11/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.11/1.01  --sup_full_bw                           [BwDemod]
% 3.11/1.01  --sup_immed_triv                        [TrivRules]
% 3.11/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.11/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.11/1.01  --sup_immed_bw_main                     []
% 3.11/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.11/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.11/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.11/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.11/1.01  
% 3.11/1.01  ------ Combination Options
% 3.11/1.01  
% 3.11/1.01  --comb_res_mult                         3
% 3.11/1.01  --comb_sup_mult                         2
% 3.11/1.01  --comb_inst_mult                        10
% 3.11/1.01  
% 3.11/1.01  ------ Debug Options
% 3.11/1.01  
% 3.11/1.01  --dbg_backtrace                         false
% 3.11/1.01  --dbg_dump_prop_clauses                 false
% 3.11/1.01  --dbg_dump_prop_clauses_file            -
% 3.11/1.01  --dbg_out_stat                          false
% 3.11/1.01  ------ Parsing...
% 3.11/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.11/1.01  
% 3.11/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.11/1.01  
% 3.11/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.11/1.01  
% 3.11/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.11/1.01  ------ Proving...
% 3.11/1.01  ------ Problem Properties 
% 3.11/1.01  
% 3.11/1.01  
% 3.11/1.01  clauses                                 16
% 3.11/1.01  conjectures                             1
% 3.11/1.01  EPR                                     3
% 3.11/1.01  Horn                                    15
% 3.11/1.01  unary                                   6
% 3.11/1.01  binary                                  7
% 3.11/1.01  lits                                    30
% 3.11/1.01  lits eq                                 4
% 3.11/1.01  fd_pure                                 0
% 3.11/1.01  fd_pseudo                               0
% 3.11/1.01  fd_cond                                 0
% 3.11/1.01  fd_pseudo_cond                          1
% 3.11/1.01  AC symbols                              0
% 3.11/1.01  
% 3.11/1.01  ------ Schedule dynamic 5 is on 
% 3.11/1.01  
% 3.11/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.11/1.01  
% 3.11/1.01  
% 3.11/1.01  ------ 
% 3.11/1.01  Current options:
% 3.11/1.01  ------ 
% 3.11/1.01  
% 3.11/1.01  ------ Input Options
% 3.11/1.01  
% 3.11/1.01  --out_options                           all
% 3.11/1.01  --tptp_safe_out                         true
% 3.11/1.01  --problem_path                          ""
% 3.11/1.01  --include_path                          ""
% 3.11/1.01  --clausifier                            res/vclausify_rel
% 3.11/1.01  --clausifier_options                    --mode clausify
% 3.11/1.01  --stdin                                 false
% 3.11/1.01  --stats_out                             all
% 3.11/1.01  
% 3.11/1.01  ------ General Options
% 3.11/1.01  
% 3.11/1.01  --fof                                   false
% 3.11/1.01  --time_out_real                         305.
% 3.11/1.01  --time_out_virtual                      -1.
% 3.11/1.01  --symbol_type_check                     false
% 3.11/1.01  --clausify_out                          false
% 3.11/1.01  --sig_cnt_out                           false
% 3.11/1.01  --trig_cnt_out                          false
% 3.11/1.01  --trig_cnt_out_tolerance                1.
% 3.11/1.01  --trig_cnt_out_sk_spl                   false
% 3.11/1.01  --abstr_cl_out                          false
% 3.11/1.01  
% 3.11/1.01  ------ Global Options
% 3.11/1.01  
% 3.11/1.01  --schedule                              default
% 3.11/1.01  --add_important_lit                     false
% 3.11/1.01  --prop_solver_per_cl                    1000
% 3.11/1.01  --min_unsat_core                        false
% 3.11/1.01  --soft_assumptions                      false
% 3.11/1.01  --soft_lemma_size                       3
% 3.11/1.01  --prop_impl_unit_size                   0
% 3.11/1.01  --prop_impl_unit                        []
% 3.11/1.01  --share_sel_clauses                     true
% 3.11/1.01  --reset_solvers                         false
% 3.11/1.01  --bc_imp_inh                            [conj_cone]
% 3.11/1.01  --conj_cone_tolerance                   3.
% 3.11/1.01  --extra_neg_conj                        none
% 3.11/1.01  --large_theory_mode                     true
% 3.11/1.01  --prolific_symb_bound                   200
% 3.11/1.01  --lt_threshold                          2000
% 3.11/1.01  --clause_weak_htbl                      true
% 3.11/1.01  --gc_record_bc_elim                     false
% 3.11/1.01  
% 3.11/1.01  ------ Preprocessing Options
% 3.11/1.01  
% 3.11/1.01  --preprocessing_flag                    true
% 3.11/1.01  --time_out_prep_mult                    0.1
% 3.11/1.01  --splitting_mode                        input
% 3.11/1.01  --splitting_grd                         true
% 3.11/1.01  --splitting_cvd                         false
% 3.11/1.01  --splitting_cvd_svl                     false
% 3.11/1.01  --splitting_nvd                         32
% 3.11/1.01  --sub_typing                            true
% 3.11/1.01  --prep_gs_sim                           true
% 3.11/1.01  --prep_unflatten                        true
% 3.11/1.01  --prep_res_sim                          true
% 3.11/1.01  --prep_upred                            true
% 3.11/1.01  --prep_sem_filter                       exhaustive
% 3.11/1.01  --prep_sem_filter_out                   false
% 3.11/1.01  --pred_elim                             true
% 3.11/1.01  --res_sim_input                         true
% 3.11/1.01  --eq_ax_congr_red                       true
% 3.11/1.01  --pure_diseq_elim                       true
% 3.11/1.01  --brand_transform                       false
% 3.11/1.01  --non_eq_to_eq                          false
% 3.11/1.01  --prep_def_merge                        true
% 3.11/1.01  --prep_def_merge_prop_impl              false
% 3.11/1.01  --prep_def_merge_mbd                    true
% 3.11/1.01  --prep_def_merge_tr_red                 false
% 3.11/1.01  --prep_def_merge_tr_cl                  false
% 3.11/1.01  --smt_preprocessing                     true
% 3.11/1.01  --smt_ac_axioms                         fast
% 3.11/1.01  --preprocessed_out                      false
% 3.11/1.01  --preprocessed_stats                    false
% 3.11/1.01  
% 3.11/1.01  ------ Abstraction refinement Options
% 3.11/1.01  
% 3.11/1.01  --abstr_ref                             []
% 3.11/1.01  --abstr_ref_prep                        false
% 3.11/1.01  --abstr_ref_until_sat                   false
% 3.11/1.01  --abstr_ref_sig_restrict                funpre
% 3.11/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.11/1.01  --abstr_ref_under                       []
% 3.11/1.01  
% 3.11/1.01  ------ SAT Options
% 3.11/1.01  
% 3.11/1.01  --sat_mode                              false
% 3.11/1.01  --sat_fm_restart_options                ""
% 3.11/1.01  --sat_gr_def                            false
% 3.11/1.01  --sat_epr_types                         true
% 3.11/1.01  --sat_non_cyclic_types                  false
% 3.11/1.01  --sat_finite_models                     false
% 3.11/1.01  --sat_fm_lemmas                         false
% 3.11/1.01  --sat_fm_prep                           false
% 3.11/1.01  --sat_fm_uc_incr                        true
% 3.11/1.01  --sat_out_model                         small
% 3.11/1.01  --sat_out_clauses                       false
% 3.11/1.01  
% 3.11/1.01  ------ QBF Options
% 3.11/1.01  
% 3.11/1.01  --qbf_mode                              false
% 3.11/1.01  --qbf_elim_univ                         false
% 3.11/1.01  --qbf_dom_inst                          none
% 3.11/1.01  --qbf_dom_pre_inst                      false
% 3.11/1.01  --qbf_sk_in                             false
% 3.11/1.01  --qbf_pred_elim                         true
% 3.11/1.01  --qbf_split                             512
% 3.11/1.01  
% 3.11/1.01  ------ BMC1 Options
% 3.11/1.01  
% 3.11/1.01  --bmc1_incremental                      false
% 3.11/1.01  --bmc1_axioms                           reachable_all
% 3.11/1.01  --bmc1_min_bound                        0
% 3.11/1.01  --bmc1_max_bound                        -1
% 3.11/1.01  --bmc1_max_bound_default                -1
% 3.11/1.01  --bmc1_symbol_reachability              true
% 3.11/1.01  --bmc1_property_lemmas                  false
% 3.11/1.01  --bmc1_k_induction                      false
% 3.11/1.01  --bmc1_non_equiv_states                 false
% 3.11/1.01  --bmc1_deadlock                         false
% 3.11/1.01  --bmc1_ucm                              false
% 3.11/1.01  --bmc1_add_unsat_core                   none
% 3.11/1.01  --bmc1_unsat_core_children              false
% 3.11/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.11/1.01  --bmc1_out_stat                         full
% 3.11/1.01  --bmc1_ground_init                      false
% 3.11/1.01  --bmc1_pre_inst_next_state              false
% 3.11/1.01  --bmc1_pre_inst_state                   false
% 3.11/1.01  --bmc1_pre_inst_reach_state             false
% 3.11/1.01  --bmc1_out_unsat_core                   false
% 3.11/1.01  --bmc1_aig_witness_out                  false
% 3.11/1.01  --bmc1_verbose                          false
% 3.11/1.01  --bmc1_dump_clauses_tptp                false
% 3.11/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.11/1.01  --bmc1_dump_file                        -
% 3.11/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.11/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.11/1.01  --bmc1_ucm_extend_mode                  1
% 3.11/1.01  --bmc1_ucm_init_mode                    2
% 3.11/1.01  --bmc1_ucm_cone_mode                    none
% 3.11/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.11/1.01  --bmc1_ucm_relax_model                  4
% 3.11/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.11/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.11/1.01  --bmc1_ucm_layered_model                none
% 3.11/1.01  --bmc1_ucm_max_lemma_size               10
% 3.11/1.01  
% 3.11/1.01  ------ AIG Options
% 3.11/1.01  
% 3.11/1.01  --aig_mode                              false
% 3.11/1.01  
% 3.11/1.01  ------ Instantiation Options
% 3.11/1.01  
% 3.11/1.01  --instantiation_flag                    true
% 3.11/1.01  --inst_sos_flag                         false
% 3.11/1.01  --inst_sos_phase                        true
% 3.11/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.11/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.11/1.01  --inst_lit_sel_side                     none
% 3.11/1.01  --inst_solver_per_active                1400
% 3.11/1.01  --inst_solver_calls_frac                1.
% 3.11/1.01  --inst_passive_queue_type               priority_queues
% 3.11/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.11/1.01  --inst_passive_queues_freq              [25;2]
% 3.11/1.01  --inst_dismatching                      true
% 3.11/1.01  --inst_eager_unprocessed_to_passive     true
% 3.11/1.01  --inst_prop_sim_given                   true
% 3.11/1.01  --inst_prop_sim_new                     false
% 3.11/1.01  --inst_subs_new                         false
% 3.11/1.01  --inst_eq_res_simp                      false
% 3.11/1.01  --inst_subs_given                       false
% 3.11/1.01  --inst_orphan_elimination               true
% 3.11/1.01  --inst_learning_loop_flag               true
% 3.11/1.01  --inst_learning_start                   3000
% 3.11/1.01  --inst_learning_factor                  2
% 3.11/1.01  --inst_start_prop_sim_after_learn       3
% 3.11/1.01  --inst_sel_renew                        solver
% 3.11/1.01  --inst_lit_activity_flag                true
% 3.11/1.01  --inst_restr_to_given                   false
% 3.11/1.01  --inst_activity_threshold               500
% 3.11/1.01  --inst_out_proof                        true
% 3.11/1.01  
% 3.11/1.01  ------ Resolution Options
% 3.11/1.01  
% 3.11/1.01  --resolution_flag                       false
% 3.11/1.01  --res_lit_sel                           adaptive
% 3.11/1.01  --res_lit_sel_side                      none
% 3.11/1.01  --res_ordering                          kbo
% 3.11/1.01  --res_to_prop_solver                    active
% 3.11/1.01  --res_prop_simpl_new                    false
% 3.11/1.01  --res_prop_simpl_given                  true
% 3.11/1.01  --res_passive_queue_type                priority_queues
% 3.11/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.11/1.01  --res_passive_queues_freq               [15;5]
% 3.11/1.01  --res_forward_subs                      full
% 3.11/1.01  --res_backward_subs                     full
% 3.11/1.01  --res_forward_subs_resolution           true
% 3.11/1.01  --res_backward_subs_resolution          true
% 3.11/1.01  --res_orphan_elimination                true
% 3.11/1.01  --res_time_limit                        2.
% 3.11/1.01  --res_out_proof                         true
% 3.11/1.01  
% 3.11/1.01  ------ Superposition Options
% 3.11/1.01  
% 3.11/1.01  --superposition_flag                    true
% 3.11/1.01  --sup_passive_queue_type                priority_queues
% 3.11/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.11/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.11/1.01  --demod_completeness_check              fast
% 3.11/1.01  --demod_use_ground                      true
% 3.11/1.01  --sup_to_prop_solver                    passive
% 3.11/1.01  --sup_prop_simpl_new                    true
% 3.11/1.01  --sup_prop_simpl_given                  true
% 3.11/1.01  --sup_fun_splitting                     false
% 3.11/1.01  --sup_smt_interval                      50000
% 3.11/1.01  
% 3.11/1.01  ------ Superposition Simplification Setup
% 3.11/1.01  
% 3.11/1.01  --sup_indices_passive                   []
% 3.11/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.11/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.11/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.11/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.11/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.11/1.01  --sup_full_bw                           [BwDemod]
% 3.11/1.01  --sup_immed_triv                        [TrivRules]
% 3.11/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.11/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.11/1.01  --sup_immed_bw_main                     []
% 3.11/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.11/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.11/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.11/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.11/1.01  
% 3.11/1.01  ------ Combination Options
% 3.11/1.01  
% 3.11/1.01  --comb_res_mult                         3
% 3.11/1.01  --comb_sup_mult                         2
% 3.11/1.01  --comb_inst_mult                        10
% 3.11/1.01  
% 3.11/1.01  ------ Debug Options
% 3.11/1.01  
% 3.11/1.01  --dbg_backtrace                         false
% 3.11/1.01  --dbg_dump_prop_clauses                 false
% 3.11/1.01  --dbg_dump_prop_clauses_file            -
% 3.11/1.01  --dbg_out_stat                          false
% 3.11/1.01  
% 3.11/1.01  
% 3.11/1.01  
% 3.11/1.01  
% 3.11/1.01  ------ Proving...
% 3.11/1.01  
% 3.11/1.01  
% 3.11/1.01  % SZS status Theorem for theBenchmark.p
% 3.11/1.01  
% 3.11/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.11/1.01  
% 3.11/1.01  fof(f8,axiom,(
% 3.11/1.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.11/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.11/1.01  
% 3.11/1.01  fof(f20,plain,(
% 3.11/1.01    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.11/1.01    inference(ennf_transformation,[],[f8])).
% 3.11/1.01  
% 3.11/1.01  fof(f21,plain,(
% 3.11/1.01    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.11/1.01    inference(flattening,[],[f20])).
% 3.11/1.01  
% 3.11/1.01  fof(f49,plain,(
% 3.11/1.01    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.11/1.01    inference(cnf_transformation,[],[f21])).
% 3.11/1.01  
% 3.11/1.01  fof(f14,conjecture,(
% 3.11/1.01    ! [X0] : (l1_pre_topc(X0) => k2_pre_topc(X0,k2_struct_0(X0)) = k2_struct_0(X0))),
% 3.11/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.11/1.01  
% 3.11/1.01  fof(f15,negated_conjecture,(
% 3.11/1.01    ~! [X0] : (l1_pre_topc(X0) => k2_pre_topc(X0,k2_struct_0(X0)) = k2_struct_0(X0))),
% 3.11/1.01    inference(negated_conjecture,[],[f14])).
% 3.11/1.01  
% 3.11/1.01  fof(f27,plain,(
% 3.11/1.01    ? [X0] : (k2_pre_topc(X0,k2_struct_0(X0)) != k2_struct_0(X0) & l1_pre_topc(X0))),
% 3.11/1.01    inference(ennf_transformation,[],[f15])).
% 3.11/1.01  
% 3.11/1.01  fof(f35,plain,(
% 3.11/1.01    ? [X0] : (k2_pre_topc(X0,k2_struct_0(X0)) != k2_struct_0(X0) & l1_pre_topc(X0)) => (k2_pre_topc(sK1,k2_struct_0(sK1)) != k2_struct_0(sK1) & l1_pre_topc(sK1))),
% 3.11/1.01    introduced(choice_axiom,[])).
% 3.11/1.01  
% 3.11/1.01  fof(f36,plain,(
% 3.11/1.01    k2_pre_topc(sK1,k2_struct_0(sK1)) != k2_struct_0(sK1) & l1_pre_topc(sK1)),
% 3.11/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f35])).
% 3.11/1.01  
% 3.11/1.01  fof(f55,plain,(
% 3.11/1.01    l1_pre_topc(sK1)),
% 3.11/1.01    inference(cnf_transformation,[],[f36])).
% 3.11/1.01  
% 3.11/1.01  fof(f6,axiom,(
% 3.11/1.01    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.11/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.11/1.01  
% 3.11/1.01  fof(f34,plain,(
% 3.11/1.01    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.11/1.01    inference(nnf_transformation,[],[f6])).
% 3.11/1.01  
% 3.11/1.01  fof(f46,plain,(
% 3.11/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.11/1.01    inference(cnf_transformation,[],[f34])).
% 3.11/1.01  
% 3.11/1.01  fof(f12,axiom,(
% 3.11/1.01    ! [X0] : (l1_struct_0(X0) => k3_subset_1(u1_struct_0(X0),k1_struct_0(X0)) = k2_struct_0(X0))),
% 3.11/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.11/1.01  
% 3.11/1.01  fof(f25,plain,(
% 3.11/1.01    ! [X0] : (k3_subset_1(u1_struct_0(X0),k1_struct_0(X0)) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 3.11/1.01    inference(ennf_transformation,[],[f12])).
% 3.11/1.01  
% 3.11/1.01  fof(f53,plain,(
% 3.11/1.01    ( ! [X0] : (k3_subset_1(u1_struct_0(X0),k1_struct_0(X0)) = k2_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.11/1.01    inference(cnf_transformation,[],[f25])).
% 3.11/1.01  
% 3.11/1.01  fof(f10,axiom,(
% 3.11/1.01    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.11/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.11/1.01  
% 3.11/1.01  fof(f23,plain,(
% 3.11/1.01    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.11/1.01    inference(ennf_transformation,[],[f10])).
% 3.11/1.01  
% 3.11/1.01  fof(f51,plain,(
% 3.11/1.01    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.11/1.01    inference(cnf_transformation,[],[f23])).
% 3.11/1.01  
% 3.11/1.01  fof(f1,axiom,(
% 3.11/1.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.11/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.11/1.01  
% 3.11/1.01  fof(f16,plain,(
% 3.11/1.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.11/1.01    inference(ennf_transformation,[],[f1])).
% 3.11/1.01  
% 3.11/1.01  fof(f28,plain,(
% 3.11/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.11/1.01    inference(nnf_transformation,[],[f16])).
% 3.11/1.01  
% 3.11/1.01  fof(f29,plain,(
% 3.11/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.11/1.01    inference(rectify,[],[f28])).
% 3.11/1.01  
% 3.11/1.01  fof(f30,plain,(
% 3.11/1.01    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.11/1.01    introduced(choice_axiom,[])).
% 3.11/1.01  
% 3.11/1.01  fof(f31,plain,(
% 3.11/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.11/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).
% 3.11/1.01  
% 3.11/1.01  fof(f38,plain,(
% 3.11/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.11/1.01    inference(cnf_transformation,[],[f31])).
% 3.11/1.01  
% 3.11/1.01  fof(f2,axiom,(
% 3.11/1.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.11/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.11/1.01  
% 3.11/1.01  fof(f32,plain,(
% 3.11/1.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.11/1.01    inference(nnf_transformation,[],[f2])).
% 3.11/1.01  
% 3.11/1.01  fof(f33,plain,(
% 3.11/1.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.11/1.01    inference(flattening,[],[f32])).
% 3.11/1.01  
% 3.11/1.01  fof(f40,plain,(
% 3.11/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.11/1.01    inference(cnf_transformation,[],[f33])).
% 3.11/1.01  
% 3.11/1.01  fof(f58,plain,(
% 3.11/1.01    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.11/1.01    inference(equality_resolution,[],[f40])).
% 3.11/1.01  
% 3.11/1.01  fof(f11,axiom,(
% 3.11/1.01    ! [X0] : (l1_struct_0(X0) => v1_xboole_0(k1_struct_0(X0)))),
% 3.11/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.11/1.01  
% 3.11/1.01  fof(f24,plain,(
% 3.11/1.01    ! [X0] : (v1_xboole_0(k1_struct_0(X0)) | ~l1_struct_0(X0))),
% 3.11/1.01    inference(ennf_transformation,[],[f11])).
% 3.11/1.01  
% 3.11/1.01  fof(f52,plain,(
% 3.11/1.01    ( ! [X0] : (v1_xboole_0(k1_struct_0(X0)) | ~l1_struct_0(X0)) )),
% 3.11/1.01    inference(cnf_transformation,[],[f24])).
% 3.11/1.01  
% 3.11/1.01  fof(f7,axiom,(
% 3.11/1.01    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 3.11/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.11/1.01  
% 3.11/1.01  fof(f19,plain,(
% 3.11/1.01    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.11/1.01    inference(ennf_transformation,[],[f7])).
% 3.11/1.01  
% 3.11/1.01  fof(f48,plain,(
% 3.11/1.01    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.11/1.01    inference(cnf_transformation,[],[f19])).
% 3.11/1.01  
% 3.11/1.01  fof(f47,plain,(
% 3.11/1.01    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.11/1.01    inference(cnf_transformation,[],[f34])).
% 3.11/1.01  
% 3.11/1.01  fof(f5,axiom,(
% 3.11/1.01    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X2)) => r1_tarski(X2,k3_subset_1(X0,X1)))))),
% 3.11/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.11/1.01  
% 3.11/1.01  fof(f17,plain,(
% 3.11/1.01    ! [X0,X1] : (! [X2] : ((r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.11/1.01    inference(ennf_transformation,[],[f5])).
% 3.11/1.01  
% 3.11/1.01  fof(f18,plain,(
% 3.11/1.01    ! [X0,X1] : (! [X2] : (r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.11/1.01    inference(flattening,[],[f17])).
% 3.11/1.01  
% 3.11/1.01  fof(f45,plain,(
% 3.11/1.01    ( ! [X2,X0,X1] : (r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.11/1.01    inference(cnf_transformation,[],[f18])).
% 3.11/1.01  
% 3.11/1.01  fof(f9,axiom,(
% 3.11/1.01    ! [X0] : (l1_struct_0(X0) => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.11/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.11/1.01  
% 3.11/1.01  fof(f22,plain,(
% 3.11/1.01    ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0))),
% 3.11/1.01    inference(ennf_transformation,[],[f9])).
% 3.11/1.01  
% 3.11/1.01  fof(f50,plain,(
% 3.11/1.01    ( ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0)) )),
% 3.11/1.01    inference(cnf_transformation,[],[f22])).
% 3.11/1.01  
% 3.11/1.01  fof(f13,axiom,(
% 3.11/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 3.11/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.11/1.01  
% 3.11/1.01  fof(f26,plain,(
% 3.11/1.01    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.11/1.01    inference(ennf_transformation,[],[f13])).
% 3.11/1.01  
% 3.11/1.01  fof(f54,plain,(
% 3.11/1.01    ( ! [X0,X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.11/1.01    inference(cnf_transformation,[],[f26])).
% 3.11/1.01  
% 3.11/1.01  fof(f42,plain,(
% 3.11/1.01    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.11/1.01    inference(cnf_transformation,[],[f33])).
% 3.11/1.01  
% 3.11/1.01  fof(f56,plain,(
% 3.11/1.01    k2_pre_topc(sK1,k2_struct_0(sK1)) != k2_struct_0(sK1)),
% 3.11/1.01    inference(cnf_transformation,[],[f36])).
% 3.11/1.01  
% 3.11/1.01  cnf(c_12,plain,
% 3.11/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.11/1.01      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.11/1.01      | ~ l1_pre_topc(X1) ),
% 3.11/1.01      inference(cnf_transformation,[],[f49]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_19,negated_conjecture,
% 3.11/1.01      ( l1_pre_topc(sK1) ),
% 3.11/1.01      inference(cnf_transformation,[],[f55]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_284,plain,
% 3.11/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.11/1.01      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.11/1.01      | sK1 != X1 ),
% 3.11/1.01      inference(resolution_lifted,[status(thm)],[c_12,c_19]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_285,plain,
% 3.11/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.11/1.01      | m1_subset_1(k2_pre_topc(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 3.11/1.01      inference(unflattening,[status(thm)],[c_284]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_818,plain,
% 3.11/1.01      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.11/1.01      | m1_subset_1(k2_pre_topc(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 3.11/1.01      inference(predicate_to_equality,[status(thm)],[c_285]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_10,plain,
% 3.11/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.11/1.01      inference(cnf_transformation,[],[f46]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_820,plain,
% 3.11/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.11/1.01      | r1_tarski(X0,X1) = iProver_top ),
% 3.11/1.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_1355,plain,
% 3.11/1.01      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.11/1.01      | r1_tarski(k2_pre_topc(sK1,X0),u1_struct_0(sK1)) = iProver_top ),
% 3.11/1.01      inference(superposition,[status(thm)],[c_818,c_820]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_16,plain,
% 3.11/1.01      ( ~ l1_struct_0(X0)
% 3.11/1.01      | k3_subset_1(u1_struct_0(X0),k1_struct_0(X0)) = k2_struct_0(X0) ),
% 3.11/1.01      inference(cnf_transformation,[],[f53]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_14,plain,
% 3.11/1.01      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 3.11/1.01      inference(cnf_transformation,[],[f51]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_265,plain,
% 3.11/1.01      ( l1_struct_0(X0) | sK1 != X0 ),
% 3.11/1.01      inference(resolution_lifted,[status(thm)],[c_14,c_19]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_266,plain,
% 3.11/1.01      ( l1_struct_0(sK1) ),
% 3.11/1.01      inference(unflattening,[status(thm)],[c_265]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_304,plain,
% 3.11/1.01      ( k3_subset_1(u1_struct_0(X0),k1_struct_0(X0)) = k2_struct_0(X0)
% 3.11/1.01      | sK1 != X0 ),
% 3.11/1.01      inference(resolution_lifted,[status(thm)],[c_16,c_266]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_305,plain,
% 3.11/1.01      ( k3_subset_1(u1_struct_0(sK1),k1_struct_0(sK1)) = k2_struct_0(sK1) ),
% 3.11/1.01      inference(unflattening,[status(thm)],[c_304]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_1,plain,
% 3.11/1.01      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.11/1.01      inference(cnf_transformation,[],[f38]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_826,plain,
% 3.11/1.01      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 3.11/1.01      | r1_tarski(X0,X1) = iProver_top ),
% 3.11/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_5,plain,
% 3.11/1.01      ( r1_tarski(X0,X0) ),
% 3.11/1.01      inference(cnf_transformation,[],[f58]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_823,plain,
% 3.11/1.01      ( r1_tarski(X0,X0) = iProver_top ),
% 3.11/1.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_15,plain,
% 3.11/1.01      ( ~ l1_struct_0(X0) | v1_xboole_0(k1_struct_0(X0)) ),
% 3.11/1.01      inference(cnf_transformation,[],[f52]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_11,plain,
% 3.11/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.11/1.01      | ~ r2_hidden(X2,X0)
% 3.11/1.01      | ~ v1_xboole_0(X1) ),
% 3.11/1.01      inference(cnf_transformation,[],[f48]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_9,plain,
% 3.11/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.11/1.01      inference(cnf_transformation,[],[f47]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_144,plain,
% 3.11/1.01      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.11/1.01      inference(prop_impl,[status(thm)],[c_9]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_145,plain,
% 3.11/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.11/1.01      inference(renaming,[status(thm)],[c_144]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_180,plain,
% 3.11/1.01      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X2) | ~ v1_xboole_0(X2) ),
% 3.11/1.01      inference(bin_hyper_res,[status(thm)],[c_11,c_145]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_246,plain,
% 3.11/1.01      ( ~ r2_hidden(X0,X1)
% 3.11/1.01      | ~ r1_tarski(X1,X2)
% 3.11/1.01      | ~ l1_struct_0(X3)
% 3.11/1.01      | k1_struct_0(X3) != X2 ),
% 3.11/1.01      inference(resolution_lifted,[status(thm)],[c_15,c_180]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_247,plain,
% 3.11/1.01      ( ~ r2_hidden(X0,X1)
% 3.11/1.01      | ~ r1_tarski(X1,k1_struct_0(X2))
% 3.11/1.01      | ~ l1_struct_0(X2) ),
% 3.11/1.01      inference(unflattening,[status(thm)],[c_246]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_316,plain,
% 3.11/1.01      ( ~ r2_hidden(X0,X1)
% 3.11/1.01      | ~ r1_tarski(X1,k1_struct_0(X2))
% 3.11/1.01      | sK1 != X2 ),
% 3.11/1.01      inference(resolution_lifted,[status(thm)],[c_266,c_247]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_317,plain,
% 3.11/1.01      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,k1_struct_0(sK1)) ),
% 3.11/1.01      inference(unflattening,[status(thm)],[c_316]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_816,plain,
% 3.11/1.01      ( r2_hidden(X0,X1) != iProver_top
% 3.11/1.01      | r1_tarski(X1,k1_struct_0(sK1)) != iProver_top ),
% 3.11/1.01      inference(predicate_to_equality,[status(thm)],[c_317]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_1247,plain,
% 3.11/1.01      ( r2_hidden(X0,k1_struct_0(sK1)) != iProver_top ),
% 3.11/1.01      inference(superposition,[status(thm)],[c_823,c_816]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_2033,plain,
% 3.11/1.01      ( r1_tarski(k1_struct_0(sK1),X0) = iProver_top ),
% 3.11/1.01      inference(superposition,[status(thm)],[c_826,c_1247]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_8,plain,
% 3.11/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.11/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.11/1.01      | ~ r1_tarski(X2,k3_subset_1(X1,X0))
% 3.11/1.01      | r1_tarski(X0,k3_subset_1(X1,X2)) ),
% 3.11/1.01      inference(cnf_transformation,[],[f45]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_177,plain,
% 3.11/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.11/1.01      | ~ r1_tarski(X2,X1)
% 3.11/1.01      | ~ r1_tarski(X0,k3_subset_1(X1,X2))
% 3.11/1.01      | r1_tarski(X2,k3_subset_1(X1,X0)) ),
% 3.11/1.01      inference(bin_hyper_res,[status(thm)],[c_8,c_145]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_382,plain,
% 3.11/1.01      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.11/1.01      inference(prop_impl,[status(thm)],[c_9]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_383,plain,
% 3.11/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.11/1.01      inference(renaming,[status(thm)],[c_382]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_410,plain,
% 3.11/1.01      ( ~ r1_tarski(X0,X1)
% 3.11/1.01      | ~ r1_tarski(X2,X1)
% 3.11/1.01      | ~ r1_tarski(X0,k3_subset_1(X1,X2))
% 3.11/1.01      | r1_tarski(X2,k3_subset_1(X1,X0)) ),
% 3.11/1.01      inference(bin_hyper_res,[status(thm)],[c_177,c_383]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_815,plain,
% 3.11/1.01      ( r1_tarski(X0,X1) != iProver_top
% 3.11/1.01      | r1_tarski(X2,X1) != iProver_top
% 3.11/1.01      | r1_tarski(X0,k3_subset_1(X1,X2)) != iProver_top
% 3.11/1.01      | r1_tarski(X2,k3_subset_1(X1,X0)) = iProver_top ),
% 3.11/1.01      inference(predicate_to_equality,[status(thm)],[c_410]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_2266,plain,
% 3.11/1.01      ( r1_tarski(X0,X1) != iProver_top
% 3.11/1.01      | r1_tarski(X0,k3_subset_1(X1,k1_struct_0(sK1))) = iProver_top
% 3.11/1.01      | r1_tarski(k1_struct_0(sK1),X1) != iProver_top ),
% 3.11/1.01      inference(superposition,[status(thm)],[c_2033,c_815]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_2271,plain,
% 3.11/1.01      ( r1_tarski(X0,X1) != iProver_top
% 3.11/1.01      | r1_tarski(X0,k3_subset_1(X1,k1_struct_0(sK1))) = iProver_top ),
% 3.11/1.01      inference(forward_subsumption_resolution,
% 3.11/1.01                [status(thm)],
% 3.11/1.01                [c_2266,c_2033]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_2631,plain,
% 3.11/1.01      ( r1_tarski(X0,k2_struct_0(sK1)) = iProver_top
% 3.11/1.01      | r1_tarski(X0,u1_struct_0(sK1)) != iProver_top ),
% 3.11/1.01      inference(superposition,[status(thm)],[c_305,c_2271]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_3177,plain,
% 3.11/1.01      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.11/1.01      | r1_tarski(k2_pre_topc(sK1,X0),k2_struct_0(sK1)) = iProver_top ),
% 3.11/1.01      inference(superposition,[status(thm)],[c_1355,c_2631]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_13,plain,
% 3.11/1.01      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 3.11/1.01      | ~ l1_struct_0(X0) ),
% 3.11/1.01      inference(cnf_transformation,[],[f50]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_309,plain,
% 3.11/1.01      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 3.11/1.01      | sK1 != X0 ),
% 3.11/1.01      inference(resolution_lifted,[status(thm)],[c_13,c_266]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_310,plain,
% 3.11/1.01      ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 3.11/1.01      inference(unflattening,[status(thm)],[c_309]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_817,plain,
% 3.11/1.01      ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 3.11/1.01      inference(predicate_to_equality,[status(thm)],[c_310]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_17,plain,
% 3.11/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.11/1.01      | r1_tarski(X0,k2_pre_topc(X1,X0))
% 3.11/1.01      | ~ l1_pre_topc(X1) ),
% 3.11/1.01      inference(cnf_transformation,[],[f54]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_272,plain,
% 3.11/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.11/1.01      | r1_tarski(X0,k2_pre_topc(X1,X0))
% 3.11/1.01      | sK1 != X1 ),
% 3.11/1.01      inference(resolution_lifted,[status(thm)],[c_17,c_19]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_273,plain,
% 3.11/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.11/1.01      | r1_tarski(X0,k2_pre_topc(sK1,X0)) ),
% 3.11/1.01      inference(unflattening,[status(thm)],[c_272]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_819,plain,
% 3.11/1.01      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.11/1.01      | r1_tarski(X0,k2_pre_topc(sK1,X0)) = iProver_top ),
% 3.11/1.01      inference(predicate_to_equality,[status(thm)],[c_273]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_1055,plain,
% 3.11/1.01      ( r1_tarski(k2_struct_0(sK1),k2_pre_topc(sK1,k2_struct_0(sK1))) = iProver_top ),
% 3.11/1.01      inference(superposition,[status(thm)],[c_817,c_819]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_3,plain,
% 3.11/1.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.11/1.01      inference(cnf_transformation,[],[f42]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_824,plain,
% 3.11/1.01      ( X0 = X1
% 3.11/1.01      | r1_tarski(X1,X0) != iProver_top
% 3.11/1.01      | r1_tarski(X0,X1) != iProver_top ),
% 3.11/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_1834,plain,
% 3.11/1.01      ( k2_pre_topc(sK1,k2_struct_0(sK1)) = k2_struct_0(sK1)
% 3.11/1.01      | r1_tarski(k2_pre_topc(sK1,k2_struct_0(sK1)),k2_struct_0(sK1)) != iProver_top ),
% 3.11/1.01      inference(superposition,[status(thm)],[c_1055,c_824]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_20,plain,
% 3.11/1.01      ( l1_pre_topc(sK1) = iProver_top ),
% 3.11/1.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_18,negated_conjecture,
% 3.11/1.01      ( k2_pre_topc(sK1,k2_struct_0(sK1)) != k2_struct_0(sK1) ),
% 3.11/1.01      inference(cnf_transformation,[],[f56]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_30,plain,
% 3.11/1.01      ( l1_struct_0(X0) = iProver_top | l1_pre_topc(X0) != iProver_top ),
% 3.11/1.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_32,plain,
% 3.11/1.01      ( l1_struct_0(sK1) = iProver_top
% 3.11/1.01      | l1_pre_topc(sK1) != iProver_top ),
% 3.11/1.01      inference(instantiation,[status(thm)],[c_30]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_33,plain,
% 3.11/1.01      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 3.11/1.01      | l1_struct_0(X0) != iProver_top ),
% 3.11/1.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_35,plain,
% 3.11/1.01      ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 3.11/1.01      | l1_struct_0(sK1) != iProver_top ),
% 3.11/1.01      inference(instantiation,[status(thm)],[c_33]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_920,plain,
% 3.11/1.01      ( ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
% 3.11/1.01      | r1_tarski(k2_struct_0(sK1),k2_pre_topc(sK1,k2_struct_0(sK1))) ),
% 3.11/1.01      inference(instantiation,[status(thm)],[c_273]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_924,plain,
% 3.11/1.01      ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.11/1.01      | r1_tarski(k2_struct_0(sK1),k2_pre_topc(sK1,k2_struct_0(sK1))) = iProver_top ),
% 3.11/1.01      inference(predicate_to_equality,[status(thm)],[c_920]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_928,plain,
% 3.11/1.01      ( ~ r1_tarski(k2_pre_topc(sK1,k2_struct_0(sK1)),k2_struct_0(sK1))
% 3.11/1.01      | ~ r1_tarski(k2_struct_0(sK1),k2_pre_topc(sK1,k2_struct_0(sK1)))
% 3.11/1.01      | k2_pre_topc(sK1,k2_struct_0(sK1)) = k2_struct_0(sK1) ),
% 3.11/1.01      inference(instantiation,[status(thm)],[c_3]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_929,plain,
% 3.11/1.01      ( k2_pre_topc(sK1,k2_struct_0(sK1)) = k2_struct_0(sK1)
% 3.11/1.01      | r1_tarski(k2_pre_topc(sK1,k2_struct_0(sK1)),k2_struct_0(sK1)) != iProver_top
% 3.11/1.01      | r1_tarski(k2_struct_0(sK1),k2_pre_topc(sK1,k2_struct_0(sK1))) != iProver_top ),
% 3.11/1.01      inference(predicate_to_equality,[status(thm)],[c_928]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_2352,plain,
% 3.11/1.01      ( r1_tarski(k2_pre_topc(sK1,k2_struct_0(sK1)),k2_struct_0(sK1)) != iProver_top ),
% 3.11/1.01      inference(global_propositional_subsumption,
% 3.11/1.01                [status(thm)],
% 3.11/1.01                [c_1834,c_20,c_18,c_32,c_35,c_924,c_929]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_3469,plain,
% 3.11/1.01      ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 3.11/1.01      inference(superposition,[status(thm)],[c_3177,c_2352]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(contradiction,plain,
% 3.11/1.01      ( $false ),
% 3.11/1.01      inference(minisat,[status(thm)],[c_3469,c_35,c_32,c_20]) ).
% 3.11/1.01  
% 3.11/1.01  
% 3.11/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.11/1.01  
% 3.11/1.01  ------                               Statistics
% 3.11/1.01  
% 3.11/1.01  ------ General
% 3.11/1.01  
% 3.11/1.01  abstr_ref_over_cycles:                  0
% 3.11/1.01  abstr_ref_under_cycles:                 0
% 3.11/1.01  gc_basic_clause_elim:                   0
% 3.11/1.01  forced_gc_time:                         0
% 3.11/1.01  parsing_time:                           0.007
% 3.11/1.01  unif_index_cands_time:                  0.
% 3.11/1.01  unif_index_add_time:                    0.
% 3.11/1.01  orderings_time:                         0.
% 3.11/1.01  out_proof_time:                         0.01
% 3.11/1.01  total_time:                             0.142
% 3.11/1.01  num_of_symbols:                         46
% 3.11/1.01  num_of_terms:                           3474
% 3.11/1.01  
% 3.11/1.01  ------ Preprocessing
% 3.11/1.01  
% 3.11/1.01  num_of_splits:                          0
% 3.11/1.01  num_of_split_atoms:                     0
% 3.11/1.01  num_of_reused_defs:                     0
% 3.11/1.01  num_eq_ax_congr_red:                    18
% 3.11/1.01  num_of_sem_filtered_clauses:            1
% 3.11/1.01  num_of_subtypes:                        0
% 3.11/1.01  monotx_restored_types:                  0
% 3.11/1.01  sat_num_of_epr_types:                   0
% 3.11/1.01  sat_num_of_non_cyclic_types:            0
% 3.11/1.01  sat_guarded_non_collapsed_types:        0
% 3.11/1.01  num_pure_diseq_elim:                    0
% 3.11/1.01  simp_replaced_by:                       0
% 3.11/1.01  res_preprocessed:                       90
% 3.11/1.01  prep_upred:                             0
% 3.11/1.01  prep_unflattend:                        7
% 3.11/1.01  smt_new_axioms:                         0
% 3.11/1.01  pred_elim_cands:                        3
% 3.11/1.01  pred_elim:                              3
% 3.11/1.01  pred_elim_cl:                           3
% 3.11/1.01  pred_elim_cycles:                       5
% 3.11/1.01  merged_defs:                            8
% 3.11/1.01  merged_defs_ncl:                        0
% 3.11/1.01  bin_hyper_res:                          11
% 3.11/1.01  prep_cycles:                            4
% 3.11/1.01  pred_elim_time:                         0.002
% 3.11/1.01  splitting_time:                         0.
% 3.11/1.01  sem_filter_time:                        0.
% 3.11/1.01  monotx_time:                            0.
% 3.11/1.01  subtype_inf_time:                       0.
% 3.11/1.01  
% 3.11/1.01  ------ Problem properties
% 3.11/1.01  
% 3.11/1.01  clauses:                                16
% 3.11/1.01  conjectures:                            1
% 3.11/1.01  epr:                                    3
% 3.11/1.01  horn:                                   15
% 3.11/1.01  ground:                                 3
% 3.11/1.01  unary:                                  6
% 3.11/1.01  binary:                                 7
% 3.11/1.01  lits:                                   30
% 3.11/1.01  lits_eq:                                4
% 3.11/1.01  fd_pure:                                0
% 3.11/1.01  fd_pseudo:                              0
% 3.11/1.01  fd_cond:                                0
% 3.11/1.01  fd_pseudo_cond:                         1
% 3.11/1.01  ac_symbols:                             0
% 3.11/1.01  
% 3.11/1.01  ------ Propositional Solver
% 3.11/1.01  
% 3.11/1.01  prop_solver_calls:                      27
% 3.11/1.01  prop_fast_solver_calls:                 483
% 3.11/1.01  smt_solver_calls:                       0
% 3.11/1.01  smt_fast_solver_calls:                  0
% 3.11/1.01  prop_num_of_clauses:                    1372
% 3.11/1.01  prop_preprocess_simplified:             4223
% 3.11/1.01  prop_fo_subsumed:                       3
% 3.11/1.01  prop_solver_time:                       0.
% 3.11/1.01  smt_solver_time:                        0.
% 3.11/1.01  smt_fast_solver_time:                   0.
% 3.11/1.01  prop_fast_solver_time:                  0.
% 3.11/1.01  prop_unsat_core_time:                   0.
% 3.11/1.01  
% 3.11/1.01  ------ QBF
% 3.11/1.01  
% 3.11/1.01  qbf_q_res:                              0
% 3.11/1.01  qbf_num_tautologies:                    0
% 3.11/1.01  qbf_prep_cycles:                        0
% 3.11/1.01  
% 3.11/1.01  ------ BMC1
% 3.11/1.01  
% 3.11/1.01  bmc1_current_bound:                     -1
% 3.11/1.01  bmc1_last_solved_bound:                 -1
% 3.11/1.01  bmc1_unsat_core_size:                   -1
% 3.11/1.01  bmc1_unsat_core_parents_size:           -1
% 3.11/1.01  bmc1_merge_next_fun:                    0
% 3.11/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.11/1.01  
% 3.11/1.01  ------ Instantiation
% 3.11/1.01  
% 3.11/1.01  inst_num_of_clauses:                    430
% 3.11/1.01  inst_num_in_passive:                    57
% 3.11/1.01  inst_num_in_active:                     191
% 3.11/1.01  inst_num_in_unprocessed:                182
% 3.11/1.01  inst_num_of_loops:                      210
% 3.11/1.01  inst_num_of_learning_restarts:          0
% 3.11/1.01  inst_num_moves_active_passive:          17
% 3.11/1.01  inst_lit_activity:                      0
% 3.11/1.01  inst_lit_activity_moves:                0
% 3.11/1.01  inst_num_tautologies:                   0
% 3.11/1.01  inst_num_prop_implied:                  0
% 3.11/1.01  inst_num_existing_simplified:           0
% 3.11/1.01  inst_num_eq_res_simplified:             0
% 3.11/1.01  inst_num_child_elim:                    0
% 3.11/1.01  inst_num_of_dismatching_blockings:      78
% 3.11/1.01  inst_num_of_non_proper_insts:           306
% 3.11/1.01  inst_num_of_duplicates:                 0
% 3.11/1.01  inst_inst_num_from_inst_to_res:         0
% 3.11/1.01  inst_dismatching_checking_time:         0.
% 3.11/1.01  
% 3.11/1.01  ------ Resolution
% 3.11/1.01  
% 3.11/1.01  res_num_of_clauses:                     0
% 3.11/1.01  res_num_in_passive:                     0
% 3.11/1.01  res_num_in_active:                      0
% 3.11/1.01  res_num_of_loops:                       94
% 3.11/1.01  res_forward_subset_subsumed:            50
% 3.11/1.01  res_backward_subset_subsumed:           0
% 3.11/1.01  res_forward_subsumed:                   0
% 3.11/1.01  res_backward_subsumed:                  0
% 3.11/1.01  res_forward_subsumption_resolution:     0
% 3.11/1.01  res_backward_subsumption_resolution:    0
% 3.11/1.01  res_clause_to_clause_subsumption:       338
% 3.11/1.01  res_orphan_elimination:                 0
% 3.11/1.01  res_tautology_del:                      46
% 3.11/1.01  res_num_eq_res_simplified:              0
% 3.11/1.01  res_num_sel_changes:                    0
% 3.11/1.01  res_moves_from_active_to_pass:          0
% 3.11/1.01  
% 3.11/1.01  ------ Superposition
% 3.11/1.01  
% 3.11/1.01  sup_time_total:                         0.
% 3.11/1.01  sup_time_generating:                    0.
% 3.11/1.01  sup_time_sim_full:                      0.
% 3.11/1.01  sup_time_sim_immed:                     0.
% 3.11/1.01  
% 3.11/1.01  sup_num_of_clauses:                     57
% 3.11/1.01  sup_num_in_active:                      39
% 3.11/1.01  sup_num_in_passive:                     18
% 3.11/1.01  sup_num_of_loops:                       41
% 3.11/1.01  sup_fw_superposition:                   48
% 3.11/1.01  sup_bw_superposition:                   34
% 3.11/1.01  sup_immediate_simplified:               18
% 3.11/1.01  sup_given_eliminated:                   1
% 3.11/1.01  comparisons_done:                       0
% 3.11/1.01  comparisons_avoided:                    0
% 3.11/1.01  
% 3.11/1.01  ------ Simplifications
% 3.11/1.01  
% 3.11/1.01  
% 3.11/1.01  sim_fw_subset_subsumed:                 4
% 3.11/1.01  sim_bw_subset_subsumed:                 2
% 3.11/1.01  sim_fw_subsumed:                        10
% 3.11/1.01  sim_bw_subsumed:                        1
% 3.11/1.01  sim_fw_subsumption_res:                 1
% 3.11/1.01  sim_bw_subsumption_res:                 0
% 3.11/1.01  sim_tautology_del:                      6
% 3.11/1.01  sim_eq_tautology_del:                   5
% 3.11/1.01  sim_eq_res_simp:                        0
% 3.11/1.01  sim_fw_demodulated:                     1
% 3.11/1.01  sim_bw_demodulated:                     2
% 3.11/1.01  sim_light_normalised:                   6
% 3.11/1.01  sim_joinable_taut:                      0
% 3.11/1.01  sim_joinable_simp:                      0
% 3.11/1.01  sim_ac_normalised:                      0
% 3.11/1.01  sim_smt_subsumption:                    0
% 3.11/1.01  
%------------------------------------------------------------------------------
